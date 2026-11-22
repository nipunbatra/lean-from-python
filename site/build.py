#!/usr/bin/env python3
"""Turn the lesson .lean files into a static, notebook-style website.

The .lean files are the single source of truth:
  * `/-! ... -/` doc comments become markdown (text) cells,
  * the Lean code between them becomes code cells,
  * a doc comment starting with `@exercise` / `@solution` marks the next code cell.

Every code cell gets an "Open in playground" link to https://live.lean-lang.org
that contains all the ordinary code cells before it, so it runs like a Jupyter
kernel. `#eval` / `#check` outputs are captured by running `lean --json` on each
file, so what the page shows is what Lean really printed.

Usage:  python3 site/build.py [--check]  (writes docs/; --check compiles every Run link)
No third-party Python packages needed.
"""
from __future__ import annotations

import html
import json
import re
import subprocess
import sys
import urllib.parse
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "LeanBasics"
OUT = ROOT / "docs"
PLAYGROUND = "https://live.lean-lang.org/#code="
REPO_URL = "https://github.com/nipunbatra/lean-from-python"


# ----------------------------------------------------------------------------
# Parsing lesson files into cells
# ----------------------------------------------------------------------------

@dataclass
class Cell:
    kind: str                 # "md" | "code"
    text: str
    role: str = "normal"      # for code: "normal" | "exercise" | "solution"
    start_line: int = 0       # 1-based, code cells only
    end_line: int = 0
    outputs: list = field(default_factory=list)   # (source_line_text, message)


def parse_cells(path: Path) -> list[Cell]:
    lines = path.read_text().split("\n")
    cells: list[Cell] = []
    code_buf: list[tuple[int, str]] = []
    pending_role = "normal"

    def flush_code():
        nonlocal code_buf, pending_role
        # trim blank lines at both ends
        while code_buf and not code_buf[0][1].strip():
            code_buf.pop(0)
        while code_buf and not code_buf[-1][1].strip():
            code_buf.pop()
        if code_buf:
            cells.append(Cell("code", "\n".join(t for _, t in code_buf), pending_role,
                              code_buf[0][0], code_buf[-1][0]))
            pending_role = "normal"
        code_buf = []

    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("/-!"):
            flush_code()
            body = [line[3:]]
            while "-/" not in body[-1]:
                i += 1
                body.append(lines[i])
            body[-1] = body[-1][: body[-1].rindex("-/")]
            text = "\n".join(body).strip()
            m = re.match(r"@(exercise|solution)\b", text)
            if m:
                pending_role = m.group(1)
                text = text[m.end():].strip()
            if text:
                cells.append(Cell("md", text, role=pending_role))
        else:
            code_buf.append((i + 1, line))
        i += 1
    flush_code()
    return cells


def attach_outputs(path: Path, cells: list[Cell]) -> list[str]:
    """Run Lean on the file; attach info messages to their code cells.
    Returns a list of error strings (should be empty)."""
    proc = subprocess.run(["lake", "env", "lean", "--json", str(path)],
                          cwd=ROOT, capture_output=True, text=True)
    lines = path.read_text().split("\n")
    errors = []
    for raw in proc.stdout.splitlines():
        try:
            msg = json.loads(raw)
        except json.JSONDecodeError:
            continue
        line = msg["pos"]["line"]
        if msg["severity"] == "error":
            errors.append(f"{path.name}:{line}: {msg['data']}")
            continue
        if msg["severity"] != "information":
            continue  # skip `sorry` warnings in exercises
        for c in cells:
            if c.kind == "code" and c.start_line <= line <= c.end_line:
                src = lines[line - 1].split("--")[0].rstrip()
                c.outputs.append((src, msg["data"].strip()))
                break
    if proc.returncode != 0 and not errors:
        errors.append(f"{path.name}: lean exited {proc.returncode}: {proc.stderr[:500]}")
    return errors


# ----------------------------------------------------------------------------
# A tiny markdown renderer (headings, lists, tables, code, inline styles)
# ----------------------------------------------------------------------------

def inline(s: str) -> str:
    parts = re.split(r"(`[^`]+`)", s)
    out = []
    for p in parts:
        if p.startswith("`") and p.endswith("`") and len(p) > 1:
            out.append(f"<code>{html.escape(p[1:-1])}</code>")
            continue
        p = html.escape(p, quote=False)
        p = re.sub(r"\[([^\]]+)\]\(([^)]+)\)",
                   r'<a href="\2" target="_blank" rel="noopener">\1</a>', p)
        p = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", p)
        p = re.sub(r"(?<![\w*])\*([^*\s][^*]*?)\*(?![\w*])", r"<em>\1</em>", p)
        out.append(p)
    return "".join(out)


def split_row(row: str) -> list[str]:
    row = row.strip().strip("|")
    cells = re.split(r"(?<!\\)\|", row)
    return [c.strip().replace("\\|", "|") for c in cells]


def markdown(md: str) -> str:
    lines = md.split("\n")
    out: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        s = line.strip()
        if not s:
            i += 1
            continue
        if s.startswith("```"):
            lang = s[3:].strip() or "text"
            i += 1
            buf = []
            while i < len(lines) and not lines[i].strip().startswith("```"):
                buf.append(lines[i])
                i += 1
            i += 1
            code = "\n".join(buf)
            body = highlight_lean(code) if lang == "lean" else html.escape(code)
            out.append(f'<pre class="snippet lang-{lang}"><span class="snippet-lang">{lang}</span>'
                       f"<code>{body}</code></pre>")
            continue
        m = re.match(r"(#{1,4})\s+(.*)", s)
        if m:
            n = len(m.group(1))
            text = inline(m.group(2))
            slug = re.sub(r"[^a-z0-9]+", "-", re.sub(r"<[^>]+>", "", text).lower()).strip("-")
            out.append(f'<h{n} id="{slug}">{text}</h{n}>')
            i += 1
            continue
        if s.startswith("|"):
            rows = []
            while i < len(lines) and lines[i].strip().startswith("|"):
                rows.append(lines[i])
                i += 1
            head = split_row(rows[0])
            body = [split_row(r) for r in rows[2:]]
            t = ["<div class='table-wrap'><table><thead><tr>"]
            t += [f"<th>{inline(h)}</th>" for h in head]
            t.append("</tr></thead><tbody>")
            for r in body:
                t.append("<tr>" + "".join(f"<td>{inline(c)}</td>" for c in r) + "</tr>")
            t.append("</tbody></table></div>")
            out.append("".join(t))
            continue
        if re.match(r"[-*]\s+", s) or re.match(r"\d+\.\s+", s):
            ordered = bool(re.match(r"\d+\.\s+", s))
            pat = r"\d+\.\s+" if ordered else r"[-*]\s+"
            items: list[str] = []
            while i < len(lines) and lines[i].strip():
                l = lines[i].strip()
                if re.match(pat, l):
                    items.append(re.sub("^" + pat, "", l))
                else:
                    items[-1] += " " + l
                i += 1
            tag = "ol" if ordered else "ul"
            out.append(f"<{tag}>" + "".join(f"<li>{inline(x)}</li>" for x in items) + f"</{tag}>")
            continue
        buf = []
        while i < len(lines) and lines[i].strip() and not re.match(
                r"(#{1,4}\s|```|\||[-*]\s|\d+\.\s)", lines[i].strip()):
            buf.append(lines[i].strip())
            i += 1
        out.append(f"<p>{inline(' '.join(buf))}</p>")
    return "\n".join(out)


# ----------------------------------------------------------------------------
# Lean syntax highlighting
# ----------------------------------------------------------------------------

KEYWORDS = {"def", "theorem", "example", "lemma", "fun", "let", "have", "if", "then", "else",
            "match", "with", "structure", "inductive", "where", "deriving", "by", "do",
            "namespace", "end", "open", "import", "calc", "show", "from", "at",
            "generalizing", "instance", "class", "abbrev", "termination_by"}
TACTICS = {"rfl", "rw", "simp", "omega", "grind", "decide", "exact", "intro", "apply",
           "induction", "cases", "rcases", "obtain", "constructor", "left", "right",
           "unfold", "sorry", "exists", "exfalso", "subst", "contradiction", "simp_all",
           "assumption", "use", "refine", "specialize", "norm_num", "ring", "linarith",
           "exact?", "trivial", "nofun", "nomatch"}
TYPES = {"Nat", "Int", "List", "Prop", "String", "Bool", "Type", "True", "False", "IO",
         "Unit", "Option", "Array", "Float"}

TOKEN = re.compile(r"""
  (?P<comment>--[^\n]*|/-[\s\S]*?-/)
| (?P<string>s?!?"(?:\\.|[^"\\])*")
| (?P<command>\#[a-zA-Z]+)
| (?P<number>\b\d+\b)
| (?P<word>[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'.α-ωΑ-Ω?!]*)
| (?P<sym>[∀∃→↔∧∨¬⊢≤≥≠∣⟨⟩·×]|:=|=>|\|)
""", re.VERBOSE)


def highlight_lean(code: str) -> str:
    out, pos = [], 0
    for m in TOKEN.finditer(code):
        out.append(html.escape(code[pos:m.start()]))
        text, kind = m.group(0), m.lastgroup
        esc = html.escape(text)
        if kind == "word":
            base = text.split(".")[0]
            if text in KEYWORDS:
                esc = f'<span class="k">{esc}</span>'
            elif text in TACTICS:
                esc = f'<span class="t">{esc}</span>'
            elif base in TYPES:
                esc = f'<span class="ty">{esc}</span>'
        elif kind == "comment":
            esc = f'<span class="c">{esc}</span>'
        elif kind == "string":
            esc = f'<span class="s">{esc}</span>'
        elif kind == "command":
            esc = f'<span class="cmd">{esc}</span>'
        elif kind == "number":
            esc = f'<span class="n">{esc}</span>'
        elif kind == "sym":
            esc = f'<span class="o">{esc}</span>'
        out.append(esc)
        pos = m.end()
    out.append(html.escape(code[pos:]))
    return "".join(out)


# ----------------------------------------------------------------------------
# Page rendering
# ----------------------------------------------------------------------------

def playground_url(code: str) -> str:
    return PLAYGROUND + urllib.parse.quote(code, safe="")


ICON_PLAY = '<svg viewBox="0 0 16 16" aria-hidden="true"><path d="M4 2.5v11l9-5.5z" fill="currentColor"/></svg>'
ICON_COPY = ('<svg viewBox="0 0 16 16" aria-hidden="true"><rect x="5" y="5" width="9" height="9" rx="1.5" '
             'fill="none" stroke="currentColor" stroke-width="1.4"/><path d="M3 11V3.5A1.5 1.5 0 0 1 4.5 2H11" '
             'fill="none" stroke="currentColor" stroke-width="1.4"/></svg>')
ICON_EXTERNAL = ('<svg viewBox="0 0 16 16" aria-hidden="true"><path d="M9 2.5h4.5V7M13.5 2.5 7.5 8.5M12 9.5V13a.5.5 0 0 1-.5.5h-8'
                 'a.5.5 0 0 1-.5-.5V4.5A.5.5 0 0 1 3.5 4H7" fill="none" stroke="currentColor" stroke-width="1.4" '
                 'stroke-linecap="round" stroke-linejoin="round"/></svg>')


def compact_prefix(code: str) -> str:
    """Earlier cells, minus what is only for show (#eval/#check, comment-only lines),
    so the cell you clicked is close to the top of the playground editor."""
    keep = [l for l in code.split("\n")
            if not l.startswith(("#eval", "#check")) and not l.strip().startswith("--")]
    return re.sub(r"\n{3,}", "\n\n", "\n".join(keep)).strip()


def cell_program(prefix: str, text: str, label: str) -> str:
    prefix = compact_prefix(prefix)
    if not prefix:
        return text.strip() + "\n"
    return (f"-- Earlier cells (already loaded):\n\n{prefix}\n\n"
            f"-- ▼▼▼ {label} ▼▼▼\n\n{text.strip()}\n")


def render_code_cell(c: Cell, prefix: str, n: int) -> str:
    label = {"normal": f"[{n}]", "exercise": "exercise", "solution": "solution"}[c.role]
    title = {"normal": f"Cell [{n}]", "exercise": "Exercise", "solution": "Solution"}[c.role]
    full = cell_program(prefix, c.text, title)
    url = html.escape(playground_url(full))
    outputs = ""
    if c.outputs:
        rows = "".join(
            f'<div class="out-row"><span class="out-src">{html.escape(src)}</span>'
            f'<span class="out-val">{html.escape(val)}</span></div>'
            for src, val in c.outputs)
        outputs = f'<div class="outputs"><span class="out-label">output</span>{rows}</div>'
    block = (
        f'<div class="cell code-cell role-{c.role}">'
        f'<div class="cell-bar"><span class="cell-label">{label}</span>'
        f'<span class="cell-actions">'
        f'<button class="btn copy" type="button" data-code="{html.escape(c.text)}">{ICON_COPY}<span>Copy</span></button>'
        f'<a class="btn newtab" href="{url}" target="_blank" rel="noopener" '
        f'title="Open in a new tab" aria-label="Open in a new tab">{ICON_EXTERNAL}</a>'
        f'<button class="btn run" type="button" data-url="{url}" aria-expanded="false" '
        f'title="Run live Lean right here, with all earlier cells loaded">{ICON_PLAY}<span>Run</span></button>'
        f"</span></div>"
        f"<pre><code>{highlight_lean(c.text)}</code></pre>{outputs}</div>"
    )
    if c.role == "solution":
        return f'<details class="solution"><summary>Show solution</summary>{block}</details>'
    return block


def render_lesson(path: Path, cells: list[Cell], lessons, idx) -> str:
    title = next((c.text.split("\n")[0].lstrip("# ") for c in cells if c.kind == "md"), path.stem)
    parts, prefix_cells, n = [], [], 0
    in_exercise = False
    for c in cells:
        if c.kind == "md":
            if c.role == "exercise":
                parts.append(f'<div class="cell md-cell exercise-prompt">{markdown(c.text)}</div>')
            elif c.role != "solution":
                parts.append(f'<div class="cell md-cell">{markdown(c.text)}</div>')
            continue
        prefix = "\n\n".join(prefix_cells)
        if c.role == "normal":
            n += 1
        parts.append(render_code_cell(c, prefix, n))
        if c.role == "normal":
            prefix_cells.append(c.text)
    whole = "\n\n".join(prefix_cells) + "\n"

    prev_link = next_link = "<span></span>"
    if idx > 0:
        p = lessons[idx - 1]
        prev_link = f'<a class="pager prev" href="{p[0]}.html">← {html.escape(p[1])}</a>'
    if idx < len(lessons) - 1:
        q = lessons[idx + 1]
        next_link = f'<a class="pager next" href="{q[0]}.html">{html.escape(q[1])} →</a>'
    src_link = (f' · <a href="{REPO_URL}/blob/main/LeanBasics/{path.name}">source</a>'
                if REPO_URL else "")
    toolbar = (
        f'<div class="lesson-tools"><a class="btn run big" href="{html.escape(playground_url(whole))}" '
        f'target="_blank" rel="noopener">{ICON_PLAY}<span>Open the whole lesson in the playground</span></a>'
        f'<span class="hint">Every proof on this page has been checked by Lean{src_link}.</span></div>'
    )
    body = toolbar + "\n".join(parts) + f'<nav class="pagers">{prev_link}{next_link}</nav>'
    return page(title, body, lessons, idx)


def page(title: str, body: str, lessons, idx) -> str:
    nav = "".join(
        f'<a href="{slug}.html" class="{"active" if i == idx else ""}">'
        f'<span class="num">{i + 1}</span>{html.escape(SHORT.get(slug, t))}</a>'
        for i, (slug, t) in enumerate(lessons))
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} · Lean from Python</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@600;700&family=Work+Sans:wght@400;500;600&family=JetBrains+Mono:wght@400;600&display=swap" rel="stylesheet">
<link rel="stylesheet" href="style.css">
</head>
<body>
<header class="top">
  <a class="brand" href="index.html">Lean <span>from Python</span></a>
  <nav class="lessons">{nav}</nav>
</header>
<main class="notebook">
{body}
</main>
<footer>Built from plain <code>.lean</code> files. Code runs in the
<a href="https://live.lean-lang.org" target="_blank" rel="noopener">official Lean playground</a>.</footer>
<script>
function closeRepl(repl) {{
  const run = repl.previousElementSibling && repl.previousElementSibling.querySelector('button.run');
  repl.remove();
  if (run) {{ run.setAttribute('aria-expanded', 'false'); run.querySelector('span').textContent = 'Run'; }}
}}
document.addEventListener('click', async (e) => {{
  const run = e.target.closest('button.run');
  if (run) {{
    const cell = run.closest('.code-cell');
    const open = cell.nextElementSibling;
    if (open && open.classList.contains('repl')) {{ closeRepl(open); return; }}
    const repl = document.createElement('div');
    repl.className = 'repl';
    repl.innerHTML =
      '<div class="repl-bar"><span class="repl-title"><span class="dot"></span>Live Lean</span>' +
      '<span class="repl-hint">Edit the code · click inside a proof to see its goal</span>' +
      '<button class="btn repl-close" type="button">Close</button></div>' +
      '<div class="repl-body"><div class="repl-loading">Starting Lean…</div>' +
      '<iframe title="Lean playground" allow="clipboard-read; clipboard-write"></iframe></div>';
    const frame = repl.querySelector('iframe');
    frame.addEventListener('load', () => repl.classList.add('loaded'));
    frame.src = run.dataset.url;
    cell.after(repl);
    run.setAttribute('aria-expanded', 'true');
    run.querySelector('span').textContent = 'Close';
    repl.scrollIntoView({{ behavior: 'smooth', block: 'nearest' }});
    return;
  }}
  const close = e.target.closest('button.repl-close');
  if (close) {{ closeRepl(close.closest('.repl')); return; }}
  const b = e.target.closest('button.copy');
  if (!b) return;
  try {{ await navigator.clipboard.writeText(b.dataset.code); }} catch (_) {{}}
  const s = b.querySelector('span'); const old = s.textContent;
  s.textContent = 'Copied'; setTimeout(() => s.textContent = old, 1200);
}});
</script>
</body>
</html>
"""


def render_index(lessons, blurbs) -> str:
    cards = "".join(
        f'<a class="lesson-card" href="{slug}.html"><span class="num">{i + 1}</span>'
        f'<span><strong>{html.escape(t.split("·")[-1].strip())}</strong>'
        f'<span class="blurb">{html.escape(blurbs[slug])}</span></span></a>'
        for i, (slug, t) in enumerate(lessons))
    body = f"""
<section class="hero">
  <h1>Learn Lean, starting from Python</h1>
  <p class="lede">A short, hands-on course in the Lean theorem prover for people who already program.
  You will start with <code>#eval 2 + 3</code> and end by <em>proving</em> that an optimized
  function always agrees with its specification.</p>
  <div class="cell md-cell teaser">
  <pre><code>{highlight_lean('''def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => sumTo n + (n + 1)

theorem gauss (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [sumTo]; grind''')}</code></pre>
  </div>
  <p>Each lesson is a notebook. Read the text, then press <strong>Run</strong> on any cell: a live Lean
  editor opens right there, with all earlier cells already loaded. Change the code, break a proof, fix it.
  You don't need to install anything.</p>
</section>
<section class="lesson-list">{cards}</section>
<section class="cell md-cell">
<h2>How to read a proof</h2>
<p>In the playground, put your cursor at the end of any line inside a <code>by</code> block.
The <strong>Infoview</strong> panel on the right shows the current <em>goal</em>: what is known
(above the <code>⊢</code>) and what is left to prove (after it). Learning Lean is mostly
learning to read that panel and choose the next step.</p>
</section>"""
    return page("Lean from Python", body, lessons, -1)


SHORT = {
    "L01_Programming": "Programming",
    "L02_FirstProofs": "First proofs",
    "L03_Induction": "Induction",
    "L04_Logic": "Logic",
    "L05_Programs": "Proving programs",
}

BLURBS = {
    "L01_Programming": "#eval, functions, lambdas, recursion and pattern matching, structures. Python → Lean.",
    "L02_FirstProofs": "Propositions are types. rfl, rw, intro, exact, and the automatic tactics omega, simp, grind.",
    "L03_Induction": "Gauss's formula by hand, then automatically. Sums of odd numbers, squares and cubes. Inequalities.",
    "L04_Logic": "And, or, not, for all, there exists, using even and odd numbers.",
    "L05_Programs": "Induction on lists. Prove that a fast accumulator sum equals the simple one, for every input.",
}


def check_run_links() -> int:
    """Compile the code behind every Run link; only `sorry` warnings are allowed."""
    import tempfile
    bad = total = 0
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp) / "Cell.lean"
        for page_path in sorted(OUT.glob("L*.html")):
            for link in re.findall(r'href="(https://live\.lean-lang\.org/#code=[^"]+)"',
                                   page_path.read_text()):
                code = urllib.parse.unquote(html.unescape(link).split("#code=", 1)[1])
                p.write_text(code)
                res = subprocess.run(["lean", "--json", str(p)], capture_output=True, text=True)
                msgs = [json.loads(x) for x in res.stdout.splitlines() if x.startswith("{")]
                errs = [m for m in msgs if m["severity"] == "error"
                        or (m["severity"] == "warning" and "sorry" not in m["data"])]
                total += 1
                if errs:
                    bad += 1
                    print(f"{page_path.name}: link {total}: {errs[0]['data'][:160]}", file=sys.stderr)
    print(f"Checked {total} Run links: {bad} broken")
    return 1 if bad else 0


def main() -> int:
    files = sorted(SRC.glob("L*.lean"))
    OUT.mkdir(exist_ok=True)
    parsed, lessons, all_errors = [], [], []
    for f in files:
        cells = parse_cells(f)
        all_errors += attach_outputs(f, cells)
        title = next(c.text.split("\n")[0].lstrip("# ") for c in cells if c.kind == "md")
        parsed.append((f, cells))
        lessons.append((f.stem, title))
    if all_errors:
        print("Lean reported errors:\n" + "\n".join(all_errors), file=sys.stderr)
        return 1
    for i, (f, cells) in enumerate(parsed):
        (OUT / f"{f.stem}.html").write_text(render_lesson(f, cells, lessons, i))
    (OUT / "index.html").write_text(render_index(lessons, BLURBS))
    (OUT / "style.css").write_text((ROOT / "site" / "style.css").read_text())
    (OUT / ".nojekyll").write_text("")
    print(f"Wrote {len(parsed)} lessons + index to {OUT.relative_to(ROOT)}/")
    if "--check" in sys.argv:
        return check_run_links()
    return 0


if __name__ == "__main__":
    sys.exit(main())

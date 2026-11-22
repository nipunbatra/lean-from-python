# Lean from Python

A short, hands-on Lean 4 course for people who already program, written as notebooks.

| # | Lesson | What you learn |
|---|---|---|
| 1 | [Programming](LeanBasics/L01_Programming.lean) | `#eval`, functions, recursion, pattern matching, structures |
| 2 | [First proofs](LeanBasics/L02_FirstProofs.lean) | propositions as types; `rfl`, `rw`, `intro`, `exact`, `omega`, `simp`, `grind` |
| 3 | [Induction](LeanBasics/L03_Induction.lean) | 1 + 2 + ⋯ + n = n(n+1)/2 by hand and automatically; odd numbers, squares, cubes |
| 4 | [Logic](LeanBasics/L04_Logic.lean) | ∧ ∨ ¬ ∀ ∃ with even and odd numbers |
| 5 | [Proving programs](LeanBasics/L05_Programs.lean) | induction on lists; a fast sum is proved equal to the simple one |

## Two ways to work

**In the browser (no install).** Open the website. Every code cell has a **Run** button that opens
the official [Lean playground](https://live.lean-lang.org) with that cell and every earlier cell loaded.

**Locally in VS Code.** Install [elan](https://github.com/leanprover/elan) (`brew install elan-init`)
and the *Lean 4* VS Code extension, then open this folder and any file in `LeanBasics/`.
Put your cursor inside a proof and the **Lean Infoview** panel shows the current goal.

## How the site is built

The `.lean` files are the only source:

- `/-! … -/` doc comments become text cells (markdown).
- Code between them becomes code cells.
- `/-! @exercise … -/` and `/-! @solution -/` mark exercise and (collapsed) solution cells.

```bash
lake build                         # every lesson must compile
python3 site/build.py --check      # render docs/, then compile the code behind every Run link
open docs/index.html
```

`#eval`/`#check` outputs on the pages are captured from real Lean runs.
On every push to `main`, GitHub Actions runs both commands and deploys `docs/` to GitHub Pages.

/-!
# Lesson 2 · First proofs

## The big idea: propositions are types

In Lean, a mathematical statement such as `2 + 2 = 4` is a **type**, whose type is `Prop`.
A **proof** of the statement is a **value** of that type.

| Python / programming | Lean / mathematics |
|---|---|
| a type, e.g. `int` | a statement, e.g. `2 + 2 = 4` |
| a value of that type, e.g. `5` | a proof of that statement |
| the type checker accepts your value | the proof is correct |

So "Lean checked my proof" means the same as "my program type-checks". Nothing more is needed.

False statements are still perfectly good *types*. They just have no values, so nobody can prove them.
-/

#check 2 + 2 = 4      -- 2 + 2 = 4 : Prop
#check 2 + 2 = 5      -- also a Prop! It is just not provable.
#check ∀ n : Nat, n + 0 = n

/-!
## Proof #1: `rfl` ("both sides compute to the same thing")

`theorem name : statement := proof` is like `def name : type := value`.
`rfl` (short for *reflexivity*) proves `a = a`. Lean will first **compute** both sides,
so it also proves `2 + 2 = 4`:
-/

theorem two_plus_two : 2 + 2 = 4 := rfl

def square (x : Nat) : Nat := x * x

def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => sumTo n + (n + 1)

theorem square_three : square 3 = 9 := rfl
theorem gauss_100 : sumTo 100 = 5050 := rfl

/-!
`example` is a theorem without a name, which is handy for practice:
-/

example : 10 * 10 = 100 := rfl

/-!
`decide` runs a decision procedure on a statement that can be checked by
computation, such as a comparison:
-/

example : 10 < 100 := by decide
example : 7 ∣ 91 := by decide        -- "7 divides 91"

/-!
**But** `sumTo 100 = 5050` is a single fact. Gauss's formula is
`∀ n, 2 * sumTo n = n * (n + 1)`, which covers infinitely many `n`, so no amount of
computation can check it. For that we need *reasoning*, which is the job of tactics.

## Tactic mode: `by …`

After `by`, you write a sequence of **tactics**. Each tactic transforms the current
**goal**, meaning what is left to prove. In the playground, put your cursor after a
tactic and the Infoview shows the goal at that point. That panel is how you work in Lean:
you read the goal, choose the next step, and read the new goal.

In the cells below, the goal state is written in comments so you can follow along without
running anything. `⊢` means "what we must prove". The lines above it are what we *know*.

### `intro`, `rw`, `exact`
-/

theorem add_one_eq (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  -- a b : Nat
  -- h : a = b
  -- ⊢ a + 1 = b + 1
  rw [h]
  -- `rw [h]` replaces every `a` in the goal with `b`, giving
  -- ⊢ b + 1 = b + 1, which `rw` then closes automatically with rfl.

/-!
Arguments written before the colon, like `(a b : Nat) (h : a = b)`, are hypotheses.
You can instead put them after the colon using `∀` and `→`, and then **`intro`** them:
-/

example : ∀ a b : Nat, a = b → a + 1 = b + 1 := by
  intro a b h
  -- now exactly the same goal as above
  rw [h]

/-!
`→` is "implies". It is literally the function arrow: a proof of `P → Q` is a
**function** that turns a proof of `P` into a proof of `Q`.

### Library lemmas are functions too
-/

#check Nat.add_comm         -- Nat.add_comm (n m : Nat) : n + m = m + n
#check Nat.add_comm 2 3     -- a proof of 2 + 3 = 3 + 2

example (x y : Nat) : x + y = y + x := Nat.add_comm x y

example (x y z : Nat) : (x + y) + z = z + (y + x) := by
  -- ⊢ x + y + z = z + (y + x)
  rw [Nat.add_comm x y]
  -- ⊢ y + x + z = z + (y + x)
  rw [Nat.add_comm (y + x) z]
  -- closed by rfl

/-!
`exact e` closes the goal with the term `e` when `e` has *exactly* the goal's type:
-/

example (p : Nat) (h : p > 1) : p > 1 := by
  exact h

/-!
### Unfolding your own definitions

`square n = n * n` holds *by definition*, so `rfl` proves it. To *use* a definition
inside a longer proof, `rw [square]` or `unfold square` replaces it with its body:
-/

theorem square_def (n : Nat) : square n = n * n := rfl

example (n : Nat) : square (n + 1) = (n + 1) * (n + 1) := by
  unfold square
  -- ⊢ (n + 1) * (n + 1) = (n + 1) * (n + 1)
  rfl

/-!
## Automation: `omega`, `simp`, `decide`, `grind`

Writing `rw [Nat.add_comm …]` by hand gets tedious. Lean has automatic tactics:

| tactic | what it does |
|---|---|
| `omega` | solves **linear** arithmetic over `Nat`/`Int`: `+`, `-`, `*` by constants, `/` and `%` by constants, `<`, `≤`, `=` |
| `simp` | rewrites with hundreds of simplification lemmas until it gets stuck |
| `decide` | evaluates a statement that can be checked by computation |
| `grind` | a powerful general-purpose solver, which also handles nonlinear algebra such as `x * y` |
-/

example (x y : Nat) (h1 : x < y) (h2 : y < 10) : x + 1 < 10 := by omega
example (n : Nat) : (2 * n + 1) % 2 = 1 := by omega
example (n : Nat) (h : n % 4 = 3) : n % 2 = 1 := by omega
example (xs : List Nat) : (xs ++ []).length = xs.length := by simp
example (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by grind

/-!
Use the automation freely. Still, do some proofs by hand to learn what is going on,
because when a solver fails you need to know which step it could not do.

## When you are stuck

- `sorry` closes any goal, with a warning. Use it as a placeholder, like `pass` or `...` in Python.
- `exact?` searches the library for a lemma that closes the goal and suggests it.
- `#check` a lemma name to see what it says.

## Exercises
-/

/-! @exercise
**2.1** Prove this with `rfl`.
-/
example : square 5 + square 12 = square 13 := by
  sorry

/-! @solution -/
example : square 5 + square 12 = square 13 := rfl

/-! @exercise
**2.2** Prove it **by hand** using `rw` with `Nat.add_comm`.
-/
example (a b c : Nat) : a + (b + c) = a + (c + b) := by
  sorry

/-! @solution -/
example (a b c : Nat) : a + (b + c) = a + (c + b) := by
  rw [Nat.add_comm b c]

/-! @exercise
**2.3** Use `intro`, then `omega`.
-/
example : ∀ n : Nat, n % 2 = 0 → (n + 2) % 2 = 0 := by
  sorry

/-! @solution -/
example : ∀ n : Nat, n % 2 = 0 → (n + 2) % 2 = 0 := by
  intro n h
  omega

/-! @exercise
**2.4** Two hypotheses. `rw` with both, then finish.
-/
example (x y z : Nat) (h1 : x = y + 1) (h2 : y = 2 * z) : x = 2 * z + 1 := by
  sorry

/-! @solution -/
example (x y z : Nat) (h1 : x = y + 1) (h2 : y = 2 * z) : x = 2 * z + 1 := by
  rw [h1, h2]

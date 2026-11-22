/-!
# Lesson 4 · Logic: and, or, not, for all, there exists

Each logical connective comes with two skills:
1. how to **prove** a statement of that form (the goal is `P ∧ Q`)
2. how to **use** a hypothesis of that form (you have `h : P ∧ Q`)

| connective | to prove it | to use `h` |
|---|---|---|
| `P → Q` (implies) | `intro hp` | `h hp` (apply it like a function) |
| `P ∧ Q` (and) | `constructor` or `⟨hp, hq⟩` | `h.1`, `h.2`, or `obtain ⟨hp, hq⟩ := h` |
| `P ∨ Q` (or) | `left` or `right` | `rcases h with hp \| hq` (two cases) |
| `¬P` (not) | `intro hp` and derive `False` | `h hp : False` |
| `∀ x, P x` | `intro x` | `h 5 : P 5` |
| `∃ x, P x` | `⟨witness, proof⟩` or `exists witness` | `obtain ⟨x, hx⟩ := h` |

## And
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp       -- first goal: p
  · exact hq       -- second goal: q

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩   -- same thing, as a value

example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  obtain ⟨hp, hq⟩ := h        -- take the pair apart, like Python's `a, b = pair`
  exact ⟨hq, hp⟩

/-!
The `·` bullets focus on one goal at a time. A tactic can create several goals,
and each bullet handles one of them.

## Or
-/

example (p q : Prop) (hp : p) : p ∨ q := by
  left
  exact hp

example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq        -- two cases, like an if/else on which side holds
  · right; exact hp
  · left; exact hq

/-!
## A real example: even numbers

A *definition* can be a `Prop`. Here `IsEven n` means that some `k` has `n = 2k`.
-/

def IsEven (n : Nat) : Prop := ∃ k, n = 2 * k

/-!
**Proving `∃`** means giving a witness and then proving that it works:
-/

example : IsEven 10 := ⟨5, rfl⟩          -- witness 5, proof 10 = 2 * 5

example : IsEven 10 := by
  exists 5

/-!
**Using `∃`**: `obtain ⟨k, hk⟩ := h` gives you the witness `k` and the fact about it.
-/

theorem even_add (a b : Nat) (ha : IsEven a) (hb : IsEven b) : IsEven (a + b) := by
  obtain ⟨k, hk⟩ := ha       -- hk : a = 2 * k
  obtain ⟨l, hl⟩ := hb       -- hl : b = 2 * l
  -- ⊢ IsEven (a + b), i.e. ∃ m, a + b = 2 * m
  exact ⟨k + l, by omega⟩

theorem even_mul (a b : Nat) (ha : IsEven a) : IsEven (a * b) := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨k * b, by rw [hk, Nat.mul_assoc]⟩

/-!
## Not

`¬P` is *defined* as `P → False`. To prove it, assume `P` and derive a contradiction.
`omega` is happy to find a contradiction in arithmetic hypotheses.
-/

theorem one_not_even : ¬ IsEven 1 := by
  intro h                 -- h : IsEven 1
  obtain ⟨k, hk⟩ := h     -- hk : 1 = 2 * k
  omega                   -- impossible, so the goal `False` is proved

/-!
## For all, there exists, and how they combine

"There are infinitely many even numbers" says that for every `n` there is an even number bigger than `n`:
-/

theorem evens_unbounded : ∀ n, ∃ m, m > n ∧ IsEven m := by
  intro n
  exact ⟨2 * n + 2, by omega, n + 1, by omega⟩

/-!
Every number is even or its successor is. We split on `n % 2` using a library lemma:
-/

#check Nat.mod_two_eq_zero_or_one     -- n % 2 = 0 ∨ n % 2 = 1

theorem even_or_succ_even (n : Nat) : IsEven n ∨ IsEven (n + 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left
    exact ⟨n / 2, by omega⟩
  · right
    exact ⟨n / 2 + 1, by omega⟩

/-!
## Exercises
-/

/-! @exercise
**4.1** `∧` is commutative, in both directions. `↔` means "if and only if". Start with `constructor`.
-/
example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  sorry

/-! @solution -/
example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-! @exercise
**4.2** Prove that `7` is not even.
-/
example : ¬ IsEven 7 := by
  sorry

/-! @solution -/
example : ¬ IsEven 7 := by
  intro ⟨k, hk⟩       -- you can destructure right in `intro`
  omega

/-! Odd numbers, defined the same way as even ones: -/
def IsOdd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

/-! @exercise
**4.3** Using `IsOdd` (defined just above), prove that odd + odd is even.
-/
example (a b : Nat) (ha : IsOdd a) (hb : IsOdd b) : IsEven (a + b) := by
  sorry

/-! @solution -/
example (a b : Nat) (ha : IsOdd a) (hb : IsOdd b) : IsEven (a + b) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hb
  exact ⟨k + l + 1, by omega⟩

/-! @exercise
**4.4** If `n²` is even, so is `n`. Hint: use `even_or_succ_even` from above, then
`rcases` to split on which case holds. In the bad case, show that `n * n` is odd and get a contradiction.
-/
example (n : Nat) (h : IsEven (n * n)) : IsEven n := by
  sorry

/-! @solution -/
example (n : Nat) (h : IsEven (n * n)) : IsEven n := by
  rcases even_or_succ_even n with hn | hn
  · exact hn
  · -- n + 1 is even, so n is odd, so n * n is odd: contradiction
    exfalso                                  -- switch the goal to False
    obtain ⟨k, hk⟩ := hn                     -- hk : n + 1 = 2 * k
    obtain ⟨m, hm⟩ := h                      -- hm : n * n = 2 * m
    have hodd : n % 2 = 1 := by omega
    have : n * n % 2 = 1 := by
      rw [Nat.mul_mod, hodd]                 -- (a*b) % 2 = ((a%2) * (b%2)) % 2
    omega

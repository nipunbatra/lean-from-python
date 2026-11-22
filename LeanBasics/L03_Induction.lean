/-!
# Lesson 3 · Induction: 1 + 2 + ⋯ + n = n(n+1)/2

## The paper proof

Let `S(n) = 1 + 2 + ⋯ + n`. Claim: `2·S(n) = n(n+1)`.

- **Base case** `n = 0`: `2·S(0) = 0 = 0·1`. ✓
- **Inductive step**: assume `2·S(k) = k(k+1)`, which is the *induction hypothesis*. Then
  `2·S(k+1) = 2·S(k) + 2(k+1) = k(k+1) + 2(k+1) = (k+2)(k+1)`. ✓

Lean wants exactly this proof, with every step justified.

## The definition

`S` is the recursive function from Lesson 1. Its two equations are the only facts
Lean knows about it:

- `sumTo 0 = 0`
- `sumTo (n + 1) = sumTo n + (n + 1)`
-/

def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => sumTo n + (n + 1)

/-!
## Why `2 * sumTo n` and not `sumTo n = n * (n + 1) / 2`?

On `Nat`, `/` is **floor division** (Python's `//`). Equations that contain division
are awkward to rewrite, because `(a + b) / 2` is not always `a / 2 + b / 2`. So we prove
the version without division first, then derive the version with division at the end.

## Proof 1: by hand

The `induction n with` tactic splits the proof into the two cases of `Nat`:
`zero` and `succ k` (that is, `k + 1`). In the `succ` case, Lean gives us the
induction hypothesis, which we name `ih`.

`calc` writes a chain of equalities, each with its own justification,
just like a proof on a whiteboard.
-/

theorem gauss (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero =>
    -- ⊢ 2 * sumTo 0 = 0 * (0 + 1)
    rfl                        -- both sides compute to 0
  | succ k ih =>
    -- ih : 2 * sumTo k = k * (k + 1)
    -- ⊢ 2 * sumTo (k + 1) = (k + 1) * (k + 1 + 1)
    calc 2 * sumTo (k + 1)
        = 2 * (sumTo k + (k + 1))     := by rw [sumTo]       -- unfold the definition
      _ = 2 * sumTo k + 2 * (k + 1)   := by rw [Nat.mul_add] -- distribute
      _ = k * (k + 1) + 2 * (k + 1)   := by rw [ih]          -- induction hypothesis!
      _ = (k + 2) * (k + 1)           := by rw [Nat.add_mul] -- factor out (k + 1)
      _ = (k + 1) * (k + 1 + 1)       := Nat.mul_comm _ _    -- swap the factors

/-!
Each line of the `calc` matches a line of the paper proof. The library lemmas used are:
-/

#check Nat.mul_add    -- a * (b + c) = a * b + a * c
#check Nat.add_mul    -- (a + b) * c = a * c + b * c
#check Nat.mul_comm   -- a * b = b * a

/-!
## Proof 2: let automation do the algebra

The *structure* of the proof (induction, base case, use the hypothesis) is the
interesting part. The algebra is routine, so `grind` can do it. We just
unfold `sumTo` once and hand over `ih`:
-/

theorem gauss' (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo]       -- ⊢ 2 * (sumTo k + (k + 1)) = (k + 1) * (k + 1 + 1)
    grind            -- finds the algebra, using ih from the context

/-!
## The formula with division

`omega` understands division by a constant, so the textbook form takes one line.
`have` adds a fact to the context, like assigning a variable in Python:
-/

theorem gauss_div (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  have h := gauss n       -- h : 2 * sumTo n = n * (n + 1)
  omega

#eval sumTo 1000                -- 500500
#eval 1000 * 1001 / 2           -- 500500, as the theorem says

/-!
## More sums, in the same pattern

### Sum of the first n odd numbers is n²

`1 + 3 + 5 + ⋯ + (2n−1) = n²`
-/

def sumOdd : Nat → Nat
  | 0     => 0
  | n + 1 => sumOdd n + (2 * n + 1)

#eval (List.range 8).map sumOdd       -- [0, 1, 4, 9, 16, 25, 36, 49]

theorem sumOdd_eq (n : Nat) : sumOdd n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- ⊢ sumOdd (k + 1) = (k + 1) * (k + 1)
    rw [sumOdd, ih]
    -- ⊢ k * k + (2 * k + 1) = (k + 1) * (k + 1)
    grind

/-!
### Sum of squares: `1² + 2² + ⋯ + n² = n(n+1)(2n+1)/6`

Same trick as before: multiply by 6 to get rid of the division.
-/

def sumSq : Nat → Nat
  | 0     => 0
  | n + 1 => sumSq n + (n + 1) * (n + 1)

theorem sumSq_eq (n : Nat) : 6 * sumSq n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumSq]
    grind

/-!
## Induction for inequalities: `n + 1 ≤ 2ⁿ`

Induction is not only for equalities. Here the step is
`k + 2 ≤ 2 * 2^k`, which follows from `ih : k + 1 ≤ 2^k`, because `2^k ≥ 1`.
-/

theorem lt_pow_two (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    -- ih : k + 1 ≤ 2 ^ k
    -- ⊢ k + 1 + 1 ≤ 2 ^ (k + 1)
    rw [Nat.pow_succ]
    -- ⊢ k + 1 + 1 ≤ 2 ^ k * 2
    omega          -- linear in the "atom" 2 ^ k

/-!
## Reusing earlier theorems

A theorem you have proved works like a library function you can call.
Sum of cubes: `1³ + 2³ + ⋯ + n³ = (1 + 2 + ⋯ + n)²`. In the inductive step we
call `gauss k` to get the closed form of `sumTo k`.
-/

def sumCubes : Nat → Nat
  | 0     => 0
  | n + 1 => sumCubes n + (n + 1) * (n + 1) * (n + 1)

theorem nicomachus (n : Nat) : sumCubes n = sumTo n * sumTo n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have g := gauss k          -- g : 2 * sumTo k = k * (k + 1)
    rw [sumCubes, sumTo, ih]
    grind

#eval (sumCubes 10, sumTo 10 * sumTo 10)    -- (3025, 3025)

/-!
## The recipe

Almost every proof in this lesson has the same shape:

```lean
theorem foo (n : Nat) : P n := by
  induction n with
  | zero => rfl            -- or decide / simp
  | succ k ih =>
    rw [defn]              -- unfold one step of the recursive definition
    rw [ih] / grind / omega
```

## Exercises
-/

def sumPow2 : Nat → Nat
  | 0     => 0
  | n + 1 => sumPow2 n + 2 ^ n

/-! @exercise
**3.1** The sum of powers of two: `1 + 2 + 4 + ⋯ + 2ⁿ⁻¹ = 2ⁿ − 1`.
Stated without subtraction: `sumPow2 n + 1 = 2 ^ n`. (The definition of `sumPow2` is in the cell above.)
-/
theorem sumPow2_eq (n : Nat) : sumPow2 n + 1 = 2 ^ n := by
  sorry

/-! @solution -/
theorem sumPow2_eq' (n : Nat) : sumPow2 n + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumPow2, Nat.pow_succ]
    omega

/-! For the next exercise, here are the even numbers `0 + 2 + 4 + ⋯`: -/
def sumEven : Nat → Nat
  | 0     => 0
  | n + 1 => sumEven n + 2 * n

/-! @exercise
**3.2** Sum of even numbers: `0 + 2 + 4 + ⋯ + 2(n−1) = n(n−1)`.
Stated without subtraction: `sumEven n + n = n * n`.
-/
theorem sumEven_eq (n : Nat) : sumEven n + n = n * n := by
  sorry

/-! @solution -/
theorem sumEven_eq' (n : Nat) : sumEven n + n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumEven]
    grind

/-! And Fibonacci numbers, with their running sum: -/
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

def sumFib : Nat → Nat
  | 0     => 0
  | n + 1 => sumFib n + fib n

/-! @exercise
**3.3** Fibonacci: `F₀ + F₁ + ⋯ + Fₙ₋₁ + 1 = Fₙ₊₁`.
-/
theorem sumFib_eq (n : Nat) : sumFib n + 1 = fib (n + 1) := by
  sorry

/-! @solution -/
theorem sumFib_eq' (n : Nat) : sumFib n + 1 = fib (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- ⊢ sumFib (k + 1) + 1 = fib (k + 1 + 1)
    rw [sumFib, fib]
    -- ⊢ sumFib k + fib k + 1 = fib k + fib (k + 1)
    omega

/-! @exercise
**3.4** *(harder)* Prove the textbook form for the odd numbers using `sumOdd_eq`:
`sumOdd n = n ^ 2`. Hint: `Nat.pow_two` says `a ^ 2 = a * a`.
-/
example (n : Nat) : sumOdd n = n ^ 2 := by
  sorry

/-! @solution -/
example (n : Nat) : sumOdd n = n ^ 2 := by
  rw [Nat.pow_two]
  exact sumOdd_eq n

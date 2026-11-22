/-!
# Lesson 5 · Proving programs correct

So far we proved facts about numbers. The same tools prove facts about **code**.
This is where Lean differs most from Python: instead of *testing* a function
on a few inputs, you *prove* it correct for **all** inputs.

## Lists are an inductive type

A list is either empty `[]`, or `x :: xs` (an element `x` in front of a list `xs`).
`[1, 2, 3]` is shorthand for `1 :: 2 :: 3 :: []`. So lists support **induction**,
just like `Nat`: prove the statement for `[]`, then for `x :: xs` assuming it for `xs`.
-/

#eval 1 :: [2, 3]            -- [1, 2, 3]

def mySum : List Nat → Nat
  | []      => 0
  | x :: xs => x + mySum xs

def myLength : List α → Nat
  | []      => 0
  | _ :: xs => 1 + myLength xs

#eval mySum [1, 2, 3, 4]
#eval myLength ["a", "b", "c"]

/-!
(`α` is a type variable, like `T` in Python's `list[T]`. `myLength` works for lists of anything.)

## A first list proof

Is `mySum (xs ++ ys) = mySum xs + mySum ys` true? In Python you would test a few cases.
In Lean, we do induction on `xs`:
-/

theorem mySum_append (xs ys : List Nat) : mySum (xs ++ ys) = mySum xs + mySum ys := by
  induction xs with
  | nil =>
    -- ⊢ mySum ([] ++ ys) = mySum [] + mySum ys
    simp [mySum]
  | cons x xs ih =>
    -- ih : mySum (xs ++ ys) = mySum xs + mySum ys
    -- ⊢ mySum (x :: xs ++ ys) = mySum (x :: xs) + mySum ys
    simp [mySum, ih]
    omega

/-!
`simp [mySum, ih]` means "simplify, and also unfold `mySum` and rewrite with `ih`".

## The main example: a fast function equals a simple spec

`mySum` is clear but not *tail-recursive*: on a list of a million elements it
needs a million stack frames. The usual fix is an accumulator, as you would write
in Python with a loop:

```python
def fast_sum(xs):
    acc = 0
    for x in xs:
        acc += x
    return acc
```
-/

def sumAcc : List Nat → Nat → Nat
  | [],      acc => acc
  | x :: xs, acc => sumAcc xs (acc + x)

def fastSum (xs : List Nat) : Nat := sumAcc xs 0

#eval fastSum [1, 2, 3, 4]

/-!
**Claim:** `fastSum xs = mySum xs` for every list.

A direct induction gets stuck, because the accumulator changes on each recursive call.
The standard trick is to **generalize**: prove a stronger statement that holds for *every*
starting `acc`. Then the induction hypothesis is strong enough to use.
-/

theorem sumAcc_eq (xs : List Nat) (acc : Nat) : sumAcc xs acc = acc + mySum xs := by
  induction xs generalizing acc with
  | nil =>
    -- ⊢ sumAcc [] acc = acc + mySum []
    simp [sumAcc, mySum]
  | cons x xs ih =>
    -- ih : ∀ acc, sumAcc xs acc = acc + mySum xs      (note the ∀!)
    -- ⊢ sumAcc (x :: xs) acc = acc + mySum (x :: xs)
    simp [sumAcc, mySum, ih]
    omega

theorem fastSum_correct (xs : List Nat) : fastSum xs = mySum xs := by
  simp [fastSum, sumAcc_eq]

/-!
That is a complete correctness proof: the optimized function returns the same
answer as the specification **on every possible input**, which no finite test
suite can guarantee.

## Reverse

A classic example. Reversing twice gives back the original list:
-/

def myReverse : List α → List α
  | []      => []
  | x :: xs => myReverse xs ++ [x]

#eval myReverse [1, 2, 3]

theorem myReverse_append (xs ys : List α) :
    myReverse (xs ++ ys) = myReverse ys ++ myReverse xs := by
  induction xs with
  | nil => simp [myReverse]
  | cons x xs ih => simp [myReverse, ih]

theorem myReverse_myReverse (xs : List α) : myReverse (myReverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- ⊢ myReverse (myReverse xs ++ [x]) = x :: xs
    simp [myReverse, myReverse_append, ih]

/-!
Notice how `myReverse_myReverse` needed a **helper lemma** (`myReverse_append`).
This is very common: the main proof gets stuck, so you work out what fact you
are missing, prove it separately, and then use it.

## Exercises
-/

/-! @exercise
**5.1** The length of an appended list.
-/
theorem myLength_append (xs ys : List α) :
    myLength (xs ++ ys) = myLength xs + myLength ys := by
  sorry

/-! @solution -/
theorem myLength_append' (xs ys : List α) :
    myLength (xs ++ ys) = myLength xs + myLength ys := by
  induction xs with
  | nil => simp [myLength]
  | cons x xs ih =>
    simp [myLength, ih]
    omega

/-! Our own version of `map`: -/
def myMap (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: myMap f xs

/-! @exercise
**5.2** `myMap` (defined just above) doesn't change the length.
-/
theorem myLength_myMap (f : α → β) (xs : List α) : myLength (myMap f xs) = myLength xs := by
  sorry

/-! @solution -/
theorem myLength_myMap' (f : α → β) (xs : List α) :
    myLength (myMap f xs) = myLength xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [myMap, myLength, ih]

/-! @exercise
**5.3** *(harder)* Doubling every element doubles the sum.
-/
example (xs : List Nat) : mySum (xs.map (fun x => 2 * x)) = 2 * mySum xs := by
  sorry

/-! @solution -/
example (xs : List Nat) : mySum (xs.map (fun x => 2 * x)) = 2 * mySum xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [mySum, ih]
    omega

/-!
## Where to go next

- **[Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)**: builds arithmetic from scratch, one tactic at a time, in the browser. It is the best next step.
- **[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)**: real mathematics using **Mathlib**, the large library with tactics such as `ring`, `linarith` and `positivity`.
- **[Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)**: Lean as a programming language.
- **[Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)**: the logic underneath it all.
- **[Loogle](https://loogle.lean-lang.org/)**: search the library by the shape of a statement.
-/

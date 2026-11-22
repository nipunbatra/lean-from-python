/-!
# Lesson 1 · Lean is a programming language

Before Lean is a proof assistant, it is a **typed functional programming language**.
If you know Python, most of this lesson is just new syntax for old ideas.

Each grey box is a code cell. Click **▶ Run** on a cell and a live Lean editor opens
right below it, with the code from every earlier cell already loaded, much like a
Jupyter kernel. Edit anything you like. Put your cursor on a line to see its output
in the right-hand **Infoview** panel. (The ↗ button opens the same thing in a new tab.)

## Values, types, `#eval` and `#check`

- `#eval e` runs `e` and prints the result, like typing at the Python REPL.
- `#check e` prints the **type** of `e` without running it.

`Nat` is the natural numbers `0, 1, 2, …`. Lean has no "int that might be negative"
by default: `Nat` subtraction stops at zero.
-/

#eval 2 + 3
#eval 7 / 2          -- floor division, like Python's 7 // 2
#eval 7 % 2
#eval 3 - 5          -- Nat subtraction is truncated: 0, not -2
#eval (3 : Int) - 5  -- use Int if you want negatives
#check 2 + 3
#check "hello"
#check true

/-!
## Defining functions

Python:

```python
def square(x: int) -> int:
    return x * x
```

Lean:
-/

def square (x : Nat) : Nat := x * x

#eval square 12
#check square        -- shows the signature: square (x : Nat) : Nat
#check (square)      -- square : Nat → Nat   ("a function from Nat to Nat")

/-!
Notice that **function application is just a space**: `square 12`, not `square(12)`.
Several arguments are also separated by spaces:
-/

def area (width height : Nat) : Nat := width * height

#eval area 3 4
#eval area (1 + 2) 4    -- parentheses only for grouping

/-!
## Anonymous functions (lambdas)

`fun x => x + 1` is Python's `lambda x: x + 1`.
-/

#eval (fun x => x + 1) 41
#eval [1, 2, 3].map (fun x => x * 10)       -- like [x*10 for x in [1,2,3]]
#eval [1, 2, 3, 4, 5, 6].filter (fun x => x % 2 == 0)

/-!
## `if`, `let`, strings
-/

def describe (n : Nat) : String :=
  let half := n / 2
  if n % 2 == 0 then s!"{n} is even, half is {half}"
  else s!"{n} is odd"

#eval describe 10
#eval describe 7

/-!
`s!"…{x}…"` is Lean's f-string.

## Recursion and pattern matching

This is the most important idea of the lesson. A natural number is either
`0`, or `n + 1` for some smaller `n`. A function on `Nat` can be defined
by giving one equation for each case:
-/

def sumTo : Nat → Nat
  | 0     => 0
  | n + 1 => sumTo n + (n + 1)

#eval sumTo 4      -- 1 + 2 + 3 + 4
#eval sumTo 100

/-!
Compare with Python:

```python
def sum_to(n):
    if n == 0:
        return 0
    return sum_to(n - 1) + n
```

Lean checks that every recursive call is on a **smaller** input, so every
function terminates. A proof must not run forever, and the same check
applies to ordinary programs.

Two more recursive definitions that we will prove things about later:
-/

def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

#eval factorial 5
#eval (List.range 12).map fib

/-!
## Your own data types

A `structure` is like a Python `@dataclass`:
-/

structure Point where
  x : Int
  y : Int
deriving Repr

def Point.add (p q : Point) : Point := { x := p.x + q.x, y := p.y + q.y }

#eval Point.add { x := 1, y := 2 } { x := 10, y := -5 }

/-!
An `inductive` type lists all the ways to build a value, like an `Enum` that can
also carry data:
-/

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)

def Shape.roughArea : Shape → Nat
  | .circle r => 3 * r * r
  | .rect w h => w * h

#eval (Shape.rect 3 4).roughArea

/-!
`Nat` itself is defined in exactly this way:

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat     -- "n + 1"
```

Keep this in mind. **Proofs by induction** in Lesson 3 follow this same definition.

## Exercises

Open a cell, replace `sorry` with your code, and use `#eval` to test it.
`sorry` is Lean's placeholder for "not written yet". It compiles, with a warning.
(The solutions use primed names like `cube'` so that they don't clash with the exercise.)
-/

/-! @exercise
**1.1** Write `cube`, so that `cube 3 = 27`.
-/
def cube (n : Nat) : Nat := sorry

/-! @solution -/
def cube' (n : Nat) : Nat := n * n * n
#eval cube' 3

/-! @exercise
**1.2** Write `sumSquares n = 1² + 2² + … + n²` recursively, the same way as `sumTo`.
-/
def sumSquares : Nat → Nat := sorry

/-! @solution -/
def sumSquares' : Nat → Nat
  | 0     => 0
  | n + 1 => sumSquares' n + (n + 1) * (n + 1)
#eval sumSquares' 3   -- 1 + 4 + 9 = 14

/-! @exercise
**1.3** Write `pow2 n = 2ⁿ` recursively, without using `^`.
-/
def pow2 : Nat → Nat := sorry

/-! @solution -/
def pow2' : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * pow2' n
#eval pow2' 10

import Std.Data.HashMap

/-!
# Lesson 6 · Python → Lean phrasebook

Everyday Python, translated into Lean. Python is on the left and Lean is on the right.
Both are real: the Python was run to produce its output, and the Lean was checked by Lean.
Press **▶ Run** on any Lean cell to change it live.

You can read this page from top to bottom, or keep it open as a reference while you do the
other lessons. (This page starts with `import Std.Data.HashMap`, which the dictionary
section needs. The Run buttons include it for you.)

## Cheat sheet

| Python | Lean |
|---|---|
| `x = 5` (inside a function) | `let x := 5` |
| `def f(x: int) -> int:` | `def f (x : Int) : Int :=` |
| `f(3)`, `g(1, 2)` | `f 3`, `g 1 2` |
| `lambda x: x + 1` | `fun x => x + 1` or `(· + 1)` |
| `a if c else b` | `if c then a else b` |
| `f"x = {x}"` | `s!"x = {x}"` |
| `len(xs)`, `xs + ys` | `xs.length`, `xs ++ ys` |
| `[f(x) for x in xs]` | `xs.map f` |
| `[x for x in xs if p(x)]` | `xs.filter p` |
| `range(n)` | `List.range n` |
| `None` and `Optional[int]` | `none` and `Option Int` |
| `raise` / `try` | `Except` and `←` |
| `@dataclass class P:` | `structure P where` |
| `assert f(3) == 9` | `#guard f 3 == 9` |
| `print(x)` | `#eval x` or `IO.println x` |

## Numbers

Most arithmetic looks the same. The one thing to watch is that a plain number in Lean is a
`Nat`, a natural number `0, 1, 2, …`, and a `Nat` cannot go below zero.

```python
print(2 + 3, 7 // 2, 7 % 2, 2 ** 10)
print(3 - 5)
print(-7 // 2, -7 % 3)
print(2 / 3)
```
-/

#eval 2 + 3
#eval 7 / 2           -- rounds down, like `//`
#eval 7 % 2
#eval 2 ^ 10          -- power is `^`, not `**`
#eval 3 - 5           -- Nat stops at 0
#eval (3 : Int) - 5   -- Int has negatives
#eval (-7 : Int) / 2
#eval (-7 : Int) % 3
#eval (2 : Float) / 3

/-!
Both Python's `int` and Lean's `Nat`/`Int` have **no overflow**: they grow as large as needed.

## Strings

```python
name = "Ada"
print(f"Hello, {name}!")
print(len(name), name.upper())
print("a,b,c".split(","))
print(", ".join(["x", "y"]))
print(int("42"))
```
-/

def name := "Ada"

#eval s!"Hello, {name}!"     -- s!"…" is an f-string
#eval name.length
#eval name.toUpper
#eval "a,b,c".splitOn ","
#eval ", ".intercalate ["x", "y"]
#eval "42".toNat?            -- some 42
#eval "hi".toNat?            -- none (Python would raise)

/-!
Methods are called with a dot, as in Python: `name.length`. A name ending in `?` usually
means "may fail, and returns an `Option`" (see *None* below).

## Functions

Types go after a colon, like Python type hints. Unlike hints, Lean **checks** them.
Default arguments work too.

```python
def square(x: int) -> int:
    return x * x

def greet(name: str, greeting: str = "Hello") -> str:
    return f"{greeting}, {name}!"

print(square(12))
print(greet("Ada"), greet("Ada", greeting="Hi"))
```
-/

def square (x : Nat) : Nat := x * x

def greet (name : String) (greeting : String := "Hello") : String :=
  s!"{greeting}, {name}!"

#eval square 12
#eval greet "Ada"
#eval greet "Ada" (greeting := "Hi")

/-!
There is no `return`: the body *is* the result. Calling a function is a space, so
`square 12`, and `square (12 + 1)` when the argument is more than one word.

## Lambdas and passing functions around

```python
inc = lambda x: x + 1

def twice(f, x):
    return f(f(x))

print(inc(5), twice(inc, 5), twice(lambda x: x * 10, 5))
```
-/

def inc := fun (x : Nat) => x + 1

def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

#eval inc 5
#eval twice inc 5
#eval twice (· * 10) 5    -- means fun x => x * 10

/-!
`Nat → Nat` is the type "function from `Nat` to `Nat`", like `Callable[[int], int]`.

## if / else and booleans

```python
def sign(x: int) -> str:
    if x > 0:
        return "positive"
    elif x < 0:
        return "negative"
    else:
        return "zero"

print(sign(5), sign(-2), sign(0))
print(True and not False, 3 == 3, 3 != 4)
```
-/

def sign (x : Int) : String :=
  if x > 0 then "positive"
  else if x < 0 then "negative"
  else "zero"

#eval sign 5
#eval sign (-2)     -- a negative argument needs parentheses
#eval sign 0
#eval true && !false
#eval (3 == 3, 3 != 4)

/-!
In Lean, `if` is an *expression* that produces a value, like Python's `a if c else b`.
That is why every `if` needs an `else`.

## Local variables and tuples

```python
def sum_of_squares(a, b):
    a2 = a * a
    b2 = b * b
    return a2 + b2

def div_mod(a, b):
    return a // b, a % b

q, r = div_mod(17, 5)
print(sum_of_squares(3, 4), div_mod(17, 5), q * 5 + r)
```
-/

def sumOfSquares (a b : Nat) : Nat :=
  let a2 := a * a
  let b2 := b * b
  a2 + b2

def divMod (a b : Nat) : Nat × Nat := (a / b, a % b)

#eval sumOfSquares 3 4
#eval divMod 17 5
#eval let (q, r) := divMod 17 5; q * 5 + r

/-!
`Nat × Nat` is the type of pairs, like `tuple[int, int]`. A `let` cannot be reassigned
later. For loops that need a changing variable, see *Loops* below.

## Lists

```python
xs = [3, 1, 4, 1, 5]
print(len(xs), xs[0], sum(xs), max(xs))
print(xs + [9], [0] + xs)
print(sorted(xs), xs[::-1], 4 in xs, xs[1:3])
```
-/

def xs : List Nat := [3, 1, 4, 1, 5]

#eval xs.length
#eval xs[0]!          -- `!` crashes if out of range
#eval xs[10]?         -- `?` returns an Option instead: none
#eval xs.sum
#eval xs.max?         -- some 5 (an empty list has no max)
#eval xs ++ [9]
#eval 0 :: xs         -- put one element in front
#eval xs.mergeSort
#eval xs.reverse
#eval xs.contains 4
#eval (xs.drop 1).take 2   -- xs[1:3]

/-!
Lists cannot be changed in place. `xs ++ [9]` builds a new list and leaves `xs` alone,
so there is no `append` that mutates. (Lean also has `Array`, written `#[1, 2, 3]`, for
fast indexing.)

## List comprehensions → map and filter

```python
print([x * x for x in range(6)])
print([x for x in range(10) if x % 3 == 0])
print([x * x for x in range(10) if x % 2 == 0])
print(any(x > 4 for x in xs), all(x > 0 for x in xs))
print(list(zip([1, 2, 3], ["a", "b", "c"])))
print(list(enumerate(["a", "b"])))
```
-/

#eval (List.range 6).map (fun x => x * x)
#eval (List.range 10).filter (· % 3 == 0)
#eval (List.range 10).filter (· % 2 == 0) |>.map (· ^ 2)
#eval xs.any (· > 4)
#eval xs.all (· > 0)
#eval [1, 2, 3].zip ["a", "b", "c"]
#eval ["a", "b"].zipIdx   -- enumerate: (item, index)

/-!
`e |>.map f` means `e.map f`. It lets you chain steps left to right, like a pipeline.
To add a list up with a running total, use `foldl`, Python's `functools.reduce`:
`xs.foldl (· + ·) 0`.

## Loops

Lean does have `for` and `while`, inside a `do` block with `let mut` variables. This is
real, compiled code that looks almost exactly like Python:

```python
def total(xs):
    s = 0
    for x in xs:
        s += x
    return s

def countdown(n):
    out = []
    while n > 0:
        out.append(n)
        n -= 1
    return out

print(total([1, 2, 3, 4]), countdown(5))
```
-/

def total (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

def countdown (n : Nat) : List Nat := Id.run do
  let mut out := []
  let mut k := n          -- arguments are fixed: copy n
  while k > 0 do
    out := out ++ [k]
    k := k - 1
  return out

#eval total [1, 2, 3, 4]
#eval countdown 5

/-!
`Id.run do` opens a small imperative block inside a pure function. The rest of the
course mostly uses **recursion** instead, because recursion is much easier to prove
things about.

## Recursion

Recursion looks the same as in Python. Pattern matching replaces the `if n == 0`:

```python
def fact(n):
    return 1 if n == 0 else n * fact(n - 1)

print(fact(10))
print(fact(30))
```
-/

def fact : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * fact n

#eval fact 10
#eval fact 30

/-!
## None → Option

In Python any value might secretly be `None`. In Lean "might be missing" is part of the
type, `Option Nat`, and `match` makes you handle both cases. You never get
`'NoneType' object has no attribute …`.

```python
def first(xs):
    return xs[0] if xs else None

def describe(x):
    if x is None:
        return "empty"
    return f"starts with {x}"

print(first([7, 8]), first([]))
print(describe(first([7, 8])), describe(first([])))
```
-/

def first (xs : List Nat) : Option Nat :=
  match xs with
  | []     => none
  | x :: _ => some x

def describe (o : Option Nat) : String :=
  match o with
  | none   => "empty"
  | some x => s!"starts with {x}"

#eval first [7, 8]
#eval first []
#eval describe (first [7, 8])
#eval describe (first [])

/-!
`x :: rest` is the pattern "a list whose first element is `x`". Use `_` for a part you
don't need.

## Exceptions → Except

Instead of raising, a function that can fail returns `Except Error Value`. Inside a `do`
block, `←` unwraps a success or stops at the first error. This is what exceptions do in
Python, but here you can see it in the type.

```python
def safe_div(a, b):
    if b == 0:
        raise ValueError("division by zero")
    return a // b

def both(a, b, c):
    x = safe_div(a, b)
    y = safe_div(x, c)
    return x + y

for args in [(100, 5, 2), (100, 0, 2)]:
    try:
        print(both(*args))
    except ValueError as e:
        print("error:", e)
```
-/

def safeDiv (a b : Nat) : Except String Nat :=
  if b == 0 then .error "division by zero"
  else .ok (a / b)

def both (a b c : Nat) : Except String Nat := do
  let x ← safeDiv a b
  let y ← safeDiv x c
  return x + y

#eval both 100 5 2
#eval both 100 0 2

/-!
## Dictionaries

`Std.HashMap` is Lean's `dict`. As with lists, `insert` gives back a new map.

```python
ages = {"ada": 36, "alan": 41}
print(ages["ada"], ages.get("bob", 0), "alan" in ages)
ages["bob"] = 20
print(len(ages))
```
-/

def ages : Std.HashMap String Nat := Std.HashMap.ofList [("ada", 36), ("alan", 41)]

#eval ages["ada"]?
#eval ages.getD "bob" 0
#eval ages.contains "alan"
#eval (ages.insert "bob" 20).size

/-!
## Classes → structures

A `structure` is a frozen dataclass. A method is a function named `Point.something`, and
you call it as `p.something`. To get a changed copy, write `{ p with x := 0 }`, which is
`dataclasses.replace`.

```python
from dataclasses import dataclass, replace

@dataclass(frozen=True)
class Point:
    x: int
    y: int

    def norm2(self):
        return self.x ** 2 + self.y ** 2

p = Point(3, 4)
print(p.x, p.norm2())
print(replace(p, x=0))
```
-/

structure Point where
  x : Int
  y : Int
  deriving Repr

def Point.norm2 (p : Point) : Int := p.x ^ 2 + p.y ^ 2

def p : Point := { x := 3, y := 4 }

#eval p.x
#eval p.norm2
#eval { p with x := 0 }

/-!
`deriving Repr` asks Lean to write the printing code, the way `@dataclass` writes
`__repr__` for you.

## Subclasses and match → inductive types

A family of shapes is a class hierarchy in Python. In Lean it is a single `inductive` type
with one constructor per kind of shape:

```python
from dataclasses import dataclass

@dataclass
class Circle:
    r: float

@dataclass
class Rect:
    w: float
    h: float

def area(s):
    match s:
        case Circle(r):
            return 3.14 * r * r
        case Rect(w, h):
            return w * h

print(area(Circle(1.0)), area(Rect(2.0, 3.0)))
```
-/

inductive Shape where
  | circle (r : Float)
  | rect (w h : Float)

def area : Shape → Float
  | .circle r => 3.14 * r * r
  | .rect w h => w * h

#eval area (.circle 1.0)
#eval area (.rect 2.0 3.0)

/-!
Try it: press Run, add `| triangle (b h : Float)` to `Shape`, and Lean immediately tells you
that `area` is **missing a case**. Python would quietly return `None`.

## Generics

```python
from typing import TypeVar, Optional
T = TypeVar("T")

def last(xs: list[T]) -> Optional[T]:
    return xs[-1] if xs else None

print(last([1, 2, 3]), last(["a", "b"]), last([]))
```
-/

def last {α : Type} (xs : List α) : Option α :=
  xs.reverse.head?

#eval last [1, 2, 3]
#eval last ["a", "b"]
#eval last ([] : List Nat)

/-!
`{α : Type}` plays the part of the `TypeVar`. The curly braces mean "Lean works out `α`
from the arguments", so you never pass it yourself. For an empty list there is nothing to
work it out from, so we say `([] : List Nat)`.

## print and main

Printing is a side effect, and in Lean side effects show up in the type. A function of
type `IO Unit` may do input and output; a function of type `Nat → Nat` cannot.

```python
def main():
    for i in range(1, 4):
        print(f"line {i}")

main()
```
-/

def main : IO Unit := do
  for i in [1, 2, 3] do
    IO.println s!"line {i}"

#eval main

/-!
To make a program you can run from the terminal, put `main` in a file and run
`lean --run File.lean`.

## From tests to proofs

This is where the two languages part ways. Python can check *some* inputs. Lean can do
that too, and then go further and prove a statement for **every** input.

```python
assert square(3) == 9
assert all(n <= square(n) for n in range(1000))
print("1000 tests passed")
```
-/

-- unit tests, checked every time the file compiles
#guard square 3 == 9
#guard (List.range 1000).all (fun n => n ≤ square n)

-- the same fact, as a theorem
example : square 3 = 9 := rfl

-- and a fact about every n, not just 1000 of them
theorem le_square (n : Nat) : n ≤ square n := by
  unfold square
  exact Nat.le_mul_self n

/-!
`#guard` fails the build if its test is false, just like `assert`. The `theorem` is a
different kind of thing: Lean has checked it for **all** natural numbers, including the
ones no test will ever reach. Lessons 2–5 show how to write such proofs, starting with
`1 + 2 + ⋯ + n = n(n+1)/2`.
-/

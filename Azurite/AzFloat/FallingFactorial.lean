/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PochhammerRat
import Azurite.AzRat.Unary

/-!
## The falling factorial `x (x − 1) ⋯ (x − n + 1)`

`fallingFactorialPrecRound x n p mode` is the falling factorial of a float `x` and a natural
number `n`, rounded to precision `p` in `mode`, with the comparison against the exact value;
`fallingFactorial x n` rounds to nearest at the precision of `x`.
`fallingFactorialRatPrecRound q n p mode` and `fallingFactorialRat q n p` take an `AzRat`.

* It is Pochhammer's symbol reflected: `x (x − 1) ⋯ (x − n + 1) = (−1)ⁿ (−x)ₙ`.  For an even
  `n` the functions are `pochhammerPrecRound` / `pochhammerRatPrecRound` at `−x`; for an odd
  `n`, the negation of their result in the opposite rounding mode.  Everything is inherited:
  the exact zero when a factor vanishes (`x` an integer with `0 ≤ x < n`), the exact path
  for cheap products, the loop at a cost independent of `n`.
* **Special values**: `1` for `n = 0` at every `x` but `NaN`; for `n ≥ 1`, `+∞` at `+∞` and
  `(−1)ⁿ ∞` at `−∞`.
* **Contract** (`Equiv/FallingFactorial.lean`): `fallingFactorialPrecRound_eq_or`,
  `fallingFactorialRatPrecRound_eq_or` — correctly rounded, or `(nan, .eq)` when the fuel
  runs out.
-/

namespace Azurite.AzFloat

/-- The result `r` of rounding `v` in the mode `−mode`, as the result of rounding `−v` in
`mode`. -/
def negRounded (r : AzFloat × Ordering) : AzFloat × Ordering := (-r.1, r.2.swap)

/-- The falling factorial of a finite `x` (zero included) for `n ≥ 1`. -/
def fallingReal (x : AzFloat) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if n % 2 = 0 then pochReal (-x) n p mode else negRounded (pochReal (-x) n p (-mode))

/-- `x (x − 1) ⋯ (x − n + 1)` rounded to precision `p` with `mode`, and the comparison with
the exact value (`(nan, .eq)` for `p = 0` unless the value is `0` or infinite, or if the fuel
runs out). -/
def fallingFactorialPrecRound (x : AzFloat) (n p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | x =>
    if n = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
    else
      match x with
      | infinity s => (infinity (s || n % 2 == 0), .eq)
      | x => fallingReal x n p mode

/-- The falling factorial rounded to nearest at the precision of `x`. -/
def fallingFactorial (x : AzFloat) (n : Nat) : AzFloat :=
  (fallingFactorialPrecRound x n (x.precision?.getD 1) .Nearest).1

/-- `q (q − 1) ⋯ (q − n + 1)` for a rational `q`, rounded to precision `p` with `mode`, and
the comparison with the exact value (`(nan, .eq)` for `p = 0` unless the value is `0`, or if
the fuel runs out). -/
def fallingFactorialRatPrecRound (q : AzRat) (n p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if n % 2 = 0 then pochhammerRatPrecRound (-q) n p mode
  else negRounded (pochhammerRatPrecRound (-q) n p (-mode))

/-- The falling factorial of a rational, rounded to nearest at precision `p`. -/
def fallingFactorialRat (q : AzRat) (n p : Nat) : AzFloat :=
  (fallingFactorialRatPrecRound q n p .Nearest).1

end Azurite.AzFloat

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Add
import Azurite.AzFloat.Compare
import Azurite.AzFloat.Shift
import Azurite.AzFloat.Ziv

/-!
## Correctly rounded sums

`sumPrecRound xs p mode` is the exact sum of the floats `xs`, rounded once to precision `p`
with `mode`, with the comparison of the result against the exact sum — the specification is the
fold of the two-operand `Spec.add` (so any `NaN`, or both infinities, give `NaN`, one infinity
gives itself, and otherwise the real sum is rounded).

Exponents are unbounded, so the exact sum may have an enormous number of bits (`2^(10^9) +
2^(−10^9)`), yet its rounding is cheap to decide.  The algorithm never forms a number wider than
a window of about `p` bits below the largest term:

1. **Window.**  Let `e` be the largest exponent among the (finite, nonzero) terms.  The terms
   with exponent at least `e − W`, `W = p + ⌈log₂ n⌉ + 3 + 64`, are summed *exactly* (each
   pairwise sum at a precision wide enough to be exact, `exactAdd`), giving `S₁`; the rest `R`
   satisfies `|ΣR| < T = 2^(e_R + ⌈log₂ |R|⌉)` for `e_R` the largest exponent in `R`.
2. **Cancellation.**  If `|S₁| < 2^(p+4) T` the window cancelled; `S₁` replaces the window and
   the procedure restarts on `S₁ :: R`, a shorter list (the window had at least two terms, since
   a single term exceeds `2^(p+4) T` by the choice of `W`).
3. **Bracket.**  Otherwise the exact sum lies in `(lo, hi)`, where `lo` and `hi` are `S₁ ∓ T`
   rounded outward at `W` bits (`T` may be far below the last bit of `S₁`, so the ends are not
   formed exactly); the bracket is narrower than the spacing of the `(p + 1)`-bit floats around
   it, and if no such float lies in it (`roundingPossible`, MCA Algorithm 3.1) the rounding is
   that of either end.
4. **Boundary.**  Otherwise exactly one `(p + 1)`-bit float `b` lies in the bracket — the
   truncation of `hi` — and the sum is on one side of it or equal to it, according to the sign
   of `(S₁ − b) + ΣR` (`S₁ − b` is a short exact difference).  That sign is computed exactly
   by the same windowing (`signSum`: when `|S₁| > T` the sign is that of `S₁`, otherwise
   restart on `S₁ :: R`).  Equality gives the exact rounding of `b`; otherwise the midpoint of
   the half-bracket, which rounds like the sum.

Each restart drops at least one term, so the work is `O(n)` windows of `O(p + log n)` bits plus
the exact window sums.  Everything is derived from first principles; `Equiv/Sum.lean` proves
`sumPrecRound_eq`.
-/

namespace Azurite.AzFloat

/-- The exponent of a finite nonzero float, `0` for the others. -/
def expOf (x : AzFloat) : AzInt := x.exponent?.getD 0

/-- A precision at which the sum of two floats is exactly representable: from the bit above
the top bit of the larger (the carry) down to the lowest bit of either. -/
def exactSumPrec (x y : AzFloat) : Nat :=
  match x, y with
  | finite _ e₁ p₁ _ _, finite _ e₂ p₂ _ _ =>
    let top := max e₁ e₂ + 1
    let bot := min (e₁ - (AzNat.ofNat p₁).toAzInt) (e₂ - (AzNat.ofNat p₂).toAzInt)
    (top - bot).abs.toNat
  | finite _ _ p _ _, _ => p
  | _, finite _ _ p _ _ => p
  | _, _ => 1

/-- The exact sum of two finite floats (the rounding is exact at `exactSumPrec`). -/
def exactAdd (x y : AzFloat) : AzFloat := (addPrecRound x y (exactSumPrec x y) .Floor).1

/-- The exact difference of two finite floats. -/
def exactSub (x y : AzFloat) : AzFloat := exactAdd x (-y)

/-- The exact sum of a list of finite floats. -/
def exactSum (l : List AzFloat) : AzFloat := l.foldl exactAdd zero

/-- The largest exponent in a list (`0` for the empty list). -/
def maxExponent : List AzFloat → AzInt
  | [] => 0
  | x :: xs => xs.foldl (fun a y => max a (expOf y)) (expOf x)

/-- The bit length of the length of a list: `l.length < 2^(lengthBits l)`. -/
def lengthBits (l : List AzFloat) : Nat := (AzNat.ofNat l.length).size

/-- Split off the terms whose exponent is within `W` of the largest. -/
def splitWindow (l : List AzFloat) (W : Nat) : List AzFloat × List AzFloat :=
  let emax := maxExponent l
  l.partition fun x => emax - expOf x ≤ (AzNat.ofNat W).toAzInt

/-- `2^(e + k)`, a bound on the sum of fewer than `2^k` terms each below `2^e` in magnitude. -/
def tailBound (rest : List AzFloat) : AzFloat :=
  powerOf2 (maxExponent rest + (AzNat.ofNat (lengthBits rest)).toAzInt)

/-- `|x| < y`, for finite `x`, `y`. -/
def absLt (x y : AzFloat) : Bool := partialCompare x.abs y == some .lt

/-- `|x| > y`, for finite `x`, `y`. -/
def absGt (x y : AzFloat) : Bool := partialCompare x.abs y == some .gt

/-- The sign of a finite float as a comparison with zero. -/
def signOf (x : AzFloat) : Ordering := (partialCompare x zero).getD .eq

/-- The sign of the exact sum of a list of finite nonzero floats, by windowing (`fuel` exceeding
the length suffices). -/
def signSum : Nat → List AzFloat → Ordering
  | 0, _ => .eq
  | fuel + 1, l =>
    match l with
    | [] => .eq
    | _ =>
      let (win, rest) := splitWindow l (lengthBits l + 2)
      let s₁ := exactSum win
      match rest with
      | [] => signOf s₁
      | _ =>
        if absGt s₁ (tailBound rest) then signOf s₁
        else signSum fuel (if s₁ = zero then rest else s₁ :: rest)

/-- The correctly rounded sum of a list of finite nonzero floats (`fuel` exceeding the length
suffices; the `NaN` after exhaustion is never reached). -/
def sumFinite (p : Nat) (mode : RoundingMode) : Nat → List AzFloat → AzFloat × Ordering
  | 0, _ => (nan, .eq)
  | fuel + 1, l =>
    match l with
    | [] => (zero, .eq)
    | _ =>
      let (win, rest) := splitWindow l (p + lengthBits l + 3 + zivGuardBits)
      let s₁ := exactSum win
      match rest with
      | [] => setPrecRound s₁ p mode
      | _ =>
        let T := tailBound rest
        if absLt s₁ (T <<< (p + 4)) then
          sumFinite p mode fuel (if s₁ = zero then rest else s₁ :: rest)
        else
          let w := p + lengthBits l + 3 + zivGuardBits
          let lo := (addPrecRound s₁ (-T) w .Floor).1
          let hi := -(addPrecRound (-s₁) (-T) w .Floor).1
          match roundingPossible (fun q m => setPrecRound lo q m)
              (fun q m => setPrecRound hi q m) p mode with
          | some r => r
          | none =>
            let b := (setPrecRound hi (p + 1) .Floor).1
            let d := exactSub s₁ b
            match signSum (rest.length + 2) (if d = zero then rest else d :: rest) with
            | .eq => setPrecRound b p mode
            | .lt => setPrecRound (exactAdd lo b >>> (1 : Nat)) p mode
            | .gt => setPrecRound (exactAdd b hi >>> (1 : Nat)) p mode

/-- **The correctly rounded sum** of a list of floats at precision `p` with `mode`, and the
comparison of the result with the exact sum. -/
def sumPrecRound (xs : List AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if xs.any isNaN then (nan, .eq)
  else
    let pos := xs.any fun x => x == infinity true
    let neg := xs.any fun x => x == infinity false
    if pos && neg then (nan, .eq)
    else if pos then (infinity true, .eq)
    else if neg then (infinity false, .eq)
    else
      let l := xs.filter isNormal
      sumFinite p mode (l.length + 1) l

end Azurite.AzFloat

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.PiBracket
import Azurite.AzFloat.Ln2Bracket
import Azurite.AzFloat.Div
import Azurite.AzFloat.Conversion

/-!
## The natural logarithm

`ln x` by the AGM (MCA §4.8.2, `Chapter4/AGMLog.lean`, `AGMLogBound.lean`): for `0 < k ≤ 1`,
`|π/(2 AGM(1, k)) − ln(4/k)| ≤ (k²/4)(2 − ln k)`.  At working precision `w`, with
`h = ⌊w/4⌋ + 2`, the argument is scaled to `y = x · 2^ℓ ∈ [2^(2h+1), 2^(2h+2))`, so that
`k = 4/y ∈ [2^(−2h), 2^(1−2h)]` and the error is below `2^(size(2h+2) − 4h) ≤ 2^(lg w − w − 6)`;
then `ln x = π/(2 AGM(1, k)) − ℓ ln 2` up to that error.  Everything runs on enclosures: `k` by
directed division, the AGM by the interval iteration of `Agm.lean` for a fixed number of steps
(`lnSteps w = 2 ⌈lg 2h⌉ + 3`, after which `a − b ≤ 2^(3 − 5h)` by `agm_log_iterations` and two
quadratic steps), `π` from `piBracket`, `ℓ ln 2` from the float bracket `ln2Bracket` (`|ℓ|` times
the ends, outward, the signs restored by negation).

The bracket's width is at most `2^40 (w + |e| + 8)^5 2^(−w)` (`Equiv/LnBracket.lean`,
`lnBracket_spec`: the interval AGM keeps *relative*
errors, which grow only additively with the steps since the AGM is homogeneous), and `ln x`
is irrational for every float `x ≠ 1` (`irrational_log_rat`), so the certified Ziv loop needs no
fuel: `lnPrecRound` is total and proven correctly rounded.  Special values: `ln NaN = NaN`,
`ln (+∞) = +∞`, `ln 0 = −∞`, `ln x = NaN` for `x < 0`, `ln 1 = 0` exactly.
-/

namespace Azurite.AzFloat

/-- The interval AGM step iterated a fixed number of times. -/
def agmIterN (w : Nat) : Nat → AgmBounds → AgmBounds
  | 0, s => s
  | n + 1, s => agmIterN w n (agmStep w s)

/-- `h = ⌊w/4⌋ + 2`: the scaled argument has `2h + 2` bits, `k ≥ 2^(−2h)`. -/
def lnH (w : Nat) : Nat := w / 4 + 2

/-- The number of AGM steps: `2 ⌈lg 2h⌉ + 1` to reach the quadratic regime with gap `≤ 8/2^(2h)`
(`agm_log_iterations`), then two more. -/
def lnSteps (w : Nat) : Nat := 2 * Nat.clog 2 (2 * lnH w) + 3

/-- The two ends of the bracket of `ln x` at working precision `w`, for a finite positive `x`
with exponent `e` (`2^(e−1) ≤ x < 2^e`). -/
def lnBracket (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let h := lnH w
  let l : AzInt := (AzNat.ofNat (2 * h + 2)).toAzInt - e
  let y := x <<< l
  let kLo := (divPrecRound (one <<< (2 : Nat)) y w .Floor).1
  let kHi := (divPrecRound (one <<< (2 : Nat)) y w .Ceiling).1
  let s := agmIterN w (lnSteps w) ⟨one, one, kLo, kHi⟩
  let pb := piBracket w
  let qLo := (divPrecRound (pb.1 >>> (1 : Nat)) s.aHi w .Floor).1
  let qHi := (divPrecRound (pb.2 >>> (1 : Nat)) s.bLo w .Ceiling).1
  let eps := powerOf2 ((AzNat.ofNat (Nat.size (2 * h + 2))).toAzInt
    - (AzNat.ofNat (4 * h)).toAzInt)
  let lb := ln2Bracket w
  let m := ofAzNat l.abs
  let A := (mulPrecRound m lb.1 w .Floor).1
  let B := (mulPrecRound m lb.2 w .Ceiling).1
  let LLo := if l.sign then A else -B
  let LHi := if l.sign then B else -A
  ((subPrecRound (subPrecRound qLo eps w .Floor).1 LHi w .Floor).1,
    (subPrecRound (addPrecRound qHi eps w .Ceiling).1 LLo w .Ceiling).1)

/-- The bracket as a pair of `Roundable`s. -/
def lnApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := lnBracket x e w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `ln q` from a float `y = ⌊q⌋_w` below `q` (within a relative `2·2^(−w)`):
`ln y` by `lnBracket` (one AGM run), the upper end widened by `2^(2−w) ≥ ln (q/y)`.  (If `y` is
not a positive finite float the ends are `NaN`; the callers never ask.) -/
def lnFloorBracket (y : AzFloat) (w : Nat) : AzFloat × AzFloat :=
  match y with
  | y@(finite true e _ _ _) =>
    let b := lnBracket y e w
    (b.1, (addPrecRound b.2 (powerOf2 (((2 : Nat) : AzInt) - (w : AzInt))) w .Ceiling).1)
  | _ => (nan, nan)

/-- `lnFloorBracket` as a pair of `Roundable`s. -/
def lnFloorApprox (y : AzFloat) (w : Nat) : Roundable × Roundable :=
  let b := lnFloorBracket y w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `ln q` for a positive rational `q` at working precision `w`: `lnFloorApprox`
of `⌊q⌋_w`. -/
def lnRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  lnFloorApprox (ofAzRatRound q w .Floor).1 w

/-- The bracket of `ln (1 + x)` for a float `x > −1` at working precision `w`: `lnFloorApprox` of
`⌊1 + x⌋_w` (one rounded addition; for `|x| < 1` the caller starts `w` high enough that the
rounding keeps the leading bits of `x`). -/
def ln1pApprox (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  lnFloorApprox (addPrecRound one x w .Floor).1 w

end Azurite.AzFloat

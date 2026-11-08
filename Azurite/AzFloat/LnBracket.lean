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

Two paths, selected by the working precision `w` (`lnBracketCore`, `lnBracket`): the **series
path** below `lnSeriesThreshold` (DLMF 4.45.1–4.45.2 and 4.6.4: `x = m₀ 2^ℓ`, a few square
roots bring `m₀` close to `1`, then `ln y = 2 Σ t^(2j+1)/(2j+1)` with `t = (y − 1)/(y + 1)`,
everything rounded down with an exact a priori slack; `lnSeriesBracket`, documented there), and
the **AGM path** above it (`lnAgmBracket`), described here.

`ln x` by the AGM (MCA §4.8.2, `Chapter4/AGMLog.lean`, `AGMLogBound.lean`): for `0 < k ≤ 1`,
`|π/(2 AGM(1, k)) − ln(4/k)| ≤ (k²/4)(2 − ln k)`.  At working precision `w`, with
`h = ⌊w/4⌋ + 2`, the argument is scaled to `y = x · 2^ℓ ∈ [2^(2h+1), 2^(2h+2))`, so that
`k = 4/y ∈ [2^(−2h), 2^(1−2h)]` and the error is below `2^(size(2h+2) − 4h) ≤ 2^(lg w − w − 6)`;
then `ln x = π/(2 AGM(1, k)) − ℓ ln 2` up to that error.  The AGM runs on a **single pair**
with every operation rounded down (`agmStepLo`, half the work of the interval iteration
`agmStep`) for a fixed number of steps (`lnSteps w = 2 ⌈lg 2h⌉ + 3`, after which
`a − b ≤ 2^(3 − 5h)` by `agm_log_iterations` and two quadratic steps), from `(1, ⌊k⌋_w)`: the
computed `a_S, b_S` satisfy `a_S ≤ A_S`, `b_S ≤ B_S` and lie within the relative error
`δ = (2 + 8S) 2^(−w)` of the exact iterates (`relLower_agmIterLoN`; the AGM is homogeneous,
so relative errors add up over the steps), hence `b_S ≤ AGM(1, k) ≤ a_S + δ` (as `A_S ≤ 1`),
and the float `δ` is exact (`lnAgmDelta`).  `π` is from `piBracket`, `ℓ ln 2` from the float
bracket `ln2Bracket` (`|ℓ|` times the ends, outward, the signs restored by negation).

The bracket's width on either path is at most `2^40 (w + |e| + 8)^5 2^(−w)`
(`Equiv/LnBracket.lean`, `lnBracket_spec`: the rounded-down AGM keeps *relative* errors, which
grow only additively with the steps since the AGM is homogeneous), and `ln x`
is irrational for every float `x ≠ 1` (`irrational_log_rat`), so the certified Ziv loop needs no
fuel: `lnPrecRound` is total and proven correctly rounded.  Special values: `ln NaN = NaN`,
`ln (+∞) = +∞`, `ln 0 = −∞`, `ln x = NaN` for `x < 0`, `ln 1 = 0` exactly.
-/

namespace Azurite.AzFloat

/-- The interval AGM step iterated a fixed number of times (kept for the benchmark comparison
with `agmIterLoN`). -/
def agmIterN (w : Nat) : Nat → AgmBounds → AgmBounds
  | 0, s => s
  | n + 1, s => agmIterN w n (agmStep w s)

/-- `h = ⌊w/4⌋ + 2`: the scaled argument has `2h + 2` bits, `k ≥ 2^(−2h)`. -/
def lnH (w : Nat) : Nat := w / 4 + 2

/-- The number of AGM steps: `2 ⌈lg 2h⌉ + 1` to reach the quadratic regime with gap `≤ 8/2^(2h)`
(`agm_log_iterations`), then two more. -/
def lnSteps (w : Nat) : Nat := 2 * Nat.clog 2 (2 * lnH w) + 3

/-- The a priori relative error `δ = (2 + 8S) · 2^(−w)` of `S` rounded-down AGM steps at
precision `w`, as an exact float. -/
def lnAgmDelta (w S : Nat) : AzFloat :=
  ofAzNat (AzNat.ofNat (8 * S + 2)) <<< (-(AzNat.ofNat w).toAzInt)

/-- The two ends of the bracket of `ln x` at working precision `w` by the **AGM path**, for a
finite positive `x` with exponent `e` (`2^(e−1) ≤ x < 2^e`), from given brackets `pb` of `π` and
`lb` of `ln 2` (computed at precision `w` or finer). -/
def lnAgmBracket (pb lb : AzFloat × AzFloat) (x : AzFloat) (e : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  let h := lnH w
  let l : AzInt := (AzNat.ofNat (2 * h + 2)).toAzInt - e
  let y := x <<< l
  let kLo := (divPrecRound (one <<< (2 : Nat)) y w .Floor).1
  let S := lnSteps w
  let s := agmIterLoN w S (one, kLo)
  let aHi := (addPrecRound s.1 (lnAgmDelta w S) w .Ceiling).1
  let qLo := (divPrecRound (pb.1 >>> (1 : Nat)) aHi w .Floor).1
  let qHi := (divPrecRound (pb.2 >>> (1 : Nat)) s.2 w .Ceiling).1
  let eps := powerOf2 ((AzNat.ofNat (Nat.size (2 * h + 2))).toAzInt
    - (AzNat.ofNat (4 * h)).toAzInt)
  let m := ofAzNat l.abs
  let A := (mulPrecRound m lb.1 w .Floor).1
  let B := (mulPrecRound m lb.2 w .Ceiling).1
  let LLo := if l.sign then A else -B
  let LHi := if l.sign then B else -A
  ((subPrecRound (subPrecRound qLo eps w .Floor).1 LHi w .Floor).1,
    (subPrecRound (addPrecRound qHi eps w .Ceiling).1 LLo w .Ceiling).1)

/-! ### The series path -/

/-- The number of square roots taken before the series at working precision `w`:
`⌊lg w⌋ − 3` (tuned, see `docs/azfloat_plan.md`). -/
def lnSeriesK (w : Nat) : Nat := Nat.log 2 w - 3

/-- The number of series terms after `k` square roots: `(k + 1)(2J + 1) ≥ w + 1`
(`lnSeriesTerms_spec`), so that the tail `Σ_{j ≥ J} t^(2j+1)/(2j+1) ≤ (4/3) t^(2J+1)` is at most
`(4/3) 2^(−w−1)` for `t ≤ 2^(−k−1)`. -/
def lnSeriesTerms (k w : Nat) : Nat := (w + 1) / (2 * (k + 1)) + 1

/-- `k` square roots, each rounded down and clamped at `1` (the clamp never changes the value,
`√y ≥ 1` for `y ≥ 1` and `1` is a float, but keeps the proof simple). -/
def lnSqrtIter (w : Nat) : Nat → AzFloat → AzFloat
  | 0, y => y
  | k + 1, y => lnSqrtIter w k (maxOf (sqrtPrecRound y w .Floor).1 one)

/-- `n` more terms of `Σ_j t^(2j+1)/(2j+1)` from term `j`, every operation rounded down: the
state is `(s, p)` with `s` the sum so far and `p = t^(2j+1)`; `t2 = t²`. -/
def lnSeriesLoop (w : Nat) (t2 : AzFloat) : Nat → Nat → AzFloat × AzFloat → AzFloat × AzFloat
  | 0, _, sp => sp
  | n + 1, j, sp =>
    let term := (divPrecRound sp.2 (ofAzNat (AzNat.ofNat (2 * j + 1))) w .Floor).1
    lnSeriesLoop w t2 n (j + 1)
      ((addPrecRound sp.1 term w .Floor).1, (mulPrecRound sp.2 t2 w .Floor).1)

/-- The two ends of the bracket of `ln x` at working precision `w` by the **series path**
(DLMF 4.45.1–4.45.2 and 4.6.4): `x = m₀ 2^ℓ` with `m₀ ∈ [1, 2)`, `ℓ = e − 1`; `y = m₀^(1/2^k)` by
`k = lnSeriesK w` rounded-down square roots; `t = (y − 1)/(y + 1) ≤ 2^(−k−1)`;
`ln y = 2 Σ t^(2j+1)/(2j+1)` summed for `J = lnSeriesTerms k w` terms with every operation
rounded down, so `2^(k+1) s ≤ ln m₀`; the exact float `E = (20J + 18) 2^(k−w)` covers the
roundings, the tail of the series and the square roots (`lnSeriesBracket_spec`); then
`± ℓ ln 2` from the bracket `lb` of `ln 2` exactly as in `lnAgmBracket`. -/
def lnSeriesBracket (lb : AzFloat × AzFloat) (x : AzFloat) (e : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  let k := lnSeriesK w
  let J := lnSeriesTerms k w
  let l : AzInt := e - 1
  let y := lnSqrtIter w k (x <<< (-l))
  let num := (subPrecRound y one w .Floor).1
  let den := (addPrecRound y one w .Ceiling).1
  let t := (divPrecRound num den w .Floor).1
  let t2 := (sqrPrecRound t w .Floor).1
  let s := (lnSeriesLoop w t2 J 0 (zero, t)).1
  let A := s <<< ((k + 1 : Nat) : AzInt)
  let E := ofAzNat (AzNat.ofNat (20 * J + 18)) <<< ((k : AzInt) - (w : AzInt))
  let m := ofAzNat l.abs
  let B := (mulPrecRound m lb.1 w .Floor).1
  let C := (mulPrecRound m lb.2 w .Ceiling).1
  let LLo := if l.sign then B else -C
  let LHi := if l.sign then C else -B
  ((addPrecRound A LLo w .Floor).1,
    (addPrecRound (addPrecRound A E w .Ceiling).1 LHi w .Ceiling).1)

/-! ### The dispatcher -/

/-- Working precisions up to this take the series path, above it the AGM (tuned, see
`docs/azfloat_plan.md`). -/
def lnSeriesThreshold : Nat := 512

/-- The two ends of the bracket of `ln x` at working precision `w`, from given brackets `pb` of
`π` (needed above `lnSeriesThreshold` only) and `lb` of `ln 2`, computed at precision `w` or
finer: the series path up to `lnSeriesThreshold`, the AGM path above. -/
def lnBracketCore (pb lb : AzFloat × AzFloat) (x : AzFloat) (e : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  if w ≤ lnSeriesThreshold then lnSeriesBracket lb x e w else lnAgmBracket pb lb x e w

/-- The two ends of the bracket of `ln x` at working precision `w`, for a finite positive `x`
with exponent `e` (`2^(e−1) ≤ x < 2^e`): `lnBracketCore` with the brackets of `π` and `ln 2`
computed at precision `w` (`lnBracket_eq_core`; the bracket of `π` is only computed on the AGM
path). -/
def lnBracket (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  if w ≤ lnSeriesThreshold then lnSeriesBracket (ln2Bracket w) x e w
  else lnAgmBracket (piBracket w) (ln2Bracket w) x e w

/-- The bracket as a pair of `Roundable`s. -/
def lnApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := lnBracket x e w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- **Precomputed constants for `ln`**: the brackets of `π` and `ln 2` at working precision
`W`, to be shared by many logarithms at the same precision (they are about half the cost of one
`ln`).  The proof fields pin the brackets to `piBracket W`/`ln2Bracket W` and are erased at
runtime; build one with `LnConsts.make W` (or `LnConsts.forPrecision p`, `Ln.lean`). -/
structure LnConsts where
  /-- The working precision of the stored brackets. -/
  W : Nat
  /-- The bracket of `π` at precision `W` (only needed, and only computed, above
  `lnSeriesThreshold`). -/
  pi : AzFloat × AzFloat
  /-- The bracket of `ln 2` at precision `W`. -/
  ln2 : AzFloat × AzFloat
  pi_eq : lnSeriesThreshold < W → pi = piBracket W
  ln2_eq : ln2 = ln2Bracket W

/-- The constants for `ln` at working precision `W`. -/
def LnConsts.make (W : Nat) : LnConsts :=
  ⟨W, if lnSeriesThreshold < W then piBracket W else (nan, nan), ln2Bracket W,
    fun h => ite_eq_left h, rfl⟩

/-- `lnBracket x e w` with the brackets of `π` and `ln 2` taken from `c` when its precision
suffices (`w ≤ c.W`), computed afresh otherwise (the later Ziv levels). -/
def lnBracketWith (c : LnConsts) (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  if w ≤ c.W then lnBracketCore c.pi c.ln2 x e w else lnBracket x e w

/-- `lnBracketWith` as a pair of `Roundable`s. -/
def lnApproxWith (c : LnConsts) (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := lnBracketWith c x e w
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
def lnP1Approx (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  lnFloorApprox (addPrecRound one x w .Floor).1 w

end Azurite.AzFloat

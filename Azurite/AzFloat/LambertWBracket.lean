/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.Float64
import Azurite.AzFloat.PowBracket
import Azurite.AzFloat.Interval

/-!
## Brackets of the real Lambert `W` function

`W₀ x` (`x ≥ −e⁻¹`) and `W₋₁ x` (`−e⁻¹ ≤ x < 0`) are the two real roots of `W e^W = x`
(DLMF §4.13; `lambertW0`, `lambertWm1` of `DLMF/Chapter4/Section13Real.lean`).  A verified
bracket comes from an **unverified** candidate `n` (Halley's iteration, `halleyCandidate`) and a
rigorous enclosure `F` of `n eⁿ` (`mulExpBracket`): with `δ ≥ |x − n eⁿ|` from `F` and a lower
bound `D` of the derivative `|(1 + t) eᵗ|` on an interval `I ∋ W, n`, the mean value theorem
gives `|W − n| ≤ δ / D` (`mvtRound`, `Transcendental/LambertW.lean`); three rounds, each
shrinking `I` and hence raising `D`, make the bracket essentially optimal.  The candidate is
never trusted: if the result is not narrower than a target the loop falls back to a bisection
on a dyadic grid (`bisectGrid`), whose halving is trivially provable.

The two decisions that need arbitrary precision — the sign of `q = 1 + e x` (the domain
boundary `−e⁻¹`, `qAt`/`qEncl`) and the side of a test point (`sideAt`/`sideOf`) — are
certified searches (`findSome`): `x` is rational, `−e⁻¹` and the roots are irrational, so some
precision decides, and the proof of that is the (erased) termination certificate.

**The target.**  `x` enters through an enclosure function `xAt : Nat → AzFloat × AzFloat`
(precision ↦ floats below and above `x`): `floatAt x = fun _ => (x, x)` for a float and
`ratAt q` (the `Floor` and `Ceiling` roundings of `q`) for an `AzRat`, so one pipeline serves
`lambertW0PrecRound` and `lambertW0RatPrecRound`.

* `aprioriW0 x qE P`, `aprioriWm1 x qE P`: proven enclosures `[a₀, b₀]` with `a₀ ≥ −1` (`W₀`)
  or `b₀ ≤ −1` (`W₋₁`): `x/(1+x) ≤ W₀ x ≤ x` (`0 ≤ x < 3`), `ln x − ln ln x ≤ W₀ x ≤ ln x`
  (`x ≥ 3`), `−1 + √(2q/e) ≤ W₀ x ≤ min(0, −1 + √(2q))` (`x < 0`); `W₋₁ x ≤ −1 − √(2q)`,
  `−1 − √(2eq) ≤ W₋₁ x` (`q ≤ 1/4`) or `ln y − ln(−ln y) − 1 ≤ W₋₁ x` (`y = −x`).
* `lambertBracket branch x qE I₀ hs w`: the bracket at Ziv level `w`, working precision
  `w + 10 + compBits qE` (the extra bits near the branch point, where the derivative is
  `≈ √(2q)/e`).
-/

namespace Azurite.AzFloat

/-! ### The target -/

/-- The enclosure function of a float: the float itself at every precision. -/
def floatAt (x : AzFloat) : Nat → AzFloat × AzFloat := fun _ => (x, x)

/-- The enclosure function of a rational: its `Floor` and `Ceiling` roundings. -/
def ratAt (q : AzRat) : Nat → AzFloat × AzFloat :=
  fun P => ((ofAzRatRound q P .Floor).1, (ofAzRatRound q P .Ceiling).1)

/-! ### A certified search -/

/-- The first `f k = some a` (`k = 0, 1, 2, …`), given that one exists; the certificate is
erased at run time. -/
def findSome {α : Type} (f : Nat → Option α) (h : ∃ k, (f k).isSome = true) : α :=
  go h 0 (fun _ hg => absurd hg (Nat.not_lt_zero _))
where
  go (h : ∃ k, (f k).isSome = true) (k : Nat) (hk : ∀ j < k, (f j).isSome = false) : α :=
    match hf : f k with
    | some a => a
    | none => go h (k + 1) (fun j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
        · exact hk j hj'
        · rw [hf]; rfl)
  termination_by Nat.find h - k
  decreasing_by
    have hlt : k < Nat.find h := by
      by_contra hcon
      push Not at hcon
      have hspec := Nat.find_spec h
      rcases Nat.lt_or_eq_of_le hcon with hlt' | heq
      · rw [hk _ hlt'] at hspec; exact Bool.false_ne_true hspec
      · rw [heq, hf] at hspec; exact Bool.false_ne_true hspec
    omega

/-! ### `t eᵗ` and the side of a test point -/

/-- An enclosure of `t eᵗ` at precision `P` (any sign of `t`). -/
def mulExpBracket (t : AzFloat) (P : Nat) : AzFloat × AzFloat :=
  mulBracketAny t (expBracketAt t P) P

/-- `some true` when `m eᵐ < x` is certain at precision `P`, `some false` when `m eᵐ > x` is,
`none` otherwise (`x` through its enclosure at precision `P`). -/
def sideAt (xAt : Nat → AzFloat × AzFloat) (m : AzFloat) (P : Nat) : Option Bool :=
  let X := xAt P
  let F := mulExpBracket m P
  if lt F.2 X.1 then some true else if lt X.2 F.1 then some false else none

/-- The side of `m` relative to the root, decided at some precision `64 · 2^k`. -/
def sideOf (xAt : Nat → AzFloat × AzFloat) (m : AzFloat)
    (h : ∃ k, (sideAt xAt m (64 * 2 ^ k)).isSome = true) : Bool :=
  findSome (fun k => sideAt xAt m (64 * 2 ^ k)) h

/-! ### `q = 1 + e x` -/

/-- Bounds `lo ≤ q ≤ hi` of `q = 1 + e x` for `x < 0` at precision `P`, from the bracket
`[c, d]` of `e` (nonnegative lower end) and the enclosure `[x₁, x₂]` of `x`:
`1 + d x₁ ≤ 1 + e x ≤ 1 + c x₂`. -/
def qBounds (xAt : Nat → AzFloat × AzFloat) (P : Nat) : AzFloat × AzFloat :=
  let E := Encl.exp P one
  let X := xAt P
  ((addPrecRound one (mulPrecRound E.2 X.1 P .Floor).1 P .Floor).1,
    (addPrecRound one (mulPrecRound E.1 X.2 P .Ceiling).1 P .Ceiling).1)

/-- A decision about `q = 1 + e x` for `x < 0` at precision `P`: `some none` when `q < 0` is
certain (out of the domain), `some (some (lo, hi))` when `0 < lo ≤ q ≤ hi` is, `none`
otherwise. -/
def qAt (xAt : Nat → AzFloat × AzFloat) (P : Nat) : Option (Option (AzFloat × AzFloat)) :=
  let b := qBounds xAt P
  if lt b.2 zero then some none else if lt zero b.1 then some (some b) else none

/-- The decision about `q`, at some precision `64 · 2^k`. -/
def qEncl (xAt : Nat → AzFloat × AzFloat) (h : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true) :
    Option (AzFloat × AzFloat) :=
  findSome (fun k => qAt xAt (64 * 2 ^ k)) h

/-- The extra working bits near the branch point: about `−lg(q)/2 + 2`. -/
def compBits (qE : Option (AzFloat × AzFloat)) : Nat :=
  match qE with
  | some (lo, _) =>
    match lo.exponent? with
    | some e => if e.sign then 0 else (e.abs.toNat + 1) / 2 + 2
    | none => 0
  | none => 0

/-- Near the branch point (`compBits ≠ 0`) the enclosure of `q` is recomputed at
`128 + 2 compBits` bits (about 64 relative bits) and kept when its lower end is positive;
otherwise the first enclosure already has 60 relative bits. -/
def qTight (xAt : Nat → AzFloat × AzFloat) (q : AzFloat × AzFloat) : AzFloat × AzFloat :=
  if compBits (some q) = 0 then q
  else
    let b := qBounds xAt (128 + 2 * compBits (some q))
    if lt zero b.1 then b else q

/-! ### A priori enclosures -/

/-- `ln t` rounded down and up at precision `P`. -/
def lnBounds (t : AzFloat) (P : Nat) : AzFloat × AzFloat :=
  ((lnPrecRound t P .Floor).1, (lnPrecRound t P .Ceiling).1)

/-- A proven enclosure of `W₀ x` for `x > 0` from the enclosure `[x₁, x₂]` of `x` at precision
`P`: `[x₁/(1+x₁), x₂]` for `x₁ < 3`, `[ln x₁ − ln ln x₂, ln x₂]` for `x₁ ≥ 3`. -/
def aprioriW0Pos (xAt : Nat → AzFloat × AzFloat) (P : Nat) : AzFloat × AzFloat :=
  let X := xAt P
  if lt X.1 (ofAzNat (AzNat.ofNat 3)) then
    ((divPrecRound X.1 (addPrecRound one X.1 P .Ceiling).1 P .Floor).1, X.2)
  else
    let l₁ := (lnPrecRound X.1 P .Floor).1
    let l₂ := (lnPrecRound X.2 P .Ceiling).1
    ((subPrecRound l₁ (lnPrecRound l₂ P .Ceiling).1 P .Floor).1, l₂)

/-- A proven enclosure of `W₀ x` for `−e⁻¹ < x < 0` from an enclosure `[lo, hi]` of `q`:
`[max(−1, −1 + √(2 lo/e)), min(0, −1 + √(2 hi))]`. -/
def aprioriW0Neg (qlo qhi : AzFloat) (P : Nat) : AzFloat × AzFloat :=
  let E := expBracketAt one P
  let r := (sqrtPrecRound (divPrecRound (qlo <<< AzInt.ofInt 1) E.2 P .Floor).1 P .Floor).1
  let s := (sqrtPrecRound (qhi <<< AzInt.ofInt 1) P .Ceiling).1
  (maxOf (-one) (addPrecRound (-one) r P .Floor).1, minOf zero (addPrecRound (-one) s P .Ceiling).1)

/-- A proven enclosure of `W₋₁ x` for `−e⁻¹ < x < 0` from an enclosure `[lo, hi]` of `q` and the
enclosure `[x₁, x₂]` of `x`: upper end `−1 − √(2 lo)`; lower end `−1 − √(2 e hi)` when
`hi ≤ 1/4`, else `ln y − ln(−ln y) − 1` (`y = −x`) from `l₁ ≤ ln(−x₂) ≤ ln y`:
`l₁ − ln(−l₁) − 1`. -/
def aprioriWm1 (xAt : Nat → AzFloat × AzFloat) (qlo qhi : AzFloat) (P : Nat) :
    AzFloat × AzFloat :=
  let E := expBracketAt one P
  let s := (sqrtPrecRound (qlo <<< AzInt.ofInt 1) P .Floor).1
  let b := minOf (-one) (subPrecRound (-one) s P .Ceiling).1
  let a :=
    if le qhi (powerOf2 (AzInt.ofInt (-2))) then
      let t := (sqrtPrecRound (mulPrecRound (E.2 <<< AzInt.ofInt 1) qhi P .Ceiling).1 P .Ceiling).1
      (subPrecRound (-one) t P .Floor).1
    else
      let L := lnBounds (-(xAt P).2) P
      let v := -L.1
      (subPrecRound (subPrecRound L.1 (lnPrecRound v P .Ceiling).1 P .Floor).1 one P .Floor).1
  (a, b)

/-! ### The mean-value round -/

/-- `δ ≥ |x − n eⁿ|` from an enclosure `F` of `n eⁿ` and the enclosure `X` of `x`. -/
def mvtDelta (X F : AzFloat × AzFloat) (P : Nat) : AzFloat :=
  maxOf (subPrecRound F.2 X.1 P .Ceiling).1 (subPrecRound X.2 F.1 P .Ceiling).1

/-- A lower bound of `eᵃ` from a lower bound `elo0 ≤ eⁿ` of the candidate's exponential:
`elo0 · (1 + a − n)` when that factor is positive (`eᵗ ≥ 1 + t`), else the exponential of `a` at
64 bits.  (The first form costs nothing: the exponential of `n` is computed anyway.) -/
def derivLowerExp (a n elo0 : AzFloat) : AzFloat :=
  let c := (addPrecRound (subPrecRound a n 64 .Floor).1 one 64 .Floor).1
  if lt zero c then (mulPrecRound elo0 c 64 .Floor).1 else (Encl.exp 64 a).1

/-- One mean-value round: `I ∩ [n − δ/D, n + δ/D]` with `D` a lower bound of the derivative on
`I = [a, b]`: `(1 + a) eᵃ` for `W₀` (`branch0 = true`), `(−1 − b) eᵃ` for `W₋₁`, the exponential
from `derivLowerExp` with `elo0 ≤ eⁿ`; `I` itself when `D ≤ 0` cannot be certified. -/
def mvtRound (branch0 : Bool) (n elo0 δ : AzFloat) (I : AzFloat × AzFloat) (P : Nat) :
    AzFloat × AzFloat :=
  let dist := if branch0 then (addPrecRound I.1 one 64 .Floor).1
    else (subPrecRound (-one) I.2 64 .Floor).1
  if lt zero dist then
    let elo := derivLowerExp I.1 n elo0
    let D := (mulPrecRound dist elo 64 .Floor).1
    if lt zero D then
      let r := (divPrecRound δ D P .Ceiling).1
      (maxOf I.1 (subPrecRound n r P .Floor).1, minOf I.2 (addPrecRound n r P .Ceiling).1)
    else I
  else I

/-- Three mean-value rounds around the candidate `n` (clamped into `I₀`). -/
def mvtRounds (branch0 : Bool) (xAt : Nat → AzFloat × AzFloat) (n : AzFloat)
    (I₀ : AzFloat × AzFloat) (P : Nat) : AzFloat × AzFloat :=
  let E := expBracketAt n P
  let elo0 := clampNonneg E.1
  let δ := mvtDelta (xAt P) (mulBracketAny n E P) P
  let I₁ := mvtRound branch0 n elo0 δ I₀ P
  let I₂ := mvtRound branch0 n elo0 δ I₁ P
  mvtRound branch0 n elo0 δ I₂ P

/-! ### The bisection fallback -/

/-- One bisection step on the grid `2^e ℤ`: the interval `[A, B]·2^e` is refined to
`[2A, 2B]·2^(e−1)`
when `B − A ≤ 1`, then split at `M = ⌊(A + B)/2⌋` by the certified side of `M 2^e`. -/
def gridBisectStep (branch0 : Bool) (xAt : Nat → AzFloat × AzFloat)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true)
    (A B e : AzInt) : AzInt × AzInt × AzInt :=
  let (A, B, e) := if B - A ≤ AzInt.ofInt 1 then (A <<< 1, B <<< 1, e - AzInt.ofInt 1)
    else (A, B, e)
  let M := (A + B).ediv (AzInt.ofInt 2)
  let below := sideOf xAt (ofAzInt M <<< e) (hs M e)
  -- `below`: `m eᵐ < x`, i.e. `W > m` on the increasing branch, `W < m` on the decreasing one
  if below == branch0 then (M, B, e) else (A, M, e)

/-- `k` bisection steps. -/
def bisectGrid (branch0 : Bool) (xAt : Nat → AzFloat × AzFloat)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) :
    Nat → AzInt × AzInt × AzInt → AzInt × AzInt × AzInt
  | 0, s => s
  | k + 1, (A, B, e) => bisectGrid branch0 xAt hs k (gridBisectStep branch0 xAt hs A B e)

/-- The integer grid enclosing `[a, b]`: `[⌊a⌋ − 1, ⌈b⌉ + 1]` through the truncations, clamped
to the monotone region of the branch (`≥ −1` for `W₀`, `≤ −1` for `W₋₁`). -/
def gridOf (branch0 : Bool) (I : AzFloat × AzFloat) : AzInt × AzInt × AzInt :=
  let A := truncToAzInt I.1 - AzInt.ofInt 1
  let B := truncToAzInt I.2 + AzInt.ofInt 1
  if branch0 then (if A ≤ -AzInt.ofInt 1 then -AzInt.ofInt 1 else A, B, 0)
  else (A, if -AzInt.ofInt 1 ≤ B then -AzInt.ofInt 1 else B, 0)

/-- The floats of a grid interval. -/
def gridFloats (s : AzInt × AzInt × AzInt) : AzFloat × AzFloat :=
  (ofAzInt s.1 <<< s.2.2, ofAzInt s.2.1 <<< s.2.2)

/-! ### The candidate (unverified) -/

/-- One Halley step for `w e^w = x` at precision `P`. -/
def lambertHalleyStep (x w : AzFloat) (P : Nat) : AzFloat :=
  let E := (expPrecRound w P .Nearest).1
  let f := (subPrecRound (mulPrecRound w E P .Nearest).1 x P .Nearest).1
  let w1 := (addPrecRound w one P .Nearest).1
  let fp := (mulPrecRound E w1 P .Nearest).1
  let w2 := (addPrecRound w (ofAzNat (AzNat.ofNat 2)) P .Nearest).1
  let corr := (divPrecRound (mulPrecRound w2 f P .Nearest).1 (w1 <<< AzInt.ofInt 1) P .Nearest).1
  let den := (subPrecRound fp corr P .Nearest).1
  (subPrecRound w (divPrecRound f den P .Nearest).1 P .Nearest).1

/-- Halley steps at precisions `P + loss, 2P + loss, 4P + loss, …` while `2P < W`, then one at
`W + loss`: a step from an iterate with `a` correct bits gives about `min(3a − c, P' − loss)`
bits, so doubling keeps every step saturated (the last step, from `P ≥ W/2` bits, reaches `W`)
and `loss` (about `2 compBits + 16`) absorbs the cancellation in `w eʷ − x` divided by the small
derivative near the branch point.  Started at `P = W / 2^k ∈ [64, 128)` the steps cost about
`2` exponentials at precision `W` in total. -/
def halleyRefine (x w : AzFloat) (P W loss : Nat) : Nat → AzFloat
  | 0 => w
  | fuel + 1 =>
    if W ≤ 2 * P then lambertHalleyStep x w (W + loss)
    else halleyRefine x (lambertHalleyStep x w (P + loss)) (2 * P) W loss fuel

/-- Halley's iteration in `Float` from a start value. -/
def halleyFloat (x : Float) : Nat → Float → Float
  | 0, w => w
  | k + 1, w =>
    let E := Float.exp w
    let f := w * E - x
    let w1 := w + 1
    let den := E * w1 - (w + 2) * f / (2 * w1)
    halleyFloat x k (w - f / den)

/-- A `Float` seed for the branch (`none` when `Float` cannot represent the problem). -/
def seedFloat (branch0 : Bool) (x : AzFloat) : Option AzFloat :=
  let xf := toFloat64 x
  if !xf.isFinite || xf == 0 then none
  else
    let q := 1 + Float.exp 1 * xf
    let s : Float :=
      if branch0 then
        if xf ≥ 0 then (if xf < 1 then xf else Float.log xf - Float.log (1 + Float.log xf))
        else -1 + Float.sqrt (2 * q) - 2 * q / 3
      else
        if q < 0.3 then -1 - Float.sqrt (2 * q) - 2 * q / 3
        else Float.log (-xf) - Float.log (-Float.log (-xf))
    let w := halleyFloat xf 8 s
    if w.isFinite && !w.isNaN then some (ofFloat64 w) else none

/-- The branch-point series seed `−1 + p − p²/3 + 11p³/72 − 43p⁴/540` with `p = ±√(2q)`. -/
def seriesSeed (branch0 : Bool) (qlo : AzFloat) (P : Nat) : AzFloat :=
  let p0 := (sqrtPrecRound (qlo <<< AzInt.ofInt 1) P .Nearest).1
  let p := if branch0 then p0 else -p0
  let p2 := (mulPrecRound p p P .Nearest).1
  let p3 := (mulPrecRound p2 p P .Nearest).1
  let p4 := (mulPrecRound p2 p2 P .Nearest).1
  let t2 := (divPrecRound p2 (ofAzNat (AzNat.ofNat 3)) P .Nearest).1
  let t3 := (divPrecRound (mulPrecRound p3 (ofAzNat (AzNat.ofNat 11)) P .Nearest).1
    (ofAzNat (AzNat.ofNat 72)) P .Nearest).1
  let t4 := (divPrecRound (mulPrecRound p4 (ofAzNat (AzNat.ofNat 43)) P .Nearest).1
    (ofAzNat (AzNat.ofNat 540)) P .Nearest).1
  let s1 := (addPrecRound (-one) p P .Nearest).1
  let s2 := (subPrecRound s1 t2 P .Nearest).1
  let s3 := (addPrecRound s2 t3 P .Nearest).1
  (subPrecRound s3 t4 P .Nearest).1

/-- The candidate clamped into `[a, b]` (`a` when it is not finite). -/
def clampInto (I : AzFloat × AzFloat) (n : AzFloat) : AzFloat :=
  match n with
  | finite _ _ _ _ _ => maxOf I.1 (minOf I.2 n)
  | zero => maxOf I.1 (minOf I.2 zero)
  | _ => I.1

/-- The unverified candidate for `W` at working precision `W`: a seed (`Float`, the branch-point
series when `q < 2^(−40)`, or the midpoint of `I₀`) refined by Halley's iteration. -/
def halleyCandidate (branch0 : Bool) (xAt : Nat → AzFloat × AzFloat)
    (qE : Option (AzFloat × AzFloat)) (I₀ : AzFloat × AzFloat) (W : Nat) : AzFloat :=
  let loss := 2 * compBits qE + 16
  let x := (xAt (W + loss)).1
  let tiny := match qE with
    | some (lo, _) => lt lo (powerOf2 (AzInt.ofInt (-40)))
    | none => false
  let seed :=
    if tiny then
      match qE with
      | some (lo, _) => seriesSeed branch0 lo W
      | none => zero
    else
      match seedFloat branch0 x with
      | some s => s
      | none => (addPrecRound I₀.1 I₀.2 64 .Nearest).1 <<< AzInt.ofInt (-1)
  let P₀ := W / 2 ^ Nat.log2 (W / 64)
  let n := halleyRefine x (clampInto I₀ seed) P₀ W loss (W + 2)
  clampInto I₀ n

/-! ### The bracket at a Ziv level -/

/-- The working precision at Ziv level `w`: `w + 10 + compBits qE`, at least `64`. -/
def lambertWork (qE : Option (AzFloat × AzFloat)) (w : Nat) : Nat := max (w + 10 + compBits qE) 64

/-- The target width at level `w`: `max(|a₀|, |b₀|) · 2^(−w−1)`. -/
def lambertTarget (I₀ : AzFloat × AzFloat) (w : Nat) : AzFloat :=
  maxOf (maxOf I₀.1 (-I₀.1)) (maxOf I₀.2 (-I₀.2)) <<< (-(AzNat.ofNat (w + 1)).toAzInt)

/-- The bracket of the root at Ziv level `w`: the mean-value rounds around the Halley candidate
when they reach the target width, otherwise `3 W + 8` grid bisection steps. -/
def lambertBracket (branch0 : Bool) (xAt : Nat → AzFloat × AzFloat)
    (qE : Option (AzFloat × AzFloat)) (I₀ : AzFloat × AzFloat)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true)
    (w : Nat) : AzFloat × AzFloat :=
  let W := lambertWork qE w
  let n := halleyCandidate branch0 xAt qE I₀ W
  let I := mvtRounds branch0 xAt n I₀ W
  if le (subPrecRound I.2 I.1 64 .Ceiling).1 (lambertTarget I₀ w) then I
  else gridFloats (bisectGrid branch0 xAt hs (3 * W + 8) (gridOf branch0 I₀))

/-- The bracket as a pair of `Roundable`s. -/
def lambertApprox (branch0 : Bool) (xAt : Nat → AzFloat × AzFloat)
    (qE : Option (AzFloat × AzFloat)) (I₀ : AzFloat × AzFloat)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true)
    (w : Nat) : Roundable × Roundable :=
  let b := lambertBracket branch0 xAt qE I₀ hs w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Digamma
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Float64

/-!
## The real zeros of the digamma function

`psiZeroPrecRound n p mode` is the `n`-th real zero `xₙ` of `ψ` (DLMF §5.4(iii), Table 5.4.1)
rounded to precision `p` in `mode`, with the comparison against the exact value;
`psiZero n p` rounds to nearest.  `x₀ = 1.4616…` is the minimum of `Γ` on `(0, ∞)`, and for
`n ≥ 1`, `xₙ` is the zero in `(−n, −n + 1)`, an extremum of `Γ` between two poles.

* **The candidate** (`psiZeroCandidate`, unverified): Newton's iteration in `Float`
  (`psiZeroFloatSeed`: `ψ` and `ψ′` from the recurrence and five terms of their asymptotic
  series) gives a seed with about 48 bits and the slope of `ψ` there; one step
  `x₀ − ψ(x₀)/s` with `ψ(x₀)` from `digammaEncl` gives about 90 bits, and beyond that the
  secant method runs along a schedule of accuracies planned backwards (`psiZeroPlan`: the step
  to `t` bits starts from an iterate with `5t/8 + 8` bits).  At 53 bits the candidate costs
  one evaluation of `ψ`.
* **The enclosure** (`psiZeroFast`): one enclosure `[D]` of `ψ(c)` at the candidate `c`, inside
  `(−n, −n + 1)` (inside `(0, 2]` for `n = 0`) by float comparisons.  The slope of `ψ` is at
  least `1` on `(−n, −n + 1)` and at least `1/4` between two points of `(0, 2]` — bounds that
  come from the recurrence, without `ψ′` (`Transcendental/PsiZero.lean`) — so
  `|xₙ − c| ≤ δ` with `δ = max |D|` (`4δ` for `n = 0`).  The candidate is never trusted.
* **The verified fallback** (`psiZeroFallback`): nothing is proved about `Float`, so nothing
  is proved about the width of the fast enclosure.  When it is missing or wider than
  `2^(−⌊w/2⌋)`, the enclosure comes from `w + 8` steps of bisection on the unit interval of
  the zero, each by the sign of an enclosure of `ψ` at the exact middle.  Its width tends
  to `0`, which makes the function complete.
* **Fuel.**  Ziv's loop with the fuel of `ψ` itself (`lnGammaFuel`): nothing is known about
  the arithmetic nature of the zeros.  The specification `psiZeroPrecRoundFuel_zivSpec`
  (`Equiv/PsiZero.lean`): sound at every fuel, and complete in the limit of the fuel wherever
  the zero is no rounding boundary.
-/

namespace Azurite.AzFloat

/-! ### The candidate (unverified) -/

/-- The midpoint of the enclosure of `ψ(x)` at level `w`, when there is one. -/
def psiZeroEval (x : AzFloat) (pos : Bool) (w : Nat) : Option AzFloat :=
  (digammaEncl x (expOf x) pos w).map fun b =>
    (addPrecRound b.1 b.2 (w + 64) .Nearest).1 <<< AzInt.ofInt (-1)

/-- The seed: `x₀` to the precision of a `Float`; `−n + π⁻¹ arctan (π / ln n)` for `n ≥ 1`
(DLMF 5.4.20; `−1/2` for `n = 1`). -/
def psiZeroSeed (n : Nat) : AzFloat :=
  if n = 0 then ofFloat64 1.4616321449683623
  else
    let N := ofAzNat (AzNat.ofNat n)
    let L := toFloat64 (lnPrecRound N 64 .Nearest).1
    let u := Float.atan (3.141592653589793 / L) / 3.141592653589793
    (addPrecRound (-N) (ofFloat64 u) (n.log2 + 65) .Nearest).1

/-- A secant step `x₁ − f₁ (x₁ − x₀)/(f₁ − f₀)` at precision `P` (`x₁` when `f₁ = f₀`). -/
def psiZeroSecant (x₀ f₀ x₁ f₁ : AzFloat) (P : Nat) : AzFloat :=
  let d := (subPrecRound f₁ f₀ P .Nearest).1
  if eqIEEE d zero then x₁
  else
    let s := (divPrecRound (mulPrecRound f₁ (subPrecRound x₁ x₀ P .Nearest).1 P .Nearest).1 d P
      .Nearest).1
    (subPrecRound x₁ s P .Nearest).1

/-- Secant steps at 64 bits from `(x₀, f₀ = ψ(x₀), x₁)` until two iterates agree to `2^(−44)`:
the last two iterates, with the value of `ψ` at the first of them. -/
def psiZeroLow (pos : Bool) (P : Nat) : Nat → AzFloat → AzFloat → AzFloat →
    AzFloat × AzFloat × AzFloat
  | 0, x₀, f₀, x₁ => (x₀, f₀, x₁)
  | k + 1, x₀, f₀, x₁ =>
    match psiZeroEval x₁ pos 64 with
    | none => (x₀, f₀, x₁)
    | some f₁ =>
      let x₂ := psiZeroSecant x₀ f₀ x₁ f₁ P
      if lt (subPrecRound x₂ x₁ 64 .Nearest).1.abs (powerOf2 (AzInt.ofInt (-44))) then
        (x₁, f₁, x₂)
      else psiZeroLow pos P k x₁ f₁ x₂

/-- The accuracies of the secant iterates up to `T` bits, in increasing order: each is
`5/8` of the next plus `8`, down to `40`. -/
def psiZeroPlan : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, T, acc => if T ≤ 40 then acc else psiZeroPlan fuel (T * 5 / 8 + 8) (T :: acc)

/-- Secant steps along a plan: the step to `t` bits works at `t + nb + 16` bits (`nb` the bits
of the integer part) and takes `ψ(x₁)` at level `5t/4 + 16` — at `t + 16` in the last step.
The extra quarter is for the next step, where this value is the old one: the difference of
the two values of `ψ` is of the order of the error `2^(−5t/8)` of `x₁`, and has to be known to
the `3t/5` bits that the step after gains. -/
def psiZeroHigh (pos : Bool) (nb : Nat) : List Nat → AzFloat → AzFloat → AzFloat → AzFloat
  | [], _, _, x₁ => x₁
  | t :: ts, x₀, f₀, x₁ =>
    match psiZeroEval x₁ pos (if ts.isEmpty then t + 16 else t * 5 / 4 + 16) with
    | none => x₁
    | some f₁ => psiZeroHigh pos nb ts x₁ f₁ (psiZeroSecant x₀ f₀ x₁ f₁ (t + nb + 16))

/-! #### A seed and a slope in `Float` -/

/-- The shift of the `Float` series: `(y + m, ∑_{i<m} 1/(y + i)^j)` with `y + m ≥ 12`
(`j = 1` or `2`). -/
def psiFloatShift (sq : Bool) : Nat → Float → Float → Float × Float
  | 0, y, s => (y, s)
  | k + 1, y, s =>
    if y < 12 then psiFloatShift sq k (y + 1) (s + (if sq then 1 / (y * y) else 1 / y))
    else (y, s)

/-- `ψ(y)` in `Float` for `y > 0`: the recurrence up to `12`, then five terms of the
asymptotic series. -/
def psiFloat (y : Float) : Float :=
  let (y, s) := psiFloatShift false 12 y 0
  let r := 1 / (y * y)
  Float.log y - 0.5 / y - r * (1 / 12 - r * (1 / 120 - r * (1 / 252 - r * (1 / 240 - r / 132))))
    - s

/-- `ψ′(y)` in `Float` for `y > 0`. -/
def psi1Float (y : Float) : Float :=
  let (y, s) := psiFloatShift true 12 y 0
  let r := 1 / (y * y)
  1 / y + r / 2 + r / y * (1 / 6 - r * (1 / 30 - r * (1 / 42 - r / 30))) + s

/-- Newton's iteration in `Float` for `g(u) = ψ(n + 1 − u) − π cot (π u)`, the equation of
`u = xₙ + n` (`n ≥ 1`): the last iterate and the slope `π²/sin² (π u) − ψ′(n + 1 − u)` of `ψ`
there. -/
def psiZeroFloatNeg (nf : Float) : Nat → Float → Float × Float
  | 0, u =>
    let sn := Float.sin (3.141592653589793 * u)
    (u, 9.869604401089358 / (sn * sn) - psi1Float (nf + 1 - u))
  | k + 1, u =>
    let sn := Float.sin (3.141592653589793 * u)
    let g := psiFloat (nf + 1 - u) - 3.141592653589793 * Float.cos (3.141592653589793 * u) / sn
    let g' := 9.869604401089358 / (sn * sn) - psi1Float (nf + 1 - u)
    psiZeroFloatNeg nf k (u - g / g')

/-- Newton's iteration in `Float` for `ψ(x) = 0` near `x₀`. -/
def psiZeroFloatPos : Nat → Float → Float × Float
  | 0, x => (x, psi1Float x)
  | k + 1, x => psiZeroFloatPos k (x - psiFloat x / psi1Float x)

/-- A seed for `xₙ` with about 48 bits after the binary point and the slope of `ψ` there, both
from `Float` arithmetic; `none` when `n` is outside the `Float` range or the iteration left
`(0, 1)`. -/
def psiZeroFloatSeed (n : Nat) : Option (AzFloat × AzFloat) :=
  if n = 0 then
    let (x, s) := psiZeroFloatPos 6 1.4616321449683623
    if x.isFinite && s.isFinite && s > 0 then some (ofFloat64 x, ofFloat64 s) else none
  else
    let nf := n.toFloat
    let (u, s) := psiZeroFloatNeg nf 12
      (Float.atan (3.141592653589793 / Float.log nf) / 3.141592653589793)
    if u.isFinite && s.isFinite && 0 < u && u < 1 && s > 0 then
      some ((addPrecRound (-(ofAzNat (AzNat.ofNat n))) (ofFloat64 u) (n.log2 + 65) .Nearest).1,
        ofFloat64 s)
    else none

/-- The accuracy claimed for the first step from the `Float` seed: its 48 bits and the 44 of
the slope. -/
def psiZeroFirst : Nat := 90

/-- The unverified candidate for `xₙ` with about `T` bits after the binary point.  From the
`Float` seed and slope, one step `x₀ − ψ(x₀)/s` gives `min(T, 90)` bits, and the secant method
takes over along the plan above `90`.  Without the `Float` seed (an astronomically large `n`):
the seed of 5.4.20 and the secant method from 64 bits. -/
def psiZeroCandidate (n T : Nat) : AzFloat :=
  let pos := decide (n = 0)
  let nb := n.log2 + 1
  match psiZeroFloatSeed n with
  | some (x₀, s) =>
    let t₁ := min T psiZeroFirst
    match psiZeroEval x₀ pos (t₁ + 16) with
    | none => x₀
    | some f₀ =>
      let x₁ := (subPrecRound x₀ (divPrecRound f₀ s (t₁ + 16) .Nearest).1 (t₁ + nb + 16)
        .Nearest).1
      psiZeroHigh pos nb ((psiZeroPlan T T []).filter (psiZeroFirst < ·)) x₀ f₀ x₁
  | none =>
    let x₀ := psiZeroSeed n
    match psiZeroEval x₀ pos 64 with
    | none => x₀
    | some f₀ =>
      let x₁ := (addPrecRound x₀ (powerOf2 (AzInt.ofInt (-12))) (nb + 80) .Nearest).1
      let s := psiZeroLow pos (nb + 80) 12 x₀ f₀ x₁
      psiZeroHigh pos nb (psiZeroPlan T T []) s.1 s.2.1 s.2.2

/-! ### The enclosure -/

/-- Is the candidate inside the interval of `xₙ`: `(0, 2]` for `n = 0`, `(−n, −n + 1)`
otherwise? -/
def psiZeroInside (n : Nat) (c : AzFloat) : Bool :=
  if n = 0 then lt zero c && le c (ofAzNat (AzNat.ofNat 2))
  else lt (-(ofAzNat (AzNat.ofNat n))) c && lt c (-(ofAzNat (AzNat.ofNat (n - 1))))

/-- The enclosure of `xₙ` around a point `c` of its interval, from an enclosure `D` of `ψ(c)`:
`c ± δ` with `δ = max |D|` (`c ± 4δ` for `n = 0`), at `P` bits. -/
def psiZeroAround (n : Nat) (c : AzFloat) (D : Encl) (P : Nat) : Encl :=
  let δ := maxOf D.2 (-D.1)
  let r := if n = 0 then δ <<< AzInt.ofInt 2 else δ
  ((subPrecRound c r P .Floor).1, (addPrecRound c r P .Ceiling).1)

/-- The fast enclosure of `xₙ` at Ziv level `w`, around the unverified candidate; `none` when
the candidate is not inside the interval or `ψ` has no enclosure there at this level. -/
def psiZeroFast (n w : Nat) : Option Encl :=
  let c := psiZeroCandidate n (w + 4)
  if c.isFinite && psiZeroInside n c then
    (digammaEncl c (expOf c) (decide (n = 0)) (w + 24)).map fun D =>
      psiZeroAround n c D (n.log2 + w + 64)
  else none

/-! ### The verified fallback: bisection on the sign of `ψ` -/

/-- The left end of the unit interval `(l, l + 1)` that the bisection for `xₙ` starts from:
`1` for `n = 0`, `−n` otherwise. -/
def psiZeroLo (n : Nat) : Int := if n = 0 then 1 else -(n : Int)

/-- The point `(2a + 1)/2^(j+1)`, the middle of `[a, a + 1]/2^j`, exactly. -/
def psiZeroMid (j : Nat) (a : AzInt) : AzFloat :=
  ofAzInt (a + a + 1) <<< AzInt.ofInt (-((j + 1 : Nat) : Int))

/-- `k` steps of bisection for the zero of `ψ` in `[a, a + 1]/2^j`, by the sign of the
enclosure of `ψ` at the middle (at level `W`, for arguments below `2^e`): the last middle and
the enclosure of `ψ` there.  It stops early at a middle whose enclosure contains `0`; `none`
when `ψ` has no enclosure at a middle. -/
def psiZeroBisect (n W : Nat) (e : AzInt) : Nat → Nat → AzInt → Option (AzFloat × Encl)
  | 0, j, a =>
    (digammaEncl (psiZeroMid j a) e (decide (n = 0)) W).map fun D => (psiZeroMid j a, D)
  | k + 1, j, a =>
    match digammaEncl (psiZeroMid j a) e (decide (n = 0)) W with
    | none => none
    | some D =>
      if lt D.2 zero then psiZeroBisect n W e k (j + 1) (a + a + 1)
      else if lt zero D.1 then psiZeroBisect n W e k (j + 1) (a + a)
      else some (psiZeroMid j a, D)

/-- **The verified enclosure of `xₙ`** at Ziv level `w`: `w + 8` steps of bisection on
`(1, 2)` (`n = 0`) or `(−n, −n + 1)`, then the enclosure around the last middle.  Every step
is one evaluation of `ψ`, so this is slow — and its width provably tends to `0`
(`psiZeroFallback_conv`). -/
def psiZeroFallback (n w : Nat) : Option Encl :=
  (psiZeroBisect n (w + 24) (AzInt.ofInt ((n.log2 + 1 : Nat) : Int)) (w + 8) 0
    (AzInt.ofInt (psiZeroLo n))).map fun r => psiZeroAround n r.1 r.2 (n.log2 + w + 64)

/-- Is the enclosure narrower than `2^(−⌊w/2⌋)`? -/
def psiZeroNarrow (b : Encl) (w : Nat) : Bool :=
  le (subPrecRound b.2 b.1 64 .Ceiling).1 (powerOf2 (AzInt.ofInt (-((w / 2 : Nat) : Int))))

/-- The enclosure of `xₙ` at Ziv level `w`: the fast one when it exists and is narrow, the
verified fallback otherwise. -/
def psiZeroEncl (n w : Nat) : Option Encl :=
  match (psiZeroFast n w).filter (psiZeroNarrow · w) with
  | some b => some b
  | none => psiZeroFallback n w

/-- The bracket of `xₙ` as a pair of `Roundable`s. -/
def psiZeroApprox (n w : Nat) : Roundable × Roundable :=
  lnAbsGammaApproxOf (psiZeroEncl n w) w

/-- The `n`-th real zero of `ψ` rounded to precision `p` with `mode`, and the comparison with
the exact value (`(nan, .eq)` for `p = 0`, or if the fuel runs out), with the fuel of the Ziv
loop explicit. -/
def psiZeroPrecRoundFuel (fuel n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else zivLoop (psiZeroApprox n) p mode fuel (max 64 (p + 32))

/-- The `n`-th real zero of `ψ` rounded to precision `p` with `mode`, and the comparison with
the exact value: `psiZeroPrecRoundFuel` at the fuel `lnGammaFuel p`.  The specification is
`psiZeroPrecRoundFuel_zivSpec` (`Equiv/PsiZero.lean`). -/
def psiZeroPrecRound (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  psiZeroPrecRoundFuel (lnGammaFuel p) n p mode

/-- The `n`-th real zero of `ψ` rounded to nearest at precision `p`. -/
def psiZero (n p : Nat) : AzFloat := (psiZeroPrecRound n p .Nearest).1

end Azurite.AzFloat

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Compare
import Azurite.AzFloat.Precision
import Azurite.AzInt.DivRound
import Azurite.AzInt.Parity
import Azurite.AzInt.ShiftRight
import Azurite.AzNat.Add
import Azurite.AzNat.Mul
import Azurite.AzNat.IsMultipleOfPow2
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Square
import Azurite.AzNat.Sub

/-!
# Addition and subtraction of `AzFloat`s

Correctly rounded `x + y` and `x − y` at a destination precision `p`, in the spirit of Brent and
Zimmermann, *Modern Computer Arithmetic*, §3.2.1–3.2.2 (Algorithm FPadd and the discussion of
cancellation), but organized around one primitive: `roundScaled`, which rounds an exact integer
times a power of two to `p` bits with `AzInt.shiftRightRound`.  Rounding once from the exact
value removes FPadd's round/sticky/carry bookkeeping and its second rounding, and cancellation
in a subtraction only makes the exact difference short.

For operands of the same sign with `b` the one of larger exponent, `T = max(p_b, p)` and gap
`G = e_b − e_c`:

* **near case** (`G ≤ T + 1`): the exact sum or difference is an integer of at most
  `T + p_c + 1` bits on the common scale `min(ulp b, ulp c)`; round it.
* **far case** (`G ≥ T + 2`): `c` is below `2^(e_b − T − 2)`, so `b ± c` lies in an open interval
  of that width next to `b` that contains no point or midpoint of the destination grid (even
  when `b` is a power of two and the grid below it is finer); every value in it rounds the same
  way, so the representative `8·b_core ± 1` at scale `2^(e_b − T − 3)` is rounded instead.  This
  is FPadd's "the small operand only sets the sticky bit", with cost bounded by the precisions
  rather than by the gap.

`addPrecRound` dispatches the special values (`∞ + (−∞)` is `NaN`, a zero operand means
re-rounding the other) and the signs; `subPrecRound x y = addPrecRound x (−y)`.  The `+` and
`−` instances round to nearest at the larger of the two precisions.  `Equiv/Arith.lean` proves
`addPrecRound x y p mode = liftVal₂ Spec.add x y p mode`.
-/

namespace Azurite.AzFloat

/-- Round the exact value `(−1)^(¬s) · S · 2^w` to precision `p`, with the comparison of the
result against it.  `S = 0` gives `zero`; a zero precision gives `NaN`. -/
def roundScaled (s : Bool) (S : AzNat) (w : AzInt) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else if S = 0 then (zero, .eq)
  else
    let ex := w + (AzNat.ofNat S.size).toAzInt
    if S.size ≤ p then (mkFinite s ex p S, .eq)
    else
      let r := AzInt.shiftRightRound (AzInt.mkNorm s S) mode (S.size - p)
      let a := r.1.abs
      if a.size = p + 1 then (mkFinite r.1.sign (ex + 1) p (a.shiftRight 1), r.2)
      else (mkFinite r.1.sign ex p a, r.2)

/-- The common scale of two values with ulps `2^wb` and `2^wc`, and the shifts onto it. -/
def alignShifts (wb wc : AzInt) : AzInt × Nat × Nat :=
  let w := min wb wc
  (w, (wb - w).abs.toNat, (wc - w).abs.toNat)

/-- `(−1)^(¬s) · (b + c)` rounded to precision `p`, for padding-free significands `nb`, `nc`
with exponents `eb ≥ ec`. -/
def addMagnitudes (s : Bool) (eb : AzInt) (nb : AzNat) (ec : AzInt) (nc : AzNat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  let pb := nb.size
  let T := max pb p
  if (AzNat.ofNat (T + 2)).toAzInt ≤ eb - ec then
    roundScaled s ((nb.shiftLeft (T - pb + 3)).addUInt64 1)
      (eb - (AzNat.ofNat (T + 3)).toAzInt) p mode
  else
    let (w, kb, kc) :=
      alignShifts (eb - (AzNat.ofNat pb).toAzInt) (ec - (AzNat.ofNat nc.size).toAzInt)
    roundScaled s (nb.shiftLeft kb + nc.shiftLeft kc) w p mode

/-- `(−1)^(¬s) · (b − c)` rounded to precision `p`, for `b > c` (as values) with exponents
`eb ≥ ec`. -/
def subMagnitudes (s : Bool) (eb : AzInt) (nb : AzNat) (ec : AzInt) (nc : AzNat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  let pb := nb.size
  let T := max pb p
  if (AzNat.ofNat (T + 2)).toAzInt ≤ eb - ec then
    roundScaled s (nb.shiftLeft (T - pb + 3) - 1) (eb - (AzNat.ofNat (T + 3)).toAzInt) p mode
  else
    let (w, kb, kc) :=
      alignShifts (eb - (AzNat.ofNat pb).toAzInt) (ec - (AzNat.ofNat nc.size).toAzInt)
    roundScaled s (nb.shiftLeft kb - nc.shiftLeft kc) w p mode

/-- `x + y` rounded to precision `p` with `mode`, and the comparison with the exact sum. -/
def addPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x, y with
  | nan, _ => (nan, .eq)
  | _, nan => (nan, .eq)
  | infinity s, infinity t => if s = t then (infinity s, .eq) else (nan, .eq)
  | infinity s, _ => (infinity s, .eq)
  | _, infinity t => (infinity t, .eq)
  | zero, y => setPrecRound y p mode
  | x, zero => setPrecRound x p mode
  | finite s e₁ p₁ m₁ _, finite t e₂ p₂ m₂ _ =>
    let n₁ := coreSignificand p₁ m₁
    let n₂ := coreSignificand p₂ m₂
    if s = t then
      if AzInt.compare e₁ e₂ = .lt then addMagnitudes s e₂ n₂ e₁ n₁ p mode
      else addMagnitudes s e₁ n₁ e₂ n₂ p mode
    else
      match compareMagnitude e₁ m₁ e₂ m₂ with
      | .eq => (zero, .eq)
      | .gt => subMagnitudes s e₁ n₁ e₂ n₂ p mode
      | .lt => subMagnitudes t e₂ n₂ e₁ n₁ p mode

/-- `x − y` rounded to precision `p` with `mode`, and the comparison with the exact difference. -/
def subPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  addPrecRound x (-y) p mode

/-- The precision for `+` and `−`: the larger of the operands' (`1` if neither has one). -/
def combinedPrecision (x y : AzFloat) : Nat :=
  max (x.precision?.getD 1) (y.precision?.getD 1)

instance : Add AzFloat := ⟨fun x y => (addPrecRound x y (combinedPrecision x y) .Nearest).1⟩
instance : Sub AzFloat := ⟨fun x y => (subPrecRound x y (combinedPrecision x y) .Nearest).1⟩

/-! ### Multiplication and squaring

MCA §3.3, Algorithm FPmultiply: the exact product of `±n₁ · 2^(e₁ − p₁)` and `±n₂ · 2^(e₂ − p₂)`
is `±(n₁ n₂) · 2^((e₁ − p₁) + (e₂ − p₂))`, so the significands are multiplied in full (the
`p₁`- and `p₂`-bit cores, no truncation to `n + g` digits) and the product rounded once with
`roundScaled`.  A short product (MCA Algorithm 3.4) only approximates the high part and would need
a fallback to decide the rounding and the comparison; it is left for a later performance pass. -/

/-- `x · y` rounded to precision `p` with `mode`, and the comparison with the exact product.
`0 · (±∞)` is `NaN`; the sign of an infinite product is the product of the signs. -/
def mulPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x, y with
  | nan, _ => (nan, .eq)
  | _, nan => (nan, .eq)
  | infinity s, infinity t => (infinity (s == t), .eq)
  | infinity _, zero => (nan, .eq)
  | zero, infinity _ => (nan, .eq)
  | infinity s, finite t _ _ _ _ => (infinity (s == t), .eq)
  | finite s _ _ _ _, infinity t => (infinity (s == t), .eq)
  | zero, _ => (zero, .eq)
  | _, zero => (zero, .eq)
  | finite s e₁ p₁ m₁ _, finite t e₂ p₂ m₂ _ =>
    roundScaled (s == t) (coreSignificand p₁ m₁ * coreSignificand p₂ m₂)
      (e₁ - (AzNat.ofNat p₁).toAzInt + (e₂ - (AzNat.ofNat p₂).toAzInt)) p mode

/-- `x²` rounded to precision `p` with `mode`, and the comparison with the exact square; the
significand is squared with `AzNat.square`. -/
def sqrPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (infinity true, .eq)
  | zero => (zero, .eq)
  | finite _ e q m _ =>
    let w := e - (AzNat.ofNat q).toAzInt
    roundScaled true (AzNat.square (coreSignificand q m)) (w + w) p mode

instance : Mul AzFloat := ⟨fun x y => (mulPrecRound x y (combinedPrecision x y) .Nearest).1⟩

/-- `x²` rounded to nearest at the precision of `x`. -/
def sqr (x : AzFloat) : AzFloat := (sqrPrecRound x (x.precision?.getD 1) .Nearest).1

/-! ### Division

MCA §3.4.2: `x / y = ±(n₁ / n₂) · 2^((e₁ − p₁) − (e₂ − p₂))` for cores `n₁`, `n₂`.  With
`g = p + p₂ − p₁`, or one less when `n₁ / 2^p₁ ≥ n₂ / 2^p₂`, the quotient `n₁ · 2^g / n₂` lies in
`[2^(p−1), 2^p)`, so one rounded integer division (`AzInt.divRound`, which decides the rounding
and the comparison from the remainder) gives the `p`-bit significand, and only a carry to `2^p`
remains to be normalized.  Approximate schemes (Newton reciprocal, short division, Barrett) all
need a correction step before they round correctly and are not used. -/

/-- Normalize a signed integer `r` with `2^(p−1) ≤ |r| ≤ 2^p` into the precision-`p` float of
value `r · 2^(e − p)`: a carry to `2^p` is halved with the exponent raised. -/
def normalizeCarry (r : AzInt) (e : AzInt) (p : Nat) : AzFloat :=
  if r.abs.size = p + 1 then mkFinite r.sign (e + 1) p (r.abs.shiftRight 1)
  else mkFinite r.sign e p r.abs

/-- The rounded quotient of two cores (`n₁` of `p₁` bits at exponent `e₁`, `n₂` of `p₂` bits at
`e₂`), with sign `s`; `hge` says whether `n₁ / 2^p₁ ≥ n₂ / 2^p₂`. -/
def divCores (s : Bool) (e₁ : AzInt) (n₁ : AzNat) (p₁ : Nat) (e₂ : AzInt) (n₂ : AzNat)
    (p₂ : Nat) (hge : Bool) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let g : AzInt :=
    (AzNat.ofNat (p + p₂)).toAzInt - (AzNat.ofNat (p₁ + (if hge then 1 else 0))).toAzInt
  let A := if g.sign then n₁.shiftLeft g.abs.toNat else n₁
  let B := if g.sign then n₂ else n₂.shiftLeft g.abs.toNat
  let qo := AzInt.divRound (AzInt.mkNorm s A) B.toAzInt mode
  let w := e₁ - (AzNat.ofNat p₁).toAzInt - (e₂ - (AzNat.ofNat p₂).toAzInt) - g
  (normalizeCarry qo.1 (w + (AzNat.ofNat p).toAzInt) p, qo.2)

/-- `x / y` rounded to precision `p` with `mode`, and the comparison with the exact quotient.
`∞ / ∞` and `0 / 0` are `NaN`; `x / 0 = ±∞` with the sign of `x`; `x / ∞ = 0`. -/
def divPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x, y with
  | nan, _ => (nan, .eq)
  | _, nan => (nan, .eq)
  | infinity _, infinity _ => (nan, .eq)
  | infinity s, zero => (infinity s, .eq)
  | infinity s, finite t _ _ _ _ => (infinity (s == t), .eq)
  | zero, zero => (nan, .eq)
  | zero, _ => (zero, .eq)
  | finite _ _ _ _ _, infinity _ => (zero, .eq)
  | finite s _ _ _ _, zero => (infinity s, .eq)
  | finite s e₁ p₁ m₁ _, finite t e₂ p₂ m₂ _ =>
    divCores (s == t) e₁ (coreSignificand p₁ m₁) p₁ e₂ (coreSignificand p₂ m₂) p₂
      (compareMagnitude 0 m₁ 0 m₂ != .lt) p mode

instance : Div AzFloat := ⟨fun x y => (divPrecRound x y (combinedPrecision x y) .Nearest).1⟩

/-- The rounding of the fraction `±num / den` to precision `p`, for any numerator and denominator
(no reduction to lowest terms, hence no gcd): the quotient machinery of division applied to the
raw integers.  `den = 0` is unspecified. -/
def ofFractionRound (s : Bool) (num den : AzNat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else if num = 0 then (zero, .eq)
  else
    divCores s (AzNat.ofNat num.size).toAzInt num num.size (AzNat.ofNat den.size).toAzInt den
      den.size (compare (num.shiftLeft den.size) (den.shiftLeft num.size) != .lt) p mode

/-! ### Square root

MCA §3.5, Algorithm FPSqrt, extended to round-to-nearest (Exercise 3.14): for `x = n · 2^(e − q)`
with core `n` of `q` bits, write `e − q = t + 2w` with `t = 2p − q − δ`, `δ = e mod 2`, so that
`M = n · 2^t ∈ [2^(2p−2), 2^(2p))` and `√x = √M · 2^w` with `√M ∈ [2^(p−1), 2^p)`.  The integer
square root `s = ⌊√⌊M⌋⌋` has `p` bits; `√M` is exactly `s` iff the remainder vanishes and no bits
of `n` were shifted out, and its position relative to the midpoint `s + 1/2` is the exact integer
comparison of `4M = n · 2^(t+2)` with `(2s + 1)²`.  Those three facts determine the rounding in
every mode (`roundFromFloor`), and a carry to `2^p` is normalized as for division. -/

/-- Round a real `y ∈ [s, s + 1)` to an integer, given its floor `s`, whether `y = s`, and the
comparison of `y` with the midpoint `s + 1/2`; the tag compares the result with `y`. -/
def roundFromFloor (s : AzNat) (exact : Bool) (cmpMid : Ordering) (mode : RoundingMode) :
    AzNat × Ordering :=
  if exact then (s, .eq) else
  match mode with
  | .Floor | .Down => (s, .lt)
  | .Ceiling | .Up => (s.addUInt64 1, .gt)
  | .Nearest =>
    match cmpMid with
    | .lt => (s, .lt)
    | .gt => (s.addUInt64 1, .gt)
    | .eq => if s.isOdd then (s.addUInt64 1, .gt) else (s, .lt)

/-- Compare `n · 2^t` with `c` exactly (`t` may be negative). -/
def compareScaled (n : AzNat) (t : AzInt) (c : AzNat) : Ordering :=
  if t.sign then compare (n.shiftLeft t.abs.toNat) c else compare n (c.shiftLeft t.abs.toNat)

/-- The rounded square root of `n · 2^(e − q)` (core `n` of `q` bits) to precision `p`. -/
def sqrtCore (e : AzInt) (n : AzNat) (q : Nat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  let δ : Nat := if e.isOdd then 1 else 0
  let t : AzInt := (AzNat.ofNat (2 * p)).toAzInt - (AzNat.ofNat (q + δ)).toAzInt
  let M := if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat
  let sr := AzNat.sqrtRem M
  let exact := decide (sr.2 = 0) && (t.sign || n.isMultipleOfPow2 t.abs.toNat)
  let cmpMid := compareScaled n (t + (AzNat.ofNat 2).toAzInt)
    (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1))
  let ro := roundFromFloor sr.1 exact cmpMid mode
  let w := (e - (AzNat.ofNat (2 * p)).toAzInt + (AzNat.ofNat δ).toAzInt).shiftRight 1
  (normalizeCarry (AzInt.mkNorm true ro.1) (w + (AzNat.ofNat p).toAzInt) p, ro.2)

/-- `√x` rounded to precision `p` with `mode`, and the comparison with the exact root; negative
inputs (including `−∞`) give `NaN`. -/
def sqrtPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m _ => if s then sqrtCore e (coreSignificand q m) q p mode else (nan, .eq)

/-- `√x` rounded to nearest at the precision of `x`. -/
def sqrt (x : AzFloat) : AzFloat := (sqrtPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat

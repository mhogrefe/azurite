/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.RoundToInteger
import Azurite.AzNat.LogBase
import Azurite.AzNat.RootInt
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.TrailingZeros
import Azurite.AzRat.Construct
import Azurite.AzRat.LogBase

/-!
# When `log_b x` is rational

For a base `b ≥ 2` that is not a power of two and a positive float `x`, `log_b x` is rational
exactly when `x` is a positive integer `c^r` for the *primitive root* `c` of `b` (`b = c^s` with
`s` maximal), and then it is `r / s`.  `maxRootBase b` finds `c` and `s` (`s ≤ 63` for a
64-bit base, by trying the perfect-power tests downward), and `logBaseExactCore? x b` returns the
rational `r / s` when `x` is such an integer and `none` otherwise.  For a positive rational `q`,
`log_b q` is rational exactly when `q = c^r` for an integer `r` (possibly negative), and
`logBaseExactRat? q b` returns `r / s` then (`AzRat.checkedLogBaseAbs` with the base `c`).
For `log_b (1 + x)`, `logBaseP1ExactCore? x b` returns `r / s` when `x` is a positive integer with
`1 + x = c^r` (a non-integer `x` never gives a rational `log_b (1 + x)` for such a base).
`Equiv/LogBaseExact.lean` proves the values and, for `none`, the irrationality of the logarithm.

**No materialisation of a huge integer.**  `logBaseExactCore?` and `logBaseP1ExactCore?` convert
the float to a rational first, which for an exponent `e` costs `e` bits.  The public
`logBaseExact?` and `logBaseP1Exact?` first decide from the exponent and the significand alone
whether the value can be a power of `c` at all (`logBaseExactSkip`, `logBaseP1ExactSkip`): a
non-integer never is, and an integer `x = core · 2^(e − q)` with `e > q` has
`v₂(x) = v₂(core) + e − q` and bit length `e`, so the valuation test of
`AzNat.valuationGuard` (for `x`) and the lifting-the-exponent test `v₂(n − 1) + 3 >
2 size c + size (size n)` (for `n = 1 + x`) can be evaluated without building `x`.  When the
tests do not exclude a power, `e` is at most about `q · log₂ c / log₂ (odd part of c)`, resp.
`q + 2 size c + size e`, and the conversion is cheap.
-/

namespace Azurite.AzFloat

/-- The largest `s ∈ [2, t]` with `b` a perfect `s`-th power, or `1`. -/
def maxPowExp (b : AzNat) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | s + 2 => if b.isPow (s + 2) then s + 2 else maxPowExp b (s + 1)

/-- The primitive root of a base `b` whose perfect-power exponents are at most `t`: `b = c^s` with
`s ≤ t` maximal. -/
def maxRootBaseBounded (b : AzNat) (t : ℕ) : AzNat × ℕ :=
  let s := maxPowExp b t
  (if s = 1 then b else b.rootInt s, s)

/-- The primitive root of a 64-bit base: `b = c^s` with `s ≤ 63` maximal.  Only exponents up to
`size b − 1` can work (`2^s ≤ c^s = b < 2^(size b)`), so the search is bounded by
`min 63 (size b − 1)` — for small bases a handful of root tests instead of 62. -/
def maxRootBase (b : AzNat) : AzNat × ℕ := maxRootBaseBounded b (min 63 (b.size - 1))

/-- `log_b x` as a rational when `x` is a positive integer power `c^r` of the primitive root `c`
of `b` (`r / s` for `b = c^s`), `none` otherwise; converts `x` to a rational first. -/
def logBaseExactCore? (x : AzFloat) (b : AzNat) : Option AzRat :=
  match x.toAzRat? with
  | some q =>
    if q.sign = true ∧ q.den = 1 ∧ q.num ≠ 0 then
      let cs := maxRootBase b
      (AzNat.checkedLogBase cs.1 q.num).map fun r =>
        AzRat.ofAzInts (AzNat.ofNat r).toAzInt (AzNat.ofNat cs.2).toAzInt
    else none
  | none => none

/-- `some (r / s)` when `q = c^r` for the primitive root `c` of `b = c^s` and an integer `r`,
`none` otherwise. -/
def logBaseExactRat? (q : AzRat) (b : AzNat) : Option AzRat :=
  let cs := maxRootBase b
  (AzRat.checkedLogBaseAbs (UInt64.ofNat cs.1.toNat) q).map fun r =>
    AzRat.ofAzInts (AzInt.ofInt r) (AzNat.ofNat cs.2).toAzInt

/-- `some (r / s)` when `x` is a positive integer with `1 + x = c^r` for the primitive root `c`
of `b = c^s`, `none` otherwise (the integer test comes first, so non-integers cost nothing). -/
def logBaseP1ExactCore? (x : AzFloat) (b : AzNat) : Option AzRat :=
  if x.isInteger then
    match x.toAzRat? with
    | some q =>
      if q.sign = true ∧ q.den = 1 ∧ q.num ≠ 0 then
        let cs := maxRootBase b
        (AzNat.checkedLogBase cs.1 (q.num + 1)).map fun r =>
          AzRat.ofAzInts (AzNat.ofNat r).toAzInt (AzNat.ofNat cs.2).toAzInt
      else none
    | none => none
  else none

/-- The 2-adic valuation of a nonzero `AzNat`. -/
def twoAdic (m : AzNat) : ℕ := m.trailingZeros.getD 0

/-- A cheap sufficient test, from the exponent and the significand alone, that a float `x` is
not a positive integer power of `c ≥ 2`: `x` is not an integer, or `x = core · 2^(e − q)` with
`e > q` fails the valuation test of `AzNat.valuationGuard` (computed from
`v₂(x) = v₂(core) + e − q` and `size x = e`). -/
def logBaseExactSkip (x : AzFloat) (c : AzNat) : Bool :=
  match x with
  | finite _ e q m _ =>
    if !(isInteger x) then true
    else if e ≤ (AzNat.ofNat q).toAzInt then false
    else
      let en := e.abs.toNat
      let tn := twoAdic (coreSignificand q m) + (en - q)
      let tc := twoAdic c
      if tc = 0 then true
      else decide (tn % tc ≠ 0 ∨ ¬ ((c.size - 1) * (tn / tc) < en ∧ en ≤ c.size * (tn / tc) + 1))
  | _ => false

/-- A cheap sufficient test, from the exponent and the significand alone, that `1 + x` is not
a power of `c ≥ 2` for a float `x`: `x` is not an integer, or `x = core · 2^(e − q) > 0` with
`e > q` has `v₂((1 + x) − 1) + 3 > 2 size c + size (size (1 + x))` (lifting the exponent; here
`size (1 + x) = e`). -/
def logBaseP1ExactSkip (x : AzFloat) (c : AzNat) : Bool :=
  match x with
  | finite s e q m _ =>
    if !(isInteger x) then true
    else if s = false ∨ e ≤ (AzNat.ofNat q).toAzInt then false
    else
      let en := e.abs.toNat
      decide (2 * c.size + en.size < twoAdic (coreSignificand q m) + (en - q) + 3)
  | _ => false

/-- `log_b x` as a rational when `x` is a positive integer power `c^r` of the primitive root `c`
of `b` (`r / s` for `b = c^s`), `none` otherwise.  A huge integer is never materialised
(`logBaseExactSkip`). -/
def logBaseExact? (x : AzFloat) (b : AzNat) : Option AzRat :=
  if logBaseExactSkip x (maxRootBase b).1 then none else logBaseExactCore? x b

/-- `some (r / s)` when `x` is a positive integer with `1 + x = c^r` for the primitive root `c`
of `b = c^s`, `none` otherwise.  A huge integer is never materialised
(`logBaseP1ExactSkip`). -/
def logBaseP1Exact? (x : AzFloat) (b : AzNat) : Option AzRat :=
  if logBaseP1ExactSkip x (maxRootBase b).1 then none else logBaseP1ExactCore? x b

/-! ### A float base -/

/-- The odd part of a nonzero `AzNat`: `m = 2^(twoAdic m) · oddPart m`. -/
def oddPart (m : AzNat) : AzNat := m >>> twoAdic m

/-- The dyadic exponent of a finite float `o · 2^i` of exponent `e` and significand `m`:
`i = e − size m + twoAdic m`. -/
def dyadicExp (e : AzInt) (m : AzNat) : AzInt :=
  e - (AzNat.ofNat (m.size - twoAdic m)).toAzInt

/-- **Multiplicative dependence of two positive integers**, by the Euclidean algorithm on
exponents: `some (p, q)` with `x = g^p`, `y = g^q` for a common `g` when `x` and `y` are
multiplicatively dependent (`x^b = y^a` for some `(a, b) ≠ (0, 0)`), `none` otherwise.  If
`y ≤ x` are dependent then `y ∣ x` and `x / y`, `y` are dependent again; a whole power `y^e`
with `y^e ≤ x` (`e = ⌊(size x − 1) / size y⌋`, from the bit lengths) is divided out at once.
No root is extracted: the cost is that of a few divisions, where a search for the primitive
root of `y` takes a root test for every exponent up to the bit length of `y`.  The fuel
`size x + size y` is never exhausted (every step shortens one of the numbers). -/
def mulDepExps : ℕ → AzNat → AzNat → Option (ℕ × ℕ)
  | 0, _, _ => none
  | f + 1, x, y =>
    if y = 1 then some (1, 0)
    else if x = 1 then some (0, 1)
    else if y ≤ x then
      let e := max 1 ((x.size - 1) / y.size)
      let qr := AzNat.divMod x (y.pow e)
      if qr.2 = 0 then (mulDepExps f qr.1 y).map fun pq => (pq.1 + e * pq.2, pq.2) else none
    else
      let e := max 1 ((y.size - 1) / x.size)
      let qr := AzNat.divMod y (x.pow e)
      if qr.2 = 0 then (mulDepExps f x qr.1).map fun pq => (pq.1, pq.2 + e * pq.1) else none

/-- `some (log_b x)` when it is rational, for `x = o · 2^i` and `b = s · 2^j` with `o`, `s` odd
and `b ≠ 1`.  For `j = 0` (`b = s` an odd integer) `x` and `s` must be powers `g^p`, `g^q` of a
common integer (`mulDepExps`), and the value is `p / q`; otherwise the value can only be
`i / j`, and with `a / e` that fraction
in lowest terms, `x^e = b^a` is checked through the perfect-power tests (`o = c^a` and `s = c^e`
for a common `c` when `a > 0`, and `o = s = 1` when `a < 0`). -/
def logBaseFloatExact? (i : AzInt) (o : AzNat) (j : AzInt) (s : AzNat) : Option AzRat :=
  if j = 0 then
    if i = 0 then
      (mulDepExps (o.size + s.size) o s).map fun pq =>
        AzRat.ofAzInts (AzNat.ofNat pq.1).toAzInt (AzNat.ofNat pq.2).toAzInt
    else none
  else
    let r := AzRat.ofAzInts i j
    let a := r.num.toNat
    let e := r.den.toNat
    if r.sign then
      if s.isPow e ∧ o.isPow a ∧ s.rootInt e = o.rootInt a then some r else none
    else if o = 1 ∧ s = 1 then some r else none

/-- The odd part and dyadic exponent of `1 + x` for a float `x = ±o · 2^i > −1` of sign `s`:
`1 + x = o' · 2^i'`.  For `x ≥ 0` with `i ≥ 0` the sum is the integer `o · 2^i + 1`; otherwise
`1 + x = (2^t ± o) / 2^t` with `t = −i`. -/
def onePlusDyadic (s : Bool) (i : AzInt) (o : AzNat) : AzNat × AzInt :=
  if s then
    if i.sign then
      let n := (o <<< i.abs.toNat) + 1
      (oddPart n, (AzNat.ofNat (twoAdic n)).toAzInt)
    else
      let u := ((1 : AzNat) <<< i.abs.toNat) + o
      (oddPart u, (AzNat.ofNat (twoAdic u)).toAzInt - (AzNat.ofNat i.abs.toNat).toAzInt)
  else
    let u := ((1 : AzNat) <<< i.abs.toNat) - o
    (oddPart u, (AzNat.ofNat (twoAdic u)).toAzInt - (AzNat.ofNat i.abs.toNat).toAzInt)

/-- `b^n` in machine words (modulo `2^64`), by binary exponentiation. -/
def upow64 (b : UInt64) (n : ℕ) : UInt64 :=
  if _ : n = 0 then 1
  else
    let r := upow64 (b * b) (n / 2)
    if n % 2 = 1 then b * r else r
termination_by n
decreasing_by omega

/-- A cheap sufficient test that `logBaseFloatExact?` answers `none` on `1 + x` for
`x = ±o · 2^i` (sign `s`, `o` odd) and the base `sb · 2^j`, **without building** the odd part
of `1 + x`, which has about `|i|` bits (`onePlusDyadic`):

* `i ≥ 1` (an even integer `x > 0`): `1 + x` is an odd integer above `1`.  With `j ≠ 0` the
  logarithm is irrational.  With `j = 0`, `1 + x` would be a power of the primitive root `c` of
  `sb`, excluded when `v₂(x) + 2 = i + 2 > v₂(sb − 1) + v₂(sb + 1) + size (size (1 + x))`
  (lifting the exponent: `v₂(c^r − 1) ≤ v₂(c² − 1) + v₂(r) − 1` and `c² − 1 ∣ sb² − 1`;
  `size (1 + x) = size o + i`).  The bound involves only the valuations of `sb ∓ 1`, not the
  size of `sb`, so a base as large as `x` itself is rejected too unless it is `≡ ±1` modulo a
  power of two comparable to `x`.
* `i ≤ −64` and `size o < |i|` (a tiny or moderate non-integer `x`): `1 + x = u / 2^t` with
  `t = −i` and `u = 2^t ± o` odd.  With `j = 0`, or with `i / j < 0`, there is nothing to
  find.  Otherwise `u` would be `c^a` for `c` the exact `e`-th root of `sb` (`i / j = a / e` in
  lowest terms); `c^a` is computed modulo `2^64` and compared with `u ≡ ±o`.

Whenever the test is inconclusive the caller falls back to `onePlusDyadic`. -/
def onePlusSkip (s : Bool) (i : AzInt) (o : AzNat) (j : AzInt) (sb : AzNat) : Bool :=
  let t := i.abs.toNat
  if i.sign then
    if s = false ∨ t = 0 then false
    else if j ≠ 0 then true
    else decide (2 ≤ sb.size ∧ twoAdic (sb - 1) + twoAdic (sb + 1) + (o.size + t).size < t + 2)
  else
    if t < 64 ∨ t ≤ o.size then false
    else if j = 0 then true
    else
      let r := AzRat.ofAzInts
        ((AzNat.ofNat 0).toAzInt - (AzNat.ofNat t).toAzInt) j
      if r.sign then
        if sb.isPow r.den.toNat then
          let p := upow64 (sb.rootInt r.den.toNat).toUInt64 r.num.toNat
          if s then p != o.toUInt64 else p + o.toUInt64 != 0
        else true
      else true

/-- `logBaseFloatExact?` on `1 + x` for `x = ±o · 2^i` and the base `sb · 2^j`: the cheap test
`onePlusSkip` first, then `onePlusDyadic`. -/
def logBaseFloatP1Exact? (s : Bool) (i : AzInt) (o : AzNat) (j : AzInt) (sb : AzNat) :
    Option AzRat :=
  if onePlusSkip s i o j sb then none
  else logBaseFloatExact? (onePlusDyadic s i o).2 (onePlusDyadic s i o).1 j sb

/-- The dyadic exponent of a rational: `twoAdic num − twoAdic den`. -/
def ratDyadicExp (q : AzRat) : AzInt :=
  (AzNat.ofNat (twoAdic q.num)).toAzInt - (AzNat.ofNat (twoAdic q.den)).toAzInt

/-- `some (log_b q)` when it is rational, for `q = (n / d) · 2^i` with `n`, `d` odd and coprime
and `b = s · 2^j`: only possible with `d = 1` (the float case on `n · 2^i`) or `n = 1` (the float
case on `d · 2^(−i)`, negated). -/
def logBaseRatFloatExact? (i : AzInt) (n d : AzNat) (j : AzInt) (s : AzNat) : Option AzRat :=
  if d = 1 then logBaseFloatExact? i n j s
  else if n = 1 then (logBaseFloatExact? (-i) d j s).map fun r => -r
  else none

/-- `some (log_b x)` when it is rational, for `x = o · 2^i` and `b = (n / d) · 2^j` with `n`, `d`
odd and coprime: only possible with `d = 1` (the float case with base `n · 2^j`) or `n = 1` (the
float case with base `d · 2^(−j)`, negated). -/
def logBaseRatBaseExact? (i : AzInt) (o : AzNat) (j : AzInt) (n d : AzNat) : Option AzRat :=
  if d = 1 then logBaseFloatExact? i o j n
  else if n = 1 then (logBaseFloatExact? i o (-j) d).map fun r => -r
  else none

/-- `logBaseRatBaseExact?` on `1 + x` for `x = ±o · 2^i` and the base `(n / d) · 2^j`, through
`logBaseFloatP1Exact?` (no huge odd part is built when `onePlusSkip` answers). -/
def logBaseRatBaseP1Exact? (s : Bool) (i : AzInt) (o : AzNat) (j : AzInt) (n d : AzNat) :
    Option AzRat :=
  if d = 1 then logBaseFloatP1Exact? s i o j n
  else if n = 1 then (logBaseFloatP1Exact? s i o (-j) d).map fun r => -r
  else none

/-- `some (log_{n₂} n₁)` when rational, for odd integers `n₁`, `n₂ ≥ 3` (the odd-integer-base
case of `logBaseFloatExact?`). -/
def logOddExact? (n₁ n₂ : AzNat) : Option AzRat := logBaseFloatExact? 0 n₁ 0 n₂

/-- The common value of `log_{n₂} n₁` and `log_{d₂} d₁` when both are rational and equal. -/
def logOddPairExact? (n₁ d₁ n₂ d₂ : AzNat) : Option AzRat :=
  match logOddExact? n₁ n₂, logOddExact? d₁ d₂ with
  | some v₁, some v₂ => if v₁ = v₂ then some v₁ else none
  | _, _ => none

/-- The 2-adic consistency of a candidate value `v` of `log_b q` with the dyadic exponents `i`
of `q` and `j` of `b`: `i = 0` when `j = 0`, and `v = i / j` otherwise. -/
def dyadicOK (i j : AzInt) (v : AzRat) : Bool :=
  if j = 0 then decide (i = 0) else decide (v = AzRat.ofAzInts i j)

/-- The negative candidate: `−u` when `log_{d₂} n₁ = log_{n₂} d₁ = u` is 2-adically consistent. -/
def logBaseRatRatNeg? (i : AzInt) (n₁ d₁ : AzNat) (j : AzInt) (n₂ d₂ : AzNat) : Option AzRat :=
  match logOddPairExact? n₁ d₁ d₂ n₂ with
  | some u => if dyadicOK i j (-u) then some (-u) else none
  | none => none

/-- `some (log_b q)` when it is rational, for `q = (n₁ / d₁) · 2^i` and `b = (n₂ / d₂) · 2^j`
with odd coprime pairs.  When one of `d₂`, `n₂`, `d₁`, `n₁` is `1` this is a float-base or
float-argument case; otherwise `log_b q = a/e` forces `log_{n₂} n₁ = log_{d₂} d₁ = a/e`
(for `a ≥ 0`) or `log_{d₂} n₁ = log_{n₂} d₁ = −a/e` (for `a < 0`), together with the 2-adic
condition `i e = j a` (`dyadicOK`). -/
def logBaseRatRatExact? (i : AzInt) (n₁ d₁ : AzNat) (j : AzInt) (n₂ d₂ : AzNat) :
    Option AzRat :=
  if d₂ = 1 then logBaseRatFloatExact? i n₁ d₁ j n₂
  else if n₂ = 1 then (logBaseRatFloatExact? i n₁ d₁ (-j) d₂).map fun r => -r
  else if d₁ = 1 then logBaseRatBaseExact? i n₁ j n₂ d₂
  else if n₁ = 1 then (logBaseRatBaseExact? (-i) d₁ j n₂ d₂).map fun r => -r
  else
    match logOddPairExact? n₁ d₁ n₂ d₂ with
    | some v => if dyadicOK i j v then some v else logBaseRatRatNeg? i n₁ d₁ j n₂ d₂
    | none => logBaseRatRatNeg? i n₁ d₁ j n₂ d₂

end Azurite.AzFloat

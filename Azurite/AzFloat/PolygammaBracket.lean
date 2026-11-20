/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DigammaBracket
import Azurite.AzFloat.RoundToInteger
import Azurite.AzNat.RisingFallingFactorial
import Azurite.AzNat.Factorial

/-!
## The bracket of the polygamma functions `ψ⁽ⁿ⁾(x)`, `n ≥ 1`

All enclosures are of `H(x) = (−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x)`, which is positive for `x > 0`.

**`x > 0`** (`polygammaPosEncl`).  The asymptotic series (DLMF 5.15.8–5.15.9) at a shifted
argument `y = x + δ`, as for `ψ` (`AzFloat/DigammaBracket.lean`):

  `H(x) = H(y) + n! ∑_{j<δ} (x + j)^{−n−1}`,
  `H(y) = y^{−n} [(n − 1)! + n!/(2y) + ∑_{k=1}^{N−1} (−1)^(k+1) c_k (2k) ⋯ (2k+n−1) / y^(2k) + r]`,

`c_k = T_k / (4^(2k) − 2^(2k))` with the tangent numbers, the remainder `r` between `0` and
the first omitted term (`polyNu_eq_sum_add`, `Transcendental/PolygammaStirling.lean`).  The
terms are those of `ψ` times a rising factorial, so the loop `polySumLoop` is `psiSumLoop`
with another term.  The shift sum is taken once, rounded down, and its upper end is that sum
times a factor just above `1` (`polyShiftSum`, as `harmonicEncl` does for `ψ`).  The ratio of consecutive terms is `(2k+n)(2k+n+1)/(2πy)²`: against `ψ`
the argument has to grow by the factor `1 + n/(2M)` for the same `M` terms (`polyShift`).

**`x < 0`**, not an integer (`polygammaNegEncl`): no reflection formula and no trigonometric
function.  With `m` such that `0 < x + m < 1`: for a small `m` the recurrence in positive
terms, `H(x) = H(x + m) + (−1)ⁿ⁺¹ n! ∑_{j<m} (1 − x − m + j)^{−n−1}` (`polygammaR_neg_sum`),
one evaluation and `m` terms; otherwise

  `H(x) = H(x + m) + (−1)ⁿ (H(1 − x) − H(1 − x − m))`

(`polygammaR_reflect`: the finite sums of the recurrence at `x` and at `1 − x − m` agree up
to sign), three positive arguments at a cost that does not depend on `|x|`.  `x + m` and
`1 − x − m` are each one rounding of an exact difference, so they are relatively accurate
next to the poles, where their term dominates.

Nothing is assumed about the widths.  Between two poles `ψ⁽ⁿ⁾` can vanish (for an even `n`,
next to every negative half-integer), and there the terms cancel: `polygammaEnclFor` reads
the missing bits off the enclosure and evaluates once more with that many more.  The proofs
are in `Equiv/PolygammaBracket.lean`.
-/

namespace Azurite.AzFloat

/-! ### Powers of positive enclosures by repeated squaring -/

/-- `[a]ⁿ` for a positive enclosure and `n < 2^fuel`, by repeated squaring. -/
def Encl.powBinAux (w : Nat) (a : Encl) : Nat → Nat → Encl
  | 0, _ => Encl.exact one
  | fuel + 1, n =>
    if n = 0 then Encl.exact one
    else
      let h := Encl.powBinAux w a fuel (n / 2)
      if n % 2 = 1 then Encl.mul w (Encl.mul w h h) a else Encl.mul w h h

/-- `[a]ⁿ` for a positive enclosure, by repeated squaring (`Encl.pow` multiplies `n` times). -/
def Encl.powBin (w : Nat) (a : Encl) (n : Nat) : Encl := Encl.powBinAux w a (n.log2 + 1) n

/-! ### The series for `x > 0` -/

/-- The enclosure of `c_k (2k)(2k+1) ⋯ (2k+n−1) / y^(2k)` from the tangent number table `T`
and an enclosure `p` of `y^(−2k)`. -/
def polyTermEncl (V : Nat) (T : Array AzNat) (n k : Nat) (p : Encl) : Encl :=
  Encl.mul V (psiTermEncl V T k p)
    (Encl.exact (ofAzNat (AzNat.factorialQuotient (2 * k + n - 1) (2 * k - 1))))

/-- The sum of the scaled series from the term `k` on: `p` encloses `y^(−2k)`, `acc` the terms
before `k`, `inv2` encloses `y^(−2)`.  A term below `tol`, or the last one of the table, is
not added: the remainder lies between `0` and it, with its sign `(−1)^(k+1)`. -/
def polySumLoop (V : Nat) (T : Array AzNat) (n : Nat) (inv2 : Encl) (tol : AzFloat) :
    Nat → Nat → Encl → Encl → Encl
  | 0, k, p, acc =>
    let τ := polyTermEncl V T n k p
    if k % 2 = 1 then (acc.1, (addPrecRound acc.2 τ.2 V .Ceiling).1)
    else ((subPrecRound acc.1 τ.2 V .Floor).1, acc.2)
  | fuel + 1, k, p, acc =>
    let τ := polyTermEncl V T n k p
    if le τ.2 tol then
      if k % 2 = 1 then (acc.1, (addPrecRound acc.2 τ.2 V .Ceiling).1)
      else ((subPrecRound acc.1 τ.2 V .Floor).1, acc.2)
    else
      polySumLoop V T n inv2 tol fuel (k + 1) (Encl.mul V p inv2)
        (if k % 2 = 1 then Encl.add V acc τ else Encl.sub V acc τ)

/-- The enclosure of `H(y) = (−1)ⁿ⁺¹ ψ⁽ⁿ⁾(y)` for `y > 0` from an enclosure `Y` of `y` with a
positive lower end, with `M ≥ 1` tangent numbers. -/
def polyStirlingEncl (V M n : Nat) (Y : Encl) (tol : AzFloat) : Encl :=
  let inv := Encl.div V (Encl.exact one) Y
  let inv2 := Encl.mul V inv inv
  let S := polySumLoop V (AzNat.tangentNumbers M) n inv2 tol (M - 1) 1 inv2 (Encl.exact zero)
  let lead := Encl.add V (Encl.exact (ofAzNat (AzNat.factorial (n - 1))))
    (Encl.half (Encl.mul V (Encl.exact (ofAzNat (AzNat.factorial n))) inv))
  Encl.mulPos V (Encl.add V lead S) (Encl.powBin V inv n)

/-- `yⁿ` rounded up at every step, for a positive float `y` and `n < 2^fuel`, by repeated
squaring. -/
def powUpAux (V : Nat) (y : AzFloat) : Nat → Nat → AzFloat
  | 0, _ => one
  | fuel + 1, n =>
    if n = 0 then one
    else
      let h := powUpAux V y fuel (n / 2)
      let s := (mulPrecRound h h V .Ceiling).1
      if n % 2 = 1 then (mulPrecRound s y V .Ceiling).1 else s

/-- An upper bound of `yⁿ` within the factor `(1 + 2^(1−V))^(4n)`. -/
def powUp (V : Nat) (y : AzFloat) (n : Nat) : AzFloat := powUpAux V y (n.log2 + 1) n

/-- The lower sums of `∑_{i ≤ j < i+m} (x + j)^{−k}` from a float `b ≥ x`: `lo` and `up` are the
sum of the quotients `⌊1/⌈(⌈b + j⌉)^k⌉⌋` rounded down and up. -/
def polyShiftLoop (V : Nat) (b : AzFloat) (k : Nat) :
    Nat → Nat → AzFloat → AzFloat → AzFloat × AzFloat
  | 0, _, lo, up => (lo, up)
  | m + 1, i, lo, up =>
    let y := (addPrecRound b (ofAzNat (AzNat.ofNat i)) V .Ceiling).1
    let q := (divPrecRound one (powUp V y k) V .Floor).1
    polyShiftLoop V b k m (i + 1) (addPrecRound lo q V .Floor).1 (addPrecRound up q V .Ceiling).1

/-- `∑_{j<i} (x + j)^{−n−1}` from an enclosure `X = [a, b]` of `x > 0`.  Every term is computed
once, rounded down, at the upper end `b` (`polyShiftLoop`), as in `harmonicEncl`: each
quotient is a lower bound of its term and within the factor
`(b/a)^k (1 + ε)^(5k) / (1 − ε)`, `k = n + 1`, `ε = 2^(1−V)`, of it; the upper end is the sum
of the quotients times `⌈⌈b/a⌉^k⌉ (1 + 2^(c−V))` with `2^c > 32 k`.  Half the operations of
the sum on enclosures. -/
def polyShiftSum (V : Nat) (X : Encl) (n i : Nat) : Encl :=
  let k := n + 1
  let s := polyShiftLoop V X.2 k i 0 zero zero
  let R := powUp V (divPrecRound X.2 X.1 V .Ceiling).1 k
  let K := (mulPrecRound R
    (addPrecRound one
      (powerOf2 (AzInt.ofInt (((32 * k).log2 + 1 : Nat) : Int) - (AzNat.ofNat V).toAzInt)) V
      .Ceiling).1 V .Ceiling).1
  (s.1, (mulPrecRound s.2 K V .Ceiling).1)

/-- The shift `δ` for a positive lower end `lo`: `lo + δ ≥ 2^L (1 + n/(2M)) + 1`, where the
series with `M` terms is as good for `ψ⁽ⁿ⁾` as it is for `ψ` at `2^L`. -/
def polyShift (lo : AzFloat) (n L M : Nat) : Nat :=
  let target := 2 ^ L + 2 ^ L * n / (2 * M) + 1
  if le (ofAzNat (AzNat.ofNat target)) lo then 0
  else target - (truncToAzInt lo).abs.toNat

/-- The working precision at Ziv level `w`. -/
def polyWork (n w : Nat) : Nat := w + 2 * lnGammaShiftExp w + 16 + 2 * w.log2 + 2 * n.log2

/-- The bracket of `H(x) = (−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x)` at Ziv level `w` from an enclosure `X` of `x > 0`
(positive lower end). -/
def polygammaPosEncl (n : Nat) (X : Encl) (w : Nat) : Encl :=
  let L := lnGammaShiftExp w
  let V := polyWork n w
  let M := lnGammaTerms w (L + 1)
  let δ := polyShift X.1 n L M
  let tol := powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)
  if δ = 0 then polyStirlingEncl V M n X tol
  else
    Encl.add V (polyStirlingEncl V M n (Encl.add V X (Encl.nat δ)) tol)
      (Encl.mul V (Encl.exact (ofAzNat (AzNat.factorial n))) (polyShiftSum V X n δ))

/-! ### Negative arguments -/

/-- An enclosure of `H(x)` at Ziv level `w` for a finite `x < 0` that is not an integer; `none`
when the arguments do not come out positive at this level.  With `m` such that
`0 < x + m < 1`: for `m ≤ 2^L` the recurrence itself,
`H(x) = H(x + m) + (−1)ⁿ⁺¹ n! ∑_{j<m} (1 − x − m + j)^{−n−1}` (one evaluation and `m` terms);
beyond, the three evaluations `H(x + m) + (−1)ⁿ (H(1 − x) − H(1 − x − m))`. -/
def polygammaNegEncl (n : Nat) (x : AzFloat) (w : Nat) : Option Encl :=
  let m := (truncToAzInt x).abs.toNat + 1
  let W := w + 32
  let U := Encl.add W (Encl.exact x) (Encl.nat m)
  let A₂ := Encl.sub W (Encl.neg (Encl.nat (m - 1))) (Encl.exact x)
  if m ≤ 2 ^ lnGammaShiftExp w then
    if lt zero U.1 && lt zero A₂.1 then
      let V := polyWork n w
      let T := Encl.mul V (Encl.exact (ofAzNat (AzNat.factorial n))) (polyShiftSum V A₂ n m)
      some (if n % 2 = 1 then Encl.add W (polygammaPosEncl n U w) T
        else Encl.sub W (polygammaPosEncl n U w) T)
    else none
  else
    let A₁ := Encl.sub W (Encl.exact one) (Encl.exact x)
    if lt zero U.1 && lt zero A₁.1 && lt zero A₂.1 then
      let D := Encl.sub W (polygammaPosEncl n A₁ w) (polygammaPosEncl n A₂ w)
      some (if n % 2 = 0 then Encl.add W (polygammaPosEncl n U w) D
        else Encl.sub W (polygammaPosEncl n U w) D)
    else none

/-- An enclosure of `ψ⁽ⁿ⁾(x)` at Ziv level `w` for a finite `x` that is positive (`pos`) or
negative and not an integer. -/
def polygammaEncl (n : Nat) (x : AzFloat) (pos : Bool) (w : Nat) : Option Encl :=
  (if pos then some (polygammaPosEncl n (Encl.exact x) w) else polygammaNegEncl n x w).map
    fun H => if n % 2 = 1 then H else Encl.neg H

/-! ### A second evaluation where digits cancel -/

/-- The bits of relative accuracy of an enclosure that does not contain `0`: the exponent of
its end nearer to `0` minus that of its width; `none` when it contains `0` or has no width. -/
def enclAccuracy (E : Encl) : Option Int :=
  if lt zero E.1 || lt E.2 zero then
    let wd := (subPrecRound E.2 E.1 32 .Ceiling).1
    if lt zero wd then
      some ((expOf (if lt zero E.1 then E.1 else E.2)).toInt - (expOf wd).toInt)
    else none
  else none

/-- An enclosure from the family `f` of enclosures by level, for the target precision `p`: when
the one at level `w` has fewer than `p + 8` bits but shows how many are missing, a second
evaluation with that many more, instead of leaving it to the doubling of Ziv's loop. -/
def enclRefine (f : Nat → Option Encl) (p w : Nat) : Option Encl :=
  match f w with
  | none => none
  | some E =>
    match enclAccuracy E with
    | none => some E
    | some r =>
      let d := (((p + 8 : Nat) : Int) - r).toNat
      if d = 0 ∨ w < d then some E else f (w + d + 8)

/-- `polygammaEncl` for the target precision `p` (`enclRefine`): `ψ⁽ⁿ⁾` has zeros between its
poles, next to which the terms cancel. -/
def polygammaEnclFor (n : Nat) (x : AzFloat) (pos : Bool) (p w : Nat) : Option Encl :=
  enclRefine (polygammaEncl n x pos) p w

/-- Arguments where `ψ⁽ⁿ⁾(x)` is known to be irrational, so that Ziv's loop needs no fuel
(`polygammaApprox_cert`, `Equiv/PolygammaCertificate.lean`): `n` odd, and `x` a positive
integer or a half-integer (not an integer).  There `ψ⁽ⁿ⁾(x)` is a rational number plus a
nonzero rational multiple of `π^(n+1)` (`Azurite.irrational_polygammaR_div_two`). -/
def polygammaSpecial (n : Nat) (x : AzFloat) : Bool :=
  n % 2 == 1 && x.isFinite && isInteger (x <<< AzInt.ofInt 1) && (lt zero x || !isInteger x)

end Azurite.AzFloat

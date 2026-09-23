/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Equiv.Arithmetic
import Azurite.AzMvRationalFunction.Parse
import Azurite.AzRat.Instances

/-!
# Algebraic instances for `AzMvRationalFunction`

`AzMvRationalFunction n ord` is a field: this file assembles the `Field`
instance on top of the computational operations defined earlier, plus the
bundled ring equivalence `ringEquivRatFunc` with
`ℚ(x⃗) = FractionRing (MvPolynomial (Fin n) ℚ)`. Every law is transported from
`M` through the injection `toMvRatFunc` and the `toMvRatFunc_*` commutation
theorems — no new computation is introduced, and all data fields are the
existing verified operations.

The casts are computable and factor through the `O(1)` constant embedding
`ofAzRat` and the (limb-level) `AzRat` casts; `n • r` and `z • r` are one cast
plus one multiplication. `npow`/`zpow` use the recursive defaults (a fast
componentwise power can be added later, as in the univariate case).
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzRat (toRat)

variable {n : ℕ} {ord : MonomialOrder}

/-- The target field. -/
private abbrev M (n : ℕ) := FractionRing (MvPolynomial (Fin n) ℚ)

instance : NatCast (AzMvRationalFunction n ord) := ⟨fun m => ofAzRat m⟩

@[simp] theorem toMvRatFunc_natCast (m : ℕ) :
    toMvRatFunc (m : AzMvRationalFunction n ord) = (m : M n) := by
  show toMvRatFunc (ofAzRat ((m : ℕ) : AzRat)) = _
  rw [toMvRatFunc_ofAzRat, Azurite.AzRat.toRat_natCast, map_natCast]

instance : IntCast (AzMvRationalFunction n ord) := ⟨fun z => ofAzRat z⟩

@[simp] theorem toMvRatFunc_intCast (z : ℤ) :
    toMvRatFunc (z : AzMvRationalFunction n ord) = (z : M n) := by
  show toMvRatFunc (ofAzRat ((z : ℤ) : AzRat)) = _
  rw [toMvRatFunc_ofAzRat, Azurite.AzRat.toRat_intCast, map_intCast]

instance : RatCast (AzMvRationalFunction n ord) := ⟨fun q => ofAzRat q⟩

@[simp] theorem toMvRatFunc_ratCast (q : ℚ) :
    toMvRatFunc (q : AzMvRationalFunction n ord) = (q : M n) := by
  show toMvRatFunc (ofAzRat ((q : ℚ) : AzRat)) = _
  rw [toMvRatFunc_ofAzRat, Azurite.AzRat.toRat_ratCast]
  simp

instance : NNRatCast (AzMvRationalFunction n ord) := ⟨fun q => ofAzRat q⟩

@[simp] theorem toMvRatFunc_nnratCast (q : ℚ≥0) :
    toMvRatFunc (q : AzMvRationalFunction n ord) = (q : M n) := by
  show toMvRatFunc (ofAzRat ((q : ℚ≥0) : AzRat)) = _
  rw [toMvRatFunc_ofAzRat, Azurite.AzRat.toRat_nnratCast]
  simp

instance : Nontrivial (AzMvRationalFunction n ord) := ⟨0, 1, fun h => by
  have h1 : (0 : M n) = 1 := by rw [← toMvRatFunc_zero, ← toMvRatFunc_one, h]
  exact absurd h1 zero_ne_one⟩

/-- **`AzMvRationalFunction n ord` is a field.** Every law is transported from
`M = ℚ(x⃗)` through `toMvRatFunc_injective`; the data fields are the existing
computable operations (`m • r`/`z • r`/`q • r` are one cast plus one
multiplication; `r ^ m`/`r ^ z` use the recursive default powers). -/
instance instField : Field (AzMvRationalFunction n ord) where
  add_assoc a b c := toMvRatFunc_injective (by simp only [toMvRatFunc_add]; ring)
  zero_add a := toMvRatFunc_injective (by
    simp only [toMvRatFunc_add, toMvRatFunc_zero]; ring)
  add_zero a := toMvRatFunc_injective (by
    simp only [toMvRatFunc_add, toMvRatFunc_zero]; ring)
  add_comm a b := toMvRatFunc_injective (by simp only [toMvRatFunc_add]; ring)
  mul_assoc a b c := toMvRatFunc_injective (by simp only [toMvRatFunc_mul]; ring)
  one_mul a := toMvRatFunc_injective (by
    simp only [toMvRatFunc_mul, toMvRatFunc_one]; ring)
  mul_one a := toMvRatFunc_injective (by
    simp only [toMvRatFunc_mul, toMvRatFunc_one]; ring)
  left_distrib a b c := toMvRatFunc_injective (by
    simp only [toMvRatFunc_add, toMvRatFunc_mul]; ring)
  right_distrib a b c := toMvRatFunc_injective (by
    simp only [toMvRatFunc_add, toMvRatFunc_mul]; ring)
  zero_mul a := toMvRatFunc_injective (by
    simp only [toMvRatFunc_mul, toMvRatFunc_zero]; ring)
  mul_zero a := toMvRatFunc_injective (by
    simp only [toMvRatFunc_mul, toMvRatFunc_zero]; ring)
  mul_comm a b := toMvRatFunc_injective (by simp only [toMvRatFunc_mul]; ring)
  neg_add_cancel a := toMvRatFunc_injective (by
    simp only [toMvRatFunc_add, toMvRatFunc_neg, toMvRatFunc_zero]; ring)
  sub_eq_add_neg _ _ := rfl
  div_eq_mul_inv _ _ := rfl
  -- `m • r` / `z • r` are one cast plus one multiplication (the default
  -- `nsmulRec`/`zsmulRec` would be `m` additions); the casts are `O(1)`
  -- through `ofAzRat`.
  nsmul m r := (m : AzMvRationalFunction n ord) * r
  nsmul_zero r := toMvRatFunc_injective (by
    show toMvRatFunc (((0 : ℕ) : AzMvRationalFunction n ord) * r) = toMvRatFunc 0
    simp only [toMvRatFunc_mul, toMvRatFunc_natCast, toMvRatFunc_zero]
    push_cast
    ring)
  nsmul_succ m r := toMvRatFunc_injective (by
    show toMvRatFunc (((m + 1 : ℕ) : AzMvRationalFunction n ord) * r)
      = toMvRatFunc (((m : ℕ) : AzMvRationalFunction n ord) * r + r)
    simp only [toMvRatFunc_mul, toMvRatFunc_add, toMvRatFunc_natCast]
    push_cast
    ring)
  zsmul z r := (z : AzMvRationalFunction n ord) * r
  zsmul_zero' r := toMvRatFunc_injective (by
    show toMvRatFunc (((0 : ℤ) : AzMvRationalFunction n ord) * r) = toMvRatFunc 0
    simp only [toMvRatFunc_mul, toMvRatFunc_intCast, toMvRatFunc_zero]
    push_cast
    ring)
  zsmul_succ' m r := toMvRatFunc_injective (by
    show toMvRatFunc ((((m + 1 : ℕ) : ℤ) : AzMvRationalFunction n ord) * r)
      = toMvRatFunc ((((m : ℕ) : ℤ) : AzMvRationalFunction n ord) * r + r)
    simp only [toMvRatFunc_mul, toMvRatFunc_add, toMvRatFunc_intCast]
    push_cast
    ring)
  zsmul_neg' m r := toMvRatFunc_injective (by
    show toMvRatFunc (((Int.negSucc m) : AzMvRationalFunction n ord) * r)
      = toMvRatFunc (-((((m + 1 : ℕ) : ℤ) : AzMvRationalFunction n ord) * r))
    simp only [toMvRatFunc_mul, toMvRatFunc_neg, toMvRatFunc_intCast]
    push_cast [Int.negSucc_eq]
    ring)
  -- `r ^ m` / `r ^ z` run the componentwise `pow`/`zpow` (no gcd; the parts
  -- and the factor use sliding-window powers), so they are `O(log m)`
  -- multiplications rather than the default `O(m)`.
  npow m r := pow r m
  npow_zero r := toMvRatFunc_injective (by
    show toMvRatFunc (pow r 0) = toMvRatFunc 1
    rw [toMvRatFunc_pow, pow_zero, toMvRatFunc_one])
  npow_succ m r := toMvRatFunc_injective (by
    show toMvRatFunc (pow r (m + 1)) = toMvRatFunc (pow r m * r)
    rw [toMvRatFunc_mul, toMvRatFunc_pow, toMvRatFunc_pow, pow_succ])
  zpow z r := zpow r z
  zpow_zero' r := toMvRatFunc_injective (by
    show toMvRatFunc (zpow r 0) = toMvRatFunc 1
    rw [toMvRatFunc_zpow, zpow_zero, toMvRatFunc_one])
  zpow_succ' m r := toMvRatFunc_injective (by
    show toMvRatFunc (zpow r ((m.succ : ℕ) : ℤ)) = toMvRatFunc (zpow r ((m : ℕ) : ℤ) * r)
    rw [toMvRatFunc_mul, toMvRatFunc_zpow, toMvRatFunc_zpow, zpow_natCast, zpow_natCast,
      pow_succ])
  zpow_neg' m r := toMvRatFunc_injective (by
    show toMvRatFunc (zpow r (Int.negSucc m)) = toMvRatFunc ((zpow r ((m.succ : ℕ) : ℤ))⁻¹)
    rw [toMvRatFunc_inv, toMvRatFunc_zpow, toMvRatFunc_zpow, zpow_negSucc, zpow_natCast])
  natCast_zero := toMvRatFunc_injective (by
    rw [toMvRatFunc_natCast, toMvRatFunc_zero, Nat.cast_zero])
  natCast_succ m := toMvRatFunc_injective (by
    rw [toMvRatFunc_natCast, toMvRatFunc_add, toMvRatFunc_natCast, toMvRatFunc_one,
      Nat.cast_succ])
  intCast_ofNat m := toMvRatFunc_injective (by
    rw [toMvRatFunc_intCast, toMvRatFunc_natCast, Int.cast_natCast])
  intCast_negSucc m := toMvRatFunc_injective (by
    rw [toMvRatFunc_intCast, toMvRatFunc_neg, toMvRatFunc_natCast, Int.cast_negSucc])
  mul_inv_cancel a ha := toMvRatFunc_injective (by
    rw [toMvRatFunc_mul, toMvRatFunc_inv, toMvRatFunc_one]
    exact mul_inv_cancel₀ fun h =>
      ha (toMvRatFunc_injective (h.trans toMvRatFunc_zero.symm)))
  inv_zero := toMvRatFunc_injective (by
    rw [toMvRatFunc_inv, toMvRatFunc_zero, inv_zero])
  nnqsmul q a := (q : AzMvRationalFunction n ord) * a
  qsmul q a := (q : AzMvRationalFunction n ord) * a
  nnratCast_def q := toMvRatFunc_injective (by
    simp only [toMvRatFunc_nnratCast, toMvRatFunc_div, toMvRatFunc_natCast]
    rw [NNRat.cast_def])
  ratCast_def q := toMvRatFunc_injective (by
    simp only [toMvRatFunc_ratCast, toMvRatFunc_div, toMvRatFunc_intCast,
      toMvRatFunc_natCast]
    rw [Rat.cast_def])

/-- **The bundled ring equivalence with `ℚ(x⃗)`**: `equivRatFunc`, together with
the `toMvRatFunc_add`/`toMvRatFunc_mul` commutation theorems. -/
noncomputable def ringEquivRatFunc :
    AzMvRationalFunction n ord ≃+* FractionRing (MvPolynomial (Fin n) ℚ) :=
  { equivRatFunc with
    map_add' := toMvRatFunc_add
    map_mul' := toMvRatFunc_mul }

end Azurite.AzMvRationalFunction

namespace Azurite

-- Sanity checks: numeric literals, field operations, smul, and pow all
-- compute (string-anchored via `toStrWith (XyzVar 2)`).

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def rr (s : String) : AzMvRationalFunction 2 .Degrevlex :=
  (AzMvRationalFunction.parseStrWith (XyzVar 2) s).getD 0

private def render (r : AzMvRationalFunction 2 .Degrevlex) : String :=
  AzMvRationalFunction.toStrWith (XyzVar 2) r

#guard render ((rr "1/x" + rr "1/(x+1)") * (rr "x^2+x")) == "2*x+1"
#guard (rr "x*y/2") ^ (3 : ℕ) == rr "x^3*y^3/8"
#guard render ((2 : ℕ) • rr "x*y/2") == "x*y"
#guard render (((-1 : ℤ) : AzMvRationalFunction 2 .Degrevlex) * rr "x*y") == "-x*y"
#guard render (((3 / 4 : ℚ) : AzMvRationalFunction 2 .Degrevlex)) == "3/4"
#guard render (rr "x*y/2" / rr "x*y/2") == "1"
-- the field `^` now runs the fast componentwise `pow`/`zpow`
#guard (rr "x*y/2") ^ (3 : ℕ) == rr "x^3*y^3/8"
#guard (rr "x*y/2") ^ (-2 : ℤ) == rr "4/(x^2*y^2)"

end Azurite

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRationalFunction.Compare
import Azurite.AzRationalFunction.Equiv.Parse
import Azurite.AzPolynomial.Equiv.Compare
import Azurite.AzPolynomial.Equiv.Predicates

/-!
# The `LinearOrder` on `AzRationalFunction`

Lawfulness of the display-fraction comparison of
`Azurite.AzRationalFunction.Compare`: the `LinearOrder AzRationalFunction`
instance in the house style (`compare := compare` with
`compare_eq_compareOfLessAndEq`), built on the lawful `AzPolynomial` order
lexicographically (denominator first) — the display pair determines the
value (`ofNumDen_displayNum_displayDen`), so comparison-equality is
equality.

Plus the order-embedding theorems: a polynomial displays as `(p, 1)`
(`displayNum_ofPolynomial` / `displayDen_ofPolynomial`), so the canonical
map `ofPolynomial` is strictly order-preserving (`ofPolynomial_lt_iff`,
`ofPolynomial_strictMono`).
-/

namespace Azurite.AzRationalFunction

open Polynomial

/-! ### Component shims: the raw `AzPolynomial.compare` vs the lawful order -/

private theorem pcmp_lt {p q : Azurite.AzPolynomial AzInt} :
    AzPolynomial.compare p q = .lt ↔ p < q := by
  show Ord.compare p q = .lt ↔ p < q
  exact compare_lt_iff_lt

private theorem pcmp_eq {p q : Azurite.AzPolynomial AzInt} :
    AzPolynomial.compare p q = .eq ↔ p = q := by
  show Ord.compare p q = .eq ↔ p = q
  exact compare_eq_iff_eq

private theorem pcmp_gt {p q : Azurite.AzPolynomial AzInt} :
    AzPolynomial.compare p q = .gt ↔ q < p := by
  show Ord.compare p q = .gt ↔ q < p
  exact compare_gt_iff_gt

/-! ### Laws of the display-lexicographic comparison -/

/-- Equal displays mean equal values: the display pair re-normalizes to the
original. -/
private theorem eq_of_display_eq {r s : AzRationalFunction}
    (hn : displayNum r = displayNum s) (hd : displayDen r = displayDen s) : r = s := by
  rw [← ofNumDen_displayNum_displayDen r, ← ofNumDen_displayNum_displayDen s, hn, hd]

private theorem compare_self' (r : AzRationalFunction) : compare r r = .eq := by
  rw [compare, pcmp_eq.mpr rfl]
  show AzPolynomial.compare (displayNum r) (displayNum r) = .eq
  exact pcmp_eq.mpr rfl

private theorem compare_swap' (r s : AzRationalFunction) :
    compare s r = (compare r s).swap := by
  rw [compare, compare]
  rcases lt_trichotomy (displayDen r) (displayDen s) with h | h | h
  · rw [pcmp_lt.mpr h, pcmp_gt.mpr h]
    rfl
  · rw [pcmp_eq.mpr h, pcmp_eq.mpr h.symm]
    show AzPolynomial.compare (displayNum s) (displayNum r)
      = (AzPolynomial.compare (displayNum r) (displayNum s)).swap
    rcases lt_trichotomy (displayNum r) (displayNum s) with h2 | h2 | h2
    · rw [pcmp_lt.mpr h2, pcmp_gt.mpr h2]
      rfl
    · rw [pcmp_eq.mpr h2, pcmp_eq.mpr h2.symm]
      rfl
    · rw [pcmp_gt.mpr h2, pcmp_lt.mpr h2]
      rfl
  · rw [pcmp_gt.mpr h, pcmp_lt.mpr h]
    rfl

private theorem eq_of_compare_eq' {r s : AzRationalFunction}
    (h : compare r s = .eq) : r = s := by
  rw [compare] at h
  rcases hdd : AzPolynomial.compare (displayDen r) (displayDen s) with _ | _ | _ <;>
    rw [hdd] at h
  · simp at h
  · have h2 : AzPolynomial.compare (displayNum r) (displayNum s) = .eq := h
    exact eq_of_display_eq (pcmp_eq.mp h2) (pcmp_eq.mp hdd)
  · simp at h

private theorem compare_trans' {r s t : AzRationalFunction}
    (h1 : compare r s ≠ .gt) (h2 : compare s t ≠ .gt) : compare r t ≠ .gt := by
  rw [compare] at h1 h2 ⊢
  rcases lt_trichotomy (displayDen r) (displayDen s) with hab | hab | hab <;>
    rcases lt_trichotomy (displayDen s) (displayDen t) with hbc | hbc | hbc
  · rw [pcmp_lt.mpr (hab.trans hbc)]
    simp
  · rw [pcmp_lt.mpr (hbc ▸ hab)]
    simp
  · rw [pcmp_gt.mpr hbc] at h2
    exact absurd rfl h2
  · rw [pcmp_lt.mpr (by rw [hab]; exact hbc)]
    simp
  · -- equal display denominators throughout: numerators compose
    rw [pcmp_eq.mpr (hab.trans hbc)]
    rw [pcmp_eq.mpr hab] at h1
    rw [pcmp_eq.mpr hbc] at h2
    have h1' : AzPolynomial.compare (displayNum r) (displayNum s) ≠ .gt := h1
    have h2' : AzPolynomial.compare (displayNum s) (displayNum t) ≠ .gt := h2
    show AzPolynomial.compare (displayNum r) (displayNum t) ≠ .gt
    rw [Ne, pcmp_gt] at h1' h2' ⊢
    exact fun hlt => absurd hlt (not_lt.mpr ((not_lt.mp h1').trans (not_lt.mp h2')))
  · rw [pcmp_gt.mpr hbc] at h2
    exact absurd rfl h2
  · rw [pcmp_gt.mpr hab] at h1
    exact absurd rfl h1
  · rw [pcmp_gt.mpr hab] at h1
    exact absurd rfl h1
  · rw [pcmp_gt.mpr hab] at h1
    exact absurd rfl h1

/-! ### The `LinearOrder` instance -/

instance : LinearOrder AzRationalFunction where
  le_refl r := by
    show compare r r ≠ .gt
    rw [compare_self']
    simp
  le_trans _ _ _ := compare_trans'
  le_antisymm r s h1 h2 := by
    have h2' : (compare r s).swap ≠ .gt := by
      rw [← compare_swap']
      exact h2
    apply eq_of_compare_eq'
    rcases h : compare r s with _ | _ | _
    · rw [h] at h2'
      exact absurd rfl h2'
    · rfl
    · exact absurd h h1
  le_total r s := by
    show compare r s ≠ .gt ∨ compare s r ≠ .gt
    rw [compare_swap' r s]
    rcases compare r s with _ | _ | _ <;> simp
  lt_iff_le_not_ge r s := by
    show compare r s = .lt ↔ compare r s ≠ .gt ∧ ¬ compare s r ≠ .gt
    rw [compare_swap' r s]
    rcases compare r s with _ | _ | _ <;> simp
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  min_def := fun _ _ => rfl
  max_def := fun _ _ => rfl
  compare := compare
  compare_eq_compareOfLessAndEq r s := by
    rw [compareOfLessAndEq]
    rcases h : compare r s with _ | _ | _
    · rw [ite_eq_left (show r < s from h)]
    · rw [ite_eq_right (show ¬ r < s from fun h2 => by
          rw [show compare r s = .lt from h2] at h
          exact absurd h (by simp)),
        ite_eq_left (eq_of_compare_eq' h)]
    · rw [ite_eq_right (show ¬ r < s from fun h2 => by
          rw [show compare r s = .lt from h2] at h
          exact absurd h (by simp)),
        ite_eq_right (fun h2 => by
          subst h2
          rw [compare_self'] at h
          exact absurd h (by simp))]

/-! ### Coefficient-map bridges (redeclared: the `Equiv/Basic` ones are private) -/

private theorem hιinj : Function.Injective AzInt.toIntRingHom :=
  fun a b h => Azurite.AzInt.ringEquivInt.injective (by simpa using h)

private theorem hκinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective

private theorem toPolyQ_eq' (p : Azurite.AzPolynomial AzInt) :
    toPolyQ p
      = ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).map (Int.castRingHom ℚ) := by
  rw [toPolyQ, Polynomial.map_map]

private theorem toPolyQ_ne_zero' {p : Azurite.AzPolynomial AzInt} (hp : p ≠ 0) :
    toPolyQ p ≠ 0 := by
  rw [toPolyQ, Ne, Polynomial.map_eq_zero_iff
    (fun a b h => Azurite.AzInt.ringEquivInt.injective (by
      have := Int.cast_injective (α := ℚ) h
      simpa using this))]
  exact AzPolynomial.toPoly_ne_zero hp

private theorem intPoly_smul' (c : AzInt) (p : Azurite.AzPolynomial AzInt) :
    (AzPolynomial.toPoly (c • p)).map AzInt.toIntRingHom
      = Polynomial.C c.toInt * (AzPolynomial.toPoly p).map AzInt.toIntRingHom := by
  rw [Azurite.AzPolynomial.toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.map_mul,
    Polynomial.map_C]
  rfl

private theorem toPolyQ_smul' (c : AzInt) (p : Azurite.AzPolynomial AzInt) :
    toPolyQ (c • p) = Polynomial.C ((c.toInt : ℚ)) * toPolyQ p := by
  rw [toPolyQ, toPolyQ, Azurite.AzPolynomial.toPoly_smul, Polynomial.smul_eq_C_mul,
    Polynomial.map_mul, Polynomial.map_C]
  rfl

private theorem lcPos_int' {p : Azurite.AzPolynomial AzInt}
    (h : (0 : AzInt) < p.leadingCoeff) :
    0 < ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).leadingCoeff := by
  have h1 : ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).leadingCoeff
      = p.leadingCoeff.toInt := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective hιinj,
      Polynomial.coeff_map, ← Polynomial.leadingCoeff, leadingCoeff_toPoly]
    rfl
  rw [h1]
  rwa [Azurite.AzInt.lt_iff_toInt_lt, show (0 : AzInt).toInt = 0 from rfl] at h

private theorem isCoprime_C_right' {c : ℚ} (hc : c ≠ 0) (p : ℚ[X]) :
    IsCoprime p (Polynomial.C c) :=
  ⟨0, Polynomial.C c⁻¹, by
    rw [zero_mul, zero_add, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]⟩

private theorem isCoprime_C_left' {c : ℚ} (hc : c ≠ 0) (p : ℚ[X]) :
    IsCoprime (Polynomial.C c) p :=
  (isCoprime_C_right' hc p).symm

/-! ### The display of `ofPolynomial` -/

private theorem display_ofPolynomial (p : Azurite.AzPolynomial AzInt) :
    displayNum (ofPolynomial p) = p ∧ displayDen (ofPolynomial p) = 1 := by
  by_cases hp : p = 0
  · -- zero: `ofPolynomial 0 = 0`, which displays as `(0, 1)`
    subst hp
    have h0 : ofPolynomial (0 : Azurite.AzPolynomial AzInt) = 0 := by
      show ofNumDen 0 1 = 0
      rw [ofNumDen, ite_eq_left (Or.inl rfl)]
    rw [h0]
    constructor
    · apply toPoly_inj.mp
      rw [show displayNum (0 : AzRationalFunction)
          = (0 : AzInt) • (1 : Azurite.AzPolynomial AzInt) from rfl,
        Azurite.AzPolynomial.toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.C_0,
        zero_mul, toPoly_zero]
    · apply toPoly_inj.mp
      rw [show displayDen (0 : AzRationalFunction)
          = (1 : AzInt) • (1 : Azurite.AzPolynomial AzInt) from rfl,
        Azurite.AzPolynomial.toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.C_1,
        one_mul]
  set r := ofPolynomial p with hr
  -- the represented value is `p`, so the display fraction equals `p / 1`
  have hφdd0 : algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (displayDen r)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (toPolyQ_ne_zero' (displayDen_ne_zero r))
  have hval := toRatFunc_ofNumDen (displayNum r) (displayDen r) (displayDen_ne_zero r)
  rw [ofNumDen_displayNum_displayDen r, hr, toRatFunc_ofPolynomial] at hval
  have hcrossQ : toPolyQ (displayNum r) = toPolyQ p * toPolyQ (displayDen r) := by
    apply RatFunc.algebraMap_injective ℚ
    rw [map_mul]
    exact (div_eq_iff hφdd0).mp hval.symm
  -- the scalar components of the factor are nonzero
  have hfac0 : r.factor ≠ 0 := by
    intro h0
    have h1 : toRatFunc r = 0 := by
      rw [toRatFunc, h0, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [hr, toRatFunc_ofPolynomial] at h1
    exact RatFunc.algebraMap_ne_zero (toPolyQ_ne_zero' hp) h1
  have hfn0 : r.factor.num ≠ 0 := by
    intro h0
    apply hfac0
    have hden1 : r.factor.den = 1 := by
      have hcop := (Azurite.AzNat.coprime_iff _ _).mp r.factor.reduced
      rw [h0] at hcop
      have h1 : r.factor.den.toNat = 1 :=
        (Nat.coprime_zero_left _).mp
          (by rwa [show (0 : AzNat).toNat = 0 from rfl] at hcop)
      exact Azurite.AzNat.toNat_injective (by rw [h1]; rfl)
    have hsign : r.factor.sign = true := r.factor.zero_sign h0
    exact Azurite.AzRat.ext (by rw [hsign]; rfl) (by rw [h0]; rfl) (by rw [hden1]; rfl)
  have hfnN : r.factor.num.toNat ≠ 0 := fun h =>
    hfn0 (Azurite.AzNat.toNat_injective (by rw [h]; rfl))
  have haZ0 : (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt).toInt ≠ 0 := by
    rw [show (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt).toInt
      = if r.factor.sign then (r.factor.num.toNat : ℤ)
        else -(r.factor.num.toNat : ℤ) from rfl]
    split <;> omega
  have hfdN : r.factor.den.toNat ≠ 0 := fun h =>
    r.factor.den_nz (Azurite.AzNat.toNat_injective (by rw [h]; rfl))
  have hbZ : (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt
      = (r.factor.den.toNat : ℤ) := rfl
  have hbZ0 : (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt ≠ 0 := by
    rw [hbZ]
    omega
  -- the display pair is coprime over `ℚ[X]` (unit scalars on a reduced pair)
  have hcop_display : IsCoprime (toPolyQ (displayNum r)) (toPolyQ (displayDen r)) := by
    rw [displayNum, displayDen, toPolyQ_smul', toPolyQ_smul']
    have hcopr : IsCoprime (toPolyQ r.num) (toPolyQ r.den) :=
      (Azurite.AzPolynomial.coprime_int_iff r.num r.den).mp r.reduced
    have haQ0 : ((⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt).toInt : ℚ)
        ≠ 0 := by exact_mod_cast haZ0
    have hbQ0 : ((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt : ℚ) ≠ 0 := by
      exact_mod_cast hbZ0
    exact (isCoprime_C_left' haQ0 _).mul_left
      ((isCoprime_C_right' hbQ0 _).mul_right hcopr)
  -- the display denominator divides the display numerator, so it is a unit
  have hdd_unit : IsUnit (toPolyQ (displayDen r)) :=
    hcop_display.isUnit_of_dvd' ⟨toPolyQ p, by rw [hcrossQ]; ring⟩ dvd_rfl
  have hdenQ_unit : IsUnit (toPolyQ r.den) := by
    rw [displayDen, toPolyQ_smul'] at hdd_unit
    exact isUnit_of_mul_isUnit_right hdd_unit
  -- a primitive positive constant unit is `1`
  have hden1 : r.den = 1 := by
    have hdeg : ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom).natDegree = 0 := by
      have hu := Polynomial.natDegree_eq_zero_of_isUnit hdenQ_unit
      rw [toPolyQ_eq'] at hu
      rwa [Polynomial.natDegree_map_eq_of_injective hκinj] at hu
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hcoeff_pos : 0 < ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom).coeff 0 := by
      have h1 := lcPos_int' r.den_lc_pos
      rwa [Polynomial.leadingCoeff, hdeg] at h1
    have hcont1 : ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom).content = 1 := by
      rw [Azurite.AzPolynomial.content_toPoly, r.den_content]
      rfl
    rw [hC, Polynomial.content_C, ← Int.abs_eq_normalize] at hcont1
    have hc1 : ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom).coeff 0 = 1 := by
      rcases abs_cases (((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom).coeff 0) with
        ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    apply toPoly_inj.mp
    apply Polynomial.map_injective _ hιinj
    rw [toPoly_one, Polynomial.map_one, hC, hc1, Polynomial.C_1]
  -- the display denominator is the constant `factor.den`
  have hddZC : (AzPolynomial.toPoly (displayDen r)).map AzInt.toIntRingHom
      = Polynomial.C (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt := by
    rw [displayDen, intPoly_smul', hden1, toPoly_one, Polynomial.map_one, mul_one]
  -- the cross identity in `ℤ[X]`
  have hcrossZ : (AzPolynomial.toPoly (displayNum r)).map AzInt.toIntRingHom
      = (AzPolynomial.toPoly p).map AzInt.toIntRingHom
        * (AzPolynomial.toPoly (displayDen r)).map AzInt.toIntRingHom := by
    apply Polynomial.map_injective _ hκinj
    rw [Polynomial.map_mul, ← toPolyQ_eq', ← toPolyQ_eq', ← toPolyQ_eq']
    exact hcrossQ
  -- content bookkeeping pins `factor.den = 1`
  have haabs : |(⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt).toInt|
      = (r.factor.num.toNat : ℤ) := by
    rw [show (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt).toInt
      = if r.factor.sign then (r.factor.num.toNat : ℤ)
        else -(r.factor.num.toNat : ℤ) from rfl]
    split
    · exact abs_of_nonneg (Int.natCast_nonneg _)
    · rw [abs_neg]
      exact abs_of_nonneg (Int.natCast_nonneg _)
  have hbabs : |(⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt|
      = (r.factor.den.toNat : ℤ) := by
    rw [hbZ]
    exact abs_of_nonneg (Int.natCast_nonneg _)
  have hnumcont : ((AzPolynomial.toPoly r.num).map AzInt.toIntRingHom).content = 1 := by
    rw [Azurite.AzPolynomial.content_toPoly, r.num_content]
    rfl
  have hdnZ : (AzPolynomial.toPoly (displayNum r)).map AzInt.toIntRingHom
      = Polynomial.C (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt).toInt
        * (AzPolynomial.toPoly r.num).map AzInt.toIntRingHom := by
    rw [displayNum, intPoly_smul']
  have hcontEq : (r.factor.num.toNat : ℤ)
      = (p.content.toNat : ℤ) * (r.factor.den.toNat : ℤ) := by
    have h1 := congrArg Polynomial.content hcrossZ
    rw [hdnZ, hddZC, Polynomial.content_C_mul, Polynomial.content_mul,
      Polynomial.content_C, hnumcont, mul_one, ← Int.abs_eq_normalize,
      ← Int.abs_eq_normalize, haabs, hbabs,
      Azurite.AzPolynomial.content_toPoly] at h1
    exact h1
  have hfd1 : r.factor.den.toNat = 1 := by
    have h2 : r.factor.num.toNat = p.content.toNat * r.factor.den.toNat := by
      exact_mod_cast hcontEq
    have hco : Nat.Coprime r.factor.num.toNat r.factor.den.toNat :=
      (Azurite.AzNat.coprime_iff _ _).mp r.factor.reduced
    exact hco.symm.eq_one_of_dvd ⟨p.content.toNat, by rw [h2, Nat.mul_comm]⟩
  have hbZ1 : (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt = 1 := by
    rw [hbZ, hfd1]
    rfl
  -- conclude
  constructor
  · apply toPoly_inj.mp
    apply Polynomial.map_injective _ hιinj
    rw [hcrossZ, hddZC, hbZ1, Polynomial.C_1, mul_one]
  · apply toPoly_inj.mp
    apply Polynomial.map_injective _ hιinj
    rw [hddZC, hbZ1, Polynomial.C_1, toPoly_one, Polynomial.map_one]

/-- A polynomial displays with itself as the numerator. -/
theorem displayNum_ofPolynomial (p : Azurite.AzPolynomial AzInt) :
    displayNum (ofPolynomial p) = p :=
  (display_ofPolynomial p).1

/-- A polynomial displays with denominator `1`. -/
theorem displayDen_ofPolynomial (p : Azurite.AzPolynomial AzInt) :
    displayDen (ofPolynomial p) = 1 :=
  (display_ofPolynomial p).2

/-! ### The canonical map preserves order -/

/-- `ofPolynomial` reflects and preserves the strict order. -/
theorem ofPolynomial_lt_iff {p q : Azurite.AzPolynomial AzInt} :
    ofPolynomial p < ofPolynomial q ↔ p < q := by
  show compare (ofPolynomial p) (ofPolynomial q) = .lt ↔ p < q
  rw [compare, displayDen_ofPolynomial, displayDen_ofPolynomial, pcmp_eq.mpr rfl]
  show AzPolynomial.compare (displayNum (ofPolynomial p))
    (displayNum (ofPolynomial q)) = .lt ↔ p < q
  rw [displayNum_ofPolynomial, displayNum_ofPolynomial]
  exact pcmp_lt

/-- **The canonical map preserves order.** -/
theorem ofPolynomial_strictMono : StrictMono ofPolynomial :=
  fun _ _ h => ofPolynomial_lt_iff.mpr h

end Azurite.AzRationalFunction

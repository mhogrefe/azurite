/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.ComposedOps
import Azurite.AzPolynomial.Equiv.Translate
import Azurite.AzPolynomial.Equiv.NegateRoots
import Azurite.AzPolynomial.Equiv.ScaleRoots
import Azurite.AzPolynomial.Equiv.InvertRoots
import Azurite.AzPolynomial.Equiv.CauchyIndexSubresMap
import Azurite.AzPolynomial.Equiv.Resultant
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Correctness of the composed sum and composed product

`composedSum P Q` is the resultant `Res_y(P(y), Q(x − y))` and
`composedProduct P Q` the resultant `Res_y(P(y), y^m · Q(x/y))`, both over the
coefficient ring `R[x]`. This file proves their root properties over an
algebraically closed field: for `f : R →+* K` with `K` algebraically closed
(e.g. `ℤ →+* ℂ`),

  `z` is a root of `map f (toPoly (composedSum P Q))` **iff**
  `z = a + b` for roots `a` of `map f (toPoly P)` and `b` of `map f (toPoly Q)`

(`isRoot_composedSum_map_iff`), assuming only that `f` does not kill the two
leading coefficients; and

  `z` is a root of `map f (toPoly (composedProduct P Q))` **iff**
  `z = a · b` for a root `a` of `map f (toPoly P)` and a **nonzero** root `b`
  of `map f (toPoly Q)`

(`isRoot_composedProduct_map_iff`), additionally assuming `f` does not kill the
trailing coefficient of `Q` — the leading `y`-coefficient of `y^m · Q(x/y)`.
The `b ≠ 0` restriction reflects the design: roots of `Q` at `0` are dropped by
the inversion. Both statements cover `z = 0`.

The fused companions are proved under the same hypotheses as the sum (no
trailing-coefficient condition): `isRoot_composedDifference_map_iff`
(`z = a − b`) and `isRoot_composedQuotient_map_iff` (`a = z · b`, the
fraction-free form of `z = a / b`; the pair `(0, 0)` witnesses every `z`,
matching the identically-zero resultant in the indeterminate `0 / 0` case).

The proofs push the evaluation-at-`z` ring homomorphism
`evalMapHom f z : AzPolynomial R →+* K` through the resultant:

* the computable resultant is Mathlib's (`resultant_eq` + `Res_eq_resultant`);
* Mathlib's `resultant_map_map` commutes unconditionally with ring
  homomorphisms because the matrix degrees are pinned;
* the bivariate arguments collapse under `evalMapHom` to `p := map f (toPoly P)`
  paired with `q.comp (C z − X)` (sum) or `(q.reverse).scaleRoots z` (product)
  via the structural specs of the root-manipulation toolkit
  (`map_evalMapHom_toPoly_map_CRingHom`, `map_evalMapHom_toPoly_prodArg`,
  `evalMapHom_X`);
* the pinned degrees equal the true ones because the leading `y`-coefficients
  of the bivariate arguments are constants in `x` (`aₚ`, `±b_m`, and the
  trailing coefficient of `Q` respectively);
* finally the core lemmas `resultant_comp_sub_eq_zero_iff` and
  `resultant_scaleRoots_reverse_eq_zero_iff` — built on Mathlib's
  `resultant_eq_zero_iff` and `isCoprime_iff_aeval_ne_zero_of_isAlgClosed` —
  characterize the vanishing as `z = a + b` (resp. `z = a · b`, `b ≠ 0`).
-/

set_option autoImplicit false

open Polynomial

/-- Over the self-algebra, `aeval` is `eval`. -/
theorem Polynomial.aeval_self_eq_eval {K : Type _} [Field K] (p : K[X]) (a : K) :
    aeval a p = eval a p := by
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- Over an algebraically closed field, the resultant of two polynomials, the
first nonzero, vanishes iff they have a common root. -/
theorem Polynomial.resultant_eq_zero_iff_common_root {K : Type _} [Field K] [IsAlgClosed K]
    {p q : K[X]} (hp : p ≠ 0) :
    Polynomial.resultant p q = 0 ↔ ∃ a : K, p.IsRoot a ∧ q.IsRoot a := by
  rw [Polynomial.resultant_eq_zero_iff,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K]
  simp only [not_forall, not_or, not_not, Polynomial.aeval_self_eq_eval]
  constructor
  · rintro ⟨-, a, ha1, ha2⟩
    exact ⟨a, ha1, ha2⟩
  · rintro ⟨a, ha1, ha2⟩
    exact ⟨Or.inl hp, a, ha1, ha2⟩

/-- **Composed-sum core.** Over an algebraically closed field, the resultant of
`p` and `q(z − x)` vanishes iff `z = a + b` for roots `a` of `p` and `b` of `q`. -/
theorem Polynomial.resultant_comp_sub_eq_zero_iff {K : Type _} [Field K] [IsAlgClosed K]
    {p q : K[X]} (hp : p ≠ 0) (z : K) :
    Polynomial.resultant p (q.comp (Polynomial.C z - Polynomial.X)) = 0 ↔
    ∃ a b : K, p.IsRoot a ∧ q.IsRoot b ∧ z = a + b := by
  rw [Polynomial.resultant_eq_zero_iff_common_root hp]
  constructor
  · rintro ⟨a, hpa, hqa⟩
    refine ⟨a, z - a, hpa, ?_, by ring⟩
    rwa [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X] at hqa
  · rintro ⟨a, b, hpa, hqb, rfl⟩
    refine ⟨a, hpa, ?_⟩
    rw [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X, add_sub_cancel_left]
    exact hqb

/-- **Composed-difference core.** Over an algebraically closed field, the
resultant of `p` and `q(x − z)` vanishes iff `z = a − b` for roots `a` of `p`
and `b` of `q`. -/
theorem Polynomial.resultant_comp_X_sub_C_eq_zero_iff {K : Type _} [Field K] [IsAlgClosed K]
    {p q : K[X]} (hp : p ≠ 0) (z : K) :
    Polynomial.resultant p (q.comp (Polynomial.X - Polynomial.C z)) = 0 ↔
    ∃ a b : K, p.IsRoot a ∧ q.IsRoot b ∧ z = a - b := by
  rw [Polynomial.resultant_eq_zero_iff_common_root hp]
  constructor
  · rintro ⟨a, hpa, hqa⟩
    refine ⟨a, a - z, hpa, ?_, by ring⟩
    rwa [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hqa
  · rintro ⟨a, b, hpa, hqb, rfl⟩
    refine ⟨a, hpa, ?_⟩
    rw [Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_sub_cancel]
    exact hqb

/-! ### Root-level lemmas for the composed product and quotient -/

/-- For `z ≠ 0`, `z` is a root of `q.reverse` iff `z⁻¹` is a root of `q`. -/
theorem Polynomial.isRoot_reverse_iff {K : Type _} [Field K] {q : K[X]} {z : K} (hz : z ≠ 0) :
    (q.reverse).IsRoot z ↔ q.IsRoot z⁻¹ := by
  have : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have hkey := Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id K) z⁻¹ q
  rw [invOf_eq_inv, inv_inv] at hkey
  exact hkey

/-- The constant term of the reversal is the leading coefficient. -/
theorem Polynomial.reverse_coeff_zero {K : Type _} [Semiring K] (q : K[X]) :
    (q.reverse).coeff 0 = q.leadingCoeff := by
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
  rfl

/-- Over an algebraically closed field, a nonzero polynomial has a nonzero root
iff its trailing degree is less than its degree. -/
theorem Polynomial.exists_ne_zero_isRoot_iff {K : Type _} [Field K] [IsAlgClosed K]
    {q : K[X]} (hq : q ≠ 0) :
    (∃ b : K, b ≠ 0 ∧ q.IsRoot b) ↔ q.natTrailingDegree < q.natDegree := by
  constructor
  · rintro ⟨b, hb, hqb⟩
    have hrev : (q.reverse).IsRoot b⁻¹ := by
      rw [Polynomial.isRoot_reverse_iff (inv_ne_zero hb), inv_inv]; exact hqb
    by_contra hle
    have hdeg0 : (q.reverse).natDegree = 0 := by
      rw [Polynomial.reverse_natDegree]; omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, Polynomial.IsRoot, Polynomial.eval_C] at hrev
    rw [Polynomial.reverse_coeff_zero, Polynomial.leadingCoeff_eq_zero] at hrev
    exact hq hrev
  · intro hlt
    have hdeg : (q.reverse).degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree (by
        rw [Ne, Polynomial.reverse_eq_zero]; exact hq), Polynomial.reverse_natDegree]
      exact_mod_cast by omega
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_root _ hdeg
    have hw' : (q.reverse).IsRoot w := hw
    have hwne : w ≠ 0 := by
      intro h
      rw [h, Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.reverse_coeff_zero, Polynomial.leadingCoeff_eq_zero] at hw'
      exact hq hw'
    refine ⟨w⁻¹, inv_ne_zero hwne, ?_⟩
    rwa [← Polynomial.isRoot_reverse_iff hwne]

/-- **Root set of `q.scaleRoots z`.** Its roots are exactly `z · b` for `b` a
root of `q` — including `z = 0`. This is the evaluated bivariate argument
`x^m · Q(y/x)` of the composed quotient at `x = z`. -/
theorem Polynomial.isRoot_scaleRoots_iff {K : Type _} [Field K] [IsAlgClosed K]
    {q : K[X]} (hq : q ≠ 0) (z a : K) :
    (q.scaleRoots z).IsRoot a ↔ ∃ b : K, q.IsRoot b ∧ a = z * b := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [Polynomial.IsRoot, Polynomial.scaleRoots_zero, Polynomial.smul_eq_C_mul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      mul_eq_zero, or_iff_right (Polynomial.leadingCoeff_ne_zero.mpr hq), pow_eq_zero_iff']
    constructor
    · rintro ⟨rfl, hd⟩
      obtain ⟨b, hb⟩ := IsAlgClosed.exists_root q (by
        rw [Polynomial.degree_eq_natDegree hq]
        exact_mod_cast by omega)
      exact ⟨b, hb, by rw [zero_mul]⟩
    · rintro ⟨b, hqb, ha⟩
      rw [zero_mul] at ha
      refine ⟨ha, ?_⟩
      intro hd0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd0, Polynomial.IsRoot, Polynomial.eval_C] at hqb
      exact hq (by rw [Polynomial.eq_C_of_natDegree_eq_zero hd0, hqb, Polynomial.C_0])
  · have hkey := Polynomial.scaleRoots_eval₂_mul (p := q) (RingHom.id K) (z⁻¹ * a) z
    rw [show (RingHom.id K) z * (z⁻¹ * a) = a by
      simp [← mul_assoc, mul_inv_cancel₀ hz]] at hkey
    constructor
    · intro h
      rw [Polynomial.IsRoot, show Polynomial.eval a (q.scaleRoots z)
          = Polynomial.eval₂ (RingHom.id K) a (q.scaleRoots z) from rfl, hkey] at h
      have h2 : Polynomial.eval₂ (RingHom.id K) (z⁻¹ * a) q = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (pow_ne_zero _ (by simpa using hz))
        · exact h'
      exact ⟨z⁻¹ * a, h2, by field_simp⟩
    · rintro ⟨b, hqb, rfl⟩
      rw [Polynomial.IsRoot, show Polynomial.eval (z * b) (q.scaleRoots z)
          = Polynomial.eval₂ (RingHom.id K) (z * b) (q.scaleRoots z) from rfl, hkey,
        show z⁻¹ * (z * b) = b by field_simp,
        show Polynomial.eval₂ (RingHom.id K) b q = Polynomial.eval b q from rfl, hqb, mul_zero]

/-- **Composed-quotient core.** Over an algebraically closed field, the
resultant of `p` and `q.scaleRoots z` vanishes iff `a = z · b` for roots `a`
of `p` and `b` of `q` (fraction-free form of `z = a / b`). -/
theorem Polynomial.resultant_scaleRoots_eq_zero_iff {K : Type _} [Field K] [IsAlgClosed K]
    {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (z : K) :
    Polynomial.resultant p (q.scaleRoots z) = 0 ↔
    ∃ a b : K, p.IsRoot a ∧ q.IsRoot b ∧ a = z * b := by
  rw [Polynomial.resultant_eq_zero_iff_common_root hp]
  constructor
  · rintro ⟨a, hpa, ha2⟩
    obtain ⟨b, hqb, hab⟩ := (Polynomial.isRoot_scaleRoots_iff hq z a).mp ha2
    exact ⟨a, b, hpa, hqb, hab⟩
  · rintro ⟨a, b, hpa, hqb, hab⟩
    exact ⟨a, hpa, (Polynomial.isRoot_scaleRoots_iff hq z a).mpr ⟨b, hqb, hab⟩⟩

/-- **Root set of `(q.reverse).scaleRoots z`.** Its roots `a` are exactly those
with `z = a · b` for some nonzero root `b` of `q` — including `z = 0` and
`a = 0`. This is the evaluated bivariate argument `y^m · Q(x/y)` of the
composed product at `x = z`. -/
theorem Polynomial.isRoot_scaleRoots_reverse_iff {K : Type _} [Field K] [IsAlgClosed K]
    {q : K[X]} (hq : q ≠ 0) (z a : K) :
    ((q.reverse).scaleRoots z).IsRoot a ↔ ∃ b : K, q.IsRoot b ∧ b ≠ 0 ∧ z = a * b := by
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have htd := Polynomial.natTrailingDegree_le_natDegree q
  rcases eq_or_ne z 0 with rfl | hz
  · -- `z = 0`: only the leading term of the reversal survives the scaling
    rw [Polynomial.IsRoot, Polynomial.scaleRoots_zero, Polynomial.smul_eq_C_mul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      mul_eq_zero, or_iff_right (by
        rw [Polynomial.reverse_leadingCoeff]
        exact fun h => hq (Polynomial.trailingCoeff_eq_zero.mp h)),
      pow_eq_zero_iff', Polynomial.reverse_natDegree]
    constructor
    · rintro ⟨rfl, hd⟩
      obtain ⟨b, hb, hqb⟩ := (show ∃ b : K, b ≠ 0 ∧ q.IsRoot b from by
        rw [Polynomial.exists_ne_zero_isRoot_iff hq]; omega)
      exact ⟨b, hqb, hb, by rw [zero_mul]⟩
    · rintro ⟨b, hqb, hb, hzab⟩
      have ha : a = 0 := by
        rcases mul_eq_zero.mp hzab.symm with h | h
        · exact h
        · exact absurd h hb
      subst ha
      refine ⟨rfl, ?_⟩
      have : q.natTrailingDegree < q.natDegree := by
        rw [← Polynomial.exists_ne_zero_isRoot_iff hq]; exact ⟨b, hb, hqb⟩
      omega
  · rcases eq_or_ne a 0 with rfl | ha
    · -- `a = 0` is never a root when `z ≠ 0`: the constant term is `lc(q) · z^d`
      constructor
      · intro h
        exfalso
        rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero,
          Polynomial.coeff_scaleRoots, Nat.sub_zero, Polynomial.reverse_coeff_zero] at h
        exact mul_ne_zero hlc (pow_ne_zero _ hz) h
      · rintro ⟨b, -, -, hzab⟩
        rw [zero_mul] at hzab
        exact absurd hzab hz
    · -- `z, a ≠ 0`: scale the evaluation point and invert through the reversal
      have hkey := Polynomial.scaleRoots_eval₂_mul (p := q.reverse) (RingHom.id K) (z⁻¹ * a) z
      rw [show (RingHom.id K) z * (z⁻¹ * a) = a by
        simp [← mul_assoc, mul_inv_cancel₀ hz]] at hkey
      have hia : z⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero hz) ha
      constructor
      · intro h
        rw [Polynomial.IsRoot] at h
        rw [show Polynomial.eval a ((q.reverse).scaleRoots z)
            = Polynomial.eval₂ (RingHom.id K) a ((q.reverse).scaleRoots z) from rfl, hkey] at h
        have h2 : Polynomial.eval₂ (RingHom.id K) (z⁻¹ * a) q.reverse = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' (pow_ne_zero _ (by simpa using hz))
          · exact h'
        have h3 : (q.reverse).IsRoot (z⁻¹ * a) := h2
        rw [Polynomial.isRoot_reverse_iff hia] at h3
        refine ⟨(z⁻¹ * a)⁻¹, h3, inv_ne_zero hia, ?_⟩
        field_simp
      · rintro ⟨b, hqb, hb, hzab⟩
        have hab : z⁻¹ * a = b⁻¹ := by
          rw [hzab]
          field_simp [mul_comm]
        rw [Polynomial.IsRoot,
          show Polynomial.eval a ((q.reverse).scaleRoots z)
            = Polynomial.eval₂ (RingHom.id K) a ((q.reverse).scaleRoots z) from rfl, hkey, hab]
        have h3 : (q.reverse).IsRoot b⁻¹ := by
          rw [Polynomial.isRoot_reverse_iff (inv_ne_zero hb), inv_inv]
          exact hqb
        rw [show Polynomial.eval₂ (RingHom.id K) b⁻¹ q.reverse
            = Polynomial.eval b⁻¹ q.reverse from rfl, h3, mul_zero]

/-- **Composed-product core.** Over an algebraically closed field, the
resultant of `p` and `(q.reverse).scaleRoots z` vanishes iff `z = a · b` for a
root `a` of `p` and a nonzero root `b` of `q`. -/
theorem Polynomial.resultant_scaleRoots_reverse_eq_zero_iff {K : Type _} [Field K]
    [IsAlgClosed K] {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (z : K) :
    Polynomial.resultant p ((q.reverse).scaleRoots z) = 0 ↔
    ∃ a b : K, p.IsRoot a ∧ q.IsRoot b ∧ b ≠ 0 ∧ z = a * b := by
  rw [Polynomial.resultant_eq_zero_iff_common_root hp]
  constructor
  · rintro ⟨a, hpa, ha2⟩
    obtain ⟨b, hqb, hb, hzab⟩ := (Polynomial.isRoot_scaleRoots_reverse_iff hq z a).mp ha2
    exact ⟨a, b, hpa, hqb, hb, hzab⟩
  · rintro ⟨a, b, hpa, hqb, hb, hzab⟩
    exact ⟨a, hpa, (Polynomial.isRoot_scaleRoots_reverse_iff hq z a).mpr ⟨b, hqb, hb, hzab⟩⟩

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- `CRingHom` is injective. -/
theorem CRingHom_injective : Function.Injective (CRingHom : R →+* AzPolynomial R) := by
  intro a b h
  have h2 := congrArg AzPolynomial.toPoly h
  rw [CRingHom_apply, CRingHom_apply, toPoly_C, toPoly_C] at h2
  exact Polynomial.C_injective h2

variable {K : Type _} [Field K] [DecidableEq K]

/-- Map the coefficients by `f` and evaluate at `z`, as a ring homomorphism
`AzPolynomial R →+* K`. Pushing this through a resultant over `R[x]` evaluates
the composed operations at a point. -/
noncomputable def evalMapHom (f : R →+* K) (z : K) : AzPolynomial R →+* K :=
  (Polynomial.evalRingHom z).comp ((Polynomial.mapRingHom f).comp toPolyHom)

omit [DecidableEq K] in
@[simp] theorem evalMapHom_apply (f : R →+* K) (z : K) (W : AzPolynomial R) :
    evalMapHom f z W = Polynomial.eval z (Polynomial.map f (AzPolynomial.toPoly W)) := rfl

omit [DecidableEq K] in
/-- Collapse: mapping the bivariate lift `W.map CRingHom` by `evalMapHom`
recovers `map f (toPoly W)` — the coefficients are constants in `x`, unaffected
by the evaluation. -/
theorem map_evalMapHom_toPoly_map_CRingHom (f : R →+* K) (z : K) (W : AzPolynomial R) :
    Polynomial.map (evalMapHom f z) (AzPolynomial.toPoly (W.map CRingHom))
      = Polynomial.map f (AzPolynomial.toPoly W) := by
  ext n
  rw [Polynomial.coeff_map, AzPolynomial.coeff_toPoly, coeff_map', CRingHom_apply,
    evalMapHom_apply, toPoly_C, Polynomial.map_C, Polynomial.eval_C,
    Polynomial.coeff_map, AzPolynomial.coeff_toPoly]

omit [DecidableEq K] in
/-- `evalMapHom` sends the inner variable `X` to the evaluation point. -/
@[simp] theorem evalMapHom_X (f : R →+* K) (z : K) : evalMapHom f z (X : AzPolynomial R) = z := by
  rw [evalMapHom_apply, toPoly_X, Polynomial.map_X, Polynomial.eval_X]

omit [DecidableEq K] in
/-- Collapsing the bivariate sum argument: `evalMapHom` turns
`Q(x − y) = (negateRoots (Q.map CRingHom)).translate X` into `q.comp (C z − X)`
for `q = map f (toPoly Q)`. -/
theorem map_evalMapHom_toPoly_sumArg (f : R →+* K) (z : K) (Q : AzPolynomial R) :
    Polynomial.map (evalMapHom f z)
      (AzPolynomial.toPoly ((negateRoots (Q.map CRingHom)).translate X))
      = (Polynomial.map f (AzPolynomial.toPoly Q)).comp (Polynomial.C z - Polynomial.X) := by
  rw [toPoly_translate, toPoly_negateRoots, Polynomial.map_comp, Polynomial.map_comp,
    map_evalMapHom_toPoly_map_CRingHom, Polynomial.map_neg, Polynomial.map_X,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, evalMapHom_X,
    Polynomial.comp_assoc, Polynomial.neg_comp, Polynomial.X_comp, neg_sub]

/-- `CRingHom` does not kill nonzero elements. -/
theorem CRingHom_ne_zero {c : R} (hc : c ≠ 0) : (CRingHom : R →+* AzPolynomial R) c ≠ 0 :=
  fun h => hc (CRingHom_injective (by rw [h, map_zero]))

omit [DecidableEq K] in
/-- Collapsing the reversal of the bivariate lift: `evalMapHom` turns
`(toPoly (Q.map CRingHom)).reverse` into `(map f (toPoly Q)).reverse`. -/
theorem map_evalMapHom_reverse (f : R →+* K) (z : K) (Q : AzPolynomial R)
    (hfQ : f Q.leadingCoeff ≠ 0) :
    Polynomial.map (evalMapHom f z) ((AzPolynomial.toPoly (Q.map CRingHom)).reverse)
      = (Polynomial.map f (AzPolynomial.toPoly Q)).reverse := by
  have hd : (AzPolynomial.toPoly (Q.map (CRingHom : R →+* AzPolynomial R))).natDegree
      = Q.natDegree := by
    rw [AzPolynomial.natDegree_toPoly]
    exact natDegree_map_of_injective CRingHom CRingHom_injective Q
  have hd' : (Polynomial.map f (AzPolynomial.toPoly Q)).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  have hcoeff : ∀ j, (evalMapHom f z) ((AzPolynomial.toPoly (Q.map CRingHom)).coeff j)
      = f ((AzPolynomial.toPoly Q).coeff j) := fun j => by
    rw [AzPolynomial.coeff_toPoly, coeff_map', CRingHom_apply, evalMapHom_apply, toPoly_C,
      Polynomial.map_C, Polynomial.eval_C, AzPolynomial.coeff_toPoly]
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.coeff_reverse, hd, hd',
    hcoeff, Polynomial.coeff_map]

/-- The bivariate lift preserves the trailing degree. -/
theorem natTrailingDegree_toPoly_map_CRingHom (Q : AzPolynomial R) (hQ : Q ≠ 0) :
    (AzPolynomial.toPoly (Q.map (CRingHom : R →+* AzPolynomial R))).natTrailingDegree
      = (AzPolynomial.toPoly Q).natTrailingDegree := by
  have hcoeff : ∀ j, (AzPolynomial.toPoly (Q.map CRingHom)).coeff j
      = (CRingHom : R →+* AzPolynomial R) ((AzPolynomial.toPoly Q).coeff j) := fun j => by
    rw [AzPolynomial.coeff_toPoly, coeff_map', AzPolynomial.coeff_toPoly]
  have hQt : AzPolynomial.toPoly Q ≠ 0 :=
    fun h => hQ (toPoly_inj.mp (by rw [h, toPoly_zero]))
  have hQYne : AzPolynomial.toPoly (Q.map (CRingHom : R →+* AzPolynomial R)) ≠ 0 := by
    intro h
    exact hQ ((map_eq_zero_iff_of_injective CRingHom CRingHom_injective Q).mp
      (toPoly_inj.mp (h.trans toPoly_zero.symm)))
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rw [hcoeff]
    exact CRingHom_ne_zero (by
      rw [← Polynomial.trailingCoeff]
      exact fun h => hQt (Polynomial.trailingCoeff_eq_zero.mp h))
  · exact Polynomial.le_natTrailingDegree hQYne (fun m hm => by
      rw [hcoeff, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hm, map_zero])

omit [DecidableEq R] [DecidableEq K] in
/-- Mapping by `f` preserves the trailing degree when `f` does not kill the
trailing coefficient. -/
theorem natTrailingDegree_map_toPoly (f : R →+* K) (Q : AzPolynomial R)
    (hfQt : f ((AzPolynomial.toPoly Q).trailingCoeff) ≠ 0) :
    (Polynomial.map f (AzPolynomial.toPoly Q)).natTrailingDegree
      = (AzPolynomial.toPoly Q).natTrailingDegree := by
  have hne : Polynomial.map f (AzPolynomial.toPoly Q) ≠ 0 := fun h => hfQt (by
    rw [Polynomial.trailingCoeff, ← Polynomial.coeff_map, h, Polynomial.coeff_zero])
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rw [Polynomial.coeff_map]
    exact hfQt
  · exact Polynomial.le_natTrailingDegree hne (fun m hm => by
      rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hm, map_zero])

omit [DecidableEq K] in
/-- **Product collapse.** Mapping the bivariate product argument
`y^m · Q(x/y) = scaleRoots (invertRoots (Q.map CRingHom)) X 1` by `evalMapHom`
gives `(q.reverse).scaleRoots z` for `q = map f (toPoly Q)`. -/
theorem map_evalMapHom_toPoly_prodArg (f : R →+* K) (z : K) (Q : AzPolynomial R)
    (hfQ : f Q.leadingCoeff ≠ 0) (hfQt : f ((AzPolynomial.toPoly Q).trailingCoeff) ≠ 0) :
    Polynomial.map (evalMapHom f z)
      (AzPolynomial.toPoly (scaleRoots (invertRoots (Q.map CRingHom)) X 1))
      = ((Polynomial.map f (AzPolynomial.toPoly Q)).reverse).scaleRoots z := by
  have hQne : Q ≠ 0 := fun h => hfQ (by
    rw [h, show (0 : AzPolynomial R).leadingCoeff = 0 from rfl, map_zero])
  have hfold : Q.coeff ((AzPolynomial.toPoly Q).natTrailingDegree)
      = (AzPolynomial.toPoly Q).trailingCoeff := by
    rw [Polynomial.trailingCoeff, AzPolynomial.coeff_toPoly]
  have hlcrev : (evalMapHom f z)
      (((AzPolynomial.toPoly (Q.map CRingHom)).reverse).leadingCoeff) ≠ 0 := by
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff,
      natTrailingDegree_toPoly_map_CRingHom Q hQne, AzPolynomial.coeff_toPoly, coeff_map',
      CRingHom_apply, evalMapHom_apply, toPoly_C, Polynomial.map_C, Polynomial.eval_C, hfold]
    exact hfQt
  rw [toPoly_scaleRoots, toPoly_invertRoots, Polynomial.C_1, one_mul, Polynomial.comp_X,
    Polynomial.map_scaleRoots _ _ _ hlcrev, evalMapHom_X,
    map_evalMapHom_reverse f z Q hfQ]

variable [IsDomain R] [Azurite.ExactDiv R] [IsAlgClosed K]

omit [DecidableEq K] in
/-- **Correctness of the composed sum.** For `f : R →+* K` into an algebraically
closed field with `f` not killing the leading coefficients of `P` and `Q`,
`z` is a root of `map f (toPoly (composedSum P Q))` iff `z = a + b` for roots
`a` of `map f (toPoly P)` and `b` of `map f (toPoly Q)`.

**Application:** for `R = AzInt` and `f : AzInt →+* ℂ` (injective, so the
leading-coefficient hypotheses are automatic), `composedSum P Q` is a defining
polynomial of `α + β` whenever `P`, `Q` are defining polynomials of `α`, `β`. -/
theorem isRoot_composedSum_map_iff (f : R →+* K) (P Q : AzPolynomial R)
    (hfP : f P.leadingCoeff ≠ 0) (hfQ : f Q.leadingCoeff ≠ 0) (z : K) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (composedSum P Q))) z ↔
    ∃ a b : K, Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly P)) a ∧
      Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly Q)) b ∧ z = a + b := by
  have hPne : P ≠ 0 := fun h => hfP (by
    rw [h, show (0 : AzPolynomial R).leadingCoeff = 0 from rfl, map_zero])
  have hPYne : AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R)) ≠ 0 := by
    intro h
    exact hPne ((map_eq_zero_iff_of_injective CRingHom CRingHom_injective P).mp
      (toPoly_inj.mp (h.trans toPoly_zero.symm)))
  have hmapdegP : (P.map (CRingHom : R →+* AzPolynomial R)).natDegree = P.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective P
  have hmapdegQ : (Q.map (CRingHom : R →+* AzPolynomial R)).natDegree = Q.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective Q
  -- rephrase the root condition through `evalMapHom`
  show Polynomial.eval z (Polynomial.map f (AzPolynomial.toPoly (composedSum P Q))) = 0 ↔ _
  rw [← evalMapHom_apply f z]
  -- the computable resultant is Mathlib's, and homomorphisms push inside
  rw [show composedSum P Q
      = resultant (P.map CRingHom) ((negateRoots (Q.map CRingHom)).translate X) from rfl,
    resultant_eq _ _ hPYne, Azurite.BPR.Chapter4.Res_eq_resultant,
    ← Polynomial.resultant_map_map]
  -- identify the two mapped polynomials
  have hA : (AzPolynomial.toPoly (P.map CRingHom)).map (evalMapHom f z)
      = Polynomial.map f (AzPolynomial.toPoly P) := map_evalMapHom_toPoly_map_CRingHom f z P
  have hB := map_evalMapHom_toPoly_sumArg f z Q
  -- the pinned matrix degrees
  have hdegA : (AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R))).natDegree
      = P.natDegree := by
    rw [AzPolynomial.natDegree_toPoly, hmapdegP]
  have hdegB : (AzPolynomial.toPoly
      ((negateRoots (Q.map (CRingHom : R →+* AzPolynomial R))).translate X)).natDegree
      = Q.natDegree := by
    rw [AzPolynomial.natDegree_toPoly, natDegree_translate, natDegree_negateRoots, hmapdegQ]
  rw [hA, hB, hdegA, hdegB]
  -- the pinned degrees are the true degrees of the mapped polynomials
  have hdegp : (Polynomial.map f (AzPolynomial.toPoly P)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  have hdegq : (Polynomial.map f (AzPolynomial.toPoly Q)).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  have hdegqz : ((Polynomial.map f (AzPolynomial.toPoly Q)).comp
      (Polynomial.C z - Polynomial.X)).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_comp,
      show (Polynomial.C z - Polynomial.X : K[X]).natDegree = 1 from by
        rw [show (Polynomial.C z - Polynomial.X : K[X])
            = -(Polynomial.X - Polynomial.C z) by ring, natDegree_neg, natDegree_X_sub_C],
      mul_one, hdegq]
  rw [← hdegp, ← hdegqz]
  -- conclude by the composed-sum core lemma
  have hpne : Polynomial.map f (AzPolynomial.toPoly P) ≠ 0 := by
    intro h
    apply hfP
    have h2 := congrArg (fun t => Polynomial.coeff t P.natDegree) h
    simpa [Polynomial.coeff_map, AzPolynomial.coeff_toPoly, AzPolynomial.leadingCoeff] using h2
  exact Polynomial.resultant_comp_sub_eq_zero_iff hpne z

omit [DecidableEq K] in
/-- **Correctness of the composed product.** For `f : R →+* K` into an
algebraically closed field with `f` not killing the leading coefficients of
`P` and `Q` nor the trailing coefficient of `Q`, `z` is a root of
`map f (toPoly (composedProduct P Q))` iff `z = a · b` for a root `a` of
`map f (toPoly P)` and a **nonzero** root `b` of `map f (toPoly Q)` — the
roots of `Q` at `0` are dropped by the construction.

**Application:** for `R = AzInt` and `f : AzInt →+* ℂ` (injective, so all
three coefficient hypotheses are automatic), `composedProduct P Q` is a
defining polynomial of `α · β` whenever `P`, `Q` are defining polynomials of
`α`, `β` with `β ≠ 0`. -/
theorem isRoot_composedProduct_map_iff (f : R →+* K) (P Q : AzPolynomial R)
    (hfP : f P.leadingCoeff ≠ 0) (hfQ : f Q.leadingCoeff ≠ 0)
    (hfQt : f ((AzPolynomial.toPoly Q).trailingCoeff) ≠ 0) (z : K) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (composedProduct P Q))) z ↔
    ∃ a b : K, Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly P)) a ∧
      Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly Q)) b ∧ b ≠ 0 ∧ z = a * b := by
  have hPne : P ≠ 0 := fun h => hfP (by
    rw [h, show (0 : AzPolynomial R).leadingCoeff = 0 from rfl, map_zero])
  have hQne : Q ≠ 0 := fun h => hfQ (by
    rw [h, show (0 : AzPolynomial R).leadingCoeff = 0 from rfl, map_zero])
  have hPYne : AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R)) ≠ 0 := by
    intro h
    exact hPne ((map_eq_zero_iff_of_injective CRingHom CRingHom_injective P).mp
      (toPoly_inj.mp (h.trans toPoly_zero.symm)))
  have hmapdegP : (P.map (CRingHom : R →+* AzPolynomial R)).natDegree = P.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective P
  have hmapdegQ : (Q.map (CRingHom : R →+* AzPolynomial R)).natDegree = Q.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective Q
  -- rephrase the root condition through `evalMapHom`
  show Polynomial.eval z (Polynomial.map f (AzPolynomial.toPoly (composedProduct P Q))) = 0 ↔ _
  rw [← evalMapHom_apply f z]
  -- the computable resultant is Mathlib's, and homomorphisms push inside
  rw [show composedProduct P Q
      = resultant (P.map CRingHom) (scaleRoots (invertRoots (Q.map CRingHom)) X 1) from rfl,
    resultant_eq _ _ hPYne, Azurite.BPR.Chapter4.Res_eq_resultant,
    ← Polynomial.resultant_map_map]
  -- identify the two mapped polynomials
  have hA : (AzPolynomial.toPoly (P.map CRingHom)).map (evalMapHom f z)
      = Polynomial.map f (AzPolynomial.toPoly P) := map_evalMapHom_toPoly_map_CRingHom f z P
  have hB := map_evalMapHom_toPoly_prodArg f z Q hfQ hfQt
  -- the pinned matrix degrees
  have hdegA : (AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R))).natDegree
      = P.natDegree := by
    rw [AzPolynomial.natDegree_toPoly, hmapdegP]
  have htoB : AzPolynomial.toPoly (scaleRoots (invertRoots (Q.map CRingHom)) X 1)
      = ((AzPolynomial.toPoly (Q.map (CRingHom : R →+* AzPolynomial R))).reverse).scaleRoots
          (X : AzPolynomial R) := by
    rw [toPoly_scaleRoots, toPoly_invertRoots, Polynomial.C_1, one_mul, Polynomial.comp_X]
  have hdegB : (AzPolynomial.toPoly (scaleRoots (invertRoots (Q.map CRingHom)) X 1)).natDegree
      = Q.natDegree - (AzPolynomial.toPoly Q).natTrailingDegree := by
    rw [htoB, Polynomial.natDegree_scaleRoots, Polynomial.reverse_natDegree,
      natTrailingDegree_toPoly_map_CRingHom Q hQne, AzPolynomial.natDegree_toPoly, hmapdegQ]
  rw [hA, hB, hdegA, hdegB]
  -- the pinned degrees are the true degrees of the mapped polynomials
  have hdegp : (Polynomial.map f (AzPolynomial.toPoly P)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  have hdegBz : (((Polynomial.map f (AzPolynomial.toPoly Q)).reverse).scaleRoots z).natDegree
      = Q.natDegree - (AzPolynomial.toPoly Q).natTrailingDegree := by
    rw [Polynomial.natDegree_scaleRoots, Polynomial.reverse_natDegree,
      natTrailingDegree_map_toPoly f Q hfQt,
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  rw [← hdegp, ← hdegBz]
  -- conclude by the composed-product core lemma
  have hpne : Polynomial.map f (AzPolynomial.toPoly P) ≠ 0 := by
    intro h
    apply hfP
    have h2 := congrArg (fun t => Polynomial.coeff t P.natDegree) h
    simpa [Polynomial.coeff_map, AzPolynomial.coeff_toPoly, AzPolynomial.leadingCoeff] using h2
  have hqne : Polynomial.map f (AzPolynomial.toPoly Q) ≠ 0 := by
    intro h
    apply hfQ
    have h2 := congrArg (fun t => Polynomial.coeff t Q.natDegree) h
    simpa [Polynomial.coeff_map, AzPolynomial.coeff_toPoly, AzPolynomial.leadingCoeff] using h2
  exact Polynomial.resultant_scaleRoots_reverse_eq_zero_iff hpne hqne z

omit [DecidableEq K] in
/-- **Correctness of the composed difference.** Same hypotheses as the sum:
`z` is a root of `map f (toPoly (composedDifference P Q))` iff `z = a − b` for
roots `a` of `map f (toPoly P)` and `b` of `map f (toPoly Q)`. -/
theorem isRoot_composedDifference_map_iff (f : R →+* K) (P Q : AzPolynomial R)
    (hfP : f P.leadingCoeff ≠ 0) (hfQ : f Q.leadingCoeff ≠ 0) (z : K) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (composedDifference P Q))) z ↔
    ∃ a b : K, Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly P)) a ∧
      Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly Q)) b ∧ z = a - b := by
  have hPne : P ≠ 0 := fun h => hfP (by
    rw [h, show (0 : AzPolynomial R).leadingCoeff = 0 from rfl, map_zero])
  have hPYne : AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R)) ≠ 0 := by
    intro h
    exact hPne ((map_eq_zero_iff_of_injective CRingHom CRingHom_injective P).mp
      (toPoly_inj.mp (h.trans toPoly_zero.symm)))
  have hmapdegP : (P.map (CRingHom : R →+* AzPolynomial R)).natDegree = P.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective P
  have hmapdegQ : (Q.map (CRingHom : R →+* AzPolynomial R)).natDegree = Q.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective Q
  show Polynomial.eval z (Polynomial.map f (AzPolynomial.toPoly (composedDifference P Q))) = 0 ↔ _
  rw [← evalMapHom_apply f z]
  rw [show composedDifference P Q
      = resultant (P.map CRingHom) ((Q.map CRingHom).translate X) from rfl,
    resultant_eq _ _ hPYne, Azurite.BPR.Chapter4.Res_eq_resultant,
    ← Polynomial.resultant_map_map]
  have hA : (AzPolynomial.toPoly (P.map CRingHom)).map (evalMapHom f z)
      = Polynomial.map f (AzPolynomial.toPoly P) := map_evalMapHom_toPoly_map_CRingHom f z P
  have hB : (AzPolynomial.toPoly ((Q.map CRingHom).translate X)).map (evalMapHom f z)
      = (Polynomial.map f (AzPolynomial.toPoly Q)).comp (Polynomial.X - Polynomial.C z) := by
    rw [toPoly_translate, Polynomial.map_comp, map_evalMapHom_toPoly_map_CRingHom,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, evalMapHom_X]
  have hdegA : (AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R))).natDegree
      = P.natDegree := by
    rw [AzPolynomial.natDegree_toPoly, hmapdegP]
  have hdegB : (AzPolynomial.toPoly
      ((Q.map (CRingHom : R →+* AzPolynomial R)).translate X)).natDegree = Q.natDegree := by
    rw [AzPolynomial.natDegree_toPoly, natDegree_translate, hmapdegQ]
  rw [hA, hB, hdegA, hdegB]
  have hdegp : (Polynomial.map f (AzPolynomial.toPoly P)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  have hdegq : (Polynomial.map f (AzPolynomial.toPoly Q)).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  have hdegqz : ((Polynomial.map f (AzPolynomial.toPoly Q)).comp
      (Polynomial.X - Polynomial.C z)).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_comp, natDegree_X_sub_C, mul_one, hdegq]
  rw [← hdegp, ← hdegqz]
  have hpne : Polynomial.map f (AzPolynomial.toPoly P) ≠ 0 := by
    intro h
    apply hfP
    have h2 := congrArg (fun t => Polynomial.coeff t P.natDegree) h
    simpa [Polynomial.coeff_map, AzPolynomial.coeff_toPoly, AzPolynomial.leadingCoeff] using h2
  exact Polynomial.resultant_comp_X_sub_C_eq_zero_iff hpne z

omit [DecidableEq K] in
/-- **Correctness of the composed quotient.** Same hypotheses as the sum
(no trailing-coefficient condition needed — the leading `y`-coefficient of
`x^m · Q(y/x)` is `b_m`): `z` is a root of
`map f (toPoly (composedQuotient P Q))` iff `a = z · b` for roots `a` of
`map f (toPoly P)` and `b` of `map f (toPoly Q)` — the fraction-free form of
`z = a / b`. For nonzero `b` this gives the quotients `a / b`; the pair
`(a, b) = (0, 0)` witnesses every `z` at once, matching the identically-zero
resultant in the indeterminate `0 / 0` case. -/
theorem isRoot_composedQuotient_map_iff (f : R →+* K) (P Q : AzPolynomial R)
    (hfP : f P.leadingCoeff ≠ 0) (hfQ : f Q.leadingCoeff ≠ 0) (z : K) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (composedQuotient P Q))) z ↔
    ∃ a b : K, Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly P)) a ∧
      Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly Q)) b ∧ a = z * b := by
  have hPne : P ≠ 0 := fun h => hfP (by
    rw [h, show (0 : AzPolynomial R).leadingCoeff = 0 from rfl, map_zero])
  have hPYne : AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R)) ≠ 0 := by
    intro h
    exact hPne ((map_eq_zero_iff_of_injective CRingHom CRingHom_injective P).mp
      (toPoly_inj.mp (h.trans toPoly_zero.symm)))
  have hmapdegP : (P.map (CRingHom : R →+* AzPolynomial R)).natDegree = P.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective P
  have hmapdegQ : (Q.map (CRingHom : R →+* AzPolynomial R)).natDegree = Q.natDegree :=
    natDegree_map_of_injective CRingHom CRingHom_injective Q
  have hd : (AzPolynomial.toPoly (Q.map (CRingHom : R →+* AzPolynomial R))).natDegree
      = Q.natDegree := by
    rw [AzPolynomial.natDegree_toPoly, hmapdegQ]
  have hlc : (evalMapHom f z)
      ((AzPolynomial.toPoly (Q.map CRingHom)).leadingCoeff) ≠ 0 := by
    rw [Polynomial.leadingCoeff, hd, AzPolynomial.coeff_toPoly, coeff_map', CRingHom_apply,
      evalMapHom_apply, toPoly_C, Polynomial.map_C, Polynomial.eval_C]
    exact hfQ
  show Polynomial.eval z (Polynomial.map f (AzPolynomial.toPoly (composedQuotient P Q))) = 0 ↔ _
  rw [← evalMapHom_apply f z]
  rw [show composedQuotient P Q
      = resultant (P.map CRingHom) (scaleRoots (Q.map CRingHom) X 1) from rfl,
    resultant_eq _ _ hPYne, Azurite.BPR.Chapter4.Res_eq_resultant,
    ← Polynomial.resultant_map_map]
  have hA : (AzPolynomial.toPoly (P.map CRingHom)).map (evalMapHom f z)
      = Polynomial.map f (AzPolynomial.toPoly P) := map_evalMapHom_toPoly_map_CRingHom f z P
  have hB : (AzPolynomial.toPoly (scaleRoots (Q.map CRingHom) X 1)).map (evalMapHom f z)
      = (Polynomial.map f (AzPolynomial.toPoly Q)).scaleRoots z := by
    rw [toPoly_scaleRoots, Polynomial.C_1, one_mul, Polynomial.comp_X,
      Polynomial.map_scaleRoots _ _ _ hlc, evalMapHom_X,
      map_evalMapHom_toPoly_map_CRingHom]
  have hdegA : (AzPolynomial.toPoly (P.map (CRingHom : R →+* AzPolynomial R))).natDegree
      = P.natDegree := by
    rw [AzPolynomial.natDegree_toPoly, hmapdegP]
  have htoB : AzPolynomial.toPoly (scaleRoots (Q.map CRingHom) X 1)
      = (AzPolynomial.toPoly (Q.map (CRingHom : R →+* AzPolynomial R))).scaleRoots
          (X : AzPolynomial R) := by
    rw [toPoly_scaleRoots, Polynomial.C_1, one_mul, Polynomial.comp_X]
  have hdegB : (AzPolynomial.toPoly (scaleRoots (Q.map CRingHom) X 1)).natDegree
      = Q.natDegree := by
    rw [htoB, Polynomial.natDegree_scaleRoots, hd]
  rw [hA, hB, hdegA, hdegB]
  have hdegp : (Polynomial.map f (AzPolynomial.toPoly P)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  have hdegBz : ((Polynomial.map f (AzPolynomial.toPoly Q)).scaleRoots z).natDegree
      = Q.natDegree := by
    rw [Polynomial.natDegree_scaleRoots,
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero f (by rwa [leadingCoeff_toPoly]),
      AzPolynomial.natDegree_toPoly]
  rw [← hdegp, ← hdegBz]
  have hpne : Polynomial.map f (AzPolynomial.toPoly P) ≠ 0 := by
    intro h
    apply hfP
    have h2 := congrArg (fun t => Polynomial.coeff t P.natDegree) h
    simpa [Polynomial.coeff_map, AzPolynomial.coeff_toPoly, AzPolynomial.leadingCoeff] using h2
  have hqne : Polynomial.map f (AzPolynomial.toPoly Q) ≠ 0 := by
    intro h
    apply hfQ
    have h2 := congrArg (fun t => Polynomial.coeff t Q.natDegree) h
    simpa [Polynomial.coeff_map, AzPolynomial.coeff_toPoly, AzPolynomial.leadingCoeff] using h2
  exact Polynomial.resultant_scaleRoots_eq_zero_iff hpne hqne z

end Azurite.AzPolynomial

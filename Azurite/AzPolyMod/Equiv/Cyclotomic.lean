/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Correctness of the computable cyclotomic ring `CycT n p k`.**

  * `toPoly_cyclotomicPrimePow` — the coefficient array is Mathlib's
    `cyclotomic (p^k)`.
  * `cycTEquiv : CycModN (p^k) n ≃+* CycT n p k` (sending root to `ζ`),
    hence `reduceCycT : CycM (p^k) →+* CycT n p k`, the reduction of
    the abstract model modulo `n` (`reduceCycT_zetaM`,
    `reduceCycT_eq_zero_iff`): every congruence of the soundness
    chain is an equality in `CycT`.
  * `toAdjoin_eq_sum_coeff` / `toAdjoin_ofCoeffFn` — elements as sums of
    their coordinates, in both directions.
  * `sigmaAdj x` — `σ_x` on the `AdjoinRoot` side; `toAdjoin_sigmaT`
    (the computable `σ_x` is `σ_x`) and `sigmaAdj_toAdjoin_sigmaInvT`
    (Algorithm (6.1): `σ_x(σ_x⁻¹ a) = a`).
  * `findHT_spec` — Algorithm (6.2): `findHT a = some h ⟹ a = ζ^h`.
  * `lambdaAdj β` — `λ` on the `AdjoinRoot` side, `lambdaAdj_toAdjoin`
    (the Horner evaluation computes it) and `lambdaAdj_reduceCycT`
    (it is `CL.lambdaHom` of Method (10.3) on the abstract model).
-/
import Azurite.AzPolyMod.Cyclotomic
import Azurite.AzPolyMod.Equiv.GaussTower
import Azurite.AzPolynomial.Equiv.Eval
import Azurite.AzPolynomial.Equiv.Monomial

namespace Azurite

open Polynomial

namespace AzPolynomial

/-- **The coefficient array is `Φ_{p^k}`.** -/
theorem toPoly_cyclotomicPrimePow {R : Type _} [CommRing R] [DecidableEq R]
    [Nontrivial R] {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    AzPolynomial.toPoly (cyclotomicPrimePow R p k) = cyclotomic (p ^ k) R := by
  rw [CL.cyclotomic_prime_pow_eq_sum hp hk]
  apply Polynomial.ext
  intro i
  rw [coeff_toPoly_eq, Polynomial.finsetSum_coeff, coeff_cyclotomicPrimePow]
  simp only [Polynomial.coeff_X_pow]
  have hP : 0 < p ^ (k - 1) := pow_pos hp.pos _
  by_cases h : i ≤ (p - 1) * p ^ (k - 1) ∧ i % p ^ (k - 1) = 0
  · rw [ite_eq_left h]
    obtain ⟨hle, hmod⟩ := h
    have hi : i = i / p ^ (k - 1) * p ^ (k - 1) := by
      have := Nat.div_add_mod i (p ^ (k - 1))
      rw [hmod, add_zero, mul_comm] at this
      exact this.symm
    have hlt : i / p ^ (k - 1) < p := by
      rw [Nat.div_lt_iff_lt_mul hP]
      have h1 : (p - 1) * p ^ (k - 1) < p * p ^ (k - 1) :=
        Nat.mul_lt_mul_of_pos_right (by have := hp.one_lt; omega) hP
      omega
    have hiff : ∀ j, (i = j * p ^ (k - 1)) = (i / p ^ (k - 1) = j) := fun j =>
      propext ⟨fun h => by rw [h, Nat.mul_div_cancel _ hP], fun h => by rw [← h]; exact hi⟩
    simp_rw [hiff]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hlt)]
  · rw [ite_eq_right h]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [ite_eq_right]
    intro hij
    apply h
    have hj' := Finset.mem_range.mp hj
    refine ⟨?_, ?_⟩
    · rw [hij]
      exact Nat.mul_le_mul_right _ (by omega)
    · rw [hij, Nat.mul_mod_left]

/-- Coefficients vanish from the array size on. -/
theorem coeff_eq_zero_of_size_le {R : Type _} [Semiring R] (q : AzPolynomial R)
    {i : ℕ} (h : q.coeffs.size ≤ i) : q.coeff i = 0 := by
  unfold coeff
  rw [Array.getElem?_eq_none h]
  rfl

/-- A polynomial is the sum of its first `m` coordinates once `m` bounds
its size. -/
theorem toPoly_eq_sum_coeff {R : Type _} [Semiring R] (q : AzPolynomial R)
    {m : ℕ} (hm : q.coeffs.size ≤ m) :
    AzPolynomial.toPoly q = ∑ i ∈ Finset.range m, Polynomial.C (q.coeff i) * Polynomial.X ^ i := by
  apply Polynomial.ext
  intro j
  rw [coeff_toPoly_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hj : j < m
  · rw [ite_eq_left (Finset.mem_range.mpr hj)]
  · rw [ite_eq_right (by simpa using hj)]
    exact coeff_eq_zero_of_size_le q (by omega)

/-- `AzPolynomial.toPoly (normalize (ofFn c)) = Σ_{i<m} c_i x^i`. -/
theorem toPoly_normalize_ofFn {R : Type _} [Semiring R] [DecidableEq R] (m : ℕ)
    (c : ℕ → R) :
    AzPolynomial.toPoly (normalize (Array.ofFn fun i : Fin m => c i))
      = ∑ i ∈ Finset.range m, Polynomial.C (c i) * Polynomial.X ^ i := by
  apply Polynomial.ext
  intro j
  rw [coeff_toPoly_eq, coeff_normalize, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Array.getElem?_ofFn]
  rw [Finset.sum_ite_eq]
  by_cases hj : j < m
  · rw [dite_eq_left hj, Option.getD_some, ite_eq_left (Finset.mem_range.mpr hj)]
  · rw [dite_eq_right hj, Option.getD_none, ite_eq_right (by simpa using hj)]

end AzPolynomial

namespace AzPolyMod

open _root_.Azurite.AzPolynomial

section General

variable {R : Type _} [CommRing R] [DecidableEq R] [Nontrivial R] {f : AzPolynomial R}
  (hf : (AzPolynomial.toPoly f).Monic)
include hf

omit [DecidableEq R] in
/-- A reduced representative has size below the (monic) modulus. -/
theorem size_val_lt (a : AzPolyMod f) : a.val.coeffs.size < f.coeffs.size := by
  rcases a.isReduced with h | h
  · exact h
  · exfalso
    have hl := hf
    rw [Polynomial.Monic, leadingCoeff_toPoly, AzPolynomial.leadingCoeff,
      AzPolynomial.natDegree, h, coeff_eq_zero_of_size_le f (by omega)] at hl
    exact zero_ne_one hl

/-- **Elements as sums of coordinates**: for `m + 1 ≥ size f`,
`a = Σ_{i<m} a_i ζ^i`. -/
theorem toAdjoin_eq_sum_coeff (a : AzPolyMod f) {m : ℕ} (hm : f.coeffs.size ≤ m + 1) :
    toAdjoin a = ∑ i ∈ Finset.range m,
      AdjoinRoot.of (AzPolynomial.toPoly f) (a.val.coeff i) * AdjoinRoot.root (AzPolynomial.toPoly f) ^ i := by
  have hsize : a.val.coeffs.size ≤ m := by
    have := size_val_lt hf a
    omega
  rw [toAdjoin_def, toPoly_eq_sum_coeff a.val hsize, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

/-- **Coordinates to elements**: `ofCoeffFn m c = Σ_{i<m} c_i ζ^i`. -/
theorem toAdjoin_ofCoeffFn (m : ℕ) (c : ℕ → R) :
    toAdjoin (ofCoeffFn m c : AzPolyMod f) = ∑ i ∈ Finset.range m,
      AdjoinRoot.of (AzPolynomial.toPoly f) (c i) * AdjoinRoot.root (AzPolynomial.toPoly f) ^ i := by
  rw [ofCoeffFn, toAdjoin_ofPoly hf hf.ne_zero, toPoly_normalize_ofFn, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]

/-- `toAdjoin` of an accumulating fold is the sum. -/
theorem toAdjoin_foldl_add (g : ℕ → AzPolyMod f) :
    ∀ m : ℕ, toAdjoin ((List.range m).foldl (fun acc i => acc + g i) 0)
      = ∑ i ∈ Finset.range m, toAdjoin (g i)
  | 0 => by simp [toAdjoin_zero]
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      toAdjoin_add hf hf.ne_zero, toAdjoin_foldl_add g m, Finset.sum_range_succ]

end General

/-! ### The cyclotomic ring -/

section CycT

open CL CP

variable (n : AzNat) (p k : ℕ) [Fact (1 < n.toNat)]

/-- `toAdjoin ζ = root`. -/
theorem toAdjoin_zetaT :
    toAdjoin (zetaT n p k) = AdjoinRoot.root (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) := by
  rw [zetaT, toAdjoin_ofPoly (monic_toPoly_cyclotomicPrimePow _ _ _)
    (monic_toPoly_cyclotomicPrimePow _ _ _).ne_zero, AzPolynomial.toPoly_X, AdjoinRoot.mk_X]

theorem span_natCast_eq_map (m N : ℕ) :
    Ideal.span {(N : CycM m)} = (Ideal.span {(N : ℤ)}).map (AdjoinRoot.of (cyclotomic m ℤ)) := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- **`ℤ[ζ_m]/(N) ≃+* (ℤ/Nℤ)[x]/(Φ_m)`** (a root-tracking form of
`CL.cycM_quot_equiv`, built from `adjoinRootCongr`). -/
noncomputable def cycMQuotEquiv (m N : ℕ) :
    (CycM m ⧸ Ideal.span {(N : CycM m)}) ≃+* CycModN m N :=
  ((Ideal.quotEquivOfEq (span_natCast_eq_map m N) :
      (CycM m ⧸ Ideal.span {(N : CycM m)})
        ≃+* (CycM m ⧸ (Ideal.span {(N : ℤ)}).map (AdjoinRoot.of (cyclotomic m ℤ)))).trans
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (Ideal.span {(N : ℤ)})
      (cyclotomic m ℤ))).trans
    (adjoinRootCongr (Int.quotientSpanNatEquivZMod N) (by rw [map_cyclotomic, map_cyclotomic]))

/-- `cycMQuotEquiv` sends the class of `ζ` to the root. -/
theorem cycMQuotEquiv_mk_zetaM (m N : ℕ) :
    cycMQuotEquiv m N (Ideal.Quotient.mk _ (zetaM m))
      = AdjoinRoot.root (cyclotomic m (ZMod N)) := by
  rw [cycMQuotEquiv]
  erw [RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk (span_natCast_eq_map m N),
    show zetaM m = AdjoinRoot.mk (cyclotomic m ℤ) X from rfl,
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of, Polynomial.map_X]
  exact adjoinRootCongr_root _ _

variable (hp : p.Prime) (hk : 0 < k)
include hp hk

/-- **`(ℤ/nℤ)[x]/(Φ_{p^k}) ≃+* CycT n p k`**, sending the root to `ζ`. -/
noncomputable def cycTEquiv : CycModN (p ^ k) n.toNat ≃+* CycT n p k :=
  (adjoinRootCongr (AzZMod.ringEquivZMod (m := n)).symm (by
      rw [map_cyclotomic, toPoly_cyclotomicPrimePow hp hk])).trans
    (ringEquivAdjoinRoot (f := cyclotomicPrimePow (AzZMod n) p k)).symm

theorem cycTEquiv_root :
    cycTEquiv n p k hp hk (AdjoinRoot.root (cyclotomic (p ^ k) (ZMod n.toNat)))
      = zetaT n p k := by
  rw [cycTEquiv, RingEquiv.trans_apply, adjoinRootCongr_root]
  rw [RingEquiv.symm_apply_eq, ringEquivAdjoinRoot_apply, toAdjoin_zetaT]

/-- **The reduction of the abstract model into the computable ring**:
`ℤ[ζ_{p^k}] →+* CycT n p k`. -/
noncomputable def reduceCycT : CycM (p ^ k) →+* CycT n p k :=
  ((cycTEquiv n p k hp hk).toRingHom.comp (cycMQuotEquiv (p ^ k) n.toNat).toRingHom).comp
    (Ideal.Quotient.mk _)

theorem reduceCycT_zetaM : reduceCycT n p k hp hk (zetaM (p ^ k)) = zetaT n p k := by
  simp only [reduceCycT, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [cycMQuotEquiv_mk_zetaM, cycTEquiv_root]

/-- **Congruence modulo `n` in the model is equality in `CycT`.** -/
theorem reduceCycT_eq_zero_iff (x : CycM (p ^ k)) :
    reduceCycT n p k hp hk x = 0 ↔ ((n.toNat : ℕ) : CycM (p ^ k)) ∣ x := by
  simp only [reduceCycT, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    map_eq_zero_iff _ (RingEquiv.injective _)]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem reduceCycT_eq_iff (x y : CycM (p ^ k)) :
    reduceCycT n p k hp hk x = reduceCycT n p k hp hk y
      ↔ ((n.toNat : ℕ) : CycM (p ^ k)) ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, reduceCycT_eq_zero_iff]

/-! #### Roots of `Φ_{p^k}` in `AdjoinRoot (AzPolynomial.toPoly Φ)` -/

/-- `eval₂ (of Φ) w Φ = eval₂ (Int.cast) w (Φ_{p^k} over ℤ)`. -/
theorem eval₂_of_toPoly (w : AdjoinRoot (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k))) :
    eval₂ (AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k))) w
        (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k))
      = eval₂ (Int.castRingHom _) w (cyclotomic (p ^ k) ℤ) := by
  have h1 := congrArg
    (fun q => eval₂ (AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k))) w q)
    (toPoly_cyclotomicPrimePow (R := AzZMod n) hp hk)
  rw [h1, ← map_cyclotomic_int (p ^ k) (AzZMod n), Polynomial.eval₂_map]
  congr 1

theorem eval₂_root_cyclotomic_int :
    eval₂ (Int.castRingHom (AdjoinRoot (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k))))
      (AdjoinRoot.root _) (cyclotomic (p ^ k) ℤ) = 0 := by
  rw [← eval₂_of_toPoly n p k hp hk]
  exact AdjoinRoot.eval₂_root _

theorem eval₂_root_pow_cyclotomic_int {x : ℕ} (hx : ¬ p ∣ x) :
    eval₂ (Int.castRingHom (AdjoinRoot (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k))))
      (AdjoinRoot.root _ ^ x) (cyclotomic (p ^ k) ℤ) = 0 := by
  rw [cyclotomic_prime_pow_eq_sum hp hk, eval₂_finsetSum]
  simp only [eval₂_X_pow, ← pow_mul]
  have h := sum_pow_root_cyclotomic_eq_zero hp hk (eval₂_root_cyclotomic_int n p k hp hk) hx 0
  simp only [zero_add] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

/-! #### `σ_x` -/

/-- **`σ_x : ζ ↦ ζ^x`** on the `AdjoinRoot` side, for `p ∤ x`. -/
noncomputable def sigmaAdj {x : ℕ} (hx : ¬ p ∣ x) :
    AdjoinRoot (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k))
      →+* AdjoinRoot (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) :=
  AdjoinRoot.lift (AdjoinRoot.of _) (AdjoinRoot.root _ ^ x) (by
    rw [eval₂_of_toPoly n p k hp hk]
    exact eval₂_root_pow_cyclotomic_int n p k hp hk hx)

@[simp] theorem sigmaAdj_root {x : ℕ} (hx : ¬ p ∣ x) :
    sigmaAdj n p k hp hk hx (AdjoinRoot.root _) = AdjoinRoot.root _ ^ x :=
  AdjoinRoot.lift_root _

@[simp] theorem sigmaAdj_of {x : ℕ} (hx : ¬ p ∣ x) (c : AzZMod n) :
    sigmaAdj n p k hp hk hx (AdjoinRoot.of _ c) = AdjoinRoot.of _ c :=
  AdjoinRoot.lift_of _

variable {n p k}

/-- **The computable `σ_x` is `σ_x`.** -/
theorem toAdjoin_sigmaT {x : ℕ} (hx : ¬ p ∣ x) (a : CycT n p k) :
    toAdjoin (sigmaT x a) = sigmaAdj n p k hp hk hx (toAdjoin a) := by
  have hf := monic_toPoly_cyclotomicPrimePow (AzZMod n) p k
  rw [sigmaT, toAdjoin_foldl_add hf,
    toAdjoin_eq_sum_coeff hf a (m := (p - 1) * p ^ (k - 1))
      (by rw [cyclotomicPrimePow_coeffs_size]),
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toAdjoin_mul hf hf.ne_zero, toAdjoin_ofCoeff hf hf.ne_zero, map_mul, map_pow,
    sigmaAdj_of, sigmaAdj_root, ← pow_mul]
  congr 1
  rw [show zetaT n p k ^ (x * i) = (zetaT n p k).pow (x * i) from rfl,
    toAdjoin_pow hf hf.ne_zero, toAdjoin_zetaT]

/-- **Algorithm (6.1) is correct**: `σ_x (σ_x⁻¹ a) = a`. -/
theorem sigmaAdj_toAdjoin_sigmaInvT {x : ℕ} (hx : ¬ p ∣ x) (a : CycT n p k) :
    sigmaAdj n p k hp hk hx (toAdjoin (sigmaInvT x a)) = toAdjoin a := by
  have hf := monic_toPoly_cyclotomicPrimePow (AzZMod n) p k
  rw [sigmaInvT, toAdjoin_ofCoeffFn hf, map_sum]
  simp only [map_mul, map_pow, sigmaAdj_of, sigmaAdj_root, ← pow_mul]
  rw [toAdjoin_eq_sum_coeff hf a (m := (p - 1) * p ^ (k - 1))
    (by rw [cyclotomicPrimePow_coeffs_size])]
  have hcast : ∀ i, AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k))
      (sigmaInvCoeff p k x (coeffT a) i)
      = sigmaInvCoeff p k x
          (fun j => AdjoinRoot.of (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) (coeffT a j))
          i := fun i => by
    simp only [sigmaInvCoeff, map_sub]
  simp_rw [hcast]
  exact sigmaInv_spec hp hk (eval₂_root_cyclotomic_int n p k hp hk) hx _ fun i hi => by
    rw [coeffT, coeff_eq_zero_of_size_le, map_zero]
    have := size_val_lt hf a
    rw [cyclotomicPrimePow_coeffs_size] at this
    omega

/-! #### `h` and `λ` -/

/-- **Algorithm (6.2) is sound**: `findHT a = some h ⟹ a = ζ^h`. -/
theorem findHT_spec {a : CycT n p k} {h : ℕ} (hfind : findHT a = some h) :
    toAdjoin a = toAdjoin (zetaT n p k) ^ h := by
  have hf := monic_toPoly_cyclotomicPrimePow (AzZMod n) p k
  rw [toAdjoin_eq_sum_coeff hf a (m := (p - 1) * p ^ (k - 1))
    (by rw [cyclotomicPrimePow_coeffs_size]), toAdjoin_zetaT]
  exact findH_spec_map (AdjoinRoot.of _) hp hk (eval₂_root_cyclotomic_int n p k hp hk)
    (coeffT a) hfind

/-- **`λ : ζ ↦ β`** on the `AdjoinRoot` side, for a root `β ∈ ℤ/nℤ` of
`Φ_{p^k}` (the `(1.3)(e)` data `β_{p^k}`). -/
noncomputable def lambdaAdj {β : AzZMod n}
    (hβ : eval₂ (Int.castRingHom (AzZMod n)) β (cyclotomic (p ^ k) ℤ) = 0) :
    AdjoinRoot (AzPolynomial.toPoly (cyclotomicPrimePow (AzZMod n) p k)) →+* AzZMod n :=
  AdjoinRoot.lift (RingHom.id _) β (by
    rw [toPoly_cyclotomicPrimePow hp hk, ← map_cyclotomic_int (p ^ k) (AzZMod n),
      Polynomial.eval₂_map, RingHom.id_comp]
    exact hβ)

/-- **Horner evaluation computes `λ`.** -/
theorem lambdaAdj_toAdjoin {β : AzZMod n}
    (hβ : eval₂ (Int.castRingHom (AzZMod n)) β (cyclotomic (p ^ k) ℤ) = 0)
    (a : CycT n p k) :
    lambdaAdj hp hk hβ (toAdjoin a) = lambdaT β a := by
  rw [toAdjoin_def, lambdaAdj, AdjoinRoot.lift_mk, lambdaT]
  exact eval_toPoly a.val β

/-- **`λ` on the computable ring is `CL.lambdaHom` on the model**: the
(10.3) homomorphism factors through the reduction. -/
theorem lambdaAdj_reduceCycT {β : AzZMod n}
    (hβ : eval₂ (Int.castRingHom (AzZMod n)) β (cyclotomic (p ^ k) ℤ) = 0) :
    (lambdaAdj hp hk hβ).comp
        ((ringEquivAdjoinRoot (f := cyclotomicPrimePow (AzZMod n) p k)).toRingHom.comp
          (reduceCycT n p k hp hk))
      = lambdaHom (p ^ k) hβ := by
  refine AdjoinRoot.ringHom_ext (RingHom.ext_int _ _) ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [show AdjoinRoot.root (cyclotomic (p ^ k) ℤ) = zetaM (p ^ k) from rfl,
    reduceCycT_zetaM, ringEquivAdjoinRoot_apply, toAdjoin_zetaT, lambdaAdj,
    AdjoinRoot.lift_root, lambdaHom_zetaM]

end CycT

end AzPolyMod

end Azurite

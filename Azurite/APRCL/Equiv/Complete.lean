/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Completeness of the Jacobi-sum tests**: for a prime `n` the products of
  Theorems (8.5)/(9.x) are congruent to a root of unity, so the exponent search
  (6.2) succeeds — the paper's "if `h` does not exist, then `n` is composite".

  * `natCast_dvd_of_phiR_dvd`: divisibility by `n` descends along the embedding
    `φ : ℤ[ζ_{p^k}] → ℤ[ζ_{q·p^k}]`, `ζ ↦ ζ^q` — since `φ(p^k) < q`, the images of
    the power basis are distinct members of the power basis of the target, so the
    coordinates are preserved and the content criterion applies.
  * `isUnit_mk_gaussSum`: Gauss sums are units modulo `n` (`τ(χ)τ(χ⁻¹) = χ(−1)q`).
  * `findHT_complete`: `a = ζ^h` with `h < p^k` is found by `findHT`.
  * `exists_dvd_sub_zP_pow_odd`: the converse of Theorem (8.5) for prime `n`,
    from the exact identity `W·σ(u_β) = u_β^n` and Corollary (7.5).
-/
import Azurite.APRCL.Equiv.JacobiChain
import Azurite.APRCL.Equiv.JacobiStage
import Azurite.CohenLenstra.Corollary_7_5

namespace Azurite

namespace APRCL

open CL CP Finset Polynomial

/-! ### Descent of divisibility along `φ` -/

section Descent

variable {q p k : ℕ} [hqF : Fact q.Prime] (hp : p.Prime) (hk : 0 < k) (hpk : p ^ k ∣ q - 1)

include hp hk hpk in
theorem totient_pk_lt : (p ^ k).totient < q := by
  have h1 : (p ^ k).totient < p ^ k := Nat.totient_lt _ (Nat.one_lt_pow hk.ne' hp.one_lt)
  have h2 : p ^ k ≤ q - 1 := Nat.le_of_dvd (by have := hqF.out.two_le; omega) hpk
  omega

include hp hk hpk in
theorem totient_mul_pk : (q * p ^ k).totient = (q - 1) * (p ^ k).totient := by
  rw [Nat.totient_mul ((coprime_pk_q hp hk hpk).symm), Nat.totient_prime hqF.out]

include hp hk hpk in
/-- `q·i` stays below the degree of `Φ_{q·p^k}` for `i < φ(p^k)`. -/
theorem q_mul_lt_totient {i : ℕ} (hi : i < (p ^ k).totient) : q * i < (q * p ^ k).totient := by
  rw [totient_mul_pk hp hk hpk, Nat.sub_one_mul]
  have hq2 := hqF.out.two_le
  have hT := totient_pk_lt hp hk hpk
  have h1 : q * (i + 1) ≤ q * (p ^ k).totient := Nat.mul_le_mul_left q hi
  rw [mul_add, mul_one] at h1
  omega

include hp hk hpk in
/-- **Divisibility by `N` descends along `φ`.** -/
theorem natCast_dvd_of_phiR_dvd {N : ℕ} {x : CycM (p ^ k)}
    (h : ((N : ℕ) : CR q p k) ∣ phiR (q := q) hp x) : ((N : ℕ) : CycM (p ^ k)) ∣ x := by
  classical
  rw [natCast_dvd_iff_dvd_contentM] at h ⊢
  set B := cycMBasis (p ^ k)
  set B' := cycMBasis (q * p ^ k)
  -- the embedding of indices
  let f : Fin (p ^ k).totient → Fin (q * p ^ k).totient := fun i =>
    ⟨q * i, q_mul_lt_totient hp hk hpk i.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    have := congrArg Fin.val hij
    simp only [f] at this
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hqF.out.pos this)
  -- `φ x = Σ a_i • ζ'^(q i) = linearCombination B' (mapDomain f a)`
  have hφx : phiR (q := q) hp x
      = Finsupp.linearCombination ℤ B' (Finsupp.mapDomain f (B.repr x)) := by
    conv_lhs => rw [← Module.Basis.linearCombination_repr B x]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapDomain_index_inj hf]
    simp only [Finsupp.sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, cycMBasis_apply, cycMBasis_apply, map_pow, phiR_zetaM]
    simp only [f, zP, ← pow_mul]
  have hrepr : ∀ i, B'.repr (phiR (q := q) hp x) (f i) = B.repr x i := by
    intro i
    rw [hφx, Module.Basis.repr_linearCombination, Finsupp.mapDomain_apply_of_injective hf]
  -- `N ∣ every coordinate of x`
  refine Finset.dvd_gcd fun i _ => ?_
  have h1 : N ∣ (B'.repr (phiR (q := q) hp x) (f i)).natAbs :=
    h.trans (Finset.gcd_dvd (Finset.mem_univ (f i)))
  rwa [hrepr] at h1

end Descent

/-! ### Units modulo `n` -/

section Units

variable {R : Type _} [CommRing R] {N : ℕ}

/-- `x` is a unit modulo `N` when some `y` has `x·y ≡ 1 (mod N)`. -/
theorem isUnit_mk_of_mul_sub_one_dvd {x y : R} (h : (N : R) ∣ x * y - 1) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(N : R)}) x) :=
  IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ y) (by
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (Ideal.span {(N : R)})), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact h)

/-- Cancel a unit modulo `N`: `N ∣ x·u` with `u` a unit mod `N` gives `N ∣ x`. -/
theorem dvd_of_dvd_mul_isUnit_mk {x u : R} (hu : IsUnit (Ideal.Quotient.mk (Ideal.span {(N : R)}) u))
    (h : (N : R) ∣ x * u) : (N : R) ∣ x := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem] at h ⊢
  rw [map_mul] at h
  exact (hu.mul_left_eq_zero).mp h

/-- The prime `q ≠ n` is a unit modulo the prime `n`. -/
theorem isUnit_mk_natCast_q {q : ℕ} (hn : N.Prime) (hqn : ¬ q ∣ N) (hq : q.Prime) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(N : R)}) ((q : ℕ) : R)) := by
  have hco : Nat.Coprime q N := (Nat.coprime_primes hq hn).mpr fun h => hqn (h ▸ dvd_refl _)
  obtain ⟨y, hy⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco hn.one_lt
  refine isUnit_mk_of_mul_sub_one_dvd (y := (y : R)) ?_
  have h1 : 1 ≡ q * y [MOD N] := by
    rw [Nat.ModEq, hy.2, Nat.mod_eq_of_lt hn.one_lt]
  have h2 : (N : ℤ) ∣ ((q * y : ℕ) : ℤ) - ((1 : ℕ) : ℤ) := Nat.modEq_iff_dvd.mp h1
  have h3 := map_dvd (Int.castRingHom R) h2
  rw [eq_intCast, eq_intCast] at h3
  push_cast at h3
  exact h3

end Units

section GaussUnits

variable {q : ℕ} [hqF : Fact q.Prime] {R : Type _} [CommRing R] [IsDomain R] {N : ℕ}

/-- **Gauss sums are units modulo the prime `n`** (`q ∤ n`): `τ(χ)τ(χ⁻¹) = χ(−1)·q`. -/
theorem isUnit_mk_gaussSum (hn : N.Prime) (hqn : ¬ q ∣ N) {χ : MulChar (ZMod q) R} (hχ : χ ≠ 1)
    {ψ : AddChar (ZMod q) R} (hψ : ψ.IsPrimitive) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(N : R)}) (gaussSum χ ψ)) := by
  have h := tau_mul_tau_inv hχ hψ
  have hq := isUnit_mk_natCast_q (R := R) hn hqn hqF.out
  have hneg : IsUnit (Ideal.Quotient.mk (Ideal.span {(N : R)}) (χ (-1))) :=
    IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ (χ (-1))) (by rw [← map_mul, chi_neg_one_sq, map_one])
  have hprod : IsUnit (Ideal.Quotient.mk (Ideal.span {(N : R)}) (gaussSum χ ψ)
      * Ideal.Quotient.mk (Ideal.span {(N : R)}) (gaussSum χ⁻¹ ψ)) := by
    rw [← map_mul, h, map_mul]
    exact hneg.mul hq
  exact isUnit_of_mul_isUnit_left hprod

end GaussUnits

/-! ### Completeness of the exponent search -/

section FindH

variable {n : AzNat} {p k : ℕ} [Fact (1 < n.toNat)] (hp : p.Prime) (hk : 0 < k)

include hp hk in
/-- The coefficients of `ofCoeffFn m c` are `c` (for `m` below the modulus degree). -/
theorem coeffT_ofCoeffFn {m : ℕ} (hm : m ≤ (p - 1) * p ^ (k - 1)) (c : ℕ → AzZMod n) {i : ℕ}
    (hi : i < m) : AzPolyMod.coeffT (AzPolyMod.ofCoeffFn m c : AzPolyMod.CycT n p k) i = c i := by
  have hf := AzPolynomial.monic_toPoly_cyclotomicPrimePow (AzZMod n) p k
  -- the normalized array is already reduced modulo `Φ`
  have hred : AzPolynomial.modByMonic (AzPolynomial.normalize (Array.ofFn fun i : Fin m => c i))
      (AzPolynomial.cyclotomicPrimePow (AzZMod n) p k)
      = AzPolynomial.normalize (Array.ofFn fun i : Fin m => c i) := by
    rw [← toPoly_inj, AzPolynomial.toPoly_modByMonic hf hf.ne_zero,
      Polynomial.modByMonic_eq_self_iff hf, AzPolynomial.toPoly_normalize_ofFn _ c,
      AzPolynomial.toPoly_cyclotomicPrimePow hp hk, degree_cyclotomic, Nat.totient_prime_pow hp hk]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact WithBot.bot_lt_coe _)]
    intro j hj
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast (show j < p ^ (k - 1) * (p - 1) by
      have := Finset.mem_range.mp hj; rw [mul_comm]; omega)
  show ((AzPolyMod.ofPoly _ : AzPolyMod.CycT n p k).val).coeff i = c i
  rw [AzPolyMod.ofPoly]
  simp only
  rw [hred, ← coeff_toPoly_eq, AzPolynomial.toPoly_normalize_ofFn _ c,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hi)]

include hp hk in
/-- `ζ^h` as a coefficient vector. -/
theorem zetaT_pow_eq_ofCoeffFn {h : ℕ} (hh : h < p ^ k) :
    (AzPolyMod.zetaT n p k) ^ h = AzPolyMod.ofCoeffFn ((p - 1) * p ^ (k - 1))
      (fun i => ((CL.zetaCoeff p k h i : ℤ) : AzZMod n)) := by
  have hf := AzPolynomial.monic_toPoly_cyclotomicPrimePow (AzZMod n) p k
  apply AzPolyMod.toAdjoin_injective hf hf.ne_zero
  rw [AzPolyMod.toAdjoin_ofCoeffFn hf, ← AzPolyMod.ringEquivAdjoinRoot_apply, map_pow,
    AzPolyMod.ringEquivAdjoinRoot_apply, AzPolyMod.toAdjoin_zetaT,
    ← CL.sum_zetaCoeff hp hk (AzPolyMod.eval₂_root_cyclotomic_int n p k hp hk) hh]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_intCast]

include hp hk in
/-- **Algorithm (6.2) is complete**: `a = ζ^h` with `h < p^k` is found. -/
theorem findHT_complete {a : AzPolyMod.CycT n p k} {h : ℕ} (hh : h < p ^ k)
    (ha : a = AzPolyMod.zetaT n p k ^ h) : (AzPolyMod.findHT a).isSome = true := by
  set m := (p - 1) * p ^ (k - 1) with hm
  set P := p ^ (k - 1) with hP
  have hpk : p ^ k = m + P := by
    have h1 : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [hm, hP, h1, Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hp.pos), mul_comm]
  have hcoeff : ∀ i < m, AzPolyMod.coeffT a i = ((CL.zetaCoeff p k h i : ℤ) : AzZMod n) := by
    intro i hi
    rw [ha, zetaT_pow_eq_ofCoeffFn hp hk hh, coeffT_ofCoeffFn hp hk le_rfl _ hi]
  rw [AzPolyMod.findHT, CL.findH]
  split
  · rfl
  · rename_i hnone
    rw [Option.isSome_map, List.find?_isSome]
    -- `h ≥ m`: otherwise the first search would have succeeded
    have hhm : m ≤ h := by
      by_contra hlt
      push Not at hlt
      rw [List.find?_eq_none] at hnone
      apply hnone h (List.mem_range.mpr hlt)
      rw [List.all_eq_true]
      intro i hi
      rw [decide_eq_true_eq, hcoeff i (List.mem_range.mp hi), CL.zetaCoeff, ite_eq_left hlt]
      split_ifs <;> simp
    refine ⟨h - m, List.mem_range.mpr (by omega), ?_⟩
    rw [List.all_eq_true]
    intro i hi
    rw [decide_eq_true_eq, hcoeff i (List.mem_range.mp hi), CL.zetaCoeff, ite_eq_right (by omega)]
    have hmP : m % P = 0 := by rw [hm]; exact Nat.mul_mod_left _ _
    have hhP : h % P = h - m := by
      obtain ⟨r, hr⟩ : ∃ r, h = m + r := ⟨h - m, by omega⟩
      rw [hr, Nat.add_mod, hmP, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel_left]
    rw [hhP]
    split_ifs <;> simp

end FindH

/-! ### The converse of Theorem (8.5) for prime `n` -/

section OddComplete

variable {q p k N : ℕ} [hqF : Fact q.Prime] (hp : p.Prime) (hk : 0 < k) (hpk : p ^ k ∣ q - 1)
  {gu : (ZMod q)ˣ} (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu)

include hp hk hpk hg in
/-- **For prime `n` the (8.8) product is a root of unity modulo `n`**, in the common ring. -/
theorem exists_dvd_sub_zP_pow_odd (hp3 : 2 < p) (hn : N.Prime) (hqn : ¬ q ∣ N) (hpn : ¬ p ∣ N) :
    ∃ h < p ^ k, ((N : ℕ) : CR q p k) ∣ (∏ x ∈ Mset p k,
      jacobiSum (chiR hp hpk hg ^ minv p k x) (chiR hp hpk hg ^ minv p k x) ^ αc N p k x)
      - zP q p k ^ h := by
  have := isDomain_cycM (cr_pos (q := q) (k := k) hp)
  set χ := chiR hp hpk hg with hχ
  set ψ := psiR q p k hp with hψ
  have hord := orderOf_chiR hp hpk hg
  have hpa : ¬ p ∣ 1 := hp.not_dvd_one
  have hpab : ¬ p ∣ 1 + 1 := fun hd => by have := Nat.le_of_dvd two_pos hd; omega
  -- the exact identity `W · σ(u_β) = u_β^n` (`a = b = 1`)
  have hid := jacobi_tau_identity (ψ := ψ) hp hk hord (psiR_primitive hp) (natCast_q_ne_zero hp)
    hpa hpa hpab hpn (a := 1) (b := 1) (n := N)
  simp only [one_mul] at hid
  set W := ∏ x ∈ Mset p k, jacobiSum (χ ^ minv p k x) (χ ^ minv p k x) ^ αc N p k x with hW
  set Gσ := ∏ x ∈ Mset p k, gaussSum (χ ^ (N * minv p k x)) ψ ^ βc 1 1 p k x with hGσ
  set Gβ := ∏ x ∈ Mset p k, gaussSum (χ ^ minv p k x) ψ ^ βc 1 1 p k x with hGβ
  -- Corollary (7.5), reindexed by `x ↦ minv x`
  have hcor := corollary_7_5 (R := CR q p k) hn hqn χ ψ (Mset p k) (fun y => βc 1 1 p k (minv p k y))
  have hre1 : ∏ y ∈ Mset p k, ((χ ^ y) (N : ZMod q) ^ N * gaussSum (χ ^ y) ψ ^ N) ^ βc 1 1 p k (minv p k y)
      = ∏ x ∈ Mset p k, ((χ ^ minv p k x) (N : ZMod q) ^ N * gaussSum (χ ^ minv p k x) ψ ^ N)
          ^ βc 1 1 p k x := by
    refine Finset.prod_nbij' (fun y => minv p k y) (fun x => minv p k x)
      (fun y hy => minv_mem hp hk hy) (fun x hx => minv_mem hp hk hx)
      (fun y hy => minv_invol hp hk hy) (fun x hx => minv_invol hp hk hx) (fun y hy => ?_)
    rw [minv_invol hp hk hy]
  have hre2 : ∏ y ∈ Mset p k, gaussSum ((χ ^ y) ^ N) ψ ^ βc 1 1 p k (minv p k y) = Gσ := by
    rw [hGσ]
    refine Finset.prod_nbij' (fun y => minv p k y) (fun x => minv p k x)
      (fun y hy => minv_mem hp hk hy) (fun x hx => minv_mem hp hk hx)
      (fun y hy => minv_invol hp hk hy) (fun x hx => minv_invol hp hk hx) (fun y hy => ?_)
    rw [minv_invol hp hk hy, ← pow_mul, mul_comm y N]
  rw [hre1, hre2] at hcor
  -- split the first product: `c · Gβ^N`
  set c := ∏ x ∈ Mset p k, ((χ ^ minv p k x) (N : ZMod q) ^ N) ^ βc 1 1 p k x with hc
  have hsplit : ∏ x ∈ Mset p k, ((χ ^ minv p k x) (N : ZMod q) ^ N * gaussSum (χ ^ minv p k x) ψ ^ N)
      ^ βc 1 1 p k x = c * Gβ ^ N := by
    rw [hc, hGβ, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [mul_pow]
    ring
  rw [hsplit, ← hid] at hcor
  -- `N ∣ (c·W − 1)·Gσ`, and `Gσ` is a unit modulo `N`
  have hcor' : ((N : ℕ) : CR q p k) ∣ (c * W - 1) * Gσ := by
    have : c * (W * Gσ) - Gσ = (c * W - 1) * Gσ := by ring
    rwa [this] at hcor
  have hGσunit : IsUnit (Ideal.Quotient.mk (Ideal.span {((N : ℕ) : CR q p k)}) Gσ) := by
    rw [hGσ, map_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun x hx => ?_
    rw [map_pow]
    refine IsUnit.pow _ (isUnit_mk_gaussSum hn hqn ?_ (psiR_primitive hp))
    intro h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hd
    have hpx : p ∣ N * minv p k x := (dvd_pow_self p hk.ne').trans hd
    rcases (Nat.Prime.dvd_mul hp).mp hpx with h | h
    · exact hpn h
    · exact minv_not_dvd hp hk (mem_Mset.mp hx).2 h
  have hdvd : ((N : ℕ) : CR q p k) ∣ c * W - 1 := dvd_of_dvd_mul_isUnit_mk hGσunit hcor'
  -- `c` is a power of `ζ_P`
  have hNu : ((N : ZMod q)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqn
  obtain ⟨j, hj⟩ := chiR_values hp hpk hg (Units.mk0 _ hNu)
  rw [Units.val_mk0, ← hχ] at hj
  have hcpow : c = zP q p k ^ (∑ x ∈ Mset p k, j * minv p k x * N * βc 1 1 p k x) := by
    rw [hc, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx0 : minv p k x ≠ 0 := fun h0 => minv_not_dvd hp hk (mem_Mset.mp hx).2 (h0 ▸ dvd_zero p)
    rw [MulChar.pow_apply' _ hx0, hj, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  set J := ∑ x ∈ Mset p k, j * minv p k x * N * βc 1 1 p k x
  have hpk0 : 0 < p ^ k := pow_pos hp.pos k
  refine ⟨(p ^ k - J % p ^ k) % p ^ k, Nat.mod_lt _ hpk0, ?_⟩
  have hJ : J + (p ^ k - J % p ^ k) % p ^ k ≡ 0 [MOD p ^ k] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    have h1 := Nat.div_add_mod J (p ^ k)
    have h2 := Nat.mod_lt J hpk0
    by_cases h0 : J % p ^ k = 0
    · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero]
      exact Nat.dvd_of_mod_eq_zero h0
    · rw [Nat.mod_eq_of_lt (Nat.sub_lt hpk0 (Nat.pos_of_ne_zero h0))]
      exact ⟨J / p ^ k + 1, by rw [mul_add, mul_one]; omega⟩
  have hunit : c * zP q p k ^ ((p ^ k - J % p ^ k) % p ^ k) = 1 := by
    rw [hcpow, ← pow_add, pow_eq_pow_of_modEq (zP_pow_eq_one hp) hJ, pow_zero]
  have : W - zP q p k ^ ((p ^ k - J % p ^ k) % p ^ k)
      = zP q p k ^ ((p ^ k - J % p ^ k) % p ^ k) * (c * W - 1) := by
    linear_combination (-W) * hunit
  rw [this]
  exact hdvd.mul_left _

end OddComplete

/-! ### The generic converse: an exact identity gives the congruence -/

section Generic

variable {q p k N : ℕ} [hqF : Fact q.Prime] (hp : p.Prime) (hk : 0 < k) (hpk : p ^ k ∣ q - 1)
  {gu : (ZMod q)ˣ} (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu)

include hp hpk hg in
/-- **From `u·W·∏ τ(χ^(Nx))^ν = (∏ τ(χ^x)^ν)^N` to `W ≡ ζ_P^h (mod N)`** for prime `N`, with
`u` a power of `ζ_P` and the exponents `x` not killing `χ`. -/
theorem exists_dvd_sub_zP_pow_of_identity (hn : N.Prime) (hqn : ¬ q ∣ N) (hpn : ¬ p ∣ N)
    {S : Finset ℕ} {ν : ℕ → ℕ} (hS : ∀ x ∈ S, chiR hp hpk hg ^ x ≠ 1) {W u : CR q p k}
    (hu : ∃ e, u = zP q p k ^ e)
    (hid : u * W * ∏ x ∈ S, gaussSum (chiR hp hpk hg ^ (N * x)) (psiR q p k hp) ^ ν x
      = (∏ x ∈ S, gaussSum (chiR hp hpk hg ^ x) (psiR q p k hp) ^ ν x) ^ N) :
    ∃ h < p ^ k, ((N : ℕ) : CR q p k) ∣ W - zP q p k ^ h := by
  have := isDomain_cycM (cr_pos (q := q) (k := k) hp)
  set χ := chiR hp hpk hg with hχ
  set ψ := psiR q p k hp with hψ
  have hord := orderOf_chiR hp hpk hg
  set Gσ := ∏ x ∈ S, gaussSum (χ ^ (N * x)) ψ ^ ν x with hGσ
  set Gβ := ∏ x ∈ S, gaussSum (χ ^ x) ψ ^ ν x with hGβ
  have hcor := corollary_7_5 (R := CR q p k) hn hqn χ ψ S ν
  have hre2 : ∏ x ∈ S, gaussSum ((χ ^ x) ^ N) ψ ^ ν x = Gσ := by
    rw [hGσ]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← pow_mul, mul_comm x N]
  set c := ∏ x ∈ S, ((χ ^ x) (N : ZMod q) ^ N) ^ ν x with hc
  have hsplit : ∏ x ∈ S, ((χ ^ x) (N : ZMod q) ^ N * gaussSum (χ ^ x) ψ ^ N) ^ ν x = c * Gβ ^ N := by
    rw [hc, hGβ, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [mul_pow]
    ring
  rw [hre2, hsplit, ← hid] at hcor
  have hcor' : ((N : ℕ) : CR q p k) ∣ (c * u * W - 1) * Gσ := by
    have : c * (u * W * Gσ) - Gσ = (c * u * W - 1) * Gσ := by ring
    rwa [this] at hcor
  have hGσunit : IsUnit (Ideal.Quotient.mk (Ideal.span {((N : ℕ) : CR q p k)}) Gσ) := by
    rw [hGσ, map_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun x hx => ?_
    rw [map_pow]
    refine IsUnit.pow _ (isUnit_mk_gaussSum hn hqn ?_ (psiR_primitive hp))
    intro h1
    apply hS x hx
    -- `χ^(N x) = 1` forces `χ^x = 1` since `p ∤ N`
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hd
    have hco : Nat.Coprime (p ^ k) N :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)
    have hdx : p ^ k ∣ x := hco.dvd_of_dvd_mul_left hd
    rw [← hord] at hdx
    exact orderOf_dvd_iff_pow_eq_one.mp hdx
  have hdvd : ((N : ℕ) : CR q p k) ∣ c * u * W - 1 := dvd_of_dvd_mul_isUnit_mk hGσunit hcor'
  -- `c · u` is a power of `ζ_P`
  have hNu : ((N : ZMod q)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqn
  obtain ⟨j, hj⟩ := chiR_values hp hpk hg (Units.mk0 _ hNu)
  rw [Units.val_mk0, ← hχ] at hj
  obtain ⟨e, he⟩ := hu
  have hcpow : c * u = zP q p k ^ (∑ x ∈ S, j * x * N * ν x + e) := by
    rw [pow_add, ← he, hc, ← Finset.prod_pow_eq_pow_sum]
    congr 1
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hS 0 hx (pow_zero χ)
    rw [MulChar.pow_apply' _ hx0, hj, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  set J := ∑ x ∈ S, j * x * N * ν x + e
  have hpk0 : 0 < p ^ k := pow_pos hp.pos k
  refine ⟨(p ^ k - J % p ^ k) % p ^ k, Nat.mod_lt _ hpk0, ?_⟩
  have hJ : J + (p ^ k - J % p ^ k) % p ^ k ≡ 0 [MOD p ^ k] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    have h1 := Nat.div_add_mod J (p ^ k)
    have h2 := Nat.mod_lt J hpk0
    by_cases h0 : J % p ^ k = 0
    · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero]
      exact Nat.dvd_of_mod_eq_zero h0
    · rw [Nat.mod_eq_of_lt (Nat.sub_lt hpk0 (Nat.pos_of_ne_zero h0))]
      exact ⟨J / p ^ k + 1, by rw [mul_add, mul_one]; omega⟩
  have hunit : c * u * zP q p k ^ ((p ^ k - J % p ^ k) % p ^ k) = 1 := by
    rw [hcpow, ← pow_add, pow_eq_pow_of_modEq (zP_pow_eq_one hp) hJ, pow_zero]
  have : W - zP q p k ^ ((p ^ k - J % p ^ k) % p ^ k)
      = zP q p k ^ ((p ^ k - J % p ^ k) % p ^ k) * (c * u * W - 1) := by
    linear_combination (-W) * hunit
  rw [this]
  exact hdvd.mul_left _

end Generic

/-! ### The `p = 2` cases -/

section TwoComplete

variable {q N : ℕ} [hqF : Fact q.Prime] {gu : (ZMod q)ˣ} (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu)
  (hn : N.Prime) (hqn : ¬ q ∣ N) (hodd : N % 2 = 1)

include hn hqn hodd in
/-- **`p^k = 2`**: Euler's criterion, `q^((N−1)/2) ≡ ±1 (mod N)`, in `ℤ[ζ_2]`. -/
theorem exists_dvd_sub_zetaM_pow_k1 :
    ∃ h < 2 ^ 1, ((N : ℕ) : CycM (2 ^ 1)) ∣ ((q : ℕ) : CycM (2 ^ 1)) ^ ((N - 1) / 2)
      - zetaM (2 ^ 1) ^ h := by
  have : Fact N.Prime := ⟨hn⟩
  have := isDomain_cycM (show 0 < 2 ^ 1 by norm_num)
  have hq0 : ((q : ℕ) : ZMod N) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    rw [(Nat.prime_dvd_prime_iff_eq hn hqF.out).mp h] at hqn
    exact hqn dvd_rfl
  have hζ : zetaM (2 ^ 1) = -1 :=
    (isPrimitiveRoot_zetaM (show 0 < 2 ^ 1 by norm_num)).eq_neg_one_of_two_right
  have hhalf : N / 2 = (N - 1) / 2 := by omega
  rcases ZMod.pow_div_two_eq_neg_one_or_one N hq0 with h1 | h1
  · refine ⟨0, by norm_num, ?_⟩
    rw [pow_zero]
    rw [hhalf] at h1
    have h2 : ((q ^ ((N - 1) / 2) : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by push_cast; exact h1
    have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
    have h4 : ((N : ℕ) : ℤ) ∣ ((q ^ ((N - 1) / 2) : ℕ) : ℤ) - ((1 : ℕ) : ℤ) :=
      Nat.modEq_iff_dvd.mp h3.symm
    have h5 := map_dvd (Int.castRingHom (CycM (2 ^ 1))) h4
    rw [eq_intCast, eq_intCast] at h5
    push_cast at h5
    exact h5
  · refine ⟨1, by norm_num, ?_⟩
    rw [pow_one (zetaM (2 ^ 1)), hζ, sub_neg_eq_add]
    rw [hhalf] at h1
    have h2 : ((q ^ ((N - 1) / 2) + 1 : ℕ) : ZMod N) = ((0 : ℕ) : ZMod N) := by
      push_cast; rw [h1]; ring
    have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
    have h4 : N ∣ q ^ ((N - 1) / 2) + 1 := Nat.modEq_zero_iff_dvd.mp h3
    have h5 := map_dvd (Nat.castRingHom (CycM (2 ^ 1))) h4
    rw [eq_natCast, eq_natCast] at h5
    push_cast at h5
    exact h5

include hg hn hqn hodd in
/-- **`p^k = 4`, `N ≡ 1 (mod 4)`**: the converse of Theorem (9.3). -/
theorem exists_dvd_sub_zP_pow_k2_one (hpk : 2 ^ 2 ∣ q - 1) (hn4 : N % 4 = 1) :
    ∃ h < 2 ^ 2, ((N : ℕ) : CR q 2 2) ∣
      jacobiSum (chiR Nat.prime_two hpk hg) (chiR Nat.prime_two hpk hg) ^ ((N - 1) / 2)
        * ((q : ℕ) : CR q 2 2) ^ ((N - 1) / 4) - zP q 2 2 ^ h := by
  have := isDomain_cycM (cr_pos (q := q) (k := 2) Nat.prime_two)
  set χ := chiR Nat.prime_two hpk hg with hχ
  set ψ := psiR q 2 2 Nat.prime_two with hψ
  have hord : orderOf χ = 4 := orderOf_chiR Nat.prime_two hpk hg
  have hψp := psiR_primitive (q := q) (k := 2) Nat.prime_two
  have hord2 : orderOf (χ ^ 2) = 2 := by rw [orderOf_pow, hord]; decide
  have hχ21 : χ ^ 2 ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hord2; omega
  have hsq2 : gaussSum (χ ^ 2) ψ ^ 2 = ((q : ℕ) : CR q 2 2) := by
    rw [gaussSum_sq hχ21 (isQuadratic_of_orderOf hord2) hψp, ZMod.card]
    have hval : (χ ^ 2) (-1) = 1 := by
      rw [MulChar.pow_apply' χ (by norm_num) _, pow_two, chi_neg_one_sq]
    rw [hval, one_mul]
  have h82' : gaussSum (χ ^ 2) ψ * jacobiSum χ χ = gaussSum χ ψ * gaussSum χ ψ := by
    have h := eq_8_2 (p := 2) (k := 2) (χ := χ) (by rw [hord]; norm_num) ψ (a := 1) (b := 1)
      (by norm_num)
    simpa using h
  have hχn : χ ^ N = χ := by
    have h := pow_eq_pow_iff_modEq.mpr
      (show N ≡ 1 [MOD orderOf χ] from by rw [hord]; unfold Nat.ModEq; omega)
    rwa [pow_one] at h
  have hkey : gaussSum χ ψ ^ N
      = gaussSum χ ψ * (jacobiSum χ χ ^ ((N - 1) / 2) * ((q : ℕ) : CR q 2 2) ^ ((N - 1) / 4)) := by
    have h2 : gaussSum (χ ^ 2) ψ ^ ((N - 1) / 2) = ((q : ℕ) : CR q 2 2) ^ ((N - 1) / 4) := by
      rw [show (N - 1) / 2 = 2 * ((N - 1) / 4) from by omega, pow_mul, hsq2]
    conv_lhs => rw [show N = 1 + 2 * ((N - 1) / 2) from by omega]
    rw [pow_add, pow_one, pow_mul, pow_two (gaussSum χ ψ), ← h82', mul_pow, h2]
    ring
  -- the generic converse with `S = {1}`, `ν = 1`, `u = 1`
  have hid : (1 : CR q 2 2) * (jacobiSum χ χ ^ ((N - 1) / 2) * ((q : ℕ) : CR q 2 2) ^ ((N - 1) / 4))
      * ∏ x ∈ ({1} : Finset ℕ), gaussSum (χ ^ (N * x)) ψ ^ (fun _ : ℕ => 1) x
      = (∏ x ∈ ({1} : Finset ℕ), gaussSum (χ ^ x) ψ ^ (fun _ : ℕ => 1) x) ^ N := by
    simp only [Finset.prod_singleton, mul_one, pow_one, one_mul]
    rw [hχn, hkey, mul_comm]
  exact exists_dvd_sub_zP_pow_of_identity Nat.prime_two hpk hg hn hqn (by omega)
    (fun x hx => by
      simp only [Finset.mem_singleton] at hx
      subst hx
      rw [pow_one, ← hχ]
      intro h1; rw [h1, orderOf_one] at hord; omega) ⟨0, (pow_zero _).symm⟩ hid

include hg hn hqn hodd in
/-- **`p^k = 4`, `N ≡ 3 (mod 4)`**: the converse of Theorem (9.5). -/
theorem exists_dvd_sub_zP_pow_k2_three (hpk : 2 ^ 2 ∣ q - 1) (hn4 : N % 4 = 3) :
    ∃ h < 2 ^ 2, ((N : ℕ) : CR q 2 2) ∣
      jacobiSum (chiR Nat.prime_two hpk hg) (chiR Nat.prime_two hpk hg) ^ ((N + 1) / 2)
        * ((q : ℕ) : CR q 2 2) ^ ((N - 3) / 4) - zP q 2 2 ^ h := by
  have := isDomain_cycM (cr_pos (q := q) (k := 2) Nat.prime_two)
  set χ := chiR Nat.prime_two hpk hg with hχ
  set ψ := psiR q 2 2 Nat.prime_two with hψ
  have hord : orderOf χ = 4 := orderOf_chiR Nat.prime_two hpk hg
  have hψp := psiR_primitive (q := q) (k := 2) Nat.prime_two
  have hq0 : ((q : ℕ) : CR q 2 2) ≠ 0 := natCast_q_ne_zero Nat.prime_two
  have hχ1 : χ ≠ 1 := by intro h1; rw [h1, orderOf_one] at hord; omega
  have hord2 : orderOf (χ ^ 2) = 2 := by rw [orderOf_pow, hord]; decide
  have hχ21 : χ ^ 2 ≠ 1 := by intro h1; rw [h1, orderOf_one] at hord2; omega
  have hsq2 : gaussSum (χ ^ 2) ψ ^ 2 = ((q : ℕ) : CR q 2 2) := by
    rw [gaussSum_sq hχ21 (isQuadratic_of_orderOf hord2) hψp, ZMod.card]
    have hval : (χ ^ 2) (-1) = 1 := by
      rw [MulChar.pow_apply' χ (by norm_num) _, pow_two, chi_neg_one_sq]
    rw [hval, one_mul]
  have h82' : gaussSum (χ ^ 2) ψ * jacobiSum χ χ = gaussSum χ ψ * gaussSum χ ψ := by
    have h := eq_8_2 (p := 2) (k := 2) (χ := χ) (by rw [hord]; norm_num) ψ (a := 1) (b := 1)
      (by norm_num)
    simpa using h
  have hχn : χ ^ N = χ ^ 3 := pow_eq_pow_iff_modEq.mpr (by rw [hord]; unfold Nat.ModEq; omega)
  have hinv3 : χ ^ 3 = χ⁻¹ := by
    have h4 : χ ^ 4 = 1 := hord ▸ pow_orderOf_eq_one χ
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact h4
  have h72 : gaussSum χ ψ * gaussSum (χ ^ 3) ψ = χ (-1) * ((q : ℕ) : CR q 2 2) := by
    rw [hinv3]; exact tau_mul_tau_inv hχ1 hψp
  have hn1e : gaussSum χ ψ ^ (N + 1)
      = jacobiSum χ χ ^ ((N + 1) / 2) * ((q : ℕ) : CR q 2 2) ^ ((N + 1) / 4) := by
    have h2 : gaussSum (χ ^ 2) ψ ^ ((N + 1) / 2) = ((q : ℕ) : CR q 2 2) ^ ((N + 1) / 4) := by
      rw [show (N + 1) / 2 = 2 * ((N + 1) / 4) from by omega, pow_mul, hsq2]
    conv_lhs => rw [show N + 1 = 2 * ((N + 1) / 2) from by omega]
    rw [pow_mul, pow_two (gaussSum χ ψ), ← h82', mul_pow, h2]
    ring
  -- `G^N = χ(−1) · X' · G(χ³)` with `X' = J^((N+1)/2) q^((N−3)/4)`, from `q·G^N = …`
  have hmain : gaussSum χ ψ ^ N
      = χ (-1) * (jacobiSum χ χ ^ ((N + 1) / 2) * ((q : ℕ) : CR q 2 2) ^ ((N - 3) / 4))
        * gaussSum (χ ^ 3) ψ := by
    apply mul_left_cancel₀ hq0
    have hneg : χ (-1) * χ (-1) = 1 := chi_neg_one_sq χ
    have hq4 : ((q : ℕ) : CR q 2 2) ^ ((N + 1) / 4)
        = ((q : ℕ) : CR q 2 2) * ((q : ℕ) : CR q 2 2) ^ ((N - 3) / 4) := by
      rw [← pow_succ', show (N - 3) / 4 + 1 = (N + 1) / 4 by omega]
    calc ((q : ℕ) : CR q 2 2) * gaussSum χ ψ ^ N
        = χ (-1) * (χ (-1) * ((q : ℕ) : CR q 2 2)) * gaussSum χ ψ ^ N := by
          rw [← mul_assoc, hneg, one_mul]
      _ = χ (-1) * (gaussSum χ ψ * gaussSum (χ ^ 3) ψ) * gaussSum χ ψ ^ N := by rw [h72]
      _ = χ (-1) * gaussSum χ ψ ^ (N + 1) * gaussSum (χ ^ 3) ψ := by ring
      _ = χ (-1) * (jacobiSum χ χ ^ ((N + 1) / 2) * ((q : ℕ) : CR q 2 2) ^ ((N + 1) / 4))
          * gaussSum (χ ^ 3) ψ := by rw [hn1e]
      _ = _ := by rw [hq4]; ring
  obtain ⟨e, he⟩ := chiR_neg_one_eq_pow Nat.prime_two hpk hg rfl two_pos
  have hid : χ (-1) * (jacobiSum χ χ ^ ((N + 1) / 2) * ((q : ℕ) : CR q 2 2) ^ ((N - 3) / 4))
      * ∏ x ∈ ({1} : Finset ℕ), gaussSum (χ ^ (N * x)) ψ ^ (fun _ : ℕ => 1) x
      = (∏ x ∈ ({1} : Finset ℕ), gaussSum (χ ^ x) ψ ^ (fun _ : ℕ => 1) x) ^ N := by
    simp only [Finset.prod_singleton, mul_one, pow_one]
    rw [hχn, hmain]
  exact exists_dvd_sub_zP_pow_of_identity Nat.prime_two hpk hg hn hqn (by omega)
    (fun x hx => by
      simp only [Finset.mem_singleton] at hx
      subst hx
      rw [pow_one, ← hχ]; exact hχ1) ⟨e, he⟩ hid

variable {k : ℕ} (hk3 : 3 ≤ k) (hpk : 2 ^ k ∣ q - 1)

include hg hn hqn hodd hk3 hpk in
/-- **`p = 2`, `k ≥ 3`, `N ≡ 1, 3 (mod 8)`**: the converse of Theorem (9.10). -/
theorem exists_dvd_sub_zP_pow_k3_low (hn8 : N % 8 = 1 ∨ N % 8 = 3) :
    ∃ h < 2 ^ k, ((N : ℕ) : CR q 2 k) ∣ (∏ x ∈ M2set k,
        (jacobiSum (chiR Nat.prime_two hpk hg ^ minv 2 k x) (chiR Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiR Nat.prime_two hpk hg ^ minv 2 k x)
              (chiR Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc N 2 k x)
      - zP q 2 k ^ h := by
  have := isDomain_cycM (cr_pos (q := q) (k := k) Nat.prime_two)
  have hk : 0 < k := by omega
  set χ := chiR Nat.prime_two hpk hg with hχ
  set ψ := psiR q 2 k Nat.prime_two with hψ
  have hord : orderOf χ = 2 ^ k := orderOf_chiR Nat.prime_two hpk hg
  have hid := jacobi_tau_identity_M2 (ψ := ψ) hk3 hord (psiR_primitive Nat.prime_two)
    (natCast_q_ne_zero Nat.prime_two) hn8 (n := N)
  -- reindex `x ↦ minv x`
  have hre1 : ∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x
      = ∏ y ∈ M2set k, gaussSum (χ ^ y) ψ ^ αc 3 2 k (minv 2 k y) := by
    refine Finset.prod_nbij' (fun x => minv 2 k x) (fun y => minv 2 k y)
      (fun x hx => minv2_mem hk3 hx) (fun y hy => minv2_mem hk3 hy)
      (fun x hx => minv_invol Nat.prime_two hk (M2_subset_Mset hx))
      (fun y hy => minv_invol Nat.prime_two hk (M2_subset_Mset hy)) (fun x hx => ?_)
    rw [minv_invol Nat.prime_two hk (M2_subset_Mset hx)]
  have hre2 : ∏ x ∈ M2set k, gaussSum (χ ^ (N * minv 2 k x)) ψ ^ αc 3 2 k x
      = ∏ y ∈ M2set k, gaussSum (χ ^ (N * y)) ψ ^ αc 3 2 k (minv 2 k y) := by
    refine Finset.prod_nbij' (fun x => minv 2 k x) (fun y => minv 2 k y)
      (fun x hx => minv2_mem hk3 hx) (fun y hy => minv2_mem hk3 hy)
      (fun x hx => minv_invol Nat.prime_two hk (M2_subset_Mset hx))
      (fun y hy => minv_invol Nat.prime_two hk (M2_subset_Mset hy)) (fun x hx => ?_)
    rw [minv_invol Nat.prime_two hk (M2_subset_Mset hx)]
  rw [hre1, hre2] at hid
  refine exists_dvd_sub_zP_pow_of_identity Nat.prime_two hpk hg hn hqn (by omega)
    (S := M2set k) (ν := fun y => αc 3 2 k (minv 2 k y)) (fun y hy h1 => ?_) ⟨0, (pow_zero _).symm⟩
    (by rw [one_mul]; exact hid)
  have hd := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at hd
  exact M2_odd hy ((dvd_pow_self 2 hk.ne').trans hd)

include hg hn hqn hodd hk3 hpk in
/-- **`p = 2`, `k ≥ 3`, `N ≡ 5, 7 (mod 8)`**: the converse of Theorem (9.19). -/
theorem exists_dvd_sub_zP_pow_k3_high (hn8 : N % 8 = 5 ∨ N % 8 = 7) :
    ∃ h < 2 ^ k, ((N : ℕ) : CR q 2 k) ∣ (∏ x ∈ M2set k,
        (jacobiSum (chiR Nat.prime_two hpk hg ^ minv 2 k x) (chiR Nat.prime_two hpk hg ^ minv 2 k x)
          * jacobiSum (chiR Nat.prime_two hpk hg ^ minv 2 k x)
              (chiR Nat.prime_two hpk hg ^ (2 * minv 2 k x))) ^ αc N 2 k x)
        * jacobiSum (chiR Nat.prime_two hpk hg ^ 2 ^ (k - 3))
            ((chiR Nat.prime_two hpk hg ^ 2 ^ (k - 3)) ^ 3) ^ 2
      - zP q 2 k ^ h := by
  have := isDomain_cycM (cr_pos (q := q) (k := k) Nat.prime_two)
  have hk : 0 < k := by omega
  set χ := chiR Nat.prime_two hpk hg with hχ
  set ψ := psiR q 2 k Nat.prime_two with hψ
  have hord : orderOf χ = 2 ^ k := orderOf_chiR Nat.prime_two hpk hg
  have hid := jacobi_tau_identity_M2_neg (ψ := ψ) hk3 hord (psiR_primitive Nat.prime_two)
    (natCast_q_ne_zero Nat.prime_two) hn8 (n := N)
  have hre1 : ∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x
      = ∏ y ∈ M2set k, gaussSum (χ ^ y) ψ ^ αc 3 2 k (minv 2 k y) := by
    refine Finset.prod_nbij' (fun x => minv 2 k x) (fun y => minv 2 k y)
      (fun x hx => minv2_mem hk3 hx) (fun y hy => minv2_mem hk3 hy)
      (fun x hx => minv_invol Nat.prime_two hk (M2_subset_Mset hx))
      (fun y hy => minv_invol Nat.prime_two hk (M2_subset_Mset hy)) (fun x hx => ?_)
    rw [minv_invol Nat.prime_two hk (M2_subset_Mset hx)]
  have hre2 : ∏ x ∈ M2set k, gaussSum (χ ^ (N * minv 2 k x)) ψ ^ αc 3 2 k x
      = ∏ y ∈ M2set k, gaussSum (χ ^ (N * y)) ψ ^ αc 3 2 k (minv 2 k y) := by
    refine Finset.prod_nbij' (fun x => minv 2 k x) (fun y => minv 2 k y)
      (fun x hx => minv2_mem hk3 hx) (fun y hy => minv2_mem hk3 hy)
      (fun x hx => minv_invol Nat.prime_two hk (M2_subset_Mset hx))
      (fun y hy => minv_invol Nat.prime_two hk (M2_subset_Mset hy)) (fun x hx => ?_)
    rw [minv_invol Nat.prime_two hk (M2_subset_Mset hx)]
  rw [hre1, hre2] at hid
  obtain ⟨e, he⟩ := chiR_neg_one_eq_pow Nat.prime_two hpk hg rfl hk
  refine exists_dvd_sub_zP_pow_of_identity Nat.prime_two hpk hg hn hqn (by omega)
    (S := M2set k) (ν := fun y => αc 3 2 k (minv 2 k y)) (fun y hy h1 => ?_)
    ⟨e, he⟩ hid
  have hd := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at hd
  exact M2_odd hy ((dvd_pow_self 2 hk.ne').trans hd)

end TwoComplete

/-! ### Completeness of the computed tests: for prime `n` an `h` is always found -/

section JTestComplete

variable {n : AzNat} [Fact (1 < n.toNat)] {p k q : ℕ} [hqF : Fact q.Prime] (hp : p.Prime)
  (hk : 0 < k) (hpk : p ^ k ∣ q - 1) {gu : (ZMod q)ˣ}
  (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu) {f : ℕ → ℕ}
  (hf : ∀ x ∈ Finset.Icc 1 (q - 2), ((gu : ZMod q)) ^ f x = 1 - ((gu : ZMod q)) ^ x)

include hp hk in
/-- **The kernel**: a congruence `n ∣ W − ζ^h` in `ℤ[ζ_{p^k}]` with `h < p^k` makes
Algorithm (6.2) succeed on the reduction of `W`. -/
theorem findHT_reduce_isSome {W : CycM (p ^ k)} {h : ℕ} (hh : h < p ^ k)
    (hd : ((n.toNat : ℕ) : CycM (p ^ k)) ∣ W - zetaM (p ^ k) ^ h) :
    (AzPolyMod.findHT (AzPolyMod.reduceCycT n p k hp hk W)).isSome = true := by
  refine findHT_complete hp hk hh ?_
  rw [← AzPolyMod.reduceCycT_zetaM n p k hp hk, ← map_pow]
  exact (AzPolyMod.reduceCycT_eq_iff n p k hp hk _ _).mpr hd

include hp hk hpk in
/-- Descent of the common-ring congruence `N ∣ φ(W) − ζ_P^h` to `ℤ[ζ_{p^k}]`. -/
theorem dvd_sub_zetaM_of_phiR {N : ℕ} {W : CycM (p ^ k)} {h : ℕ}
    (hd : ((N : ℕ) : CR q p k) ∣ phiR (q := q) hp W - zP q p k ^ h) :
    ((N : ℕ) : CycM (p ^ k)) ∣ W - zetaM (p ^ k) ^ h := by
  apply natCast_dvd_of_phiR_dvd hp hk hpk
  rwa [map_sub, map_pow, phiR_zetaM]

include hp hk hpk hg hf in
/-- **(i1a)+(i2b) is complete for odd `p`.** -/
theorem jOdd_isSome (hp3 : 2 < p) (hn : n.toNat.Prime) (hqn : ¬ q ∣ n.toNat)
    (hpn : ¬ p ∣ n.toNat) : (jOdd n p k q f).isSome = true := by
  rw [jOdd_eq hp hk hpk hg hf]
  obtain ⟨h, hh, hd⟩ := exists_dvd_sub_zP_pow_odd hp hk hpk hg hp3 hn hqn hpn
  refine findHT_reduce_isSome hp hk hh (dvd_sub_zetaM_of_phiR hp hk hpk ?_)
  rw [map_prod]
  simpa only [map_pow, phiR_jacobiSum] using hd

omit [Fact q.Prime] in
/-- **(i1b) is complete.** -/
theorem j2k1_isSome (hq : q.Prime) (hn : n.toNat.Prime) (hqn : ¬ q ∣ n.toNat)
    (hodd : n.toNat % 2 = 1) : (j2k1 n q).isSome = true := by
  have : Fact q.Prime := ⟨hq⟩
  rw [j2k1_eq]
  obtain ⟨h, hh, hd⟩ := exists_dvd_sub_zetaM_pow_k1 (q := q) hn hqn hodd
  exact findHT_reduce_isSome Nat.prime_two one_pos hh hd

include hg hf in
/-- **(i1c) is complete.** -/
theorem j2k2_isSome (hpk : 2 ^ 2 ∣ q - 1) (hn : n.toNat.Prime) (hqn : ¬ q ∣ n.toNat)
    (hodd : n.toNat % 2 = 1) : (j2k2 n q f).isSome = true := by
  have hJ := phiR_jacobiSum (q := q) Nat.prime_two hpk hg 1 1
  simp only [pow_one] at hJ
  have h4 : n.toNat % 4 = 1 ∨ n.toNat % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · rw [j2k2_eq_one hg hf hpk h4]
    obtain ⟨h, hh, hd⟩ := exists_dvd_sub_zP_pow_k2_one hg hn hqn hodd hpk h4
    refine findHT_reduce_isSome Nat.prime_two two_pos hh
      (dvd_sub_zetaM_of_phiR Nat.prime_two two_pos hpk ?_)
    rwa [map_mul, map_pow, map_pow, map_natCast, hJ]
  · rw [j2k2_eq_three hg hf hpk h4]
    obtain ⟨h, hh, hd⟩ := exists_dvd_sub_zP_pow_k2_three hg hn hqn hodd hpk h4
    refine findHT_reduce_isSome Nat.prime_two two_pos hh
      (dvd_sub_zetaM_of_phiR Nat.prime_two two_pos hpk ?_)
    rwa [map_mul, map_pow, map_pow, map_natCast, hJ]

include hg hf in
/-- **(i1d) is complete.** -/
theorem j2k3_isSome (hk3 : 3 ≤ k) (hpk : 2 ^ k ∣ q - 1) (hn : n.toNat.Prime) (hqn : ¬ q ∣ n.toNat)
    (hodd : n.toNat % 2 = 1) : (j2k3 n k q f).isSome = true := by
  have hk : 0 < k := by omega
  have h8 : (n.toNat % 8 = 1 ∨ n.toNat % 8 = 3) ∨ (n.toNat % 8 = 5 ∨ n.toNat % 8 = 7) := by omega
  rcases h8 with h8 | h8
  · rw [j2k3_eq_low hg hf hpk hk3 h8]
    obtain ⟨h, hh, hd⟩ := exists_dvd_sub_zP_pow_k3_low hg hn hqn hodd hk3 hpk h8
    refine findHT_reduce_isSome Nat.prime_two hk hh (dvd_sub_zetaM_of_phiR Nat.prime_two hk hpk ?_)
    rwa [phiR_prod_M2]
  · rw [j2k3_eq_high hg hf hpk hk3 h8]
    obtain ⟨h, hh, hd⟩ := exists_dvd_sub_zP_pow_k3_high hg hn hqn hodd hk3 hpk h8
    refine findHT_reduce_isSome Nat.prime_two hk hh (dvd_sub_zetaM_of_phiR Nat.prime_two hk hpk ?_)
    rwa [map_mul, phiR_prod_M2, map_pow, ← pow_mul, phiR_jacobiSum, pow_mul]

include hp hk hpk hg hf in
/-- **Completeness of the `(p, q)` Jacobi test**: for prime `n` coprime to `p q`, an `h` is
found. -/
theorem jTest_isSome (hn : n.toNat.Prime) (hqn : ¬ q ∣ n.toNat) (hpn : ¬ p ∣ n.toNat) :
    (jTest n p k q f).isSome = true := by
  unfold jTest
  split_ifs with hp2 hk1 hk2
  · subst hp2 hk1
    exact j2k1_isSome hqF.out hn hqn (Nat.two_dvd_ne_zero.mp hpn)
  · subst hp2 hk2
    exact j2k2_isSome hg hf hpk hn hqn (Nat.two_dvd_ne_zero.mp hpn)
  · subst hp2
    exact j2k3_isSome hg hf (by omega) hpk hn hqn (Nat.two_dvd_ne_zero.mp hpn)
  · exact jOdd_isSome hp hk hpk hg hf (lt_of_le_of_ne hp.two_le (Ne.symm hp2)) hn hqn hpn

omit [Fact q.Prime] in
/-- **The checker's shape**: a certified generator and index table at a prime `q`, and a prime
`p ∣ q − 1`, give a successful `jTest` at `k = v_p(q − 1)` for every prime `n` coprime to `p q`. -/
theorem jTest_isSome_of_checks (hq : q.Prime) (hp : p.Prime) (hpq : p ∣ q - 1) {g : ℕ}
    (hchk : CL.checkGenerator q g = true)
    (hidx : CL.checkIndexTable q g (CL.indexTableOf (CL.indexTableArr q g)) = true)
    (hn : n.toNat.Prime) (hqn : ¬ q ∣ n.toNat) (hpn : ¬ p ∣ n.toNat) :
    (jTest n p (padicValNat p (q - 1)) q (CL.indexTableOf (CL.indexTableArr q g))).isSome = true := by
  have : Fact q.Prime := ⟨hq⟩
  have hq1 : q - 1 ≠ 0 := by have := hq.two_le; omega
  obtain ⟨gu, hgv, hg⟩ := CL.checkGenerator_spec hchk
  have hf := CL.checkIndexTable_spec hidx
  rw [← hgv] at hf
  rw [← Nat.factorization_def _ hp]
  exact jTest_isSome hp (Nat.Prime.factorization_pos_of_dvd hp hq1 hpq) (Nat.ordProj_dvd _ _) hg hf
    hn hqn hpn

end JTestComplete

end APRCL

end Azurite

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_83
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Corollary_4_80

/-!
# BPR Corollary 4.84: the quantitative homogeneous Hilbert's Nullstellensatz

Let `𝒫 = {P₁, …, P_s}` be homogeneous of degrees `dᵢ` bounded by `d`, and `P` homogeneous of
degree `p` vanishing on the common zeros of `𝒫` in `C^k` (`K` of characteristic zero, `C`
algebraically closed, `0 < p`). Then there are `n` and homogeneous `Hᵢ` of degree `cᵢ = np - dᵢ`
with `P^n = ∑ᵢ Hᵢ Pᵢ`, `np = cᵢ + dᵢ`, and `n` bounded by `(2(max d p + 1))^{2^{k+1}}`.

This is the degree-tracking form of Corollary 4.80: the exponent `n` is now explicitly bounded,
via Theorem 4.83 (the quantitative Nullstellensatz) in place of Theorem 4.78. The `Hᵢ` are, as in
4.80, the degree-`np` homogeneous components of the coefficients in the (ordinary) combination
`P^{n₀} = ∑ Bᵢ Pᵢ`, with `n = max(n₀, sup dᵢ)`.

## On the bound

BPR's stated bound is `(2d)^{2^{k+1}}` — *independent of* `p = deg P`. We obtain
`(2(max d p + 1))^{2^{k+1}}`, which depends on `p`. The discrepancy is genuine, not a looseness in
this proof: the route BPR cites (Theorem 4.83 applied to `P`, then the proof of Corollary 4.80)
must run Theorem 4.83 with the degree bound `max d p`, since Theorem 4.83 requires every input —
including `P` — to have degree at most its parameter, and `deg P = p` is unbounded here. (The
`d → d+1` shift is the usual Rabinowitsch-variable overhead from Theorem 4.83.)

A `p`-independent exponent `n` is *true* (it equals a uniform `M` with `(√Ideal(𝒫))^M ⊆
Ideal(𝒫)`, which exists by Noetherianity and depends only on `𝒫`), but a `p`-independent
*explicit bound* `(2d)^{2^{k+1}}` requires effective control of the generator degrees of
`√Ideal(𝒫)` (equivalently, an effective uniform `(√I)^M ⊆ I` bound, or effective Noether
normalization with a rank bound together with the resolution of `K[Y]`-torsion in `K[X]/I`). None
of that effective commutative algebra is currently available, so we record the `p`-dependent
bound, which is exactly the content of the cited proof.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {K : Type*} [Field K]

/-- **BPR Corollary 4.84 (Quantitative homogeneous Hilbert's Nullstellensatz).** For homogeneous
`Pᵢ` of degree `degᵢ ≤ d` and homogeneous `P` of degree `p > 0` vanishing on their common zeros in
`C^k`, there are `n ≤ (2(max d p + 1))^{2^{k+1}}` and homogeneous `Hᵢ` of degree `np − degᵢ` with
`np = (np − degᵢ) + degᵢ` and `P^n = ∑ᵢ Hᵢ Pᵢ`. -/
theorem corollary_4_84 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    {k s : ℕ} (d : ℕ) (Ps : Fin s → MvPolynomial (Fin k) K) (deg : Fin s → ℕ)
    (hPshom : ∀ i, (Ps i).IsHomogeneous (deg i)) (hdeg : ∀ i, deg i ≤ d)
    (P : MvPolynomial (Fin k) K) (p : ℕ) (hp : 0 < p) (hPhom : P.IsHomogeneous p)
    (hvanish : ∀ x : Fin k → C, (∀ i, MvPolynomial.aeval x (Ps i) = 0) →
      MvPolynomial.aeval x P = 0) :
    ∃ (n : ℕ) (H : Fin s → MvPolynomial (Fin k) K),
      n ≤ (2 * (max d p + 1)) ^ (2 ^ (k + 1)) ∧
        (∀ i, (H i).IsHomogeneous (n * p - deg i)) ∧ (∀ i, deg i ≤ n * p) ∧
          P ^ n = ∑ i, H i * Ps i := by
  classical
  set D : ℕ := max d p with hD
  set Pset : Finset (MvPolynomial (Fin k) K) := Finset.univ.image Ps with hPset
  -- `P` vanishes on `Zer(Pset)`.
  have hvanish' : ∀ x ∈ zerOfFinset C Pset, MvPolynomial.aeval x P = 0 := by
    intro x hx
    exact hvanish x fun i =>
      hx (Ps i) (by rw [hPset]; exact Finset.mem_image_of_mem Ps (Finset.mem_univ i))
  -- Degree bounds: every member of `Pset` and `P` have total degree `≤ D`.
  have htd_le : ∀ {Q : MvPolynomial (Fin k) K} {e : ℕ}, Q.IsHomogeneous e → Q.totalDegree ≤ e := by
    intro Q e hQ
    by_cases hQ0 : Q = 0
    · rw [hQ0, totalDegree_zero]; exact Nat.zero_le _
    · exact le_of_eq (hQ.totalDegree hQ0)
  have hPsD : ∀ Q ∈ Pset, Q.totalDegree ≤ D := by
    intro Q hQ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
    exact le_trans (htd_le (hPshom i)) (le_trans (hdeg i) (le_max_left _ _))
  have hPD : P.totalDegree ≤ D := le_trans (htd_le hPhom) (le_max_right _ _)
  -- Quantitative Nullstellensatz: `P^{n₀} = ∑ B Q · Q` with `n₀ ≤ (2(D+1))^{2^{k+1}}`.
  obtain ⟨n₀, B, hn₀bd, _hBdeg, hBsum⟩ := theorem_4_83 (C := C) D Pset P hPsD hPD hvanish'
  -- Hence `P^{n₀} ∈ Ideal(Pset)`.
  have hn₀ : P ^ n₀ ∈ idealOfPolys Pset := by
    rw [hBsum, idealOfPolys]
    exact Ideal.sum_mem _ fun Q hQ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr hQ))
  -- Rewrite as the span of the range and extract the indexed combination.
  have hcoe : (↑Pset : Set (MvPolynomial (Fin k) K)) = Set.range Ps := by
    rw [hPset, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [idealOfPolys, hcoe] at hn₀
  obtain ⟨B', hB'⟩ := Ideal.mem_span_range_iff_exists_fun.mp hn₀
  have hB2 : ∑ i, B' i * Ps i = P ^ n₀ := by simpa [smul_eq_mul] using hB'
  -- Choose `n` large: `n ≥ n₀` and `n * p ≥ degᵢ`.
  set n : ℕ := max n₀ (Finset.univ.sup deg) with hn
  have hn₀le : n₀ ≤ n := le_max_left _ _
  have hd' : ∀ i, deg i ≤ n * p := fun i =>
    le_trans (le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _))
      (Nat.le_mul_of_pos_right n hp)
  -- `P^n = ∑ (P^{n-n₀} B'ᵢ) Pᵢ`.
  set B'' : Fin s → MvPolynomial (Fin k) K := fun i => P ^ (n - n₀) * B' i with hB''
  have hsum : P ^ n = ∑ i, B'' i * Ps i := by
    have hpow : P ^ n = P ^ (n - n₀) * P ^ n₀ := by rw [← pow_add, Nat.sub_add_cancel hn₀le]
    rw [hpow, ← hB2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hB'']; ring
  -- The bound on `n`.
  have hdD : d ≤ D := le_max_left d p
  have hnbd : n ≤ (2 * (D + 1)) ^ (2 ^ (k + 1)) := by
    refine max_le hn₀bd (Finset.sup_le fun i _ => ?_)
    -- `degᵢ ≤ d ≤ D < 2(D+1) ≤ (2(D+1))^{2^{k+1}}`.
    calc deg i ≤ 2 * (D + 1) := by have := hdeg i; omega
      _ ≤ (2 * (D + 1)) ^ (2 ^ (k + 1)) :=
          Nat.le_self_pow (by positivity : (0 : ℕ) < 2 ^ (k + 1)).ne' _
  -- The homogeneous components.
  refine ⟨n, fun i => homogeneousComponent (n * p - deg i) (B'' i), hnbd, fun i => ?_, hd', ?_⟩
  · exact homogeneousComponent_isHomogeneous _ _
  · -- `P^n` is its own degree-`np` component; project the sum.
    have hLHS : homogeneousComponent (n * p) (P ^ n) = P ^ n := by
      have hPn : (P ^ n).IsHomogeneous (n * p) := by rw [mul_comm]; exact hPhom.pow n
      rw [homogeneousComponent_of_mem hPn, ite_eq_left rfl]
    calc P ^ n = homogeneousComponent (n * p) (P ^ n) := hLHS.symm
      _ = homogeneousComponent (n * p) (∑ i, B'' i * Ps i) := by rw [hsum]
      _ = ∑ i, homogeneousComponent (n * p) (B'' i * Ps i) := by rw [map_sum]
      _ = ∑ i, homogeneousComponent (n * p - deg i) (B'' i) * Ps i :=
          Finset.sum_congr rfl fun i _ =>
            homogeneousComponent_mul_homogeneous (hPshom i) (n * p) (hd' i) (B'' i)

end Azurite.BPR.Chapter4

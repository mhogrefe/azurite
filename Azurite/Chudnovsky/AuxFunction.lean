/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Schwarz
import Azurite.Chudnovsky.Bounds

/-!
# The auxiliary function and its analytic estimates

`PhiC L Lc c z = ∑_{i,j,k < Lc} c i j k (2z)^i ℘(z)^j (2ζ(z))^k`.

* Pole cancelling: with `poleE S z = ∏_{l ∈ S} (z − l)` for a finite set `S` of lattice points,
  `poleE² ℘` and `poleE ζ` extend holomorphically to the complement of the other lattice points
  (`exists_pExt`, `exists_qExt`), hence so does `poleE^(3 Lc) · PhiC` (`exists_psi`).
* `schwarz_PhiC`: for the lattice `ℤ + ℤτ`, if `PhiC` vanishes to order `N` at the points of
  `Z`, then `PhiC` is small at points away from the lattice.
* `cauchy_PhiC`: the resulting bound for the derivatives at the points `1/2 + m + nτ`.
-/

namespace Azurite.Chudnovsky

open Complex Set Metric Filter Topology UpperHalfPlane

variable (L : PeriodPair)

/-- `∏_{l ∈ S} (z − l)`. -/
noncomputable def poleE (S : Finset ℂ) (z : ℂ) : ℂ := ∏ l ∈ S, (z - l)

theorem differentiable_poleE (S : Finset ℂ) : Differentiable ℂ (poleE S) := by
  unfold poleE
  fun_prop

theorem norm_poleE_le {S : Finset ℂ} {z : ℂ} {X : ℝ} (h : ∀ l ∈ S, ‖z - l‖ ≤ X) :
    ‖poleE S z‖ ≤ X ^ S.card := by
  rw [poleE, norm_prod]
  calc ∏ l ∈ S, ‖z - l‖ ≤ ∏ _l ∈ S, X :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) h
    _ = X ^ S.card := by rw [Finset.prod_const]

theorem le_norm_poleE {S : Finset ℂ} {z : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (h : ∀ l ∈ S, δ ≤ ‖z - l‖) :
    δ ^ S.card ≤ ‖poleE S z‖ := by
  rw [poleE, norm_prod]
  calc δ ^ S.card = ∏ _l ∈ S, δ := by rw [Finset.prod_const]
    _ ≤ ∏ l ∈ S, ‖z - l‖ := Finset.prod_le_prod₀ (fun _ _ => hδ) h

/-- `poleE² ℘` extends holomorphically across the points of `S`. -/
theorem exists_pExt (S : Finset ℂ) (hS : ∀ s ∈ S, s ∈ L.lattice) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F ((L.lattice : Set ℂ) \ S)ᶜ ∧
      ∀ z, z ∉ L.lattice → F z = poleE S z ^ 2 * L.weierstrassP z := by
  classical
  have key : ∃ F : ℂ → ℂ, DifferentiableOn ℂ F ((L.lattice : Set ℂ) \ S)ᶜ ∧
      ∀ z, z ∉ S → F z = poleE S z ^ 2 * L.weierstrassP z := by
    refine exists_extension (f := fun z => poleE S z ^ 2 * L.weierstrassP z) S ?_ ?_
    · intro z hzV hzS
      have hzL : z ∉ L.lattice := fun h => hzV ⟨h, by simpa using hzS⟩
      have h1 := L.differentiableOn_weierstrassP.differentiableAt
        (L.isClosed_lattice.isOpen_compl.mem_nhds hzL)
      have h2 := (differentiable_poleE S).differentiableAt (x := z)
      exact (h2.pow 2).mul h1
    · intro s hs
      refine ⟨fun z => poleE (S.erase s) z ^ 2
        * ((z - s) ^ 2 * (L.weierstrassPExcept s z - 1 / s ^ 2) + 1), ?_, ?_⟩
      · have h1 : DifferentiableAt ℂ (L.weierstrassPExcept s) s :=
          (L.differentiableOn_weierstrassPExcept s).differentiableAt
            (L.isOpen_compl_lattice_sdiff.mem_nhds (by simp))
        have h2 := (differentiable_poleE (S.erase s)).differentiableAt (x := s)
        fun_prop
      · refine eventually_nhdsWithin_of_forall fun z hz => ?_
        have hzs : z - s ≠ 0 := sub_ne_zero.mpr hz
        have hE : poleE S z = (z - s) * poleE (S.erase s) z :=
          (Finset.mul_prod_erase S (fun l => z - l) hs).symm
        have hP := L.weierstrassPExcept_add ⟨s, hS s hs⟩ z
        simp only at hP
        show poleE S z ^ 2 * L.weierstrassP z = _
        rw [hE, ← hP]
        field_simp
        ring
  obtain ⟨F, hF, hFeq⟩ := key
  exact ⟨F, hF, fun z hz => hFeq z fun h => hz (hS z h)⟩

/-- `poleE ζ` extends holomorphically across the points of `S`. -/
theorem exists_qExt (S : Finset ℂ) (hS : ∀ s ∈ S, s ∈ L.lattice) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F ((L.lattice : Set ℂ) \ S)ᶜ ∧
      ∀ z, z ∉ L.lattice → F z = poleE S z * weierstrassZeta L z := by
  classical
  have key : ∃ F : ℂ → ℂ, DifferentiableOn ℂ F ((L.lattice : Set ℂ) \ S)ᶜ ∧
      ∀ z, z ∉ S → F z = poleE S z * weierstrassZeta L z := by
    refine exists_extension (f := fun z => poleE S z * weierstrassZeta L z) S ?_ ?_
    · intro z hzV hzS
      have hzL : z ∉ L.lattice := fun h => hzV ⟨h, by simpa using hzS⟩
      have h1 := (differentiableOn_weierstrassZeta L).differentiableAt
        (L.isClosed_lattice.isOpen_compl.mem_nhds hzL)
      have h2 := (differentiable_poleE S).differentiableAt (x := z)
      exact h2.mul h1
    · intro s hs
      refine ⟨fun z => poleE (S.erase s) z
        * ((z - s) * (zetaExcept L s z + 1 / s + z / s ^ 2) + 1), ?_, ?_⟩
      · have h1 : DifferentiableAt ℂ (zetaExcept L s) s :=
          (differentiableOn_zetaExcept L s).differentiableAt
            (L.isOpen_compl_lattice_sdiff.mem_nhds (by simp))
        have h2 := (differentiable_poleE (S.erase s)).differentiableAt (x := s)
        fun_prop
      · refine eventually_nhdsWithin_of_forall fun z hz => ?_
        have hzs : z - s ≠ 0 := sub_ne_zero.mpr hz
        have hE : poleE S z = (z - s) * poleE (S.erase s) z :=
          (Finset.mul_prod_erase S (fun l => z - l) hs).symm
        have hP := zetaExcept_add L ⟨s, hS s hs⟩ z
        simp only [zetaTerm] at hP
        show poleE S z * weierstrassZeta L z = _
        rw [hE, ← hP]
        field_simp
        ring
  obtain ⟨F, hF, hFeq⟩ := key
  exact ⟨F, hF, fun z hz => hFeq z fun h => hz (hS z h)⟩

/-- The auxiliary function `∑ c i j k (2z)^i ℘(z)^j (2ζ(z))^k`. -/
noncomputable def PhiC (Lc : ℕ) (c : ℕ → ℕ → ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range Lc, ∑ j ∈ Finset.range Lc, ∑ k ∈ Finset.range Lc,
    c i j k * (2 * z) ^ i * L.weierstrassP z ^ j * (2 * weierstrassZeta L z) ^ k

theorem differentiableOn_PhiC (Lc : ℕ) (c : ℕ → ℕ → ℕ → ℂ) :
    DifferentiableOn ℂ (PhiC L Lc c) (L.lattice : Set ℂ)ᶜ := by
  have h1 := L.differentiableOn_weierstrassP
  have h2 := differentiableOn_weierstrassZeta L
  unfold PhiC
  fun_prop

/-- `poleE^(3 Lc) · PhiC` extends holomorphically across the points of `S`. -/
theorem exists_psi (S : Finset ℂ) (hS : ∀ s ∈ S, s ∈ L.lattice) (Lc : ℕ)
    (c : ℕ → ℕ → ℕ → ℂ) :
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ ((L.lattice : Set ℂ) \ S)ᶜ ∧
      ∀ z, z ∉ L.lattice → Ψ z = poleE S z ^ (3 * Lc) * PhiC L Lc c z := by
  obtain ⟨P, hP, hPeq⟩ := exists_pExt L S hS
  obtain ⟨Q, hQ, hQeq⟩ := exists_qExt L S hS
  have hE : DifferentiableOn ℂ (poleE S) ((L.lattice : Set ℂ) \ S)ᶜ :=
    (differentiable_poleE S).differentiableOn
  refine ⟨fun z => ∑ i ∈ Finset.range Lc, ∑ j ∈ Finset.range Lc, ∑ k ∈ Finset.range Lc,
    c i j k * (2 * z) ^ i * P z ^ j * (2 * Q z) ^ k * poleE S z ^ (3 * Lc - 2 * j - k), ?_, ?_⟩
  · fun_prop
  · intro z hz
    simp only [PhiC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun k hk => ?_
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have e : poleE S z ^ (3 * Lc)
        = poleE S z ^ (2 * j) * poleE S z ^ k * poleE S z ^ (3 * Lc - 2 * j - k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [hPeq z hz, hQeq z hz, e, pow_mul]
    ring

theorem norm_PhiC_le (Lc : ℕ) (c : ℕ → ℕ → ℕ → ℂ) {A₀ X Y W : ℝ} (hA : ∀ i j k, ‖c i j k‖ ≤ A₀)
    {z : ℂ} (hX1 : 1 ≤ X) (hY1 : 1 ≤ Y) (hW1 : 1 ≤ W) (hX : ‖2 * z‖ ≤ X)
    (hY : ‖L.weierstrassP z‖ ≤ Y) (hW : ‖2 * weierstrassZeta L z‖ ≤ W) :
    ‖PhiC L Lc c z‖ ≤ Lc ^ 3 * (A₀ * (X * Y * W) ^ Lc) := by
  have hA0 : 0 ≤ A₀ := (norm_nonneg _).trans (hA 0 0 0)
  unfold PhiC
  calc _ ≤ ∑ _i ∈ Finset.range Lc, ∑ _j ∈ Finset.range Lc, ∑ _k ∈ Finset.range Lc,
        A₀ * (X * Y * W) ^ Lc := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)))
        have hi' := (Finset.mem_range.mp hi).le
        have hj' := (Finset.mem_range.mp hj).le
        have hk' := (Finset.mem_range.mp hk).le
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, mul_pow, mul_pow]
        have h1 : ‖2 * z‖ ^ i ≤ X ^ Lc :=
          (pow_le_pow_left₀ (norm_nonneg _) hX i).trans (pow_le_pow_right₀ hX1 hi')
        have h2 : ‖L.weierstrassP z‖ ^ j ≤ Y ^ Lc :=
          (pow_le_pow_left₀ (norm_nonneg _) hY j).trans (pow_le_pow_right₀ hY1 hj')
        have h3 : ‖2 * weierstrassZeta L z‖ ^ k ≤ W ^ Lc :=
          (pow_le_pow_left₀ (norm_nonneg _) hW k).trans (pow_le_pow_right₀ hW1 hk')
        calc ‖c i j k‖ * ‖2 * z‖ ^ i * ‖L.weierstrassP z‖ ^ j * ‖2 * weierstrassZeta L z‖ ^ k
            ≤ A₀ * X ^ Lc * Y ^ Lc * W ^ Lc := by gcongr; exact hA i j k
          _ = A₀ * (X ^ Lc * Y ^ Lc * W ^ Lc) := by ring
    _ = Lc ^ 3 * (A₀ * (X * Y * W) ^ Lc) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- Zeros of `PhiC` are zeros of its pole-free multiple. -/
theorem order_psi {S : Finset ℂ} {Lc : ℕ} {c : ℕ → ℕ → ℕ → ℂ} {Ψ : ℂ → ℂ}
    (hΨ : ∀ z, z ∉ L.lattice → Ψ z = poleE S z ^ (3 * Lc) * PhiC L Lc c z) {b : ℂ}
    (hb : b ∉ L.lattice) {N : ℕ} (h : ∀ ν < N, iteratedDeriv ν (PhiC L Lc c) b = 0) :
    (N : ℕ∞) ≤ analyticOrderAt Ψ b := by
  have hU := L.isClosed_lattice.isOpen_compl.mem_nhds hb
  have hΦ : AnalyticAt ℂ (PhiC L Lc c) b := (differentiableOn_PhiC L Lc c).analyticAt hU
  have hE : AnalyticAt ℂ (fun z => poleE S z ^ (3 * Lc)) b :=
    ((differentiable_poleE S).pow _).analyticAt b
  have hev : Ψ =ᶠ[𝓝 b] (fun z => poleE S z ^ (3 * Lc)) * PhiC L Lc c := by
    filter_upwards [hU] with z hz
    exact hΨ z hz
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hE hΦ]
  exact le_add_left ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hΦ).mpr h)

variable {τ : ℍ}

/-- **The Schwarz step.**  If `PhiC` vanishes to order `N` at the points of `Z` (of norm
`≤ r₀`), then at a point `z` of norm `≤ r₁` away from the lattice it is small: the gain is
`((r₀ + r₁)/(K/4))^(N |Z|)`, for the parallelogram of size `K ≥ 4 max(r₀, r₁) + 1`. -/
theorem schwarz_PhiC (hn : ‖(τ : ℂ)‖ = 1) (hr : |(τ : ℂ).re| ≤ 1 / 2) {C₁ C₂ : ℝ}
    (hC₁ : ∀ z, Far τ z → ‖(pairOf τ).weierstrassP z‖ ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ z, Far τ z → ‖weierstrassZeta (pairOf τ) z‖ ≤ C₂ * (1 + ‖z‖)) (Lc : ℕ)
    (c : ℕ → ℕ → ℕ → ℂ) {A₀ : ℝ} (hA : ∀ i j k, ‖c i j k‖ ≤ A₀) (Z : Finset ℂ) (N : ℕ)
    {r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀)
    (hZ : ∀ b ∈ Z, b ∉ (pairOf τ).lattice ∧ ‖b‖ ≤ r₀ ∧
      ∀ ν < N, iteratedDeriv ν (PhiC (pairOf τ) Lc c) b = 0)
    (K : ℕ) (hK0 : 4 * r₀ + 1 ≤ K) (hK1 : 4 * r₁ ≤ K) {z : ℂ} (hz : Far τ z)
    (hzr : ‖z‖ ≤ r₁) :
    ‖PhiC (pairOf τ) Lc c z‖ * ((K : ℝ) / 4) ^ (N * Z.card)
      ≤ (r₀ + r₁) ^ (N * Z.card) * ((16 * (K : ℝ) + 4) ^ ((2 * K + 1) ^ 2 * (3 * Lc))
        * (Lc ^ 3 * (A₀ * ((4 * K + 2) * max 1 C₁ * max 1 (4 * C₂ * (K + 1))) ^ Lc))) := by
  set L := pairOf τ with hL
  set S := latS τ K with hSdef
  have hS : ∀ s ∈ S, s ∈ L.lattice := fun s hs => latS_subset_lattice hs
  obtain ⟨Ψ, hΨd, hΨeq⟩ := exists_psi L S hS Lc c
  have hA0 : 0 ≤ A₀ := (norm_nonneg _).trans (hA 0 0 0)
  have hK1' : (1 : ℝ) ≤ K := by linarith
  have hKpos : (0 : ℝ) < (K : ℝ) / 4 := by linarith
  have hr₁ : 0 ≤ r₁ := (norm_nonneg z).trans hzr
  set e := (2 * K + 1) ^ 2 * (3 * Lc) with he
  set B : ℝ := (4 * K + 2) * max 1 C₁ * max 1 (4 * C₂ * (K + 1)) with hB
  have hcard : S.card ≤ (2 * K + 1) ^ 2 := card_latS_le τ K
  -- the bound on the frontier
  have hM : ∀ w ∈ frontier (Upar τ K),
      ‖Ψ w‖ ≤ (4 * (K : ℝ) + 1) ^ e * (Lc ^ 3 * (A₀ * B ^ Lc)) := by
    intro w hw
    have hfar : Far τ w := far_of_frontier hn hr hw
    have hwn : ‖w‖ ≤ 2 * K + 1 := norm_le_of_mem_Ucl hn (frontier_Upar hw).1
    rw [hΨeq w hfar.notMem, norm_mul, norm_pow]
    have hE : ‖poleE S w‖ ≤ (4 * (K : ℝ) + 1) ^ (2 * K + 1) ^ 2 := by
      refine (norm_poleE_le (X := 4 * (K : ℝ) + 1) fun l hl => ?_).trans
        (pow_le_pow_right₀ (by linarith) hcard)
      have := norm_le_of_mem_latS hn hl
      linarith [norm_sub_le w l]
    have hΦ : ‖PhiC L Lc c w‖ ≤ Lc ^ 3 * (A₀ * B ^ Lc) := by
      refine norm_PhiC_le L Lc c hA (by linarith) (le_max_left _ _) (le_max_left _ _) ?_
        ((hC₁ w hfar).trans (le_max_right _ _)) ?_
      · rw [norm_mul, Complex.norm_ofNat]
        linarith
      · rw [norm_mul, Complex.norm_ofNat]
        refine le_trans ?_ (le_max_right _ _)
        have := hC₂ w hfar
        nlinarith
    calc ‖poleE S w‖ ^ (3 * Lc) * ‖PhiC L Lc c w‖
        ≤ ((4 * (K : ℝ) + 1) ^ (2 * K + 1) ^ 2) ^ (3 * Lc) * (Lc ^ 3 * (A₀ * B ^ Lc)) := by
          gcongr
      _ = (4 * (K : ℝ) + 1) ^ e * (Lc ^ 3 * (A₀ * B ^ Lc)) := by rw [← pow_mul]
  have hdist : ∀ w ∈ frontier (Upar τ K), ∀ b ∈ Z, (K : ℝ) / 4 ≤ ‖w - b‖ := by
    intro w hw b hb
    have h1 := norm_ge_of_frontier hn hr hw
    have h2 := (hZ b hb).2.1
    have h3 := norm_sub_norm_le w b
    linarith
  have hzU : z ∈ closure (Upar τ K) := by
    refine subset_closure ⟨?_, ?_⟩
    · have := abs_coA_le hn hr z
      linarith
    · have := abs_coB_le hn hr z
      linarith
  have hsch := norm_le_of_zeros_finset (isBounded_Upar hn K) L.isOpen_compl_lattice_sdiff
    (closure_Upar_subset_compl K) hΨd Z N (fun b hb h => (hZ b hb).1 h.1)
    (fun b hb => order_psi L hΨeq (hZ b hb).1 (hZ b hb).2.2) hKpos hM hdist hzU
  -- from `Ψ` back to `PhiC`
  have hprod : (∏ b ∈ Z, ‖z - b‖) ^ N ≤ (r₀ + r₁) ^ (N * Z.card) := by
    rw [mul_comm N, pow_mul]
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_ N
    calc ∏ b ∈ Z, ‖z - b‖ ≤ ∏ _b ∈ Z, (r₀ + r₁) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun b hb => by
            have := (hZ b hb).2.1
            linarith [norm_sub_le z b]
      _ = (r₀ + r₁) ^ Z.card := by rw [Finset.prod_const]
  have hElow : ((1 : ℝ) / 4) ^ e ≤ ‖poleE S z‖ ^ (3 * Lc) := by
    have h1 : ((1 : ℝ) / 4) ^ S.card ≤ ‖poleE S z‖ :=
      le_norm_poleE (by norm_num) fun l hl => hz l (hS l hl)
    have h2 : ((1 : ℝ) / 4) ^ (2 * K + 1) ^ 2 ≤ (1 / 4) ^ S.card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
    calc ((1 : ℝ) / 4) ^ e = (((1 : ℝ) / 4) ^ (2 * K + 1) ^ 2) ^ (3 * Lc) := by rw [← pow_mul]
      _ ≤ ‖poleE S z‖ ^ (3 * Lc) := pow_le_pow_left₀ (by positivity) (h2.trans h1) _
  rw [hΨeq z hz.notMem, norm_mul, norm_pow] at hsch
  have hM0 : 0 ≤ (4 * (K : ℝ) + 1) ^ e * (Lc ^ 3 * (A₀ * B ^ Lc)) := by positivity
  have h4 : (0 : ℝ) < (4 : ℝ) ^ e := by positivity
  have key : (1 / 4 : ℝ) ^ e * (‖PhiC L Lc c z‖ * ((K : ℝ) / 4) ^ (N * Z.card))
      ≤ (r₀ + r₁) ^ (N * Z.card) * ((4 * (K : ℝ) + 1) ^ e * (Lc ^ 3 * (A₀ * B ^ Lc))) := by
    calc (1 / 4 : ℝ) ^ e * (‖PhiC L Lc c z‖ * ((K : ℝ) / 4) ^ (N * Z.card))
        ≤ ‖poleE S z‖ ^ (3 * Lc) * (‖PhiC L Lc c z‖ * ((K : ℝ) / 4) ^ (N * Z.card)) :=
          mul_le_mul_of_nonneg_right hElow (by positivity)
      _ = ‖poleE S z‖ ^ (3 * Lc) * ‖PhiC L Lc c z‖ * ((K : ℝ) / 4) ^ (N * Z.card) := by ring
      _ ≤ (∏ b ∈ Z, ‖z - b‖) ^ N * ((4 * (K : ℝ) + 1) ^ e * (Lc ^ 3 * (A₀ * B ^ Lc))) := hsch
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod hM0
  have h16 : (16 * (K : ℝ) + 4) ^ e = 4 ^ e * (4 * (K : ℝ) + 1) ^ e := by
    rw [← mul_pow]
    congr 1
    ring
  rw [h16]
  have hquarter : (1 / 4 : ℝ) ^ e * 4 ^ e = 1 := by
    rw [← mul_pow]
    norm_num
  calc ‖PhiC L Lc c z‖ * ((K : ℝ) / 4) ^ (N * Z.card)
      = 4 ^ e * ((1 / 4 : ℝ) ^ e * (‖PhiC L Lc c z‖ * ((K : ℝ) / 4) ^ (N * Z.card))) := by
        rw [← mul_assoc, mul_comm ((4 : ℝ) ^ e), hquarter, one_mul]
    _ ≤ 4 ^ e * ((r₀ + r₁) ^ (N * Z.card)
          * ((4 * (K : ℝ) + 1) ^ e * (Lc ^ 3 * (A₀ * B ^ Lc)))) :=
        mul_le_mul_of_nonneg_left key h4.le
    _ = _ := by ring

/-- The points `1/2 + m + nτ` are at distance `≥ 3/8` from the lattice. -/
theorem half_far (hn : ‖(τ : ℂ)‖ = 1) (hr : |(τ : ℂ).re| ≤ 1 / 2) (m n : ℤ) :
    ∀ l ∈ (pairOf τ).lattice, 3 / 8 ≤ ‖(1 / 2 + m + n * τ : ℂ) - l‖ := by
  intro l hl
  obtain ⟨m', n', rfl⟩ := mem_lattice_pairOf.mp hl
  have hr2 : (τ : ℂ).re ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hr
    nlinarith
  set a : ℝ := 1 / 2 + (m - m') with ha
  set b : ℝ := n - n' with hb
  have heq : (1 / 2 + m + n * τ : ℂ) - (m' + n' * τ) = (a : ℂ) + b * τ := by
    rw [ha, hb]
    push_cast
    ring
  have hsq := norm_sq_coord hn a b
  have ha2 : 1 / 4 ≤ a ^ 2 := by
    have h1 : (1 : ℝ) ≤ ((1 + 2 * (m - m') : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ (1 + 2 * (m - m')) ^ 2 := by
        have h0 : (1 + 2 * (m - m') : ℤ) ≠ 0 := by omega
        have := Int.one_le_abs h0
        nlinarith [sq_abs (1 + 2 * (m - m') : ℤ), abs_nonneg (1 + 2 * (m - m') : ℤ)]
      exact_mod_cast this
    have h2 : ((1 + 2 * (m - m') : ℤ) : ℝ) = 2 * a := by
      rw [ha]
      push_cast
      ring
    rw [h2] at h1
    nlinarith
  rw [heq]
  by_contra hlt
  push Not at hlt
  have h0 := norm_nonneg ((a : ℂ) + b * τ)
  have : ‖(a : ℂ) + b * τ‖ ^ 2 < (3 / 8) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (b + (τ : ℂ).re * a), sq_nonneg a]

theorem far_of_near {w z : ℂ} (hw : ∀ l ∈ (pairOf τ).lattice, 3 / 8 ≤ ‖w - l‖)
    (hz : ‖z - w‖ ≤ 1 / 8) : Far τ z := fun l hl => by
  have h1 := hw l hl
  have h2 : ‖w - l‖ ≤ ‖z - l‖ + ‖z - w‖ := by
    have := norm_sub_le (z - l) (z - w)
    rwa [sub_sub_sub_cancel_left] at this
  linarith

/-- **The Cauchy step**: the derivatives of `PhiC` at a point `w` at distance `≥ 3/8` from
the lattice, under the hypotheses of `schwarz_PhiC`. -/
theorem cauchy_PhiC (hn : ‖(τ : ℂ)‖ = 1) (hr : |(τ : ℂ).re| ≤ 1 / 2) {C₁ C₂ : ℝ}
    (hC₁ : ∀ z, Far τ z → ‖(pairOf τ).weierstrassP z‖ ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ z, Far τ z → ‖weierstrassZeta (pairOf τ) z‖ ≤ C₂ * (1 + ‖z‖)) (Lc : ℕ)
    (c : ℕ → ℕ → ℕ → ℂ) {A₀ : ℝ} (hA : ∀ i j k, ‖c i j k‖ ≤ A₀) (Z : Finset ℂ) (N : ℕ)
    {r₀ r₁ : ℝ} (hr₀ : 0 ≤ r₀)
    (hZ : ∀ b ∈ Z, b ∉ (pairOf τ).lattice ∧ ‖b‖ ≤ r₀ ∧
      ∀ ν < N, iteratedDeriv ν (PhiC (pairOf τ) Lc c) b = 0)
    (K : ℕ) (hK0 : 4 * r₀ + 1 ≤ K) (hK1 : 4 * r₁ ≤ K) {w : ℂ}
    (hw : ∀ l ∈ (pairOf τ).lattice, 3 / 8 ≤ ‖w - l‖) (hwr : ‖w‖ + 1 / 8 ≤ r₁) (n : ℕ) :
    ‖iteratedDeriv n (PhiC (pairOf τ) Lc c) w‖ * ((K : ℝ) / 4) ^ (N * Z.card)
      ≤ n.factorial * 8 ^ n * ((r₀ + r₁) ^ (N * Z.card)
        * ((16 * (K : ℝ) + 4) ^ ((2 * K + 1) ^ 2 * (3 * Lc))
        * (Lc ^ 3 * (A₀ * ((4 * K + 2) * max 1 C₁ * max 1 (4 * C₂ * (K + 1))) ^ Lc)))) := by
  set G : ℝ := (r₀ + r₁) ^ (N * Z.card) * ((16 * (K : ℝ) + 4) ^ ((2 * K + 1) ^ 2 * (3 * Lc))
        * (Lc ^ 3 * (A₀ * ((4 * K + 2) * max 1 C₁ * max 1 (4 * C₂ * (K + 1))) ^ Lc))) with hG
  have hKpos : (0 : ℝ) < (K : ℝ) / 4 := by linarith
  have hd : (0 : ℝ) < ((K : ℝ) / 4) ^ (N * Z.card) := by positivity
  have hsph : ∀ z ∈ sphere w (1 / 8 : ℝ),
      ‖PhiC (pairOf τ) Lc c z‖ ≤ G / ((K : ℝ) / 4) ^ (N * Z.card) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hfar : Far τ z := far_of_near hw hz.le
    have hzr : ‖z‖ ≤ r₁ := by
      have := norm_sub_norm_le z w
      linarith
    rw [le_div_iff₀ hd]
    exact schwarz_PhiC hn hr hC₁ hC₂0 hC₂ Lc c hA Z N hr₀ hZ K hK0 hK1 hfar hzr
  have hsub : closedBall w (1 / 8 : ℝ) ⊆ ((pairOf τ).lattice : Set ℂ)ᶜ := fun z hz =>
    (far_of_near hw (mem_closedBall_iff_norm.mp hz)).notMem
  have hdc : DiffContOnCl ℂ (PhiC (pairOf τ) Lc c) (ball w (1 / 8 : ℝ)) :=
    ⟨(differentiableOn_PhiC _ Lc c).mono (ball_subset_closedBall.trans hsub),
      (differentiableOn_PhiC _ Lc c).continuousOn.mono
        (closure_ball_subset_closedBall.trans hsub)⟩
  have hc := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) hdc hsph
  calc ‖iteratedDeriv n (PhiC (pairOf τ) Lc c) w‖ * ((K : ℝ) / 4) ^ (N * Z.card)
      ≤ n.factorial * (G / ((K : ℝ) / 4) ^ (N * Z.card)) / (1 / 8) ^ n
        * ((K : ℝ) / 4) ^ (N * Z.card) := mul_le_mul_of_nonneg_right hc hd.le
    _ = n.factorial * 8 ^ n * G := by
        have h8 : ((1 : ℝ) / 8) ^ n * 8 ^ n = 1 := by
          rw [← mul_pow]
          norm_num
        have h8' : (1 : ℝ) / (1 / 8) ^ n = 8 ^ n := by
          rw [one_div_pow, one_div_one_div]
        have hne := hd.ne'
        rw [div_eq_mul_one_div _ (((1 : ℝ) / 8) ^ n), h8']
        field_simp

end Azurite.Chudnovsky

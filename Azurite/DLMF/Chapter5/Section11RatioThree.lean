/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Ratio
import Azurite.DLMF.Chapter5.Section11BoydRem

/-!
# DLMF 5.11.19: `Γ(z + a)Γ(z + b)/Γ(z + c)`

Formalization of <https://dlmf.nist.gov/5.11.E19>: as `z → ∞` in `|ph z| ≤ π − δ`,
`Γ(z + a)Γ(z + b)/Γ(z + c) ∼ ∑_{k≥0} (−1)ᵏ (c − a)ₖ (c − b)ₖ/k! · Γ(a + b − c + z − k)`,
a generalized asymptotic expansion with the scale `Γ(a + b − c + z − k)` (`dlmf_5_11_19`).

With `w = z + a + b − c`, `α = c − b`, `β = c − a`, the left side is `Γ(w) P(w)`,
`P(w) = Γ(w + α)Γ(w + β)/(Γ(w + α + β)Γ(w))`, and `Γ(w − k) = Γ(w)/(w − 1)^{↓k}`, so the claim is
`P(w) − ∑_{k<n} tₖ/(w − 1)^{↓k} = O(w^{−n})`, `tₖ = (−1)ᵏ(α)ₖ(β)ₖ/k!`:

* by 5.11.13 twice, `P ∼ A(1/w)` with `A = (∑ Gₖ(α, α + β)Xᵏ)(∑ Gₖ(β, 0)Xᵏ)`
  (`hasPowExpansion_gammaP`);
* `1/(w − 1)^{↓k} ∼ Eₖ(1/w)`, `Eₖ = Xᵏ ∏_{j<k}(1 − (j + 1)X)⁻¹`, so the partial sums have the
  expansions `Bₙ = ∑_{k<n} tₖ Eₖ` (`hasPowExpansion_invFacSum`);
* `A ≡ Bₙ mod Xⁿ` (`coeff_gammaP_eq`): both coefficients are polynomials in `β`; for `β = −m`,
  `P(w) = (w + α − 1)^{↓m}/(w − 1)^{↓m} = ∑_{k≤m} tₖ/(w − 1)^{↓k}` exactly, by the Chu–Vandermonde
  identity `∑ (m choose k)(α)ₖ (u − k)^{↓(m−k)} = (u + α)^{↓m}` (`sum_choose_rise_fall`), and
  uniqueness of expansions along `w → +∞` gives `A = B_{m+1}`.
-/

open Complex Filter Topology Set Asymptotics PowerSeries
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Falling and rising factorials -/

theorem descPochhammer_smeval_int (k : ℕ) (r : ℂ) :
    (descPochhammer ℤ k).smeval r = (descPochhammer ℂ k).eval r := by
  rw [← descPochhammer_map (Int.castRingHom ℂ), Polynomial.eval_map,
    ← Polynomial.aeval_eq_smeval]
  rfl

/-- Chu–Vandermonde: `(x + y)^{↓m} = ∑ (m choose k) x^{↓k} y^{↓(m−k)}`. -/
theorem descPochhammer_eval_add (m : ℕ) (x y : ℂ) :
    (descPochhammer ℂ m).eval (x + y) = ∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℂ) * ((descPochhammer ℂ k).eval x * (descPochhammer ℂ (m - k)).eval y) := by
  have h := Ring.descPochhammer_smeval_add (R := ℂ) m (Commute.all x y)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [descPochhammer_smeval_int] at h
  exact h

theorem descPochhammer_reflect (n : ℕ) (r : ℂ) :
    (descPochhammer ℂ n).eval r = (-1) ^ n * (descPochhammer ℂ n).eval ((n : ℂ) - 1 - r) := by
  rw [descPochhammer_eval_eq_ascPochhammer, show r - n + 1 = -((n : ℂ) - 1 - r) by ring,
    ascPochhammer_eval_neg_eq_descPochhammer]

theorem ascPochhammer_eq_desc (k : ℕ) (α : ℂ) :
    (ascPochhammer ℂ k).eval α = (-1) ^ k * (descPochhammer ℂ k).eval (-α) := by
  rw [← ascPochhammer_eval_neg_eq_descPochhammer, neg_neg]

theorem neg_one_pow_mul_self (m : ℕ) : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- `∑_{k≤m} (m choose k)(α)ₖ (u − k)^{↓(m−k)} = (u + α)^{↓m}`. -/
theorem sum_choose_rise_fall (m : ℕ) (α u : ℂ) :
    ∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * (ascPochhammer ℂ k).eval α *
      (descPochhammer ℂ (m - k)).eval (u - k) = (descPochhammer ℂ m).eval (u + α) := by
  have hterm : ∀ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * (ascPochhammer ℂ k).eval α *
      (descPochhammer ℂ (m - k)).eval (u - k) = (-1) ^ m * ((m.choose k : ℂ) *
        ((descPochhammer ℂ k).eval (-α) *
          (descPochhammer ℂ (m - k)).eval ((m : ℂ) - 1 - u))) := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [ascPochhammer_eq_desc, descPochhammer_reflect (m - k) (u - k),
      show (((m - k : ℕ) : ℂ) - 1 - (u - k)) = (m : ℂ) - 1 - u by push_cast [hk']; ring]
    have : (-1 : ℂ) ^ m = (-1) ^ k * (-1) ^ (m - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hk']
    rw [this]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← descPochhammer_eval_add,
    descPochhammer_reflect m (-α + ((m : ℂ) - 1 - u)),
    show (m : ℂ) - 1 - (-α + ((m : ℂ) - 1 - u)) = u + α by ring, ← mul_assoc,
    neg_one_pow_mul_self, one_mul]

theorem descPochhammer_eval_add_split (k l : ℕ) (u : ℂ) :
    (descPochhammer ℂ (k + l)).eval u =
      (descPochhammer ℂ k).eval u * (descPochhammer ℂ l).eval (u - k) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [← add_assoc, descPochhammer_succ_eval, ih, descPochhammer_succ_eval]
    push_cast
    ring

/-! ### The coefficients `tₖ = (−1)ᵏ(α)ₖ(β)ₖ/k!` -/

/-- `tₖ(α, β) = (−1)ᵏ (α)ₖ (β)ₖ/k!`. -/
noncomputable def invFacCoeff (α β : ℂ) (k : ℕ) : ℂ :=
  (-1) ^ k * ((ascPochhammer ℂ k).eval α * (ascPochhammer ℂ k).eval β) / (k ! : ℂ)

theorem invFacCoeff_neg_nat (α : ℂ) (m k : ℕ) :
    invFacCoeff α (-(m : ℂ)) k = (m.choose k : ℂ) * (ascPochhammer ℂ k).eval α := by
  rw [invFacCoeff, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  push_cast
  rw [show ∀ A B : ℂ, (-1) ^ k * (A * ((-1) ^ k * B)) = ((-1) ^ k * (-1) ^ k) * (A * B) from
    fun A B => by ring, neg_one_pow_mul_self, one_mul]
  field_simp

theorem invFacCoeff_neg_nat_of_lt (α : ℂ) {m k : ℕ} (h : m < k) :
    invFacCoeff α (-(m : ℂ)) k = 0 := by
  rw [invFacCoeff, ascPochhammer_eval_neg_coe_nat_of_lt h]; simp

/-- At `β = −m`: `∑_{k≤m} tₖ/(w − 1)^{↓k} = (w + α − 1)^{↓m}/(w − 1)^{↓m}`. -/
theorem sum_invFacCoeff_div (α w : ℂ) (m : ℕ) (hD : (descPochhammer ℂ m).eval (w - 1) ≠ 0) :
    ∑ k ∈ Finset.range (m + 1), invFacCoeff α (-(m : ℂ)) k / (descPochhammer ℂ k).eval (w - 1) =
      (descPochhammer ℂ m).eval (w - 1 + α) / (descPochhammer ℂ m).eval (w - 1) := by
  rw [eq_div_iff hD, Finset.sum_mul, ← sum_choose_rise_fall]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsplit := descPochhammer_eval_add_split k (m - k) (w - 1)
  rw [Nat.add_sub_cancel' hk'] at hsplit
  have hDk : (descPochhammer ℂ k).eval (w - 1) ≠ 0 := by
    intro h0; rw [hsplit, h0, zero_mul] at hD; exact hD rfl
  rw [invFacCoeff_neg_nat, hsplit]
  field_simp

/-! ### The inverse factorial series -/

/-- `∏_{j<k} (1 − (j + 1)X)`. -/
noncomputable def invFacPoly (k : ℕ) : Polynomial ℂ :=
  ∏ j ∈ Finset.range k, (1 - Polynomial.C ((j : ℂ) + 1) * Polynomial.X)

/-- `Eₖ = Xᵏ ∏_{j<k}(1 − (j + 1)X)⁻¹`, the expansion of `1/(w − 1)^{↓k}` in `1/w`. -/
noncomputable def invFacTerm (k : ℕ) : ℂ⟦X⟧ := X ^ k * ((invFacPoly k : ℂ⟦X⟧))⁻¹

/-- `Bₙ = ∑_{k<n} tₖ Eₖ`. -/
noncomputable def invFacSeries (α β : ℂ) (n : ℕ) : ℂ⟦X⟧ :=
  ∑ k ∈ Finset.range n, C (invFacCoeff α β k) * invFacTerm k

theorem coeff_invFacTerm_of_lt {j k : ℕ} (h : j < k) : coeff j (invFacTerm k) = 0 := by
  rw [invFacTerm, coeff_X_pow_mul', ite_eq_right (by omega)]

theorem coeff_invFacSeries_stable (α β : ℂ) {j n : ℕ} (h : j < n) :
    coeff j (invFacSeries α β n) = coeff j (invFacSeries α β (j + 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · rw [invFacSeries, Finset.sum_range_succ, map_add, coeff_C_mul,
        coeff_invFacTerm_of_lt h', mul_zero, add_zero, ← invFacSeries, ih h']
    · rfl

theorem invFacSeries_neg_nat (α : ℂ) {m N : ℕ} (h : m + 1 ≤ N) :
    invFacSeries α (-(m : ℂ)) N = invFacSeries α (-(m : ℂ)) (m + 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_iff.mpr h) with h' | h'
    · rw [invFacSeries, Finset.sum_range_succ, invFacCoeff_neg_nat_of_lt α (by omega), map_zero,
        zero_mul, add_zero, ← invFacSeries, ih (by omega)]
    · rw [h']

/-! ### Polynomiality in `β` -/

theorem IsPolyFun.comp' {g : ℂ → ℂ} (hg : IsPolyFun g) (P : Polynomial ℂ) :
    IsPolyFun fun z => P.eval (g z) := by
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P.comp Q, fun z => by simp [hQ]⟩

theorem isPolyFun_genBernoulli {g h : ℂ → ℂ} (hg : IsPolyFun g) (hh : IsPolyFun h) (k : ℕ) :
    IsPolyFun fun z => genBernoulli (g z) (h z) k := by
  unfold genBernoulli
  refine (isPolyFun_const _).mul (isPolyFun_cSeriesExp (fun s => ?_) k)
  unfold genBernoulliSeq
  refine (hg.mul (isPolyFun_const _)).add ?_
  by_cases hs : s = 1
  · simpa [hs] using hh
  · simpa [hs] using isPolyFun_const 0

theorem isPolyFun_ratioG {g h : ℂ → ℂ} (hg : IsPolyFun g) (hh : IsPolyFun h) (k : ℕ) :
    IsPolyFun fun z => ratioG (g z) (h z) k := by
  unfold ratioG cBinom
  simp only [div_eq_mul_inv]
  exact ((hg.sub hh).comp' _ |>.mul (isPolyFun_const _)).mul
    (isPolyFun_genBernoulli ((hg.sub hh).add (isPolyFun_const 1)) hg k)

/-- `A(α, β) = (∑ Gₖ(α, α + β)Xᵏ)(∑ Gₖ(β, 0)Xᵏ)`. -/
noncomputable def gammaPSeries (α β : ℂ) : ℂ⟦X⟧ := mk (ratioG α (α + β)) * mk (ratioG β 0)

theorem isPolyFun_coeff_gammaPSeries (α : ℂ) (j : ℕ) :
    IsPolyFun fun β => coeff j (gammaPSeries α β) := by
  simp only [gammaPSeries, coeff_mul, coeff_mk]
  exact isPolyFun_sum _ fun i _ =>
    (isPolyFun_ratioG (isPolyFun_const α) ((isPolyFun_const α).add isPolyFun_id) _).mul
      (isPolyFun_ratioG isPolyFun_id (isPolyFun_const 0) _)

theorem isPolyFun_coeff_invFacSeries (α : ℂ) (n j : ℕ) :
    IsPolyFun fun β => coeff j (invFacSeries α β n) := by
  simp only [invFacSeries, map_sum, coeff_C_mul, invFacCoeff, div_eq_mul_inv]
  exact isPolyFun_sum _ fun k _ =>
    (((isPolyFun_const _).mul ((isPolyFun_const _).mul (isPolyFun_id.comp' _))).mul
      (isPolyFun_const _)).mul (isPolyFun_const _)

/-! ### Expansions in `1/w` -/

/-- `P(w) = Γ(w + α)Γ(w + β)/(Γ(w + α + β)Γ(w))`. -/
noncomputable def gammaP (α β w : ℂ) : ℂ :=
  Gamma (w + α) * Gamma (w + β) / (Gamma (w + α + β) * Gamma w)

/-- `∑_{k<n} tₖ/(w − 1)^{↓k}`. -/
noncomputable def invFacSum (α β : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, invFacCoeff α β k / (descPochhammer ℂ k).eval (w - 1)

theorem hasPowExpansion_gammaP (α β : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    HasPowExpansion (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))) (fun w => w⁻¹)
      (gammaP α β) (gammaPSeries α β) := by
  have h1 := isAsympExpansionDLMF_iff.mp (dlmf_5_11_13 α (α + β) hδ hδπ)
  have h2 := isAsympExpansionDLMF_iff.mp (dlmf_5_11_13 β 0 hδ hδπ)
  have h := h1.mul (tendsto_inv_atInf _) h2
  refine h.congr' ?_
  filter_upwards [eventually_ne_zero_atInf (closedSectorDLMF 0 (π - δ))] with w hw
  have hc : w ^ β ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  simp only [Pi.mul_apply, gammaP, add_zero, sub_zero]
  rw [show α - (α + β) = -β by ring, cpow_neg, ← add_assoc]
  rw [show ∀ A B C D E : ℂ, A / B / E⁻¹ * (C / D / E) = A * C / (B * D) * (E * E⁻¹) from
    fun A B C D E => by rw [div_inv_eq_mul]; ring, mul_inv_cancel₀ hc, mul_one]

theorem descPochhammer_eval_sub_one_eq (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (descPochhammer ℂ k).eval (w - 1) = w ^ k * (invFacPoly k).eval w⁻¹ := by
  induction k with
  | zero => simp [invFacPoly]
  | succ k ih =>
    rw [descPochhammer_succ_eval, ih]
    simp only [invFacPoly, Finset.prod_range_succ, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X]
    field_simp
    ring

theorem constantCoeff_invFacPoly (k : ℕ) : constantCoeff ((invFacPoly k : ℂ⟦X⟧)) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  simp [invFacPoly, Polynomial.eval_prod]

theorem hasPowExpansion_inv_descPochhammer (k : ℕ) {l : Filter ℂ}
    (hy : Tendsto (fun w : ℂ => w⁻¹) l (𝓝 0)) (h0 : ∀ᶠ w in l, w ≠ 0) :
    HasPowExpansion l (fun w => w⁻¹) (fun w => ((descPochhammer ℂ k).eval (w - 1))⁻¹)
      (invFacTerm k) := by
  have hX := (hasPowExpansion_id hy).pow hy k
  have hQ := (hasPowExpansion_polynomial hy (invFacPoly k)).inv hy
    (by rw [constantCoeff_invFacPoly]; exact one_ne_zero)
  refine (hX.mul hy hQ).congr' ?_
  filter_upwards [h0] with w hw
  rw [descPochhammer_eval_sub_one_eq k hw, mul_inv]
  simp only [Pi.mul_apply, inv_pow]

theorem hasPowExpansion_invFacSum (α β : ℂ) (n : ℕ) {l : Filter ℂ}
    (hy : Tendsto (fun w : ℂ => w⁻¹) l (𝓝 0)) (h0 : ∀ᶠ w in l, w ≠ 0) :
    HasPowExpansion l (fun w => w⁻¹) (invFacSum α β n) (invFacSeries α β n) := by
  induction n with
  | zero =>
    have := hasPowExpansion_const hy (0 : ℂ)
    have e : invFacSeries α β 0 = C 0 := by simp [invFacSeries]
    rw [e]
    exact this.congr' (Eventually.of_forall fun w => by simp [invFacSum])
  | succ n ih =>
    have h := ih.add ((hasPowExpansion_inv_descPochhammer n hy h0).const_mul (invFacCoeff α β n))
    rw [invFacSeries, Finset.sum_range_succ, ← invFacSeries]
    refine h.congr' (Eventually.of_forall fun w => ?_)
    simp [invFacSum, Finset.sum_range_succ, div_eq_mul_inv]

/-! ### The exact case `β = −m` -/

theorem Gamma_eq_descPochhammer_mul (x : ℂ) (m : ℕ) (h : ∀ j < m, x - 1 - j ≠ 0) :
    Gamma x = (descPochhammer ℂ m).eval (x - 1) * Gamma (x - m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih (fun j hj => h j (by omega)), descPochhammer_succ_eval]
    have := Complex.Gamma_add_one (x - 1 - m) (h m (by omega))
    rw [show x - 1 - (m : ℂ) + 1 = x - m by ring] at this
    rw [this]
    push_cast
    ring_nf

theorem gammaP_neg_nat_eq (α : ℂ) (m : ℕ) {w : ℂ} (hw : (m : ℝ) + ‖α‖ + 1 < w.re) :
    gammaP α (-(m : ℂ)) w = invFacSum α (-(m : ℂ)) (m + 1) w := by
  have hα := abs_re_le_norm α
  have hpos : ∀ x : ℂ, (m : ℝ) < x.re → ∀ j : ℕ, j ≤ m → 0 < (x - j).re := by
    intro x hx j hj
    have : (j : ℝ) ≤ m := by exact_mod_cast hj
    simp only [sub_re, natCast_re]
    linarith [norm_nonneg α]
  have hcond : ∀ x : ℂ, (m : ℝ) < x.re → ∀ j < m, x - 1 - j ≠ 0 := by
    intro x hx j hj h0
    have := hpos x hx (j + 1) hj
    rw [show x - 1 - (j : ℂ) = x - ((j + 1 : ℕ) : ℂ) by push_cast; ring, h0] at *
    simp at this
  have hwa : (m : ℝ) < (w + α).re := by simp; linarith [abs_le.mp hα]
  have hw' : (m : ℝ) < w.re := by linarith [norm_nonneg α]
  have h1 := Gamma_eq_descPochhammer_mul (w + α) m (hcond _ hwa)
  have h2 := Gamma_eq_descPochhammer_mul w m (hcond _ hw')
  have hG1 : Gamma (w + α - m) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (hpos _ hwa m le_rfl)
  have hG2 : Gamma (w - m) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (hpos _ hw' m le_rfl)
  have hGw : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith [norm_nonneg α])
  have hD : (descPochhammer ℂ m).eval (w - 1) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h2; exact hGw h2
  rw [invFacSum, sum_invFacCoeff_div α w m hD, gammaP, show w + α + -(m : ℂ) = w + α - m by ring,
    show w + -(m : ℂ) = w - m by ring, h1, h2, show w + α - 1 = w - 1 + α by ring]
  field_simp

theorem gammaPSeries_neg_nat (α : ℂ) (m : ℕ) :
    gammaPSeries α (-(m : ℂ)) = invFacSeries α (-(m : ℂ)) (m + 1) := by
  set X0 := closedSectorDLMF 0 (π - π)
  have := atInf_neBot not_isBounded_closedSector_zero
  have hy := tendsto_inv_atInf X0
  have h0 := eventually_ne_zero_atInf X0
  have hP := hasPowExpansion_gammaP α (-(m : ℂ)) Real.pi_pos le_rfl
  have hS := hasPowExpansion_invFacSum α (-(m : ℂ)) (m + 1) hy h0
  have hbig : ∀ᶠ w in Bornology.cobounded ℂ ⊓ 𝓟 X0, (m : ℝ) + ‖α‖ + 1 < ‖w‖ :=
    (tendsto_norm_cobounded_atTop.eventually_gt_atTop _).filter_mono inf_le_left
  have hS' : HasPowExpansion (Bornology.cobounded ℂ ⊓ 𝓟 X0) (fun w => w⁻¹)
      (gammaP α (-(m : ℂ))) (invFacSeries α (-(m : ℂ)) (m + 1)) := by
    refine hS.congr' ?_
    filter_upwards [hbig, mem_inf_of_right (mem_principal_self X0)] with w hw hX
    obtain ⟨-, -, hnorm⟩ := mem_closedSector_zero hX
    exact (gammaP_neg_nat_eq α m (by rwa [← hnorm])).symm
  exact HasPowExpansion.unique hy (h0.mono fun w hw => inv_ne_zero hw) hP hS'

/-- **The coefficient identity** `A ≡ Bₙ mod Xⁿ`. -/
theorem coeff_gammaP_eq (α β : ℂ) {j n : ℕ} (h : j < n) :
    coeff j (gammaPSeries α β) = coeff j (invFacSeries α β n) := by
  rw [coeff_invFacSeries_stable α β h]
  obtain ⟨P, hP⟩ :=
    (isPolyFun_coeff_gammaPSeries α j).sub (isPolyFun_coeff_invFacSeries α (j + 1) j)
  have hroot : ∀ m : ℕ, P.IsRoot (-(m : ℂ)) := fun m => by
    rw [Polynomial.IsRoot, ← hP]
    dsimp only
    rw [gammaPSeries_neg_nat,
      ← invFacSeries_neg_nat α (show m + 1 ≤ m + j + 1 by omega),
      coeff_invFacSeries_stable α _ (show j < m + j + 1 by omega), sub_self]
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => -(m : ℂ))
      (fun m n h => by simpa using h) hroot
  have := hP β
  rw [hP0, Polynomial.eval_zero, sub_eq_zero] at this
  exact this

theorem isBigO_gammaP_sub (α β : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) (n : ℕ) :
    (fun w => gammaP α β w - invFacSum α β n w) =O[
      Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))] fun w => w⁻¹ ^ n := by
  have hy := tendsto_inv_atInf (closedSectorDLMF 0 (π - δ))
  have h0 := eventually_ne_zero_atInf (closedSectorDLMF 0 (π - δ))
  have hd := ((hasPowExpansion_gammaP α β hδ hδπ).sub (hasPowExpansion_invFacSum α β n hy h0)) n
  have htr : trunc n (gammaPSeries α β - invFacSeries α β n) = 0 := by
    ext j
    rw [coeff_trunc, Polynomial.coeff_zero]
    split_ifs with hj
    · rw [map_sub, coeff_gammaP_eq α β hj, sub_self]
    · rfl
  rw [htr] at hd
  simpa using hd

/-! ### DLMF 5.11.19 -/

theorem sub_nat_ne_neg_nat {w : ℂ} {k : ℕ} (hbig : (k : ℝ) < ‖w‖) (hp : ∀ m : ℕ, w ≠ -m) :
    ∀ m : ℕ, w - k ≠ -m := by
  intro m h
  have hw : w = (k : ℂ) - m := by linear_combination h
  rcases le_or_gt m k with hmk | hmk
  · rw [hw, show (k : ℂ) - m = ((k - m : ℕ) : ℂ) by push_cast [hmk]; ring, Complex.norm_natCast]
      at hbig
    have : ((k - m : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k m
    linarith
  · exact hp (m - k) (by rw [hw]; push_cast [hmk.le]; ring)

theorem eventually_ne_neg_nat {δ : ℝ} (hδ : 0 < δ) (h : ℂ) :
    ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)), ∀ n : ℕ, z + h ≠ -n := by
  filter_upwards [eventually_shift_sector hδ h] with z hz
  obtain ⟨-, h0, -, harg⟩ := hz
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp at hn; exact h0 hn
  · have harg' : arg (-(n : ℂ)) = π := by
      rw [show -(n : ℂ) = ((-(n : ℝ) : ℝ) : ℂ) by push_cast; ring]
      exact arg_ofReal_of_neg (by have : (0 : ℝ) < n := by exact_mod_cast hpos
                                  linarith)
    rw [hn, harg', abs_of_pos Real.pi_pos] at harg
    linarith

/-- **DLMF 5.11.19**: as `z → ∞` in `|ph z| ≤ π − δ`,
`Γ(z + a)Γ(z + b)/Γ(z + c) ∼ ∑_{k≥0} (−1)ᵏ (c − a)ₖ (c − b)ₖ/k! Γ(a + b − c + z − k)`, a
generalized asymptotic expansion (2.1.20–2.1.21) with the scale `Γ(a + b − c + z − k)`. -/
theorem dlmf_5_11_19 (a b c : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)))
      (fun k z => Gamma (a + b - c + z - k))
      (fun z => Gamma (z + a) * Gamma (z + b) / Gamma (z + c))
      (fun k z => (-1) ^ k * ((ascPochhammer ℂ k).eval (c - a) *
        (ascPochhammer ℂ k).eval (c - b)) / (k ! : ℂ) * Gamma (a + b - c + z - k)) := by
  set l := Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))
  set d := a + b - c with hd
  set α := c - b with hα
  set β := c - a with hβ
  have hT := tendsto_shift_sector hδ d
  have hcob : Tendsto (fun z => z + d) l (Bornology.cobounded ℂ) := hT.mono_right inf_le_left
  have hnorm : Tendsto (fun z => ‖z + d‖) l atTop := tendsto_norm_cobounded_atTop.comp hcob
  have hp0 : ∀ᶠ z in l, ∀ m : ℕ, z + d ≠ -m := eventually_ne_neg_nat hδ d
  have hw : ∀ z k, a + b - c + z - (k : ℂ) = z + d - k := fun z k => by rw [hd]; ring
  refine ⟨fun k => ?_, fun n => ?_⟩
  · -- the scale
    have hlim : Tendsto (fun z => (z + d - ((k : ℂ) + 1))⁻¹) l (𝓝 0) := by
      have h1 := tendsto_shift_sector hδ (d - ((k : ℂ) + 1))
      refine (tendsto_inv₀_cobounded.comp (h1.mono_right inf_le_left)).congr fun z => ?_
      simp only [Function.comp_apply]
      ring_nf
    refine hlim.congr' ?_
    filter_upwards [hp0, hnorm.eventually_gt_atTop ((k : ℝ) + 1)] with z hp hbig
    have hk1 := sub_nat_ne_neg_nat (k := k + 1) (by push_cast; exact hbig) hp
    have hne : z + d - ((k : ℂ) + 1) ≠ 0 := by
      have := hk1 0; push_cast at this; simpa using this
    have hG : Gamma (z + d - ((k : ℂ) + 1)) ≠ 0 := Complex.Gamma_ne_zero (by
      intro m; have := hk1 m; push_cast at this; exact this)
    have hrec := Complex.Gamma_add_one _ hne
    have e1 : d + z - ((k + 1 : ℕ) : ℂ) = z + d - ((k : ℂ) + 1) := by push_cast; ring
    have e2 : d + z - (k : ℂ) = z + d - ((k : ℂ) + 1) + 1 := by ring
    show (z + d - ((k : ℂ) + 1))⁻¹ =
      Gamma (d + z - ((k + 1 : ℕ) : ℂ)) / Gamma (d + z - (k : ℂ))
    rw [e1, e2, hrec]
    field_simp
  · -- the bound
    have hO := (isBigO_gammaP_sub α β (half_pos hδ) (by linarith) n).comp_tendsto hT
    obtain ⟨C, hC⟩ := hO.bound
    have hq0 : (invFacPoly n).eval 0 = 1 := by
      unfold invFacPoly; simp [Polynomial.eval_prod]
    have hq : Tendsto (fun z => (invFacPoly n).eval (z + d)⁻¹) l (𝓝 1) := by
      have h0 : Tendsto (fun z => (z + d)⁻¹) l (𝓝 0) := tendsto_inv₀_cobounded.comp hcob
      have := ((invFacPoly n).continuous.tendsto 0).comp h0
      rwa [hq0] at this
    have hq2 : ∀ᶠ z in l, ‖(invFacPoly n).eval (z + d)⁻¹‖ ≤ 2 :=
      (hq.norm.eventually (ge_mem_nhds (by norm_num : ‖(1 : ℂ)‖ < 2)))
    refine isBoundedUnder_of_eventually_le (a := C * 2) ?_
    filter_upwards [hC, hq2, hp0, hnorm.eventually_gt_atTop ((n : ℝ) + 1)] with z h1 h2 hp hbig
    set w := z + d with hwdef
    have hwd : ∀ s : ℕ, d + z - (s : ℂ) = w - s := fun s => by rw [hwdef]; ring
    have hw0 : w ≠ 0 := by have := hp 0; simpa using this
    have hGw : Gamma w ≠ 0 := Complex.Gamma_ne_zero hp
    have hcond : ∀ k ≤ n, ∀ j < k, w - 1 - j ≠ 0 := fun k hk j hj => by
      have hjn : ((j + 1 : ℕ) : ℝ) < ‖w‖ := by
        have : ((j + 1 : ℕ) : ℝ) ≤ n + 1 := by
          exact_mod_cast (show j + 1 ≤ n + 1 by omega)
        linarith
      have := sub_nat_ne_neg_nat hjn hp 0
      rw [show w - 1 - (j : ℂ) = w - ((j + 1 : ℕ) : ℂ) by push_cast; ring]
      simpa using this
    have hGk : ∀ k ≤ n, Gamma (w - k) = Gamma w / (descPochhammer ℂ k).eval (w - 1) ∧
        (descPochhammer ℂ k).eval (w - 1) ≠ 0 := fun k hk => by
      have h := Gamma_eq_descPochhammer_mul w k (hcond k hk)
      have hD : (descPochhammer ℂ k).eval (w - 1) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at h; exact hGw h
      exact ⟨by rw [h]; field_simp, hD⟩
    have hF : Gamma (z + a) * Gamma (z + b) / Gamma (z + c) = Gamma w * gammaP α β w := by
      rw [gammaP, show w + α + β = z + c by rw [hwdef, hd, hα, hβ]; ring,
        show w + α = z + a by rw [hwdef, hd, hα]; ring,
        show w + β = z + b by rw [hwdef, hd, hβ]; ring]
      field_simp
    have hS : ∑ s ∈ Finset.range n, (-1) ^ s * ((ascPochhammer ℂ s).eval β *
        (ascPochhammer ℂ s).eval α) / (s ! : ℂ) * Gamma (d + z - s) =
        Gamma w * invFacSum α β n w := by
      rw [invFacSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := (Finset.mem_range.mp hk).le
      rw [hwd k, (hGk k hk').1, invFacCoeff]
      ring
    rw [hF, hS, hwd n, (hGk n le_rfl).1, ← mul_sub, descPochhammer_eval_sub_one_eq n hw0]
    rw [show Gamma w * (gammaP α β w - invFacSum α β n w) / (Gamma w / (w ^ n *
        (invFacPoly n).eval w⁻¹)) = (gammaP α β w - invFacSum α β n w) * w ^ n *
        (invFacPoly n).eval w⁻¹ by
      have := (hGk n le_rfl).2
      rw [descPochhammer_eval_sub_one_eq n hw0] at this
      field_simp]
    rw [norm_mul, norm_mul, norm_pow]
    have h1' : ‖gammaP α β w - invFacSum α β n w‖ ≤ C * ‖w⁻¹‖ ^ n := by
      simpa [Function.comp_apply, norm_pow] using h1
    rw [norm_inv, inv_pow] at h1'
    have hwn : 0 < ‖w‖ ^ n := pow_pos (norm_pos_iff.mpr hw0) n
    have hnn : 0 ≤ C * (‖w‖ ^ n)⁻¹ * ‖w‖ ^ n := mul_nonneg ((norm_nonneg _).trans h1') hwn.le
    calc ‖gammaP α β w - invFacSum α β n w‖ * ‖w‖ ^ n * ‖(invFacPoly n).eval w⁻¹‖
        ≤ (C * (‖w‖ ^ n)⁻¹) * ‖w‖ ^ n * 2 := by gcongr
      _ = C * 2 := by field_simp

end Azurite.DLMF

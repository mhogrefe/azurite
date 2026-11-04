/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5ComplexGauss

/-!
# DLMF §3.5(viii): Table 3.5.18 (5-point complex Gauss formula, `s = 1`)

All entries of Table 3.5.18 are certified by exact Gaussian-rational arithmetic in the kernel.

* For `s = 1`, `n = 5`: the nodes are the zeros of `ζ⁵ − 25ζ⁴ + 300ζ³ − 2100ζ² + 8400ζ − 15120`
  (`polyPz`, `mem_cgNodes_one_five`), and the weights are `Az(ζ)/Bz(ζ)` (`cgWeight_one_five`).
* Certificates: `exists_root_within` (a zero within `ρ` of `z` when `n|P(z)| ≤ ρ|P′(z)|`, from
  `P′/P = ∑ 1/(z − r)`), Lipschitz bounds on disks (`cEval_lip`, `norm_cEval_le`), and the quotient
  bound `norm_div_sub_div_le`; `cgRowOK_sound` and `cgTableOK_sound` (five disjoint disks give all
  five nodes); `cgTable_nodes` enumerates the nodes with their disks and weights.
* `dlmf_table_3_5_18`; `cgNodes_one_five_re_pos` (positive real parts in this case).
-/

open Polynomial Finset

namespace Azurite.DLMF

/-! ### Gaussian rationals and Horner evaluation -/

/-- Multiplication of Gaussian rationals `(re, im)`. -/
def gMul (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- Division of Gaussian rationals. -/
def gDiv (p q : ℚ × ℚ) : ℚ × ℚ :=
  ((p.1 * q.1 + p.2 * q.2) / (q.1 ^ 2 + q.2 ^ 2), (p.2 * q.1 - p.1 * q.2) / (q.1 ^ 2 + q.2 ^ 2))

/-- Horner evaluation of `∑ cᵢ zⁱ` at a Gaussian rational. -/
def gEval : List ℚ → ℚ × ℚ → ℚ × ℚ
  | [], _ => (0, 0)
  | c :: l, z => (c + (gMul z (gEval l z)).1, (gMul z (gEval l z)).2)

/-- Horner evaluation of `∑ cᵢ zⁱ` at a complex number. -/
noncomputable def cEval : List ℚ → ℂ → ℂ
  | [], _ => 0
  | c :: l, z => (c : ℂ) + z * cEval l z

/-- The complex number `re + i·im`. -/
noncomputable def gToC (p : ℚ × ℚ) : ℂ := ⟨p.1, p.2⟩

theorem gToC_mul (p q : ℚ × ℚ) : gToC (gMul p q) = gToC p * gToC q := by
  apply Complex.ext <;> simp [gToC, gMul]

theorem gToC_div (p q : ℚ × ℚ) : gToC (gDiv p q) = gToC p / gToC q := by
  apply Complex.ext <;> simp [gToC, gDiv, Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    ring

theorem cEval_toC (l : List ℚ) (z : ℚ × ℚ) : cEval l (gToC z) = gToC (gEval l z) := by
  induction l with
  | nil => simp [cEval, gEval, gToC]; rfl
  | cons c l ih =>
    rw [cEval, gEval, ih, ← gToC_mul]
    apply Complex.ext <;> simp [gToC]

theorem sq_norm_toC (p : ℚ × ℚ) : ‖gToC p‖ ^ 2 = ((p.1 ^ 2 + p.2 ^ 2 : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [gToC]; ring

theorem norm_toC_le (p : ℚ × ℚ) : ‖gToC p‖ ≤ ((|p.1| + |p.2| : ℚ) : ℝ) := by
  have := Complex.norm_le_abs_re_add_abs_im (gToC p)
  simpa [gToC] using this

theorem max_le_norm_toC (p : ℚ × ℚ) : ((max |p.1| |p.2| : ℚ) : ℝ) ≤ ‖gToC p‖ := by
  have h1 := Complex.abs_re_le_norm (gToC p)
  have h2 := Complex.abs_im_le_norm (gToC p)
  simp only [gToC] at h1 h2
  push_cast
  exact max_le (by exact_mod_cast h1) (by exact_mod_cast h2)

/-! ### Bounds on a disk -/

/-- `∑ |cᵢ| Rⁱ`. -/
def absR (R : ℚ) : List ℚ → ℚ
  | [] => 0
  | c :: l => |c| + R * absR R l

/-- A Lipschitz constant on `‖z‖ ≤ R`. -/
def lipR (R : ℚ) : List ℚ → ℚ
  | [] => 0
  | _ :: l => R * lipR R l + absR R l

theorem absR_nonneg {R : ℚ} (hR : 0 ≤ R) (l : List ℚ) : 0 ≤ absR R l := by
  induction l with
  | nil => simp [absR]
  | cons c l ih => simp only [absR]; positivity

theorem lipR_nonneg {R : ℚ} (hR : 0 ≤ R) (l : List ℚ) : 0 ≤ lipR R l := by
  induction l with
  | nil => simp [lipR]
  | cons c l ih => simp only [lipR]; have := absR_nonneg hR l; positivity

theorem norm_cEval_le {R : ℚ} (hR : 0 ≤ R) (l : List ℚ) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖cEval l z‖ ≤ absR R l := by
  induction l with
  | nil => simp [cEval, absR]
  | cons c l ih =>
    simp only [cEval, absR]
    push_cast
    calc ‖(c : ℂ) + z * cEval l z‖ ≤ ‖(c : ℂ)‖ + ‖z‖ * ‖cEval l z‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ |(c : ℝ)| + (R : ℝ) * (absR R l : ℝ) := by
          gcongr
          simp

theorem cEval_lip {R : ℚ} (hR : 0 ≤ R) (l : List ℚ) {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖cEval l z - cEval l w‖ ≤ lipR R l * ‖z - w‖ := by
  induction l with
  | nil => simp [cEval, lipR]
  | cons c l ih =>
    simp only [cEval, lipR]
    have hA := norm_cEval_le hR l hw
    push_cast
    calc ‖(c : ℂ) + z * cEval l z - ((c : ℂ) + w * cEval l w)‖
        = ‖z * (cEval l z - cEval l w) + (z - w) * cEval l w‖ := by congr 1; ring
      _ ≤ ‖z‖ * ‖cEval l z - cEval l w‖ + ‖z - w‖ * ‖cEval l w‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
      _ ≤ (R : ℝ) * ((lipR R l : ℝ) * ‖z - w‖) + ‖z - w‖ * (absR R l : ℝ) := by
          gcongr
      _ = _ := by ring

/-! ### A root near an approximate root -/

/-- If `n |P(z)| ≤ ρ |P′(z)|` (`n = deg P ≥ 1`), then `P` has a root within `ρ` of `z`
(from `P′/P = ∑ 1/(z − r)`). -/
theorem exists_root_within {P : ℂ[X]} (hP : P ≠ 0) (hdeg : 1 ≤ P.natDegree) {z : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (h : P.natDegree * ‖P.eval z‖ ≤ ρ * ‖(derivative P).eval z‖) :
    ∃ r ∈ P.roots, ‖z - r‖ ≤ ρ := by
  by_contra hall
  push Not at hall
  have hz : P.eval z ≠ 0 := by
    intro h0
    have := hall z ((mem_roots hP).mpr h0)
    simp at this; linarith
  have hsum := (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hz
  have hcard : Multiset.card P.roots = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hne : P.roots ≠ 0 := by
    intro h0; rw [h0, Multiset.card_zero] at hcard; omega
  have hlt : ‖(derivative P).eval z / P.eval z‖ < P.natDegree * ρ⁻¹ := by
    rw [hsum]
    calc ‖(P.roots.map fun r => 1 / (z - r)).sum‖
        ≤ (P.roots.map fun r => ‖1 / (z - r)‖).sum := by
          simpa [Multiset.map_map] using norm_multiset_sum_le (P.roots.map fun r => 1 / (z - r))
      _ < (P.roots.map fun _ => ρ⁻¹).sum := by
          refine Multiset.sum_lt_sum_of_nonempty hne fun r hr => ?_
          have := hall r hr
          rw [norm_div, norm_one, one_div]
          exact inv_strictAnti₀ hρ this
      _ = P.natDegree * ρ⁻¹ := by
          rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]
  rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hz)] at hlt
  have : ρ * ‖(derivative P).eval z‖ < P.natDegree * ‖P.eval z‖ := by
    calc ρ * ‖(derivative P).eval z‖ < ρ * (P.natDegree * ρ⁻¹ * ‖P.eval z‖) :=
          mul_lt_mul_of_pos_left hlt hρ
      _ = _ := by field_simp
  linarith

/-- A perturbation bound for quotients. -/
theorem norm_div_sub_div_le {A₀ A₁ B₀ B₁ : ℂ} {LA LB a b ρ : ℝ}
    (hA : ‖A₁ - A₀‖ ≤ LA * ρ) (hB : ‖B₁ - B₀‖ ≤ LB * ρ) (ha : ‖A₀‖ ≤ a) (hb : b ≤ ‖B₀‖)
    (hbp : 0 < b - LB * ρ) :
    ‖A₁ / B₁ - A₀ / B₀‖ ≤ LA * ρ / (b - LB * ρ) + a * (LB * ρ) / ((b - LB * ρ) * b) := by
  have hb0 : 0 < b := by nlinarith [norm_nonneg (B₁ - B₀)]
  have hB0 : 0 < ‖B₀‖ := hb0.trans_le hb
  have hB1 : b - LB * ρ ≤ ‖B₁‖ := by
    have := norm_sub_norm_le B₀ B₁
    rw [norm_sub_rev] at hB; linarith
  have hB1p : 0 < ‖B₁‖ := hbp.trans_le hB1
  have hB0' : B₀ ≠ 0 := norm_pos_iff.mp hB0
  have hB1' : B₁ ≠ 0 := norm_pos_iff.mp hB1p
  have e : A₁ / B₁ - A₀ / B₀ = ((A₁ - A₀) * B₀ - A₀ * (B₁ - B₀)) / (B₁ * B₀) := by
    field_simp; ring
  rw [e, norm_div, norm_mul]
  have hnum : ‖(A₁ - A₀) * B₀ - A₀ * (B₁ - B₀)‖ ≤ LA * ρ * ‖B₀‖ + a * (LB * ρ) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
    · exact (norm_nonneg _).trans ha
  have hLA : 0 ≤ LA * ρ := (norm_nonneg _).trans hA
  have hLB : 0 ≤ LB * ρ := (norm_nonneg _).trans hB
  calc ‖(A₁ - A₀) * B₀ - A₀ * (B₁ - B₀)‖ / (‖B₁‖ * ‖B₀‖)
      ≤ (LA * ρ * ‖B₀‖ + a * (LB * ρ)) / (‖B₁‖ * ‖B₀‖) := by gcongr
    _ = LA * ρ / ‖B₁‖ + a * (LB * ρ) / (‖B₁‖ * ‖B₀‖) := by field_simp
    _ ≤ LA * ρ / (b - LB * ρ) + a * (LB * ρ) / ((b - LB * ρ) * b) := by
        have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
        gcongr

/-! ### The case `n = 5`, `s = 1` -/

/-- `ζ⁵ p_5(1/ζ)` for `s = 1`. -/
def lPz : List ℚ := [-15120, 8400, -2100, 300, -25, 1]
def lPz' : List ℚ := [8400, -4200, 900, -100, 5]
/-- `ζ⁴ A(1/ζ)` and `ζ⁴ p_5′(1/ζ)`: the weight is `w = Az(ζ)/Bz(ζ)`. -/
def lAz : List ℚ := [-15120, -6720, -1260, -120, -5]
def lBz : List ℚ := [-75600, 33600, -6300, 600, -25]

/-- The node polynomial `ζ⁵ − 25ζ⁴ + 300ζ³ − 2100ζ² + 8400ζ − 15120`. -/
noncomputable def polyPz : ℂ[X] :=
  X ^ 5 - C 25 * X ^ 4 + C 300 * X ^ 3 - C 2100 * X ^ 2 + C 8400 * X - C 15120

theorem natDegree_polyPz : polyPz.natDegree = 5 := by unfold polyPz; compute_degree!

theorem polyPz_ne_zero : polyPz ≠ 0 := by
  intro h; have := natDegree_polyPz; rw [h, natDegree_zero] at this; omega

theorem eval_polyPz (z : ℂ) : polyPz.eval z = cEval lPz z := by
  simp [polyPz, cEval, lPz]; ring

theorem eval_derivative_polyPz (z : ℂ) : (derivative polyPz).eval z = cEval lPz' z := by
  simp [polyPz, cEval, lPz']; ring

theorem cgMu_one (j : ℕ) : cgMu 1 j = ((j.factorial : ℝ))⁻¹ := by
  rw [cgMu, add_comm, Real.Gamma_nat_eq_factorial]

theorem eval_cgP_one_five (u : ℂ) :
    (cgP 1 5).eval u = 1 - 25 * u + 300 * u ^ 2 - 2100 * u ^ 3 + 8400 * u ^ 4 - 15120 * u ^ 5 := by
  simp [cgP, cgc, sum_range_succ, prod_range_succ, Nat.choose]
  ring

theorem cgP_one_five : cgP 1 5 = 1 - C 25 * X + C 300 * X ^ 2 - C 2100 * X ^ 3 +
    C 8400 * X ^ 4 - C 15120 * X ^ 5 :=
  Polynomial.funext fun u => by rw [eval_cgP_one_five]; simp

theorem eval_derivative_cgP_one_five (u : ℂ) :
    (derivative (cgP 1 5)).eval u =
      -25 + 600 * u - 6300 * u ^ 2 + 33600 * u ^ 3 - 75600 * u ^ 4 := by
  rw [cgP_one_five]
  simp
  ring

theorem cgA_one_five (u : ℂ) :
    cgA 1 5 u = -5 - 120 * u - 1260 * u ^ 2 - 6720 * u ^ 3 - 15120 * u ^ 4 := by
  simp [cgA, cgc, cgMu_one, sum_range_succ, prod_range_succ, Nat.choose, Nat.factorial]
  ring

theorem polyPz_eq (ζ : ℂ) (hζ : ζ ≠ 0) : polyPz.eval ζ = ζ ^ 5 * (cgP 1 5).eval ζ⁻¹ := by
  rw [eval_cgP_one_five]
  simp [polyPz]
  field_simp

theorem mem_cgNodes_one_five {ζ : ℂ} : ζ ∈ cgNodes 1 5 ↔ polyPz.eval ζ = 0 := by
  rw [mem_cgNodes one_pos]
  constructor
  · rintro ⟨h0, h⟩; rw [polyPz_eq ζ h0, h, mul_zero]
  · intro h
    have h0 : ζ ≠ 0 := by rintro rfl; simp [polyPz] at h
    refine ⟨h0, ?_⟩
    rw [polyPz_eq ζ h0] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 5 h0)

theorem cgWeight_one_five {ζ : ℂ} (hζ : ζ ∈ cgNodes 1 5) :
    cgWeight 1 5 ζ = cEval lAz ζ / cEval lBz ζ := by
  have h0 : ζ ≠ 0 := ((mem_cgNodes one_pos).mp hζ).1
  have hu : (cgP 1 5).IsRoot ζ⁻¹ := ((mem_cgNodes one_pos).mp hζ).2
  have hd := cgP_derivative_ne_zero one_pos hu
  rw [cgWeight_eq one_pos hζ, cgA_one_five]
  rw [eval_derivative_cgP_one_five] at hd ⊢
  have hB : cEval lBz ζ ≠ 0 := by
    have e : cEval lBz ζ = ζ ^ 4 * (-25 + 600 * ζ⁻¹ - 6300 * ζ⁻¹ ^ 2 + 33600 * ζ⁻¹ ^ 3 -
        75600 * ζ⁻¹ ^ 4) := by
      simp [cEval, lBz]; field_simp; ring
    rw [e]; exact mul_ne_zero (pow_ne_zero 4 h0) hd
  rw [div_eq_div_iff hd hB]
  simp [cEval, lAz, lBz]
  field_simp
  ring

theorem card_cgNodes {s : ℝ} (hs : 0 < s) (n : ℕ) : #(cgNodes s n) = n := by
  rw [cgNodes, card_image_of_injective _ inv_injective, card_cgNodesU hs]

/-! ### Certified rows -/

/-- A row: an approximation `x + iy` of the node, and the printed `ζ_k` and `w_k` as
`(mantissa, decimals)` for the real and imaginary parts. -/
structure CGRow where
  x : ℚ
  y : ℚ
  Xr : ℤ × ℕ
  Xi : ℤ × ℕ
  Wr : ℤ × ℕ
  Wi : ℤ × ℕ

/-- `|v − M/10^d| ≤ 5/10^{d+1}`: `v` rounds to the printed `M/10^d`. -/
def RoundsTo (v : ℝ) (p : ℤ × ℕ) : Prop := |v - p.1 / 10 ^ p.2| ≤ 5 / 10 ^ (p.2 + 1)

/-- The weight error bound `δ` at the approximation `z̃` for a disk of radius `ρ`. -/
def cgDelta (ρ : ℚ) (z : ℚ × ℚ) : ℚ :=
  let R := |z.1| + |z.2| + ρ
  let A0 := gEval lAz z
  let B0 := gEval lBz z
  let b := max |B0.1| |B0.2|
  lipR R lAz * ρ / (b - lipR R lBz * ρ) +
    (|A0.1| + |A0.2|) * (lipR R lBz * ρ) / ((b - lipR R lBz * ρ) * b)

/-- The exact checks for one row. -/
def cgRowOK (ρ : ℚ) (r : CGRow) : Bool :=
  decide (0 < ρ) &&
    decide (25 * ((gEval lPz (r.x, r.y)).1 ^ 2 + (gEval lPz (r.x, r.y)).2 ^ 2) ≤
      ρ ^ 2 * ((gEval lPz' (r.x, r.y)).1 ^ 2 + (gEval lPz' (r.x, r.y)).2 ^ 2)) &&
    decide (|r.x - (r.Xr.1 : ℚ) / 10 ^ r.Xr.2| + ρ ≤ 5 / 10 ^ (r.Xr.2 + 1)) &&
    decide (|r.y - (r.Xi.1 : ℚ) / 10 ^ r.Xi.2| + ρ ≤ 5 / 10 ^ (r.Xi.2 + 1)) &&
    decide (0 < max |(gEval lBz (r.x, r.y)).1| |(gEval lBz (r.x, r.y)).2| -
      lipR (|r.x| + |r.y| + ρ) lBz * ρ) &&
    decide (|(gDiv (gEval lAz (r.x, r.y)) (gEval lBz (r.x, r.y))).1 - (r.Wr.1 : ℚ) / 10 ^ r.Wr.2| +
      cgDelta ρ (r.x, r.y) ≤ 5 / 10 ^ (r.Wr.2 + 1)) &&
    decide (|(gDiv (gEval lAz (r.x, r.y)) (gEval lBz (r.x, r.y))).2 - (r.Wi.1 : ℚ) / 10 ^ r.Wi.2| +
      cgDelta ρ (r.x, r.y) ≤ 5 / 10 ^ (r.Wi.2 + 1))

theorem roundsTo_of_le {v : ℝ} {q ρ : ℚ} {p : ℤ × ℕ} (hv : |v - q| ≤ ρ)
    (h : |q - (p.1 : ℚ) / 10 ^ p.2| + ρ ≤ 5 / 10 ^ (p.2 + 1)) : RoundsTo v p := by
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  unfold RoundsTo
  calc |v - p.1 / 10 ^ p.2| ≤ |v - q| + |(q : ℝ) - p.1 / 10 ^ p.2| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

theorem cgRowOK_sound {ρ : ℚ} {r : CGRow} (h : cgRowOK ρ r = true) :
    ∃ ζ ∈ cgNodes 1 5, ‖ζ - gToC (r.x, r.y)‖ ≤ ρ ∧ RoundsTo ζ.re r.Xr ∧ RoundsTo ζ.im r.Xi ∧
      RoundsTo (cgWeight 1 5 ζ).re r.Wr ∧ RoundsTo (cgWeight 1 5 ζ).im r.Wi ∧
      ‖cgWeight 1 5 ζ - gToC (gDiv (gEval lAz (r.x, r.y)) (gEval lBz (r.x, r.y)))‖ ≤
        (cgDelta ρ (r.x, r.y) : ℝ) := by
  simp only [cgRowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hρ, hP⟩, hx⟩, hy⟩, hbp⟩, hwr⟩, hwi⟩ := h
  set z := (r.x, r.y)
  have hρr : (0 : ℝ) < ρ := by exact_mod_cast hρ
  -- a root within `ρ`
  have hroot : (polyPz.natDegree : ℝ) * ‖polyPz.eval (gToC z)‖ ≤
      ρ * ‖(derivative polyPz).eval (gToC z)‖ := by
    rw [natDegree_polyPz, eval_polyPz, eval_derivative_polyPz, cEval_toC, cEval_toC]
    have h1 := sq_norm_toC (gEval lPz z)
    have h2 := sq_norm_toC (gEval lPz' z)
    have hsq : ((5 : ℝ) * ‖gToC (gEval lPz z)‖) ^ 2 ≤ ((ρ : ℝ) * ‖gToC (gEval lPz' z)‖) ^ 2 := by
      rw [mul_pow, mul_pow, h1, h2]
      have := (Rat.cast_le (K := ℝ)).mpr hP
      push_cast at this ⊢
      linarith
    push_cast
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  obtain ⟨ζ, hζr, hζ⟩ := exists_root_within polyPz_ne_zero (by rw [natDegree_polyPz]; norm_num)
    hρr hroot
  rw [norm_sub_rev] at hζ
  have hζn : ζ ∈ cgNodes 1 5 :=
    mem_cgNodes_one_five.mpr ((mem_roots polyPz_ne_zero).mp hζr)
  -- the weight
  set R : ℚ := |r.x| + |r.y| + ρ
  have hR : 0 ≤ R := by positivity
  have hz0 : ‖gToC z‖ ≤ (R : ℝ) := by
    have := norm_toC_le z
    simp only [R, z] at this ⊢; push_cast at this ⊢; linarith
  have hζR : ‖ζ‖ ≤ (R : ℝ) := by
    have := norm_toC_le z
    have h3 : ‖ζ‖ ≤ ‖gToC z‖ + ‖ζ - gToC z‖ := by
      have := norm_add_le (gToC z) (ζ - gToC z); simpa using this
    simp only [R, z] at this ⊢; push_cast at this ⊢; linarith
  have hlip : ∀ l, ‖cEval l ζ - cEval l (gToC z)‖ ≤ (lipR R l : ℝ) * ρ := fun l => by
    have hl : (0 : ℝ) ≤ lipR R l := by exact_mod_cast lipR_nonneg hR l
    exact (cEval_lip hR l hζR hz0).trans (mul_le_mul_of_nonneg_left hζ hl)
  have hW : ‖cgWeight 1 5 ζ - gToC (gDiv (gEval lAz z) (gEval lBz z))‖ ≤
      (cgDelta ρ z : ℝ) := by
    rw [cgWeight_one_five hζn, gToC_div, ← cEval_toC, ← cEval_toC]
    have hbp' : (0 : ℝ) < ((max |(gEval lBz z).1| |(gEval lBz z).2| : ℚ) : ℝ) -
        (lipR R lBz : ℝ) * ρ := by exact_mod_cast hbp
    have h := norm_div_sub_div_le (a := ((|(gEval lAz z).1| + |(gEval lAz z).2| : ℚ) : ℝ))
      (b := ((max |(gEval lBz z).1| |(gEval lBz z).2| : ℚ) : ℝ)) (hlip lAz) (hlip lBz)
      (by rw [cEval_toC]; exact norm_toC_le _) (by rw [cEval_toC]; exact max_le_norm_toC _) hbp'
    refine h.trans_eq ?_
    simp only [cgDelta, R, z]
    push_cast
    ring
  refine ⟨ζ, hζn, hζ, ?_, ?_, ?_, ?_, hW⟩
  · refine roundsTo_of_le (q := r.x) ?_ hx
    calc |ζ.re - r.x| = |(ζ - gToC z).re| := by simp [gToC, z]
      _ ≤ ‖ζ - gToC z‖ := Complex.abs_re_le_norm _
      _ ≤ ρ := hζ
  · refine roundsTo_of_le (q := r.y) ?_ hy
    calc |ζ.im - r.y| = |(ζ - gToC z).im| := by simp [gToC, z]
      _ ≤ ‖ζ - gToC z‖ := Complex.abs_im_le_norm _
      _ ≤ ρ := hζ
  · refine roundsTo_of_le (q := (gDiv (gEval lAz z) (gEval lBz z)).1) ?_ hwr
    calc |(cgWeight 1 5 ζ).re - ((gDiv (gEval lAz z) (gEval lBz z)).1 : ℝ)|
        = |(cgWeight 1 5 ζ - gToC (gDiv (gEval lAz z) (gEval lBz z))).re| := by simp [gToC]
      _ ≤ _ := Complex.abs_re_le_norm _
      _ ≤ _ := hW
  · refine roundsTo_of_le (q := (gDiv (gEval lAz z) (gEval lBz z)).2) ?_ hwi
    calc |(cgWeight 1 5 ζ).im - ((gDiv (gEval lAz z) (gEval lBz z)).2 : ℝ)|
        = |(cgWeight 1 5 ζ - gToC (gDiv (gEval lAz z) (gEval lBz z))).im| := by simp [gToC]
      _ ≤ _ := Complex.abs_im_le_norm _
      _ ≤ _ := hW

/-! ### The table -/

/-- The printed values of a row. -/
def cgTab (rows : List CGRow) : List ((ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ)) :=
  rows.map fun r => (r.Xr, r.Xi, r.Wr, r.Wi)

/-- Table 3.5.18 is correctly rounded and complete: every row is a node `ζ_k` and its weight
`w_k` (real and imaginary parts), and every node is a row. -/
def CGTableSpec (tab : List ((ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ))) : Prop :=
  (∀ p ∈ tab, ∃ ζ ∈ cgNodes 1 5, RoundsTo ζ.re p.1 ∧ RoundsTo ζ.im p.2.1 ∧
      RoundsTo (cgWeight 1 5 ζ).re p.2.2.1 ∧ RoundsTo (cgWeight 1 5 ζ).im p.2.2.2) ∧
  ∀ ζ ∈ cgNodes 1 5, ∃ p ∈ tab, RoundsTo ζ.re p.1 ∧ RoundsTo ζ.im p.2.1 ∧
      RoundsTo (cgWeight 1 5 ζ).re p.2.2.1 ∧ RoundsTo (cgWeight 1 5 ζ).im p.2.2.2

/-- The exact checks for the whole table: every row, disjoint disks, five rows. -/
def cgTableOK (ρ : ℚ) (rows : List CGRow) : Bool :=
  rows.all (cgRowOK ρ) &&
    decide (rows.Pairwise fun r t => 4 * ρ ^ 2 < (r.x - t.x) ^ 2 + (r.y - t.y) ^ 2) &&
    decide (rows.length = 5)

theorem cgTableOK_sound {ρ : ℚ} {rows : List CGRow} (h : cgTableOK ρ rows = true) :
    CGTableSpec (cgTab rows) := by
  classical
  simp only [cgTableOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hrows, hpw⟩, hlen⟩ := h
  have hrow : ∀ i : Fin rows.length, ∃ ζ ∈ cgNodes 1 5,
      ‖ζ - gToC (rows[i].x, rows[i].y)‖ ≤ ρ ∧ RoundsTo ζ.re rows[i].Xr ∧
      RoundsTo ζ.im rows[i].Xi ∧ RoundsTo (cgWeight 1 5 ζ).re rows[i].Wr ∧
      RoundsTo (cgWeight 1 5 ζ).im rows[i].Wi := fun i => by
    obtain ⟨ζ, h1, h2, h3, h4, h5, h6, -⟩ := cgRowOK_sound (hrows rows[i] (List.getElem_mem _))
    exact ⟨ζ, h1, h2, h3, h4, h5, h6⟩
  choose ζs hmem hnear hre him hwre hwim using hrow
  have hinj : Function.Injective ζs := by
    intro i j hij
    by_contra hne
    have hsep : ∀ i j : Fin rows.length, i < j →
        4 * ρ ^ 2 < (rows[i].x - rows[j].x) ^ 2 + (rows[i].y - rows[j].y) ^ 2 :=
      fun i j h => List.pairwise_iff_getElem.mp hpw i j i.2 j.2 h
    have key : ∀ i j : Fin rows.length, i ≠ j →
        (4 * ρ ^ 2 : ℝ) < ((rows[i].x - rows[j].x) ^ 2 + (rows[i].y - rows[j].y) ^ 2 : ℚ) :=
      fun i j h => by
        rcases lt_or_gt_of_ne h with h | h
        · exact_mod_cast hsep i j h
        · have := hsep j i h; exact_mod_cast (by linarith : _ < _)
    have hd : ‖gToC (rows[i].x, rows[i].y) - gToC (rows[j].x, rows[j].y)‖ ≤ 2 * ρ := by
      calc ‖gToC (rows[i].x, rows[i].y) - gToC (rows[j].x, rows[j].y)‖
          = ‖(gToC (rows[i].x, rows[i].y) - ζs i) + (ζs j - gToC (rows[j].x, rows[j].y))‖ := by
            rw [hij]; congr 1; ring
        _ ≤ ‖gToC (rows[i].x, rows[i].y) - ζs i‖ + ‖ζs j - gToC (rows[j].x, rows[j].y)‖ :=
            norm_add_le _ _
        _ ≤ ρ + ρ := add_le_add (by rw [norm_sub_rev]; exact hnear i) (hnear j)
        _ = 2 * ρ := by ring
    have hsq : ‖gToC (rows[i].x, rows[i].y) - gToC (rows[j].x, rows[j].y)‖ ^ 2 =
        (((rows[i].x - rows[j].x) ^ 2 + (rows[i].y - rows[j].y) ^ 2 : ℚ) : ℝ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [gToC]; ring
    have hρ0 : (0 : ℝ) ≤ ρ := by
      have := (norm_nonneg _).trans (hnear i); exact this
    have h4 : ‖gToC (rows[i].x, rows[i].y) - gToC (rows[j].x, rows[j].y)‖ ^ 2 ≤ (2 * ρ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hd 2
    have := key i j hne
    rw [hsq] at h4
    push_cast at this h4
    nlinarith
  have hsub : univ.image ζs ⊆ cgNodes 1 5 := fun t ht => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact hmem i
  have hcard : #(univ.image ζs) = 5 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hlen]
  have heq : univ.image ζs = cgNodes 1 5 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_cgNodes one_pos, hcard])
  refine ⟨fun p hp => ?_, fun ζ hζ => ?_⟩
  · simp only [cgTab, List.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    exact ⟨ζs ⟨i, hi⟩, hmem _, hre _, him _, hwre _, hwim _⟩
  · rw [← heq] at hζ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hζ
    refine ⟨(rows[i].Xr, rows[i].Xi, rows[i].Wr, rows[i].Wi), ?_, hre i, him i, hwre i, hwim i⟩
    simp only [cgTab, List.mem_map]
    exact ⟨rows[i], List.getElem_mem _, rfl⟩

/-- The nodes enumerated by the rows of a checked table, with their certified disks and weights. -/
theorem cgTable_nodes {ρ : ℚ} {rows : List CGRow} (h : cgTableOK ρ rows = true) :
    ∃ ζs : Fin rows.length → ℂ, Function.Injective ζs ∧ univ.image ζs = cgNodes 1 5 ∧
      ∀ i, ‖ζs i - gToC (rows[i].x, rows[i].y)‖ ≤ ρ ∧
        ‖cgWeight 1 5 (ζs i) - gToC (gDiv (gEval lAz (rows[i].x, rows[i].y))
          (gEval lBz (rows[i].x, rows[i].y)))‖ ≤ (cgDelta ρ (rows[i].x, rows[i].y) : ℝ) := by
  classical
  have h' := h
  simp only [cgTableOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨⟨hrows, hpw⟩, hlen⟩ := h'
  have hrow : ∀ i : Fin rows.length, ∃ ζ ∈ cgNodes 1 5,
      ‖ζ - gToC (rows[i].x, rows[i].y)‖ ≤ ρ ∧
      ‖cgWeight 1 5 ζ - gToC (gDiv (gEval lAz (rows[i].x, rows[i].y))
        (gEval lBz (rows[i].x, rows[i].y)))‖ ≤ (cgDelta ρ (rows[i].x, rows[i].y) : ℝ) :=
    fun i => by
      obtain ⟨ζ, h1, h2, -, -, -, -, h7⟩ := cgRowOK_sound (hrows rows[i] (List.getElem_mem _))
      exact ⟨ζ, h1, h2, h7⟩
  choose ζs hmem hnear hw using hrow
  have hinj : Function.Injective ζs := by
    intro i j hij
    by_contra hne
    have hsep : ∀ i j : Fin rows.length, i < j →
        4 * ρ ^ 2 < (rows[i].x - rows[j].x) ^ 2 + (rows[i].y - rows[j].y) ^ 2 :=
      fun i j h => List.pairwise_iff_getElem.mp hpw i j i.2 j.2 h
    have key : (4 * ρ ^ 2 : ℝ) < ((rows[i].x - rows[j].x) ^ 2 + (rows[i].y - rows[j].y) ^ 2 : ℚ) :=
      by
        rcases lt_or_gt_of_ne hne with h | h
        · exact_mod_cast hsep i j h
        · have := hsep j i h; exact_mod_cast (by linarith : _ < _)
    have hd : ‖gToC (rows[i].x, rows[i].y) - gToC (rows[j].x, rows[j].y)‖ ≤ 2 * ρ := by
      calc ‖gToC (rows[i].x, rows[i].y) - gToC (rows[j].x, rows[j].y)‖
          = ‖(gToC (rows[i].x, rows[i].y) - ζs i) + (ζs j - gToC (rows[j].x, rows[j].y))‖ := by
            rw [hij]; congr 1; ring
        _ ≤ ‖gToC (rows[i].x, rows[i].y) - ζs i‖ + ‖ζs j - gToC (rows[j].x, rows[j].y)‖ :=
            norm_add_le _ _
        _ ≤ ρ + ρ := add_le_add (by rw [norm_sub_rev]; exact hnear i) (hnear j)
        _ = 2 * ρ := by ring
    have hsq : ‖gToC (rows[i].x, rows[i].y) - gToC (rows[j].x, rows[j].y)‖ ^ 2 =
        (((rows[i].x - rows[j].x) ^ 2 + (rows[i].y - rows[j].y) ^ 2 : ℚ) : ℝ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [gToC]; ring
    have h4 : ‖gToC (rows[i].x, rows[i].y) - gToC (rows[j].x, rows[j].y)‖ ^ 2 ≤ (2 * ρ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hd 2
    rw [hsq] at h4
    push_cast at key h4
    nlinarith
  have hsub : univ.image ζs ⊆ cgNodes 1 5 := fun t ht => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact hmem i
  have hcard : #(univ.image ζs) = 5 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hlen]
  exact ⟨ζs, hinj, Finset.eq_of_subset_of_card_le hsub (by rw [card_cgNodes one_pos, hcard]),
    fun i => ⟨hnear i, hw i⟩⟩

/-! ### Table 3.5.18 (`ρ = 10^{−30}`, approximations to 40 decimals) -/

/-- The approximations and printed values of Table 3.5.18. -/
def cgRows_3_5_18 : List CGRow := [
  ⟨36556943254635722582432079600954338543570 / 10 ^ 40,
    65437368993600772940210715093936863183638 / 10 ^ 40,
    (3655694325, 9), (6543736899, 9), (3839661630, 9), (-2735703863, 10)⟩,
  ⟨36556943254635722582432079600954338543570 / 10 ^ 40,
    -65437368993600772940210715093936863183638 / 10 ^ 40,
    (3655694325, 9), (-6543736899, 9), (3839661630, 9), (2735703863, 10)⟩,
  ⟨57009532986717894191702153689698616208477 / 10 ^ 40,
    32102656003085498884250106529721172123215 / 10 ^ 40,
    (5700953299, 9), (3210265600, 9), (-2507945221, 8), (2187252294, 9)⟩,
  ⟨57009532986717894191702153689698616208477 / 10 ^ 40,
    -32102656003085498884250106529721172123215 / 10 ^ 40,
    (5700953299, 9), (-3210265600, 9), (-2507945221, 8), (-2187252294, 9)⟩,
  ⟨62867047517292766451731533418694090495907 / 10 ^ 40,
    0,
    (6286704752, 9), (0, 9), (4347958116, 8), (0, 9)⟩]

set_option maxRecDepth 100000 in
theorem cgTableOK_3_5_18 : cgTableOK (1 / 10 ^ 30) cgRows_3_5_18 = true := by
  decide +kernel

/-- **Table 3.5.18** (5-point complex Gauss formula 3.5.36, `s = 1`): the nodes `ζ_k` and weights
`w_k` (real and imaginary parts, as printed) are correctly rounded, and the table is complete. -/
theorem dlmf_table_3_5_18 : CGTableSpec [
    ((3655694325, 9), (6543736899, 9), (3839661630, 9), (-2735703863, 10)),
    ((3655694325, 9), (-6543736899, 9), (3839661630, 9), (2735703863, 10)),
    ((5700953299, 9), (3210265600, 9), (-2507945221, 8), (2187252294, 9)),
    ((5700953299, 9), (-3210265600, 9), (-2507945221, 8), (-2187252294, 9)),
    ((6286704752, 9), (0, 9), (4347958116, 8), (0, 9))] :=
  cgTableOK_sound cgTableOK_3_5_18

/-- "The complex Gauss nodes `ζ_k` have positive real part", for `n = 5`, `s = 1`. -/
theorem cgNodes_one_five_re_pos {ζ : ℂ} (hζ : ζ ∈ cgNodes 1 5) : 0 < ζ.re := by
  obtain ⟨p, hp, hre, -⟩ := dlmf_table_3_5_18.2 ζ hζ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  unfold RoundsTo at hre
  rw [abs_le] at hre
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num at hre <;> linarith [hre.1]

end Azurite.DLMF

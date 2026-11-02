/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5LaplaceShift

/-!
# DLMF §2.5(iii): shifting the line of integration of `x^{−z} Γ(1 − z) G(z)`

The contour shifts of 2.5.42–2.5.43 all have the shape: `G` is analytic on a half-plane
`ℜz > a₀` except for a set `P` of poles with finitely many in every strip, and grows at most
polynomially in `|ℑz|` on vertical strips (`StripData`). Then `x^{−z} Γ(1 − z) G(z)` has, in the
strip `p < ℜz < q`, the singularities `P` together with the poles `1, 2, 3, …` of `Γ(1 − z)`, and
since `Γ(1 − z)` decays faster than any power of `|ℑz|` (`exists_Gamma_strip_bound`) the line
integral over `ℜz = p` equals the residue sum plus the line integral over `ℜz = q`
(`shift_Gamma_mul`, from `lineIntegral_shift`). The theorem also returns, for each singularity, a
radius whose punctured disc is free of singularities, which is what the residue computations of
2.5.44 need.

Also: `residue_congr`, `residue_const_mul`, `residue_eq_residue` (independence of the radius) and
`exists_isolating_radii`.
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### Residue algebra -/

theorem residue_congr {F G : ℂ → ℂ} {s : ℂ} {R : ℝ} (hR : 0 < R)
    (h : ∀ z ∈ annulus s 0 R, F z = G z) : residue F s R = residue G s R := by
  simp only [residue, laurentCoeff]
  congr 1
  refine circleIntegral.integral_congr (by positivity) fun z hz => ?_
  have hzA : z ∈ annulus s 0 R := by
    rw [mem_sphere, dist_eq_norm] at hz
    exact ⟨by rw [hz]; positivity, by rw [hz]; linarith⟩
  rw [h z hzA]

theorem residue_const_mul (c : ℂ) (F : ℂ → ℂ) (s : ℂ) (R : ℝ) :
    residue (fun z => c * F z) s R = c * residue F s R := by
  have h := circleIntegral.integral_smul c (fun z => F z / (z - s) ^ ((-1 : ℤ) + 1)) s (R / 2)
  simp only [smul_eq_mul] at h
  simp only [residue, laurentCoeff, mul_div_assoc]
  rw [h]
  ring

/-- The residue does not depend on the radius, as long as `F` is analytic on the punctured disc. -/
theorem residue_eq_residue {F : ℂ → ℂ} {s : ℂ} {R R' : ℝ}
    (hF : DifferentiableOn ℂ F (annulus s 0 R)) (hR' : 0 < R') (hle : R' ≤ R) :
    residue F s R = residue F s R' := by
  have hsub : annulus s 0 R' ⊆ annulus s 0 R := fun z hz => ⟨hz.1, hz.2.trans_le hle⟩
  rw [residue_eq hF ⟨by positivity, by linarith⟩ (r := R' / 2),
    residue_eq (hF.mono hsub) ⟨by positivity, by linarith⟩ (r := R' / 2)]

/-! ### Isolating radii -/

/-- For a finite set `s` of positive values of `f`, there is `ε > 0` below all of them. -/
theorem exists_pos_le_of_finite {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ ε > 0, ∀ i ∈ s, ε ≤ f i := by
  classical
  rcases hs.toFinset.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun i hi => ?_⟩
    exact absurd (hs.mem_toFinset.mpr hi) (by simp [h])
  · obtain ⟨i₀, hi₀, hmin⟩ := hs.toFinset.exists_min_image f h
    exact ⟨f i₀, hf i₀ (hs.mem_toFinset.mp hi₀), fun i hi => hmin i (hs.mem_toFinset.mpr hi)⟩

/-- A finite set inside an open set admits radii with the isolation properties required by the
residue theorem `rectBoundary_eq_sum_residues`. -/
theorem exists_isolating_radii (S : Finset ℂ) {U : Set ℂ} (hU : IsOpen U) (hS : ↑S ⊆ U) :
    ∃ R : ℂ → ℝ, ∀ s ∈ S, 0 < R s ∧ ball s (R s) ⊆ U ∧ ∀ t ∈ S, t ≠ s → R s ≤ dist t s := by
  have : ∀ s : ℂ, ∃ r : ℝ, s ∈ S → 0 < r ∧ ball s r ⊆ U ∧ ∀ t ∈ S, t ≠ s → r ≤ dist t s := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hU s (hS hs)
      obtain ⟨ε, hε, hεle⟩ := exists_pos_le_of_finite ((S.erase s).finite_toSet)
        (fun t => dist t s) fun t ht => dist_pos.mpr (Finset.mem_erase.mp ht).1
      refine ⟨min r₁ ε, fun _ => ⟨lt_min hr₁ hε, (ball_subset_ball (min_le_left _ _)).trans hball,
        fun t ht hne => (min_le_right _ _).trans (hεle t (Finset.mem_erase.mpr ⟨hne, ht⟩))⟩⟩
    · exact ⟨1, fun h => absurd h hs⟩
  choose R hR using this
  exact ⟨R, fun s hs => hR s hs⟩

/-! ### Integrability on a vertical line from a decay bound -/

/-- A function continuous on the vertical line `ℜz = σ` and bounded by `K/y²` for `|y| ≥ Y`
(`Y ≥ 1`) is integrable on the line. -/
theorem integrable_line_of_decay {F : ℂ → ℂ} {σ : ℝ} (hcont : Continuous fun y : ℝ => F (σ + y * I))
    {K Y : ℝ} (hY : 1 ≤ Y) (hK : ∀ y : ℝ, Y ≤ |y| → ‖F (σ + y * I)‖ ≤ K / y ^ 2) :
    Integrable fun y : ℝ => F (σ + y * I) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -Y) (b := Y)).exists_bound_of_continuousOn
    hcont.continuousOn
  set C : ℝ := (1 + Y ^ 2) * (|B| + |K|)
  refine (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rcases le_or_gt |y| Y with hy | hy
  · have h2 : (1 : ℝ) ≤ (1 + Y ^ 2) / (1 + y ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [abs_le.mp hy, sq_abs y]
    calc ‖F (σ + y * I)‖ ≤ |B| := (hB y (abs_le.mp hy)).trans (le_abs_self B)
      _ ≤ (|B| + |K|) * ((1 + Y ^ 2) / (1 + y ^ 2)) :=
          le_mul_of_one_le_right (by positivity) h2 |>.trans' (by linarith [abs_nonneg K])
      _ = C * (1 + y ^ 2)⁻¹ := by simp only [C]; ring
  · have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    calc ‖F (σ + y * I)‖ ≤ K / y ^ 2 := hK y hy.le
      _ ≤ |K| / y ^ 2 := div_le_div_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ |K| * ((1 + Y ^ 2) / (1 + y ^ 2)) := by
          rw [div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg K)
          rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div,
            le_div_iff₀ (by positivity)]
          nlinarith
      _ ≤ C * (1 + y ^ 2)⁻¹ := by
          have e : C * (1 + y ^ 2)⁻¹ =
              |K| * ((1 + Y ^ 2) / (1 + y ^ 2)) + (1 + Y ^ 2) * |B| * (1 + y ^ 2)⁻¹ := by
            simp only [C]; ring
          have : 0 ≤ (1 + Y ^ 2) * |B| * (1 + y ^ 2)⁻¹ := by positivity
          rw [e]
          linarith

/-! ### The data for the contour shifts -/

/-- `G` is analytic on `ℜz > a₀` off a set `P` of singularities with finitely many in every
strip, and grows at most polynomially in `|ℑz|` on every vertical strip `a ≤ ℜz ≤ b`, `a > a₀`. -/
structure StripData (G : ℂ → ℂ) (P : Set ℂ) (a₀ : ℝ) : Prop where
  diff : ∀ z : ℂ, a₀ < z.re → z ∉ P → DifferentiableAt ℂ G z
  finite : ∀ a b : ℝ, (P ∩ {z : ℂ | a ≤ z.re ∧ z.re ≤ b}).Finite
  poly : ∀ a b : ℝ, a₀ < a → ∃ C m Y : ℝ, 0 ≤ C ∧ 0 ≤ m ∧ 1 ≤ Y ∧
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → Y ≤ |z.im| → ‖G z‖ ≤ C * |z.im| ^ m

/-- The singularities of `Γ(1 − z) G(z)`: those of `G` and the poles `1, 2, 3, …` of `Γ(1 − z)`. -/
def sing (P : Set ℂ) : Set ℂ := P ∪ {z | ∃ n : ℕ, z = n + 1}

theorem finite_sing_strip {P : Set ℂ} (hP : ∀ a b : ℝ, (P ∩ {z : ℂ | a ≤ z.re ∧ z.re ≤ b}).Finite)
    (a b : ℝ) : (sing P ∩ {z : ℂ | a ≤ z.re ∧ z.re ≤ b}).Finite := by
  rw [sing, union_inter_distrib_right]
  refine (hP a b).union
    (((Finset.range ⌈b⌉₊).finite_toSet.image fun n : ℕ => (n : ℂ) + 1).subset ?_)
  rintro z ⟨⟨n, rfl⟩, -, hb⟩
  refine ⟨n, ?_, rfl⟩
  simp only [Finset.coe_range, mem_Iio]
  have : (n : ℝ) + 1 ≤ b := by simpa using hb
  exact Nat.lt_ceil.mpr (by linarith)

/-- Differentiability of `Γ(1 − z)` at `z` when `z` is not a pole `1, 2, …`. -/
theorem differentiableAt_Gamma_one_sub {z : ℂ} (hz : ∀ n : ℕ, z ≠ n + 1) :
    DifferentiableAt ℂ (fun z => Gamma (1 - z)) z := by
  refine (differentiableAt_Gamma _ fun n hn => hz n ?_).comp z
    ((differentiableAt_const _).sub differentiableAt_id)
  linear_combination -hn

theorem notMem_sing_iff {P : Set ℂ} {z : ℂ} : z ∉ sing P ↔ z ∉ P ∧ ∀ n : ℕ, z ≠ n + 1 := by
  simp only [sing, mem_union, mem_ofPred_eq, not_or, not_exists]

/-- The decay of `Γ(1 − z) G(z)` on a strip, from a polynomial bound on `G` and the decay of
`Γ`: `|Γ(1 − z) G(z)| ≤ MC/|ℑz|²` for `|ℑz| ≥ Y`. -/
theorem norm_Gamma_mul_le {G : ℂ → ℂ} {C m Y M : ℝ} {k : ℕ} (hC0 : 0 ≤ C) (hY : 1 ≤ Y)
    (hM0 : 0 ≤ M) {p q : ℝ}
    (hCm : ∀ z : ℂ, p ≤ z.re → z.re ≤ q → Y ≤ |z.im| → ‖G z‖ ≤ C * |z.im| ^ m)
    (hM : ∀ σ ∈ Icc (1 - q) (1 - p), ∀ y : ℝ, y ≠ 0 → ‖Gamma (σ + y * I)‖ ≤ M / |y| ^ k)
    (hk : ⌈m⌉₊ + 2 ≤ k) {σ : ℝ} (hσ : σ ∈ Icc p q) {y : ℝ} (hyY : Y ≤ |y|) :
    ‖Gamma (1 - (σ + y * I)) * G (σ + y * I)‖ ≤ M * C / y ^ 2 := by
  have hy : 1 ≤ |y| := hY.trans hyY
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy; linarith
  have e : (1 : ℂ) - (σ + y * I) = ((1 - σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by push_cast; ring
  have hΓ : ‖Gamma (1 - (σ + y * I))‖ ≤ M / |y| ^ k := by
    rw [e]
    have := hM (1 - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-y) (neg_ne_zero.mpr hy0)
    rwa [abs_neg] at this
  have hGb : ‖G (σ + y * I)‖ ≤ C * |y| ^ m := by
    simpa using hCm (σ + y * I) (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using hyY)
  have hk2 : |y| ^ m ≤ |y| ^ (k - 2 : ℕ) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hy ?_
    have : (⌈m⌉₊ : ℝ) ≤ ((k - 2 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_sub_of_add_le hk)
    linarith [Nat.le_ceil m]
  have hkk : |y| ^ k = |y| ^ (k - 2 : ℕ) * y ^ 2 := by
    rw [← sq_abs, ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ k)]
  rw [norm_mul]
  calc ‖Gamma (1 - (σ + y * I))‖ * ‖G (σ + y * I)‖ ≤ M / |y| ^ k * (C * |y| ^ (k - 2 : ℕ)) :=
        mul_le_mul hΓ (hGb.trans (mul_le_mul_of_nonneg_left hk2 hC0)) (norm_nonneg _)
          (div_nonneg hM0 (by positivity))
    _ = M * C / y ^ 2 := by
        rw [hkk]
        have : |y| ^ (k - 2 : ℕ) ≠ 0 := pow_ne_zero _ (abs_pos.mpr hy0).ne'
        field_simp

/-- `x^{−z} Γ(1 − z) G(z)` is integrable on every vertical line `ℜz = σ > a₀` free of
singularities. -/
theorem integrable_Gamma_mul_line {G : ℂ → ℂ} {P : Set ℂ} {a₀ : ℝ} (hG : StripData G P a₀) {σ : ℝ}
    (ha : a₀ < σ) (hσs : ∀ z ∈ sing P, z.re ≠ σ) {x : ℝ} (hx : 0 < x) :
    Integrable fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) *
      (Gamma (1 - (σ + y * I)) * G (σ + y * I)) := by
  obtain ⟨C, m, Y, hC0, hm0, hY, hCm⟩ := hG.poly σ σ ha
  set k : ℕ := ⌈m⌉₊ + ⌈σ⌉₊ + 2 with hkdef
  obtain ⟨M, hM0, hM⟩ := exists_Gamma_strip_bound (a := 1 - σ) (b := 1 - σ) k (by
    have : (k : ℝ) = ⌈m⌉₊ + ⌈σ⌉₊ + 2 := by simp [hkdef]
    rw [this]
    linarith [Nat.le_ceil σ, (Nat.cast_nonneg ⌈m⌉₊ : (0 : ℝ) ≤ ⌈m⌉₊)])
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hcont : Continuous fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) *
      (Gamma (1 - (σ + y * I)) * G (σ + y * I)) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hz : (σ : ℂ) + y * I ∉ sing P := fun h => hσs _ h (by simp)
    obtain ⟨hzP, hzn⟩ := notMem_sing_iff.mp hz
    have hd : DifferentiableAt ℂ (fun z => (x : ℂ) ^ (-z) * (Gamma (1 - z) * G z))
        ((σ : ℂ) + y * I) :=
      (differentiable_neg.const_cpow (Or.inl hx0) _).mul ((differentiableAt_Gamma_one_sub hzn).mul
        (hG.diff _ (by simpa using ha) hzP))
    exact hd.continuousAt.comp (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
  refine integrable_line_of_decay (F := fun z => (x : ℂ) ^ (-z) * (Gamma (1 - z) * G z))
    (σ := σ) hcont hY (K := x ^ (-σ) * (M * C)) fun y hy => ?_
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero]
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_Gamma_mul_le hC0 hY hM0 hCm hM (by simp [hkdef])
    ⟨le_rfl, le_rfl⟩ hy) (Real.rpow_nonneg hx.le _)

/-- **The contour shift**: for `a₀ < p < q` with no singularity on the lines `ℜz = p`, `ℜz = q`,
`(2πi)⁻¹ ∫_{p} x^{−z} Γ(1 − z) G(z) dz = ∑_{p<ℜz<q} res[−x^{−z} Γ(1 − z) G(z)] +
(2πi)⁻¹ ∫_{q} x^{−z} Γ(1 − z) G(z) dz`, the sum running over the singularities of `Γ(1 − z) G(z)`
in the open strip, each with a radius `R s` whose punctured disc is free of singularities. -/
theorem shift_Gamma_mul {G : ℂ → ℂ} {P : Set ℂ} {a₀ : ℝ} (hG : StripData G P a₀) {p q : ℝ}
    (ha : a₀ < p) (hpq : p < q) (hp : ∀ z ∈ sing P, z.re ≠ p) (hq : ∀ z ∈ sing P, z.re ≠ q)
    {x : ℝ} (hx : 0 < x) :
    ∃ (S : Finset ℂ) (R : ℂ → ℝ),
      (∀ z, z ∈ S ↔ z ∈ sing P ∧ p < z.re ∧ z.re < q) ∧
      (∀ s ∈ S, 0 < R s ∧ ∀ z ∈ ball s (R s), z ≠ s → a₀ < z.re ∧ z ∉ sing P) ∧
      (2 * π : ℂ)⁻¹ * (∫ y : ℝ, (x : ℂ) ^ (-((p : ℂ) + y * I)) *
          (Gamma (1 - (p + y * I)) * G (p + y * I))) =
        ∑ s ∈ S, residue (fun z => -((x : ℂ) ^ (-z) * (Gamma (1 - z) * G z))) s (R s) +
          (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (x : ℂ) ^ (-((q : ℂ) + y * I)) *
            (Gamma (1 - (q + y * I)) * G (q + y * I)) := by
  classical
  -- the singularities near the strip, and a margin `ε` free of singularities
  have hT : (sing P ∩ {z : ℂ | p - 1 ≤ z.re ∧ z.re ≤ q + 1}).Finite :=
    finite_sing_strip hG.finite _ _
  obtain ⟨ε₁, hε₁, hε₁le⟩ := exists_pos_le_of_finite hT (fun z => min |z.re - p| |z.re - q|)
    fun z hz => lt_min (abs_pos.mpr (sub_ne_zero.mpr (hp z hz.1)))
      (abs_pos.mpr (sub_ne_zero.mpr (hq z hz.1)))
  set ε : ℝ := min (min ε₁ 1) (p - a₀) / 2 with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    have := lt_min (lt_min hε₁ one_pos) (sub_pos.mpr ha)
    positivity
  have hε1 : ε < 1 := by
    rw [hεdef]
    have := min_le_right ε₁ 1
    have := min_le_left (min ε₁ 1) (p - a₀)
    linarith
  have hεε₁ : ε < ε₁ := by
    rw [hεdef]
    have := min_le_left ε₁ 1
    have := min_le_left (min ε₁ 1) (p - a₀)
    linarith
  have hεa : ε < p - a₀ := by
    rw [hεdef]
    have := min_le_right (min ε₁ 1) (p - a₀)
    linarith
  set U : Set ℂ := {z : ℂ | p - ε < z.re ∧ z.re < q + ε} with hUdef
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  -- singularities in `U` lie in the open strip
  have hsingU : ∀ z ∈ sing P, z ∈ U → p < z.re ∧ z.re < q := fun z hz hzU => by
    have hzU : p - ε < z.re ∧ z.re < q + ε := hzU
    have hzT : z ∈ sing P ∩ {z : ℂ | p - 1 ≤ z.re ∧ z.re ≤ q + 1} :=
      ⟨hz, by linarith [hzU.1], by linarith [hzU.2]⟩
    have h1 := (le_min_iff.mp (hε₁le z hzT)).1
    have h2 := (le_min_iff.mp (hε₁le z hzT)).2
    have hp' := hp z hz
    have hq' := hq z hz
    constructor
    · by_contra hcon
      push Not at hcon
      have hlt : z.re < p := lt_of_le_of_ne hcon hp'
      have habs : |z.re - p| = p - z.re := by
        rw [abs_sub_comm]
        exact abs_of_pos (by linarith)
      linarith [hzU.1]
    · by_contra hcon
      push Not at hcon
      have hlt : q < z.re := lt_of_le_of_ne hcon (Ne.symm hq')
      have habs : |z.re - q| = z.re - q := abs_of_pos (by linarith)
      linarith [hzU.2]
  have hT' : (sing P ∩ {z : ℂ | p < z.re ∧ z.re < q}).Finite :=
    hT.subset fun z hz => ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨S, hSmem⟩ : ∃ S : Finset ℂ, ∀ z, z ∈ S ↔ z ∈ sing P ∧ p < z.re ∧ z.re < q :=
    ⟨hT'.toFinset, fun z => by rw [Set.Finite.mem_toFinset]; rfl⟩
  have hSU : ↑S ⊆ U := fun z hz => by
    rw [Finset.mem_coe, hSmem] at hz
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨R, hR⟩ := exists_isolating_radii S hU hSU
  -- the integrand `F(z) = x^{−z} Γ(1 − z) G(z)` is analytic on `U` off `S`
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hpow : Differentiable ℂ fun z : ℂ => (x : ℂ) ^ (-z) :=
    differentiable_neg.const_cpow (Or.inl hx0)
  have hdiff : ∀ z ∈ U, z ∉ sing P →
      DifferentiableAt ℂ (fun z => (x : ℂ) ^ (-z) * (Gamma (1 - z) * G z)) z := fun z hzU hz => by
    obtain ⟨hzP, hzn⟩ := notMem_sing_iff.mp hz
    exact (hpow z).mul ((differentiableAt_Gamma_one_sub hzn).mul
      (hG.diff z (by linarith [hzU.1]) hzP))
  have hFd : DifferentiableOn ℂ (fun z => (x : ℂ) ^ (-z) * (Gamma (1 - z) * G z)) (U \ ↑S) :=
    fun z hz => (hdiff z hz.1 fun hs => hz.2 (by
      rw [Finset.mem_coe, hSmem]; exact ⟨hs, hsingU z hs hz.1⟩)).differentiableWithinAt
  -- the decay 2.5.34 of `Γ(1 − z) G(z)` on the strip
  obtain ⟨C, m, Y, hC0, hm0, hY, hCm⟩ := hG.poly p q ha
  set k : ℕ := ⌈m⌉₊ + ⌈q⌉₊ + 2 with hkdef
  obtain ⟨M, hM0, hM⟩ := exists_Gamma_strip_bound (a := 1 - q) (b := 1 - p) k (by
    have : (k : ℝ) = ⌈m⌉₊ + ⌈q⌉₊ + 2 := by simp [hkdef]
    rw [this]
    linarith [Nat.le_ceil q, (Nat.cast_nonneg ⌈m⌉₊ : (0 : ℝ) ≤ ⌈m⌉₊)])
  have hbound : ∀ σ ∈ Icc p q, ∀ y : ℝ, Y ≤ |y| →
      ‖Gamma (1 - (σ + y * I)) * G (σ + y * I)‖ ≤ M * C / y ^ 2 := fun σ hσ y hyY =>
    norm_Gamma_mul_le hC0 hY hM0 hCm hM (by simp [hkdef]) hσ hyY
  have h34 : ∀ ε > 0, ∀ᶠ y : ℝ in cocompact ℝ, ∀ σ ∈ Icc p q,
      ‖Gamma (1 - (σ + y * I)) * G (σ + y * I)‖ ≤ ε := fun ε hε => by
    refine eventually_cocompact_of_abs_ge (max Y (Real.sqrt ((M * C + 1) / ε))) fun y hy σ hσ => ?_
    have hyY : Y ≤ |y| := (le_max_left _ _).trans hy
    have hy1 : 1 ≤ |y| := hY.trans hyY
    have hsq : (M * C + 1) / ε ≤ y ^ 2 := by
      rw [← sq_abs]
      calc (M * C + 1) / ε = Real.sqrt ((M * C + 1) / ε) ^ 2 :=
            (Real.sq_sqrt (div_nonneg (by linarith [mul_nonneg hM0 hC0]) hε.le)).symm
        _ ≤ |y| ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) ((le_max_right _ _).trans hy) 2
    refine (hbound σ hσ y hyY).trans ?_
    have hy2 : 0 < y ^ 2 := by rw [← sq_abs]; exact one_pos.trans_le (one_le_pow₀ hy1)
    rw [div_le_iff₀ hy2]
    rw [div_le_iff₀ hε] at hsq
    nlinarith
  -- integrability on the two lines
  have hFp := integrable_Gamma_mul_line hG ha hp hx
  have hFq := integrable_Gamma_mul_line hG (ha.trans hpq) hq hx
  -- the shift
  have hshift := lineIntegral_shift (F := fun z => (x : ℂ) ^ (-z) * (Gamma (1 - z) * G z)) hpq hU
    (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩)
    (fun s hs => ((hSmem s).mp hs).2) hFd R hR
    (tendsto_horizontal_of_sup (G := fun z => Gamma (1 - z) * G z) hx hpq.le h34 atTop
      atTop_le_cocompact)
    (by
      have := tendsto_horizontal_of_sup (G := fun z => Gamma (1 - z) * G z) hx hpq.le h34 atBot
        atBot_le_cocompact
      refine (this.comp tendsto_neg_atTop_atBot).congr' (Eventually.of_forall fun T => ?_)
      simp only [Function.comp]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      rw [show ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) = σ - T * I by push_cast; ring])
    hFp hFq
  refine ⟨S, R, hSmem, fun s hs => ⟨(hR s hs).1, fun z hz hzs => ?_⟩, ?_⟩
  · have hzU : z ∈ U := (hR s hs).2.1 hz
    refine ⟨by linarith [hzU.1], fun hzP => ?_⟩
    have hzS : z ∈ S := (hSmem z).mpr ⟨hzP, hsingU z hzP hzU⟩
    have := (hR s hs).2.2 z hzS hzs
    rw [mem_ball] at hz
    linarith
  · have hres : ∀ s ∈ S, residue (fun z => -((x : ℂ) ^ (-z) * (Gamma (1 - z) * G z))) s (R s) =
        -residue (fun z => (x : ℂ) ^ (-z) * (Gamma (1 - z) * G z)) s (R s) := fun s _ =>
      residue_neg _ s (R s)
    rw [Finset.sum_congr rfl hres, Finset.sum_neg_distrib, hshift]
    have hπ : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
    ring

end Azurite.DLMF

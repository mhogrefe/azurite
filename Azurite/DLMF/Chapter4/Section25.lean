/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section9Log
import Azurite.DLMF.Chapter4.Section24

/-!
# DLMF §4.25 Continued Fractions

The continued fraction `b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` has convergents `cfA a b r / cfB a b r`
(§1.12). Each formula is stated as: the denominators are eventually nonzero and the convergents
tend to the function.

* 4.25.1 (`z ≠ ±½π, ±(3/2)π, …`): `dlmf_4_25_1`. `Yᵣ = Bᵣ − iAᵣ` satisfies
  `Yᵣ′ = −iYᵣ + zYᵣ₋₁` (`hasDerivAt_tanY`), so `uᵣ = e^{iz}Yᵣ/(2r − 1)!!` has
  `uᵣ′ = z uᵣ₋₁/(2r − 1)`, `uᵣ(0) = 1`, and `uᵣ → 1` by the mean value inequality
  (`tendsto_tanU`). Hence `Bᵣ/(2r − 1)!! → cos z` and `Aᵣ/(2r − 1)!! → sin z`.
* 4.25.4 (`z` off the cuts of Figure 4.23.1(ii)): `dlmf_4_25_4`, from 4.9.2 with `iz` in place
  of `z` (`cfP_scale_first`, `cfQ_change_first`).
* 4.25.3: `dlmf_4_25_3` in `Section25Arcsin.lean`.
* 4.25.2, 4.25.5: `dlmf_4_25_2`, `dlmf_4_25_5` in `Section25Exp.lean`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-- Changing the first partial numerator leaves the denominators unchanged. -/
theorem cfQ_change_first {a a' b : ℕ → ℂ} (h : ∀ r ≥ 2, a' r = a r) :
    ∀ k, cfQ a' b k = cfQ a b k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      show b (k + 1) * cfQ a' b (k + 1) + a' (k + 1) * cfQ a' b k =
        b (k + 1) * cfQ a b (k + 1) + a (k + 1) * cfQ a b k
      rw [ih (k + 1) (by omega), ih k (by omega)]
      rcases k with _ | k
      · simp [cfQ]
      · rw [h (k + 2) (by omega)]

/-- Scaling the first partial numerator (with `b₀ = 0`) scales the numerators. -/
theorem cfP_scale_first {a a' b : ℕ → ℂ} (c : ℂ) (hb : b 0 = 0) (h1 : a' 1 = c * a 1)
    (h : ∀ r ≥ 2, a' r = a r) : ∀ k, cfP a' b (k + 1) = c * cfP a b (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [cfP, hb]
    | 1 => simp [cfP, hb, h1]
    | k + 2 =>
      show b (k + 2) * cfP a' b (k + 2) + a' (k + 2) * cfP a' b (k + 1) =
        c * (b (k + 2) * cfP a b (k + 2) + a (k + 2) * cfP a b (k + 1))
      rw [ih (k + 1) (by omega), ih k (by omega), h (k + 2) (by omega)]
      ring

/-- The partial numerators of 4.25.4: `a₁ = z`, `aᵣ = (r − 1)²z²`. -/
noncomputable def arctanCFa (z : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then z else (((r - 1) ^ 2 : ℕ) : ℂ) * z ^ 2

/-- **DLMF 4.25.4**: `arctan z = z/(1 + z²/(3 + 4z²/(5 + 9z²/(7 + 16z²/(9 + ⋯)))))`, `z` in the
open cut plane of Figure 4.23.1(ii). -/
theorem dlmf_4_25_4 {z : ℂ} (hz : z ∈ arctanCut) :
    (∀ᶠ r in atTop, cfB (arctanCFa z) (lg2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (arctanCFa z) (lg2b z) r / cfB (arctanCFa z) (lg2b z) r) atTop
        (𝓝 (arctanD z)) := by
  have hcut : ∀ x : ℝ, x ≤ -1 ∨ 1 ≤ x → I * z ≠ x := by
    intro x hx h
    have hz' : z = -I * x := by
      have : z = -I * (I * z) := by ring_nf; rw [I_sq]; ring
      rw [this, h]
    rcases hz with hz | hz
    · apply hz; rw [hz']; simp
    · rw [hz'] at hz; simp at hz
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)] at hz; linarith
      · rw [abs_of_pos (by linarith)] at hz; linarith
  obtain ⟨hB, hT⟩ := dlmf_4_9_2 (I * z) hcut
  have hb0 : lg2b (I * z) 0 = 0 := by simp [lg2b]
  have hagree : ∀ r ≥ 2, arctanCFa z r = lg2a (I * z) r := by
    intro r hr
    have hr1 : r ≠ 1 := by omega
    simp only [arctanCFa, lg2a, hr1, ↓reduceIte]
    rw [mul_pow, I_sq]; ring
  have hfirst : arctanCFa z 1 = (2 * I)⁻¹ * lg2a (I * z) 1 := by
    simp only [arctanCFa, lg2a, ↓reduceIte]
    field_simp
  have hQ : ∀ r, cfB (arctanCFa z) (lg2b z) r = cfB (lg2a (I * z)) (lg2b (I * z)) r := by
    intro r
    exact cfQ_change_first hagree (r + 1)
  have hP : ∀ r, cfA (arctanCFa z) (lg2b z) r =
      (2 * I)⁻¹ * cfA (lg2a (I * z)) (lg2b (I * z)) r := by
    intro r
    exact cfP_scale_first _ hb0 hfirst hagree r
  refine ⟨hB.mono fun r hr => by rwa [hQ], ?_⟩
  have hlim := hT.const_mul (2 * I)⁻¹
  rw [arctanD_eq hz, Complex.arctan]
  convert hlim using 2 with r
  · rw [hP, hQ]; ring
  · rw [show (1 + z * I) / (1 - z * I) = (1 + I * z) / (1 - I * z) by ring_nf]
    field_simp
    ring_nf
    rw [I_sq]; ring

/-! ### 4.25.1 -/

/-- The partial numerators of 4.25.1: `a₁ = z`, `aᵣ = −z²` (the `bᵣ = 2r − 1` are `lg2b`). -/
noncomputable def tanCFa (z : ℂ) (r : ℕ) : ℂ := if r = 1 then z else -z ^ 2

/-- `Yᵣ = Bᵣ − iAᵣ` (`= θᵣ(−iz)` with the reverse Bessel polynomial `θᵣ`). -/
noncomputable def tanY (r : ℕ) (z : ℂ) : ℂ :=
  cfB (tanCFa z) (lg2b z) r - I * cfA (tanCFa z) (lg2b z) r

theorem tanY_zero (z : ℂ) : tanY 0 z = 1 := by
  simp [tanY, cfA, cfB, cfP, cfQ, lg2b]

theorem tanY_one (z : ℂ) : tanY 1 z = 1 - I * z := by
  simp [tanY, cfA, cfB, cfP, cfQ, lg2b, tanCFa]; norm_num

theorem tanY_succ_succ (r : ℕ) (z : ℂ) :
    tanY (r + 2) z = (2 * ((r : ℂ) + 2) - 1) * tanY (r + 1) z - z ^ 2 * tanY r z := by
  have ha : tanCFa z (r + 2) = -z ^ 2 := by simp [tanCFa]
  have hb : lg2b z (r + 2) = 2 * ((r : ℂ) + 2) - 1 := by
    simp only [lg2b, show r + 2 ≠ 0 by omega, ↓reduceIte]; push_cast; ring
  simp only [tanY, cfA_succ_succ, cfB_succ_succ, ha, hb]
  ring

/-- `Yᵣ′ = −iYᵣ + zYᵣ₋₁` (from `θₙ′ = θₙ − xθₙ₋₁`). -/
theorem hasDerivAt_tanY (n : ℕ) (x : ℂ) :
    HasDerivAt (tanY (n + 1)) (-I * tanY (n + 1) x + x * tanY n x) x := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    match n with
    | 0 =>
      rw [show tanY 1 = fun x => 1 - I * x from funext tanY_one]
      show HasDerivAt (fun x => 1 - I * x) (-I * (1 - I * x) + x * tanY 0 x) x
      rw [tanY_zero]
      convert ((hasDerivAt_id x).const_mul I).const_sub 1 using 1
      · rfl
      · ring_nf; rw [I_sq]; ring
    | 1 =>
      have e : tanY 2 = fun x => 3 * (1 - I * x) - x ^ 2 := by
        funext x; rw [tanY_succ_succ, tanY_one, tanY_zero]; push_cast; ring
      rw [e]
      show HasDerivAt (fun x => 3 * (1 - I * x) - x ^ 2)
        (-I * (3 * (1 - I * x) - x ^ 2) + x * tanY 1 x) x
      rw [tanY_one]
      have := ((((hasDerivAt_id x).const_mul I).const_sub 1).const_mul 3).sub
        ((hasDerivAt_id x).fun_pow 2)
      convert this using 1
      · funext y; simp only [Pi.sub_apply, id]
      · simp only [id]; push_cast; ring_nf; rw [I_sq]; ring
    | n + 2 =>
      have e : tanY (n + 3) = fun x =>
          (2 * ((n : ℂ) + 1 + 2) - 1) * tanY (n + 2) x - x ^ 2 * tanY (n + 1) x := by
        funext x; rw [tanY_succ_succ]; push_cast; ring_nf
      rw [e]
      have h2 := ih (n + 1) (by omega) x
      have h1 := ih n (by omega) x
      have := (h2.const_mul (2 * ((n : ℂ) + 1 + 2) - 1)).sub
        (((hasDerivAt_id x).fun_pow 2).mul h1)
      convert this using 1
      · funext y; simp only [Pi.sub_apply, Pi.mul_apply, id]
      · have r2 := tanY_succ_succ n x
        simp only [id, show n + 1 + 1 = n + 2 from rfl]
        push_cast at r2 ⊢
        linear_combination x * r2

/-- `(2r − 1)!! = 1·3⋯(2r − 1)`. -/
noncomputable def oddFact (r : ℕ) : ℂ := ∏ i ∈ Finset.range r, (2 * (i : ℂ) + 1)

theorem oddFact_succ (r : ℕ) : oddFact (r + 1) = oddFact r * (2 * r + 1) :=
  Finset.prod_range_succ _ _

theorem oddFact_ne_zero (r : ℕ) : oddFact r ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact_mod_cast (show (2 * i + 1 : ℕ) ≠ 0 by omega)

/-- `uᵣ = e^{iz}Yᵣ/(2r − 1)!!`, with `uᵣ′ = z uᵣ₋₁/(2r − 1)` and `uᵣ(0) = 1`. -/
noncomputable def tanU (r : ℕ) (z : ℂ) : ℂ := exp (I * z) * tanY r z / oddFact r

theorem tanY_at_zero (r : ℕ) : tanY r 0 = oddFact r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [tanY_zero, oddFact]
    | 1 => simp [tanY_one, oddFact]
    | r + 2 =>
      rw [tanY_succ_succ, ih (r + 1) (by omega), oddFact_succ (r + 1)]
      push_cast; ring

theorem tanU_at_zero (r : ℕ) : tanU r 0 = 1 := by
  simp [tanU, tanY_at_zero, oddFact_ne_zero]

theorem hasDerivAt_tanU (n : ℕ) (x : ℂ) :
    HasDerivAt (tanU (n + 1)) (x * tanU n x / (2 * n + 1)) x := by
  have hl : HasDerivAt (fun x : ℂ => I * x) I x := by
    simpa using (hasDerivAt_id x).const_mul I
  have he : HasDerivAt (fun x => exp (I * x)) (I * exp (I * x)) x := by
    convert hl.cexp using 1; ring
  have := (he.mul (hasDerivAt_tanY n x)).div_const (oddFact (n + 1))
  unfold tanU
  convert this using 1
  rw [oddFact_succ]
  have h1 := oddFact_ne_zero n
  have h2 : (2 * (n : ℂ) + 1) ≠ 0 := by exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  field_simp
  ring_nf

theorem continuous_tanY (r : ℕ) : Continuous (tanY r) := by
  rcases r with _ | r
  · rw [show tanY 0 = fun _ => 1 from funext tanY_zero]; exact continuous_const
  · exact continuous_iff_continuousAt.mpr fun x => (hasDerivAt_tanY r x).continuousAt

/-- `uᵣ(z) → 1`. -/
theorem tendsto_tanU (z : ℂ) : Tendsto (fun r => tanU r z) atTop (𝓝 1) := by
  set R := ‖z‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, 2 * R ^ 2 ≤ 2 * r₀ + 1 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (2 * R ^ 2)
    exact ⟨n, by linarith⟩
  have hcont : ∀ r, Continuous (tanU r) := fun r =>
    ((continuous_const.mul continuous_id).cexp.mul (continuous_tanY r)).div_const _
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hcont r₀).continuousOn
  set K := max K₀ 2 with hK
  -- uniform bound on the ball for `r ≥ r₀`
  have hstep : ∀ n ≥ r₀, (∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖tanU n x‖ ≤ K) →
      ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖tanU (n + 1) x - 1‖ ≤ R ^ 2 * K / (2 * n + 1) := by
    intro n hn hb x hx
    have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := tanU (n + 1)) (C := R * K / (2 * n + 1))
      (fun y _ => (hasDerivAt_tanU n y).hasDerivWithinAt)
      (fun y hy => by
        rw [norm_div, norm_mul]
        have h2 : ‖(2 * (n : ℂ) + 1)‖ = 2 * n + 1 := by
          rw [show (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
            Real.norm_eq_abs, abs_of_pos hpos]
        rw [h2]
        have hy' : ‖y‖ ≤ R := by simpa using hy
        exact div_le_div_of_nonneg_right (mul_le_mul hy' (hb y hy) (norm_nonneg _) hR0.le)
          hpos.le)
      (convex_closedBall 0 R) (Metric.mem_closedBall_self hR0.le) hx
    rw [tanU_at_zero, sub_zero] at hmv
    have hx' : ‖x‖ ≤ R := by simpa using hx
    calc ‖tanU (n + 1) x - 1‖ ≤ R * K / (2 * n + 1) * ‖x‖ := hmv
      _ ≤ R * K / (2 * n + 1) * R := by
          have : (0 : ℝ) ≤ K := le_trans (by norm_num) (le_max_right _ _)
          gcongr
      _ = R ^ 2 * K / (2 * n + 1) := by ring
  have hbound : ∀ n ≥ r₀, ∀ x ∈ Metric.closedBall (0 : ℂ) R, ‖tanU n x‖ ≤ K := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact fun x hx => (hK₀ x hx).trans (le_max_left _ _)
    | succ n hn ih =>
      intro x hx
      have h := hstep n hn ih x hx
      have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
      have hle : R ^ 2 * K / (2 * n + 1) ≤ K / 2 := by
        rw [div_le_div_iff₀ hpos (by norm_num)]
        have : (2 * r₀ + 1 : ℝ) ≤ 2 * n + 1 := by exact_mod_cast (by omega : 2 * r₀ + 1 ≤ 2 * n + 1)
        have hK2 : (2 : ℝ) ≤ K := le_max_right _ _
        nlinarith
      calc ‖tanU (n + 1) x‖ ≤ ‖tanU (n + 1) x - 1‖ + ‖(1 : ℂ)‖ := norm_le_norm_sub_add _ _
        _ ≤ K / 2 + 1 := by rw [norm_one]; linarith
        _ ≤ K := by have : (2 : ℝ) ≤ K := le_max_right _ _; linarith
  have hz : z ∈ Metric.closedBall (0 : ℂ) R := by simp [hR]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => R ^ 2 * K / (2 * ((n - 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    refine tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop (by norm_num) ?_)
    exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (r₀ + 1)] with n hn
  rw [norm_norm]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega]
  exact hstep m (by omega) (hbound m (by omega)) z hz

theorem tan_cf_neg (z : ℂ) (r : ℕ) :
    cfA (tanCFa (-z)) (lg2b (-z)) r = -cfA (tanCFa z) (lg2b z) r ∧
      cfB (tanCFa (-z)) (lg2b (-z)) r = cfB (tanCFa z) (lg2b z) r := by
  have hb : lg2b (-z) = lg2b z := rfl
  have hagree : ∀ r ≥ 2, tanCFa (-z) r = tanCFa z r := by
    intro r hr
    have : r ≠ 1 := by omega
    simp [tanCFa, this]
  have h1 : tanCFa (-z) 1 = -1 * tanCFa z 1 := by simp [tanCFa]
  rw [hb]
  refine ⟨?_, cfQ_change_first hagree (r + 1)⟩
  rw [cfA, cfA, cfP_scale_first (-1) (by simp [lg2b]) h1 hagree r]
  ring

/-- **DLMF 4.25.1**: `tan z = z/(1 − z²/(3 − z²/(5 − z²/(7 − ⋯))))`, `z ≠ ±½π, ±(3/2)π, …`.
The normalized denominators and numerators tend to `cos z` and `sin z` (`tendsto_tanU`). -/
theorem dlmf_4_25_1 {z : ℂ} (hz : ∀ k : ℤ, z ≠ (2 * k + 1) * π / 2) :
    (∀ᶠ r in atTop, cfB (tanCFa z) (lg2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (tanCFa z) (lg2b z) r / cfB (tanCFa z) (lg2b z) r) atTop
        (𝓝 (tan z)) := by
  have hc : cos z ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp h
    exact hz k hk
  have hY : ∀ w : ℂ, Tendsto (fun r => tanY r w / oddFact r) atTop (𝓝 (exp (-(I * w)))) := by
    intro w
    have := (tendsto_tanU w).const_mul (exp (-(I * w)))
    rw [mul_one] at this
    refine this.congr fun r => ?_
    simp only [tanU]
    rw [mul_div_assoc, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
  have hB : Tendsto (fun r => cfB (tanCFa z) (lg2b z) r / oddFact r) atTop (𝓝 (cos z)) := by
    have := ((hY z).add (hY (-z))).div_const 2
    rw [cos, show z * I = -(I * -z) by ring, show -z * I = -(I * z) by ring, add_comm]
    refine this.congr fun r => ?_
    obtain ⟨-, hb⟩ := tan_cf_neg z r
    obtain ⟨ha, -⟩ := tan_cf_neg z r
    simp only [tanY, ha, hb]
    ring
  have hA : Tendsto (fun r => cfA (tanCFa z) (lg2b z) r / oddFact r) atTop (𝓝 (sin z)) := by
    have := ((hY (-z)).sub (hY z)).div_const (2 * I)
    rw [sin]
    convert this using 2 with r
    · obtain ⟨ha, hb⟩ := tan_cf_neg z r
      simp only [tanY, ha, hb]
      field_simp
      ring
    · rw [show -(I * -z) = z * I by ring, show -(I * z) = -z * I by ring]
      field_simp
      ring_nf
      rw [I_sq]; ring
  have hB0 : ∀ᶠ r in atTop, cfB (tanCFa z) (lg2b z) r ≠ 0 := by
    filter_upwards [hB.eventually_ne hc] with r hr h
    rw [h, zero_div] at hr; exact hr rfl
  refine ⟨hB0, ?_⟩
  have := hA.div hB hc
  rw [← tan_eq_sin_div_cos] at this
  refine this.congr fun r => ?_
  have := oddFact_ne_zero r
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ this]

end Azurite.DLMF

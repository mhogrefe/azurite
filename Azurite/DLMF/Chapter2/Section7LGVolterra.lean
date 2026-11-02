/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# DLMF §2.7(iii): the Volterra equation behind the Liouville–Green theorem

Let `I ⊆ ℝ` be an open interval `(a₁, a₂)` (finite or infinite ends), `q` continuous on `I` and
absolutely integrable on `(a₁, x]` for every `x ∈ I`, and `ξ` an antiderivative of some
`s ≥ 0` on `I`. With `V(x) = ∫_{a₁}^{x} |q|` (`volterraV`), the Volterra integral equation

`u(x) = 1 − ½ ∫_{a₁}^{x} (1 − e^{2ξ(v) − 2ξ(x)}) q(v) u(v) dv`

has a solution (`VolterraLG.exists_solution`), the sum of the Picard iterates `lgIter`, with
`|u(x) − 1| ≤ e^{V(x)/2} − 1`, `u′ = −s P` and `P′ = −2sP + q u`, where
`P(x) = e^{−2ξ(x)} ∫_{a₁}^{x} e^{2ξ} q u` satisfies `|P(x)| ≤ 2(e^{V(x)/2} − 1)`.

`x → a₁+` within `I` is the filter `ioLowerEnd I` (`atBot` on the subtype `I`); `∫_{a₁}^{x}` is the
set integral over `I ∩ (−∞, x]`.
-/

open Filter Topology Set MeasureTheory

namespace Azurite.DLMF

/-! ### The ends of an open interval -/

/-- `x → a₁+` within the interval `I` (`a₁ = inf I`, possibly `−∞`). -/
def ioLowerEnd (I : Set ℝ) : Filter ℝ := map Subtype.val (atBot : Filter I)

/-- `x → a₂−` within the interval `I` (`a₂ = sup I`, possibly `+∞`). -/
def ioUpperEnd (I : Set ℝ) : Filter ℝ := map Subtype.val (atTop : Filter I)

variable {I : Set ℝ}

theorem eventually_ioLowerEnd (hne : I.Nonempty) {P : ℝ → Prop} :
    (∀ᶠ x in ioLowerEnd I, P x) ↔ ∃ a ∈ I, ∀ x ∈ I, x ≤ a → P x := by
  have : Nonempty I := hne.to_subtype
  rw [ioLowerEnd, eventually_map, eventually_atBot]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, ha, fun x hx hxa => h ⟨x, hx⟩ hxa⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨⟨a, ha⟩, fun x hxa => h x.1 x.2 hxa⟩

theorem eventually_ioUpperEnd (hne : I.Nonempty) {P : ℝ → Prop} :
    (∀ᶠ x in ioUpperEnd I, P x) ↔ ∃ a ∈ I, ∀ x ∈ I, a ≤ x → P x := by
  have : Nonempty I := hne.to_subtype
  rw [ioUpperEnd, eventually_map, eventually_atTop]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, ha, fun x hx hxa => h ⟨x, hx⟩ hxa⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨⟨a, ha⟩, fun x hxa => h x.1 x.2 hxa⟩

theorem ioLowerEnd_neBot (hne : I.Nonempty) : (ioLowerEnd I).NeBot := by
  have : Nonempty I := hne.to_subtype
  exact Filter.map_neBot

theorem ioUpperEnd_neBot (hne : I.Nonempty) : (ioUpperEnd I).NeBot := by
  have : Nonempty I := hne.to_subtype
  exact Filter.map_neBot

theorem eventually_mem_ioLowerEnd : ∀ᶠ x in ioLowerEnd I, x ∈ I :=
  eventually_map.mpr (Eventually.of_forall fun x => x.2)

theorem eventually_mem_ioUpperEnd : ∀ᶠ x in ioUpperEnd I, x ∈ I :=
  eventually_map.mpr (Eventually.of_forall fun x => x.2)

theorem exists_lt_mem (hI : IsOpen I) {v : ℝ} (hv : v ∈ I) : ∃ z ∈ I, z < v := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hI v hv
  refine ⟨v - δ / 2, hball ?_, by linarith⟩
  rw [Metric.mem_ball, Real.dist_eq, show v - δ / 2 - v = -(δ / 2) by ring, abs_neg,
    abs_of_pos (by linarith)]
  linarith

theorem exists_gt_mem (hI : IsOpen I) {v : ℝ} (hv : v ∈ I) : ∃ z ∈ I, v < z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hI v hv
  refine ⟨v + δ / 2, hball ?_, by linarith⟩
  rw [Metric.mem_ball, Real.dist_eq, show v + δ / 2 - v = δ / 2 by ring,
    abs_of_pos (by linarith)]
  linarith

/-- A decreasing sequence in `I` tending to its lower end. -/
theorem exists_seq_ioLowerEnd (hI : IsOpen I) (hIc : I.OrdConnected) (hne : I.Nonempty) :
    ∃ y : ℕ → ℝ, (∀ n, y n ∈ I) ∧ Antitone y ∧ ∀ v ∈ I, ∃ n, y n < v := by
  obtain ⟨x₀, hx₀⟩ := hne
  by_cases hb : BddBelow I
  · set a := sInf I
    have ha : ∀ v ∈ I, a < v := fun v hv => by
      obtain ⟨z, hz, hzv⟩ := exists_lt_mem hI hv
      exact (csInf_le hb hz).trans_lt hzv
    have hax : a < x₀ := ha x₀ hx₀
    refine ⟨fun n => a + (x₀ - a) / (n + 1), fun n => ?_, fun m n hmn => ?_, fun v hv => ?_⟩
    · have hpos : 0 < (x₀ - a) / (n + 1) := by positivity
      obtain ⟨z, hz, hzlt⟩ := exists_lt_of_csInf_lt ⟨x₀, hx₀⟩ (show a < a + (x₀ - a) / (n + 1)
        by linarith)
      have hle : (x₀ - a) / (n + 1) ≤ x₀ - a :=
        div_le_self (by linarith) (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
      exact hIc.out hz hx₀ ⟨hzlt.le, by linarith⟩
    · have hmn' : (m : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have : (x₀ - a) / (n + 1) ≤ (x₀ - a) / (m + 1) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) hmn'
      simp only
      linarith
    · have hv' := ha v hv
      obtain ⟨n, hn⟩ := exists_nat_gt ((x₀ - a) / (v - a))
      refine ⟨n, ?_⟩
      have h1 : x₀ - a < n * (v - a) := by rwa [div_lt_iff₀ (by linarith)] at hn
      have h2 : (x₀ - a) / (n + 1) < v - a := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      simp only
      linarith
  · rw [not_bddBelow_iff] at hb
    refine ⟨fun n => x₀ - n, fun n => ?_, fun m n hmn => ?_, fun v _ => ?_⟩
    · obtain ⟨z, hz, hzlt⟩ := hb (x₀ - n)
      exact hIc.out hz hx₀ ⟨hzlt.le, by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith⟩
    · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      simp only
      linarith
    · obtain ⟨n, hn⟩ := exists_nat_gt (x₀ - v)
      exact ⟨n, by simp only; linarith⟩

/-- `∫_{a₁}^{x} q → 0` as `x → a₁+`. -/
theorem tendsto_setIntegral_ioLowerEnd (hI : IsOpen I) (hIc : I.OrdConnected) (hne : I.Nonempty)
    {q : ℝ → ℝ} (hint : ∀ x ∈ I, IntegrableOn q (I ∩ Iic x)) :
    Tendsto (fun y => ∫ v in I ∩ Iic y, q v) (ioLowerEnd I) (𝓝 0) := by
  obtain ⟨y, hyI, hyanti, hy⟩ := exists_seq_ioLowerEnd hI hIc hne
  have hmono : Antitone fun n => I ∩ Iic (y n) :=
    fun m n h => inter_subset_inter_right _ (Iic_subset_Iic.mpr (hyanti h))
  have hlim := tendsto_setIntegral_of_antitone (μ := volume) (f := fun v => |q v|)
    (fun n => hI.measurableSet.inter measurableSet_Iic) hmono ⟨0, (hint _ (hyI 0)).abs⟩
  have hempty : (⋂ n, I ∩ Iic (y n)) = ∅ := by
    ext v
    simp only [mem_iInter, mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_forall]
    by_cases hv : v ∈ I
    · obtain ⟨n, hn⟩ := hy v hv
      exact ⟨n, fun h => absurd h.2 (not_le.mpr hn)⟩
    · exact ⟨0, fun h => hv h.1⟩
  rw [hempty, Measure.restrict_empty, integral_zero_measure] at hlim
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim δ hδ
  rw [eventually_ioLowerEnd hne]
  refine ⟨y N, hyI N, fun x _ hxy => ?_⟩
  have hNN := hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (setIntegral_nonneg
    (hI.measurableSet.inter measurableSet_Iic) fun v _ => abs_nonneg _)] at hNN
  rw [Real.dist_eq, sub_zero]
  calc |∫ v in I ∩ Iic x, q v| ≤ ∫ v in I ∩ Iic x, |q v| := abs_integral_le_integral_abs
    _ ≤ ∫ v in I ∩ Iic (y N), |q v| :=
        setIntegral_mono_set (hint _ (hyI N)).abs (ae_of_all _ fun v => abs_nonneg _)
          (show I ∩ Iic x ⊆ I ∩ Iic (y N) from
            inter_subset_inter_right _ (Iic_subset_Iic.mpr hxy)).eventuallyLE
    _ < δ := hNN

/-- `d/dx ∫_{a₁}^{x} q = q(x)`. -/
theorem hasDerivAt_setIntegral_Iic (hI : IsOpen I) (hIc : I.OrdConnected) {q : ℝ → ℝ}
    (hq : ContinuousOn q I) (hint : ∀ x ∈ I, IntegrableOn q (I ∩ Iic x)) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (fun y => ∫ v in I ∩ Iic y, q v) (q x) x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hI x hx
  set x₀ := x - δ / 2 with hx₀
  have hx₀I : x₀ ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, show x - δ / 2 - x = -(δ / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith)
  have hFTC := intervalIntegral.integral_hasDerivAt_right
    (ContinuousOn.intervalIntegrable_of_Icc (by rw [hx₀]; linarith) (hq.mono (hIc.out hx₀I hx)))
    (hq.stronglyMeasurableAtFilter hI x hx) (hq.continuousAt (hI.mem_nhds hx))
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ I ∧ x₀ < y :=
    Filter.Eventually.and (hI.mem_nhds hx) (lt_mem_nhds (show x₀ < x by rw [hx₀]; linarith))
  refine (hFTC.const_add (∫ v in I ∩ Iic x₀, q v)).congr_of_eventuallyEq ?_
  filter_upwards [hnear] with y ⟨hyI, hxy⟩
  have hsplit : I ∩ Iic y = (I ∩ Iic x₀) ∪ Ioc x₀ y := by
    ext v
    simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
    constructor
    · rintro ⟨hv, hvy⟩
      by_cases h : v ≤ x₀
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨not_le.mp h, hvy⟩
    · rintro (⟨hv, h⟩ | ⟨h1, h2⟩)
      · exact ⟨hv, h.trans hxy.le⟩
      · exact ⟨hIc.out hx₀I hyI ⟨h1.le, h2⟩, h2⟩
  rw [hsplit, setIntegral_union (disjoint_left.mpr fun v hv hv' => not_lt.mpr hv.2 hv'.1)
    measurableSet_Ioc (hint _ hx₀I) ((hint _ hyI).mono_set (fun v hv =>
      ⟨hIc.out hx₀I hyI ⟨hv.1.le, hv.2⟩, hv.2⟩)),
    intervalIntegral.integral_of_le hxy.le]

/-- A function with zero derivative on an open interval is constant there. -/
theorem eq_of_hasDerivAt_zero (hIc : I.OrdConnected) {D : ℝ → ℝ}
    (hD : ∀ x ∈ I, HasDerivAt D 0 x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : D x = D y := by
  wlog hxy : x < y generalizing x y
  · rcases (not_lt.mp hxy).lt_or_eq with h | h
    · exact (this hy hx h).symm
    · rw [h]
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope D (fun _ => 0) hxy
    (fun z hz => (hD z (hIc.out hx hy hz)).continuousAt.continuousWithinAt)
    (fun z hz => hD z (hIc.out hx hy (Ioo_subset_Icc_self hz)))
  have : D y - D x = 0 := by
    have hne : y - x ≠ 0 := by linarith
    field_simp at hslope
    linarith
  linarith

theorem tsum_pow_div_factorial (t : ℝ) : ∑' n : ℕ, t ^ n / n.factorial = Real.exp t := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-! ### The Volterra equation -/

/-- Hypotheses for the Liouville–Green Volterra equation. -/
structure VolterraLG (I : Set ℝ) (q ξ s : ℝ → ℝ) : Prop where
  isOpen : IsOpen I
  ordConnected : I.OrdConnected
  nonempty : I.Nonempty
  q_cont : ContinuousOn q I
  q_int : ∀ x ∈ I, IntegrableOn q (I ∩ Iic x)
  ξ_deriv : ∀ x ∈ I, HasDerivAt ξ (s x) x
  s_nonneg : ∀ x ∈ I, 0 ≤ s x

/-- `V(x) = ∫_{a₁}^{x} |q|`. -/
noncomputable def volterraV (I : Set ℝ) (q : ℝ → ℝ) (x : ℝ) : ℝ := ∫ v in I ∩ Iic x, |q v|

/-- The Picard iterates `h₀ = 1`,
`h_{n+1}(x) = −½ ∫_{a₁}^{x} (1 − e^{2ξ(v)−2ξ(x)}) q(v) hₙ(v) dv`. -/
noncomputable def lgIter (I : Set ℝ) (q ξ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun x => -(1 / 2) * ∫ v in I ∩ Iic x,
      (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * lgIter I q ξ n v

namespace VolterraLG

variable {q ξ s : ℝ → ℝ} (H : VolterraLG I q ξ s)
include H

theorem measR (x : ℝ) : MeasurableSet (I ∩ Iic x) := H.isOpen.measurableSet.inter measurableSet_Iic

theorem ξ_cont : ContinuousOn ξ I :=
  fun x hx => (H.ξ_deriv x hx).continuousAt.continuousWithinAt

theorem ξ_mono {v x : ℝ} (hv : v ∈ I) (hx : x ∈ I) (hvx : v ≤ x) : ξ v ≤ ξ x := by
  rcases hvx.lt_or_eq with h | h
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope ξ s h
      (H.ξ_cont.mono (H.ordConnected.out hv hx))
      (fun z hz => H.ξ_deriv z (H.ordConnected.out hv hx (Ioo_subset_Icc_self hz)))
    have hs := H.s_nonneg c (H.ordConnected.out hv hx (Ioo_subset_Icc_self hc))
    rw [hslope] at hs
    have := (div_nonneg_iff.mp hs)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  · rw [h]

theorem exp_le {v x : ℝ} (hv : v ∈ I) (hx : x ∈ I) (hvx : v ≤ x) :
    Real.exp (2 * ξ v - 2 * ξ x) ≤ 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by linarith [H.ξ_mono hv hx hvx])

theorem abs_kernel_le {v x : ℝ} (hv : v ∈ I) (hx : x ∈ I) (hvx : v ≤ x) :
    |1 - Real.exp (2 * ξ v - 2 * ξ x)| ≤ 1 := by
  have h1 := H.exp_le hv hx hvx
  have h2 := Real.exp_pos (2 * ξ v - 2 * ξ x)
  rw [abs_le]
  constructor <;> linarith

theorem aesm {h : ℝ → ℝ} (hh : ContinuousOn h I) (x : ℝ) :
    AEStronglyMeasurable h (volume.restrict (I ∩ Iic x)) :=
  (hh.mono inter_subset_left).aestronglyMeasurable (H.measR x)

/-- Integrability of `k q h` on `(a₁, x]` for `k`, `h` continuous on `I` and bounded there. -/
theorem integrableOn_mul {k h : ℝ → ℝ} (hk : ContinuousOn k I) (hh : ContinuousOn h I) {x : ℝ}
    (hx : x ∈ I) {C : ℝ} (hC : ∀ v ∈ I ∩ Iic x, |k v * h v| ≤ C) :
    IntegrableOn (fun v => k v * q v * h v) (I ∩ Iic x) := by
  refine Integrable.mono' ((H.q_int x hx).abs.const_mul C) ?_ ?_
  · exact ((H.aesm hk x).mul (H.aesm H.q_cont x)).mul (H.aesm hh x)
  · refine (ae_restrict_iff' (H.measR x)).mpr (Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, show k v * q v * h v = (k v * h v) * q v by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC v hv) (abs_nonneg _)

theorem V_hasDerivAt {x : ℝ} (hx : x ∈ I) : HasDerivAt (volterraV I q) |q x| x :=
  hasDerivAt_setIntegral_Iic H.isOpen H.ordConnected H.q_cont.abs (fun y hy => (H.q_int y hy).abs)
    hx

theorem V_cont : ContinuousOn (volterraV I q) I :=
  fun _ hx => (H.V_hasDerivAt hx).continuousAt.continuousWithinAt

theorem V_nonneg (x : ℝ) : 0 ≤ volterraV I q x :=
  setIntegral_nonneg (H.measR x) fun _ _ => abs_nonneg _

theorem V_mono {v x : ℝ} (hx : x ∈ I) (hvx : v ≤ x) : volterraV I q v ≤ volterraV I q x :=
  setIntegral_mono_set (H.q_int x hx).abs (ae_of_all _ fun _ => abs_nonneg _)
    (show I ∩ Iic v ⊆ I ∩ Iic x from
      inter_subset_inter_right _ (Iic_subset_Iic.mpr hvx)).eventuallyLE

theorem V_tendsto : Tendsto (volterraV I q) (ioLowerEnd I) (𝓝 0) :=
  tendsto_setIntegral_ioLowerEnd H.isOpen H.ordConnected H.nonempty fun y hy => (H.q_int y hy).abs

/-- `∫_{a₁}^{x} |q(v)| Φ′(V(v)) dv = Φ(V(x)) − Φ(0)`. -/
theorem integral_abs_mul_comp_V {Φ Φ' : ℝ → ℝ} (hΦ : ∀ t, HasDerivAt Φ (Φ' t) t)
    (hΦ' : Continuous Φ') :
    (∀ x ∈ I, IntegrableOn (fun v => |q v| * Φ' (volterraV I q v)) (I ∩ Iic x)) ∧
      ∀ x ∈ I, ∫ v in I ∩ Iic x, |q v| * Φ' (volterraV I q v) =
        Φ (volterraV I q x) - Φ 0 := by
  have hcont : ContinuousOn (fun v => |q v| * Φ' (volterraV I q v)) I :=
    H.q_cont.abs.mul (hΦ'.comp_continuousOn H.V_cont)
  have hint : ∀ x ∈ I, IntegrableOn (fun v => |q v| * Φ' (volterraV I q v)) (I ∩ Iic x) := by
    intro x hx
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hΦ'.continuousOn (s := Icc 0 (volterraV I q x)))
    refine Integrable.mono' ((H.q_int x hx).abs.mul_const M) ?_ ?_
    · exact (H.aesm H.q_cont.abs x).mul (H.aesm (hΦ'.comp_continuousOn H.V_cont) x)
    · refine (ae_restrict_iff' (H.measR x)).mpr (Eventually.of_forall fun v hv => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using hM _ ⟨H.V_nonneg v, H.V_mono hx hv.2⟩)
        (abs_nonneg _)
  refine ⟨hint, fun x hx => ?_⟩
  set D : ℝ → ℝ := fun y => (∫ v in I ∩ Iic y, |q v| * Φ' (volterraV I q v)) -
    (Φ (volterraV I q y) - Φ 0) with hD
  have hDd : ∀ y ∈ I, HasDerivAt D 0 y := by
    intro y hy
    have h1 := hasDerivAt_setIntegral_Iic H.isOpen H.ordConnected hcont hint hy
    have h2 := (hΦ (volterraV I q y)).comp y (H.V_hasDerivAt hy)
    exact (h1.sub (h2.sub_const (Φ 0))).congr_deriv (by ring)
  have hlim : Tendsto D (ioLowerEnd I) (𝓝 0) := by
    have h1 := tendsto_setIntegral_ioLowerEnd H.isOpen H.ordConnected H.nonempty hint
    have h2 : Tendsto (fun y => Φ (volterraV I q y) - Φ 0) (ioLowerEnd I) (𝓝 0) := by
      have := ((hΦ 0).continuousAt.tendsto.comp H.V_tendsto).sub_const (Φ 0)
      simpa using this
    simpa using h1.sub h2
  have hconst : Tendsto D (ioLowerEnd I) (𝓝 (D x)) :=
    tendsto_const_nhds.congr' (eventually_mem_ioLowerEnd.mono fun y hy =>
      eq_of_hasDerivAt_zero H.ordConnected hDd hx hy)
  have := ioLowerEnd_neBot H.nonempty
  have := tendsto_nhds_unique hconst hlim
  simp only [hD] at this
  linarith

/-- `T_h(x) = ∫_{a₁}^{x} (1 − e^{2ξ(v) − 2ξ(x)}) q(v) h(v) dv` splits as
`∫ q h − e^{−2ξ(x)} ∫ e^{2ξ} q h`. -/
theorem kernel_split {h : ℝ → ℝ} (hh : ContinuousOn h I) {x : ℝ} (hx : x ∈ I) {C : ℝ}
    (hC : ∀ v ∈ I ∩ Iic x, |h v| ≤ C) :
    ∫ v in I ∩ Iic x, (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * h v =
      (∫ v in I ∩ Iic x, 1 * q v * h v) -
        Real.exp (-(2 * ξ x)) * ∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * h v := by
  have hexp : ContinuousOn (fun v => Real.exp (2 * ξ v)) I :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul H.ξ_cont)
  have i1 : IntegrableOn (fun v => 1 * q v * h v) (I ∩ Iic x) :=
    H.integrableOn_mul continuousOn_const hh hx (C := C) fun v hv => by simpa using hC v hv
  have i2 : IntegrableOn (fun v => Real.exp (2 * ξ v) * q v * h v) (I ∩ Iic x) := by
    refine H.integrableOn_mul hexp hh hx (C := Real.exp (2 * ξ x) * C) fun v hv => ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [H.ξ_mono hv.1 hx hv.2])) (hC v hv)
      (abs_nonneg _) (Real.exp_pos _).le
  rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [show 2 * ξ v - 2 * ξ x = -(2 * ξ x) + 2 * ξ v by ring, Real.exp_add]
  ring

/-- `d/dx T_h(x) = 2 s(x) e^{−2ξ(x)} ∫_{a₁}^{x} e^{2ξ} q h`. -/
theorem hasDerivAt_kernel {h : ℝ → ℝ} (hh : ContinuousOn h I)
    (hb : ∀ x ∈ I, ∃ C, ∀ v ∈ I ∩ Iic x, |h v| ≤ C) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (fun y => ∫ v in I ∩ Iic y, (1 - Real.exp (2 * ξ v - 2 * ξ y)) * q v * h v)
      (2 * s x * (Real.exp (-(2 * ξ x)) *
        ∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * h v)) x := by
  have hexp : ContinuousOn (fun v => Real.exp (2 * ξ v)) I :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul H.ξ_cont)
  have i1 : ∀ y ∈ I, IntegrableOn (fun v => 1 * q v * h v) (I ∩ Iic y) := fun y hy => by
    obtain ⟨C, hC⟩ := hb y hy
    exact H.integrableOn_mul continuousOn_const hh hy (C := C) fun v hv => by simpa using hC v hv
  have i2 : ∀ y ∈ I, IntegrableOn (fun v => Real.exp (2 * ξ v) * q v * h v) (I ∩ Iic y) :=
    fun y hy => by
      obtain ⟨C, hC⟩ := hb y hy
      refine H.integrableOn_mul hexp hh hy (C := Real.exp (2 * ξ y) * C) fun v hv => ?_
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [H.ξ_mono hv.1 hy hv.2])) (hC v hv)
        (abs_nonneg _) (Real.exp_pos _).le
  have hA := hasDerivAt_setIntegral_Iic H.isOpen H.ordConnected
    ((continuousOn_const.mul H.q_cont).mul hh) i1 hx
  have hB := hasDerivAt_setIntegral_Iic H.isOpen H.ordConnected
    ((hexp.mul H.q_cont).mul hh) i2 hx
  have hE : HasDerivAt (fun y => Real.exp (-(2 * ξ y))) (Real.exp (-(2 * ξ x)) * -(2 * s x)) x :=
    ((H.ξ_deriv x hx).const_mul 2).neg.exp
  refine (hA.sub (hE.mul hB)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [H.isOpen.mem_nhds hx] with y hy
    obtain ⟨C, hC⟩ := hb y hy
    exact H.kernel_split hh hy hC
  · have : Real.exp (-(2 * ξ x)) * Real.exp (2 * ξ x) = 1 := by
      rw [← Real.exp_add]; simp
    simp only [Pi.mul_apply, one_mul]
    linear_combination (-(q x * h x)) * this

/-! ### Picard iteration -/

theorem lgIter_bound (n : ℕ) :
    ContinuousOn (lgIter I q ξ n) I ∧ ∀ x ∈ I,
      |lgIter I q ξ n x| ≤ (volterraV I q x / 2) ^ n / n.factorial := by
  induction n with
  | zero => exact ⟨continuousOn_const, fun x _ => by simp [lgIter]⟩
  | succ n ih =>
    obtain ⟨hc, hb⟩ := ih
    have hbd : ∀ x ∈ I, ∃ C, ∀ v ∈ I ∩ Iic x, |lgIter I q ξ n v| ≤ C := fun x hx =>
      ⟨(volterraV I q x / 2) ^ n / n.factorial, fun v hv => (hb v hv.1).trans (by
        gcongr
        · exact div_nonneg (H.V_nonneg v) zero_le_two
        · exact H.V_mono hx hv.2)⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact ((H.hasDerivAt_kernel hc hbd hx).const_mul (-(1 / 2))).continuousAt.continuousWithinAt
    · -- `Φ(t) = (t/2)^{n+1}/(n+1)!`, `Φ′(t) = ½ (t/2)^n/n!`
      have hΦ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t / 2) ^ (n + 1) / ((n + 1).factorial : ℝ))
          ((t / 2) ^ n / (n.factorial : ℝ) / 2) t := by
        intro t
        have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
        have h2 := ((hasDerivAt_pow (n + 1) (t / 2)).comp t h1).div_const
          ((n + 1).factorial : ℝ)
        refine h2.congr_deriv ?_
        rw [Nat.add_sub_cancel, Nat.factorial_succ]
        push_cast
        field_simp
      obtain ⟨hint, heq⟩ := H.integral_abs_mul_comp_V hΦ (by fun_prop)
      have key := heq x hx
      simp only [zero_div, zero_pow (Nat.succ_ne_zero n), sub_zero] at key
      show |-(1 / 2) * _| ≤ _
      rw [abs_mul, abs_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)]
      have hle : |∫ v in I ∩ Iic x, (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * lgIter I q ξ n v| ≤
          ∫ v in I ∩ Iic x, |q v| * ((volterraV I q v / 2) ^ n / n.factorial / 2) * 2 := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le ((hint x hx).mul_const 2) ?_
        refine (ae_restrict_iff' (H.measR x)).mpr (Eventually.of_forall fun v hv => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 := H.abs_kernel_le hv.1 hx hv.2
        have h2 := hb v hv.1
        calc |1 - Real.exp (2 * ξ v - 2 * ξ x)| * |q v| * |lgIter I q ξ n v|
            ≤ 1 * |q v| * ((volterraV I q v / 2) ^ n / n.factorial) := by gcongr
          _ = |q v| * ((volterraV I q v / 2) ^ n / n.factorial / 2) * 2 := by ring
      rw [integral_mul_const, key] at hle
      linarith

theorem lgIter_summable {x : ℝ} (hx : x ∈ I) :
    Summable fun n => |lgIter I q ξ n x| :=
  (Real.summable_pow_div_factorial (volterraV I q x / 2)).of_nonneg_of_le (fun _ => abs_nonneg _)
    fun n => (H.lgIter_bound n).2 x hx

/-- The solution `u = ∑ hₙ` of the Volterra equation. -/
noncomputable def sol (_ : VolterraLG I q ξ s) (x : ℝ) : ℝ := ∑' n, lgIter I q ξ n x

theorem sol_sub_one {x : ℝ} (hx : x ∈ I) :
    |H.sol x - 1| ≤ Real.exp (volterraV I q x / 2) - 1 := by
  have hs := (H.lgIter_summable hx).of_abs
  rw [sol, hs.tsum_eq_zero_add, show lgIter I q ξ 0 x = 1 from rfl, add_sub_cancel_left]
  have hsum := (Real.summable_pow_div_factorial (volterraV I q x / 2))
  have h1 : Real.exp (volterraV I q x / 2) - 1 =
      ∑' n : ℕ, (volterraV I q x / 2) ^ (n + 1) / (n + 1).factorial := by
    rw [← tsum_pow_div_factorial, hsum.tsum_eq_zero_add]
    simp
  rw [h1]
  have hs1 : Summable fun n => ‖lgIter I q ξ (n + 1) x‖ := by
    simpa only [Real.norm_eq_abs] using (summable_nat_add_iff 1).mpr (H.lgIter_summable hx)
  have h2 := norm_tsum_le_tsum_norm hs1
  rw [Real.norm_eq_abs] at h2
  refine h2.trans (Summable.tsum_le_tsum (fun n => ?_) hs1 ((summable_nat_add_iff 1).mpr hsum))
  rw [Real.norm_eq_abs]
  exact (H.lgIter_bound (n + 1)).2 x hx

theorem abs_sol_le {x : ℝ} (hx : x ∈ I) : |H.sol x| ≤ Real.exp (volterraV I q x / 2) := by
  have := H.sol_sub_one hx
  have h := abs_sub_abs_le_abs_sub (H.sol x) 1
  rw [abs_one] at h
  linarith

theorem sol_cont : ContinuousOn H.sol I := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := exists_gt_mem H.isOpen hx
  have hS : IsOpen (I ∩ Iio b) := H.isOpen.inter isOpen_Iio
  have hc : ContinuousOn H.sol (I ∩ Iio b) :=
    continuousOn_tsum (fun n => (H.lgIter_bound n).1.mono inter_subset_left)
      (Real.summable_pow_div_factorial (volterraV I q b / 2)) fun n y hy => by
        rw [Real.norm_eq_abs]
        refine ((H.lgIter_bound n).2 y hy.1).trans ?_
        gcongr
        · exact div_nonneg (H.V_nonneg y) zero_le_two
        · exact H.V_mono hb hy.2.le
  exact (hc.continuousAt (hS.mem_nhds ⟨hx, hxb⟩)).continuousWithinAt

theorem sol_bdd : ∀ x ∈ I, ∃ C, ∀ v ∈ I ∩ Iic x, |H.sol v| ≤ C := fun x hx =>
  ⟨Real.exp (volterraV I q x / 2), fun v hv => (H.abs_sol_le hv.1).trans
    (Real.exp_le_exp.mpr (by linarith [H.V_mono hx hv.2]))⟩

/-- The Volterra equation `u(x) = 1 − ½ ∫_{a₁}^{x} (1 − e^{2ξ(v)−2ξ(x)}) q(v) u(v) dv`. -/
theorem sol_eq {x : ℝ} (hx : x ∈ I) :
    H.sol x = 1 - 1 / 2 * ∫ v in I ∩ Iic x, (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * H.sol v := by
  have hs := (H.lgIter_summable hx).of_abs
  simp only [sol]
  rw [hs.tsum_eq_zero_add]
  simp only [lgIter]
  rw [tsum_mul_left]
  -- interchange of `∑` and `∫`
  have hF : ∀ n, IntegrableOn
      (fun v => (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * lgIter I q ξ n v) (I ∩ Iic x) := by
    intro n
    have hexp : ContinuousOn (fun v => 1 - Real.exp (2 * ξ v - 2 * ξ x)) I :=
      continuousOn_const.sub (Real.continuous_exp.comp_continuousOn
        ((continuousOn_const.mul H.ξ_cont).sub continuousOn_const))
    refine H.integrableOn_mul hexp (H.lgIter_bound n).1 hx
      (C := (volterraV I q x / 2) ^ n / n.factorial) fun v hv => ?_
    rw [abs_mul]
    calc |1 - Real.exp (2 * ξ v - 2 * ξ x)| * |lgIter I q ξ n v|
        ≤ 1 * ((volterraV I q v / 2) ^ n / n.factorial) :=
          mul_le_mul (H.abs_kernel_le hv.1 hx hv.2) ((H.lgIter_bound n).2 v hv.1)
            (abs_nonneg _) zero_le_one
      _ ≤ (volterraV I q x / 2) ^ n / n.factorial := by
          rw [one_mul]
          gcongr
          · exact div_nonneg (H.V_nonneg v) zero_le_two
          · exact H.V_mono hx hv.2
  have hFs : Summable fun n => ∫ v in I ∩ Iic x,
      ‖(1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * lgIter I q ξ n v‖ := by
    refine ((Real.summable_pow_div_factorial (volterraV I q x / 2)).mul_left
      (volterraV I q x)).of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      fun n => ?_
    calc ∫ v in I ∩ Iic x, ‖(1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * lgIter I q ξ n v‖
        ≤ ∫ v in I ∩ Iic x, |q v| * ((volterraV I q x / 2) ^ n / n.factorial) := by
          refine setIntegral_mono_on (hF n).norm ((H.q_int x hx).abs.mul_const _) (H.measR x)
            fun v hv => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          calc |1 - Real.exp (2 * ξ v - 2 * ξ x)| * |q v| * |lgIter I q ξ n v|
              ≤ 1 * |q v| * ((volterraV I q x / 2) ^ n / n.factorial) := by
                gcongr
                · exact H.abs_kernel_le hv.1 hx hv.2
                · refine ((H.lgIter_bound n).2 v hv.1).trans ?_
                  gcongr
                  · exact div_nonneg (H.V_nonneg v) zero_le_two
                  · exact H.V_mono hx hv.2
            _ = |q v| * ((volterraV I q x / 2) ^ n / n.factorial) := by ring
      _ = volterraV I q x * ((volterraV I q x / 2) ^ n / n.factorial) := by
          rw [integral_mul_const, volterraV]
  rw [integral_tsum_of_summable_integral_norm hF hFs]
  have : ∀ v, ∑' n, (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * lgIter I q ξ n v =
      (1 - Real.exp (2 * ξ v - 2 * ξ x)) * q v * ∑' n, lgIter I q ξ n v := fun v => tsum_mul_left
  simp only [this]
  ring

/-- `P(x) = e^{−2ξ(x)} ∫_{a₁}^{x} e^{2ξ} q u`. -/
noncomputable def solP (_ : VolterraLG I q ξ s) (x : ℝ) : ℝ :=
  Real.exp (-(2 * ξ x)) * ∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * ∑' n, lgIter I q ξ n v

theorem sol_hasDerivAt {x : ℝ} (hx : x ∈ I) : HasDerivAt H.sol (-(s x) * H.solP x) x := by
  have hK := (H.hasDerivAt_kernel H.sol_cont H.sol_bdd hx).const_mul (1 / 2) |>.const_sub 1
  refine hK.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [H.isOpen.mem_nhds hx] with y hy using H.sol_eq hy
  · simp only [solP, sol]
    ring

theorem solP_hasDerivAt {x : ℝ} (hx : x ∈ I) :
    HasDerivAt H.solP (-2 * s x * H.solP x + q x * H.sol x) x := by
  have hexp : ContinuousOn (fun v => Real.exp (2 * ξ v)) I :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul H.ξ_cont)
  have i2 : ∀ y ∈ I, IntegrableOn (fun v => Real.exp (2 * ξ v) * q v * H.sol v) (I ∩ Iic y) :=
    fun y hy => by
      obtain ⟨C, hC⟩ := H.sol_bdd y hy
      refine H.integrableOn_mul hexp H.sol_cont hy (C := Real.exp (2 * ξ y) * C) fun v hv => ?_
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [H.ξ_mono hv.1 hy hv.2])) (hC v hv)
        (abs_nonneg _) (Real.exp_pos _).le
  have hB := hasDerivAt_setIntegral_Iic H.isOpen H.ordConnected
    ((hexp.mul H.q_cont).mul H.sol_cont) i2 hx
  have hE : HasDerivAt (fun y => Real.exp (-(2 * ξ y))) (Real.exp (-(2 * ξ x)) * -(2 * s x)) x :=
    ((H.ξ_deriv x hx).const_mul 2).neg.exp
  refine (hE.mul hB).congr_deriv ?_
  have : Real.exp (-(2 * ξ x)) * Real.exp (2 * ξ x) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [solP, sol, Pi.mul_apply]
  linear_combination (q x * ∑' n, lgIter I q ξ n x) * this

theorem abs_solP_le {x : ℝ} (hx : x ∈ I) :
    |H.solP x| ≤ 2 * (Real.exp (volterraV I q x / 2) - 1) := by
  have hΦ : ∀ t : ℝ, HasDerivAt (fun t => 2 * Real.exp (t / 2)) (Real.exp (t / 2)) t := by
    intro t
    have := (((hasDerivAt_id t).div_const 2).exp).const_mul 2
    exact this.congr_deriv (by simp only [id]; ring)
  obtain ⟨hint, heq⟩ := H.integral_abs_mul_comp_V hΦ (by fun_prop)
  have key := heq x hx
  simp only [zero_div, Real.exp_zero, mul_one] at key
  have hle : |∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * H.sol v| ≤
      Real.exp (2 * ξ x) * ∫ v in I ∩ Iic x, |q v| * Real.exp (volterraV I q v / 2) := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hint x hx).const_mul _) ?_
    refine (ae_restrict_iff' (H.measR x)).mpr (Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (2 * ξ v) ≤ Real.exp (2 * ξ x) :=
      Real.exp_le_exp.mpr (by linarith [H.ξ_mono hv.1 hx hv.2])
    have h2 := H.abs_sol_le hv.1
    calc Real.exp (2 * ξ v) * |q v| * |H.sol v|
        ≤ Real.exp (2 * ξ x) * |q v| * Real.exp (volterraV I q v / 2) := by gcongr
      _ = Real.exp (2 * ξ x) * (|q v| * Real.exp (volterraV I q v / 2)) := by ring
  rw [key] at hle
  have hP : H.solP x = Real.exp (-(2 * ξ x)) *
      ∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * H.sol v := rfl
  rw [hP, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hee : Real.exp (-(2 * ξ x)) * Real.exp (2 * ξ x) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-(2 * ξ x)) * |∫ v in I ∩ Iic x, Real.exp (2 * ξ v) * q v * H.sol v|
      ≤ Real.exp (-(2 * ξ x)) * (Real.exp (2 * ξ x) *
          (2 * Real.exp (volterraV I q x / 2) - 2)) :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = 2 * (Real.exp (volterraV I q x / 2) - 1) := by
        rw [← mul_assoc, hee]
        ring

/-- **The Volterra solution**: `u′ = −sP`, `P′ = −2sP + qu`, `|u − 1| ≤ e^{V/2} − 1`,
`|P| ≤ 2(e^{V/2} − 1)`. -/
theorem exists_solution :
    ∃ u P : ℝ → ℝ, (∀ x ∈ I, HasDerivAt u (-(s x) * P x) x) ∧
      (∀ x ∈ I, HasDerivAt P (-2 * s x * P x + q x * u x) x) ∧
      ∀ x ∈ I, |u x - 1| ≤ Real.exp (volterraV I q x / 2) - 1 ∧
        |P x| ≤ 2 * (Real.exp (volterraV I q x / 2) - 1) :=
  ⟨H.sol, H.solP, fun _ hx => H.sol_hasDerivAt hx, fun _ hx => H.solP_hasDerivAt hx,
    fun _ hx => ⟨H.sol_sub_one hx, H.abs_solP_le hx⟩⟩

end VolterraLG

end Azurite.DLMF

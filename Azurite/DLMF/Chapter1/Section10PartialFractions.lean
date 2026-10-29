/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section10Laurent
import Azurite.DLMF.Chapter1.Section10Products
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# DLMF §1.10(x): Infinite Partial Fractions

Formalizations of <https://dlmf.nist.gov/1.10.x>.

* 1.10.23: `dlmf_1_10_23`. If `F(z) = ∏_{n=1}^∞ aₙ(z)` with analytic factors and convergence that
  is uniform on compact subsets of `D`, then `F` is analytic. This is the locally uniform limit
  theorem, `TendstoLocallyUniformlyOn.differentiableOn`.
* 1.10.24: `dlmf_1_10_24`. If moreover the product converges in the sense of §1.10(ix) and no
  factor vanishes, then `F ≠ 0` and `F′/F = Σ aₙ′/aₙ`. The proof uses `logDeriv_fun_prod` on
  the partial products and `TendstoLocallyUniformlyOn.deriv`.
* 1.10.25 (Mittag-Leffler): `dlmf_1_10_25` treats `f(z) = Σ aₙ(1/(z − zₙ) + 1/zₙ)`
  (`mittagLeffler`). The series converges and `f` is analytic off the `zₙ`. Near `zₖ`,
  `f = aₖ/(z − zₖ) + g` with `g` analytic, and the residue at `zₖ` is `aₖ`.
  * Added hypothesis: `|zₙ| → ∞`. DLMF leaves it implicit; without it the poles could accumulate.
  * Dropped hypothesis: `zₙ ≠ 0` is not needed, since Lean's `1/0 = 0`.
  * Proof: on `|z| < R`, the terms with `|zₙ| > 2R` are bounded by `2R|aₙ zₙ^{−2}|`
    (`norm_mlTerm_le`). This leaves finitely many rational terms plus an analytic remainder
    (`mittagLeffler_split`).
-/

open Filter Topology Metric Complex Finset
open scoped Real

namespace Azurite.DLMF

/-! ### Products of analytic functions -/

/-- **DLMF 1.10.23**: if `aₙ(z)` is analytic in `D` for all `n ≥ 1` and `F(z) = ∏_{n=1}^∞ aₙ(z)`
with the partial products converging uniformly on every compact subset of `D`, then `F` is
analytic in `D`. -/
theorem dlmf_1_10_23 {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n ≥ 1, DifferentiableOn ℂ (a n) D) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun m z => ∏ n ∈ Ico 1 (m + 1), a n z) F atTop K) :
    AnalyticOnNhd ℂ F D :=
  (((tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu).differentiableOn
    (Eventually.of_forall fun _ => DifferentiableOn.fun_finsetProd fun n hn =>
      ha n (Finset.mem_Ico.mp hn).1) hD).analyticOnNhd hD

/-- **DLMF 1.10.24**: if moreover the product converges at each `z ∈ D` (in the sense of
§1.10(ix)) and `aₙ(z) ≠ 0` for `n ≥ 1`, `z ∈ D`, then `F(z) ≠ 0` in `D` and
`F′(z)/F(z) = ∑_{n=1}^∞ aₙ′(z)/aₙ(z)`. -/
theorem dlmf_1_10_24 {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n ≥ 1, DifferentiableOn ℂ (a n) D) {F : ℂ → ℂ}
    (hu : ∀ K ⊆ D, IsCompact K →
      TendstoUniformlyOn (fun m z => ∏ n ∈ Ico 1 (m + 1), a n z) F atTop K)
    (hc : ∀ z ∈ D, InfProdConverges fun n => a n z - 1) (hne : ∀ n ≥ 1, ∀ z ∈ D, a n z ≠ 0) :
    (∀ z ∈ D, F z ≠ 0) ∧ ∀ z ∈ D,
      Tendsto (fun m => ∑ n ∈ Ico 1 (m + 1), deriv (a n) z / a n z) atTop
        (𝓝 (deriv F z / F z)) := by
  set P : ℕ → ℂ → ℂ := fun m z => ∏ n ∈ Ico 1 (m + 1), a n z with hP
  have hloc : TendstoLocallyUniformlyOn P F atTop D :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mpr hu
  have hPd : ∀ m, DifferentiableOn ℂ (P m) D := fun m =>
    DifferentiableOn.fun_finsetProd fun n hn => ha n (Finset.mem_Ico.mp hn).1
  have hF0 : ∀ z ∈ D, F z ≠ 0 := by
    intro z hz h0
    obtain ⟨Pv, hPv, hPz⟩ := (hc z hz).exists_tendsto
    have heq : ∀ m, partialProd (fun n => a n z - 1) 1 m = P m z := fun m => by
      simp [partialProd, hP]
    have hlim : Tendsto (fun m => P m z) atTop (𝓝 Pv) := hPv.congr heq
    rw [tendsto_nhds_unique (hloc.tendsto_at hz) hlim] at h0
    obtain ⟨n, hn, h⟩ := hPz.mp h0
    exact hne n hn z hz (by linear_combination h)
  refine ⟨hF0, fun z hz => ?_⟩
  have hder : Tendsto (fun m => deriv (P m) z) atTop (𝓝 (deriv F z)) :=
    (hloc.deriv (Eventually.of_forall hPd) hD).tendsto_at hz
  refine (hder.div (hloc.tendsto_at hz) (hF0 z hz)).congr fun m => ?_
  have hlog := logDeriv_fun_prod (s := Ico 1 (m + 1)) (f := a) (x := z)
    (fun n hn => hne n (Finset.mem_Ico.mp hn).1 z hz)
    (fun n hn => (ha n (Finset.mem_Ico.mp hn).1).differentiableAt (hD.mem_nhds hz))
  simp only [logDeriv_apply] at hlog
  exact hlog

/-! ### Mittag-Leffler's expansion -/

/-- The term `aₙ (1/(z − zₙ) + 1/zₙ)`. -/
noncomputable def mlTerm (a zs : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ := a n * (1 / (z - zs n) + 1 / zs n)

/-- **DLMF 1.10.25**: `f(z) = ∑_{n=1}^∞ aₙ (1/(z − zₙ) + 1/zₙ)`. -/
noncomputable def mittagLeffler (a zs : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, mlTerm a zs (n + 1) z

theorem differentiableAt_mlTerm (a zs : ℕ → ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ zs n) :
    DifferentiableAt ℂ (mlTerm a zs n) z := by
  unfold mlTerm
  simp only [one_div]
  have h1 : DifferentiableAt ℂ (fun w => w - zs n) z := by fun_prop
  exact ((h1.inv (sub_ne_zero.mpr hz : (fun w => w - zs n) z ≠ 0)).add_const _).const_mul _

theorem norm_mlTerm_le {a c z : ℂ} {R : ℝ} (hc : 2 * R < ‖c‖) (hz : ‖z‖ < R) :
    ‖a * (1 / (z - c) + 1 / c)‖ ≤ 2 * R * ‖a * (c ^ 2)⁻¹‖ := by
  have hR : 0 < R := (norm_nonneg _).trans_lt hz
  have hc0 : c ≠ 0 := norm_pos_iff.mp (by linarith)
  have hzc' : ‖c‖ / 2 ≤ ‖z - c‖ := by
    rw [norm_sub_rev]
    linarith [norm_sub_norm_le c z]
  have hzc : z - c ≠ 0 := norm_pos_iff.mp (by linarith [norm_nonneg c])
  have heq : 1 / (z - c) + 1 / c = z / (c * (z - c)) := by
    field_simp
    ring
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  rw [heq, norm_mul, norm_div, norm_mul, norm_mul, norm_inv, norm_pow]
  calc ‖a‖ * (‖z‖ / (‖c‖ * ‖z - c‖)) ≤ ‖a‖ * (R / (‖c‖ * (‖c‖ / 2))) := by
        gcongr
    _ = 2 * R * (‖a‖ * (‖c‖ ^ 2)⁻¹) := by
        field_simp

/-- On `|z| < R`, the Mittag-Leffler series splits into finitely many terms with `|zₙ| ≤ 2R` and an
analytic remainder `G`. -/
theorem mittagLeffler_split {a zs : ℕ → ℂ} (hinf : Tendsto (fun n => ‖zs n‖) atTop atTop)
    (hs : Summable fun n => ‖a n * (zs n ^ 2)⁻¹‖) {R : ℝ} (hR : 0 < R) :
    ∃ Fs : Finset ℕ, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 R) ∧
      (∀ n ∉ Fs, 2 * R < ‖zs (n + 1)‖) ∧ ∀ z ∈ ball (0 : ℂ) R,
        HasSum (fun n => mlTerm a zs (n + 1) z)
          (∑ n ∈ Fs, mlTerm a zs (n + 1) z + G z) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hinf.eventually (eventually_gt_atTop (2 * R)))
  set Fs := (range N).filter fun n => ‖zs (n + 1)‖ ≤ 2 * R
  have hout : ∀ n ∉ Fs, 2 * R < ‖zs (n + 1)‖ := fun n hn => by
    by_cases hnN : n < N
    · simp only [Fs, mem_filter, mem_range, not_and, not_le] at hn
      exact hn hnN
    · exact hN (n + 1) (by omega)
  set u : ℕ → ℝ := fun n => 2 * R * ‖a (n + 1) * (zs (n + 1) ^ 2)⁻¹‖
  have hu : Summable u := ((summable_nat_add_iff 1).mpr hs).mul_left _
  set T : ℕ → ℂ → ℂ := fun n z => if n ∈ Fs then 0 else mlTerm a zs (n + 1) z with hT
  have hTle : ∀ n, ∀ z ∈ ball (0 : ℂ) R, ‖T n z‖ ≤ u n := by
    intro n z hz
    rw [mem_ball, dist_zero_right] at hz
    by_cases hn : n ∈ Fs
    · simp only [hT, hn, ↓reduceIte, norm_zero, u]
      positivity
    · simp only [hT, hn, ↓reduceIte, mlTerm, u]
      exact norm_mlTerm_le (hout n hn) hz
  have hTd : ∀ n, DifferentiableOn ℂ (T n) (ball 0 R) := by
    intro n
    by_cases hn : n ∈ Fs
    · simp only [hT, hn, ↓reduceIte]
      exact differentiableOn_const _
    · simp only [hT, hn, ↓reduceIte]
      intro z hz
      rw [mem_ball, dist_zero_right] at hz
      have hzc : z ≠ zs (n + 1) := fun h => by
        have := hout n hn
        rw [← h] at this
        linarith
      exact (differentiableAt_mlTerm a zs (n + 1) hzc).differentiableWithinAt
  refine ⟨Fs, fun z => ∑' n, T n z,
    differentiableOn_tsum_of_summable_norm hu hTd isOpen_ball hTle, hout, fun z hz => ?_⟩
  have hsT : Summable fun n => T n z :=
    Summable.of_norm_bounded hu fun n => hTle n z hz
  have hfin : HasSum (fun n => if n ∈ Fs then mlTerm a zs (n + 1) z else 0)
      (∑ n ∈ Fs, if n ∈ Fs then mlTerm a zs (n + 1) z else 0) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by simp [hn]
  rw [sum_congr rfl fun n hn => (by simp [hn] :
    (if n ∈ Fs then mlTerm a zs (n + 1) z else 0) = mlTerm a zs (n + 1) z)] at hfin
  convert hfin.add hsT.hasSum using 1
  funext n
  by_cases hn : n ∈ Fs <;> simp [hT, hn]

/-- **DLMF 1.10.25** (Mittag-Leffler's expansion): if `zₘ ≠ zₙ` (`m ≠ n`), `|zₙ| → ∞` and
`∑ |aₙ zₙ^{−2}|` converges, then `f(z) = ∑_{n=1}^∞ aₙ (1/(z − zₙ) + 1/zₙ)` converges and is
analytic at every `z ≠ zₙ`; near `zₖ`, `f(z) = aₖ/(z − zₖ) + g(z)` with `g` analytic (a simple pole
when `aₖ ≠ 0`), and the residue at `zₖ` is `aₖ`. -/
theorem dlmf_1_10_25 {a zs : ℕ → ℂ} (hinj : ∀ m ≥ 1, ∀ n ≥ 1, m ≠ n → zs m ≠ zs n)
    (hinf : Tendsto (fun n => ‖zs n‖) atTop atTop)
    (hs : Summable fun n => ‖a n * (zs n ^ 2)⁻¹‖) :
    (∀ z, (∀ n ≥ 1, z ≠ zs n) →
      HasSum (fun n => mlTerm a zs (n + 1) z) (mittagLeffler a zs z) ∧
        AnalyticAt ℂ (mittagLeffler a zs) z) ∧
    ∀ k ≥ 1, ∃ r > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball (zs k) r) ∧
      (∀ z ∈ ball (zs k) r, z ≠ zs k → mittagLeffler a zs z = a k / (z - zs k) + g z) ∧
      residue (mittagLeffler a zs) (zs k) r = a k := by
  -- the split on the ball of radius `R`, and `f` equals it there
  have hsplit := fun (R : ℝ) (hR : 0 < R) => mittagLeffler_split hinf hs hR
  have hfeq : ∀ {R : ℝ} {Fs : Finset ℕ} {G : ℂ → ℂ}, (∀ z ∈ ball (0 : ℂ) R,
      HasSum (fun n => mlTerm a zs (n + 1) z) (∑ n ∈ Fs, mlTerm a zs (n + 1) z + G z)) →
      ∀ z ∈ ball (0 : ℂ) R, mittagLeffler a zs z = ∑ n ∈ Fs, mlTerm a zs (n + 1) z + G z :=
    fun h z hz => (h z hz).tsum_eq
  have hterm : ∀ n z, z ≠ zs n → DifferentiableAt ℂ (mlTerm a zs n) z := fun n _ hz =>
    differentiableAt_mlTerm a zs n hz
  refine ⟨fun z hz => ?_, fun k hk => ?_⟩
  · obtain ⟨Fs, G, hG, -, hsum⟩ := hsplit (‖z‖ + 1) (by positivity)
    have hzR : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by
      rw [mem_ball, dist_zero_right]
      linarith
    refine ⟨?_, ?_⟩
    · rw [hfeq hsum z hzR]
      exact hsum z hzR
    set U := ball (0 : ℂ) (‖z‖ + 1) ∩ ⋂ n ∈ Fs, {w | w ≠ zs (n + 1)}
    have hUo : IsOpen U := isOpen_ball.inter (isOpen_biInter_finset fun n _ =>
      isOpen_ne)
    have hzU : z ∈ U := ⟨hzR, Set.mem_iInter₂.mpr fun n _ => hz (n + 1) (by omega)⟩
    have hd : DifferentiableOn ℂ (fun w => ∑ n ∈ Fs, mlTerm a zs (n + 1) w + G w) U :=
      (DifferentiableOn.fun_sum fun n hn w hw =>
        (hterm _ w (Set.mem_iInter₂.mp hw.2 n hn)).differentiableWithinAt).add
        (hG.mono Set.inter_subset_left)
    exact (hd.analyticAt (hUo.mem_nhds hzU)).congr
      (eventually_of_mem (hUo.mem_nhds hzU) fun w hw => (hfeq hsum w hw.1).symm)
  · obtain ⟨Fs, G, hG, hout, hsum⟩ := hsplit (‖zs k‖ + 1) (by positivity)
    have hkF : k - 1 ∈ Fs := by
      by_contra h
      have := hout _ h
      rw [Nat.sub_add_cancel hk] at this
      linarith [norm_nonneg (zs k)]
    set U := ball (0 : ℂ) (‖zs k‖ + 1) ∩ ⋂ n ∈ Fs.erase (k - 1), {w | w ≠ zs (n + 1)}
    have hUo : IsOpen U := isOpen_ball.inter (isOpen_biInter_finset fun n _ => isOpen_ne)
    have hkU : zs k ∈ U := by
      refine ⟨by rw [mem_ball, dist_zero_right]; linarith, Set.mem_iInter₂.mpr fun n hn => ?_⟩
      have hne : n + 1 ≠ k := fun h => (Finset.mem_erase.mp hn).1 (by omega)
      exact (hinj _ (by omega) k hk hne).symm
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUo _ hkU
    set g : ℂ → ℂ := fun z => a k / zs k + ∑ n ∈ Fs.erase (k - 1), mlTerm a zs (n + 1) z + G z
      with hgdef
    have hgd : DifferentiableOn ℂ g (ball (zs k) r) := fun w hw =>
      (((differentiableAt_const _).add (DifferentiableAt.fun_sum fun n hn =>
        hterm _ w (Set.mem_iInter₂.mp (hrU hw).2 n hn))).add
        (hG.differentiableAt (isOpen_ball.mem_nhds (hrU hw).1))).differentiableWithinAt
    have hfg : ∀ z ∈ ball (zs k) r, z ≠ zs k → mittagLeffler a zs z = a k / (z - zs k) + g z := by
      intro z hz hzk
      rw [hfeq hsum z (hrU hz).1, ← add_sum_erase _ _ hkF, Nat.sub_add_cancel hk, hgdef, mlTerm]
      simp only
      ring
    refine ⟨r, hr, g, hgd, hfg, ?_⟩
    -- the residue
    have hann : DifferentiableOn ℂ (mittagLeffler a zs) (annulus (zs k) 0 r) := by
      intro z hz
      have hz' : 0 < ‖z - zs k‖ ∧ ‖z - zs k‖ < r := hz
      have hzb : z ∈ ball (zs k) r := by rw [mem_ball, dist_eq_norm]; exact hz'.2
      have hzk : z ≠ zs k := fun h => by rw [h, sub_self, norm_zero] at hz'; exact lt_irrefl _ hz'.1
      have hev : (fun w => a k / (w - zs k) + g w) =ᶠ[𝓝 z] mittagLeffler a zs := by
        filter_upwards [isOpen_ball.mem_nhds hzb, isOpen_ne.mem_nhds hzk] with w hw hwk
        exact (hfg w hw hwk).symm
      have hd1 : DifferentiableAt ℂ (fun w => a k / (w - zs k) + g w) z :=
        ((differentiableAt_const _).div (show DifferentiableAt ℂ (fun w => w - zs k) z by fun_prop)
          (sub_ne_zero.mpr hzk : (fun w => w - zs k) z ≠ 0)).add
          (hgd.differentiableAt (isOpen_ball.mem_nhds hzb))
      exact (hd1.congr_of_eventuallyEq hev.symm).differentiableWithinAt
    have hr2 : r / 2 ∈ Set.Ioo 0 r := ⟨by positivity, by linarith⟩
    rw [residue_eq hann hr2]
    have hsph : Set.EqOn (mittagLeffler a zs) (fun z => a k * (z - zs k)⁻¹ + g z)
        (sphere (zs k) (r / 2)) := by
      intro z hz
      have hzr : dist z (zs k) = r / 2 := hz
      rw [hfg z (by rw [mem_ball]; linarith) (fun h => by rw [h, dist_self] at hzr; linarith),
        div_eq_mul_inv]
    have hgc : ContinuousOn g (Metric.closedBall (zs k) (r / 2)) :=
      hgd.continuousOn.mono (closedBall_subset_ball (by linarith))
    have hi1 : CircleIntegrable (fun z => a k * (z - zs k)⁻¹) (zs k) (r / 2) :=
      (continuousOn_const.mul (ContinuousOn.inv₀ (f := fun z => z - zs k) (by fun_prop)
        fun z hz h => by
        rw [sub_eq_zero] at h
        rw [h, mem_sphere, dist_self] at hz
        linarith)).circleIntegrable (by positivity)
    have hi2 : CircleIntegrable g (zs k) (r / 2) :=
      (hgc.mono sphere_subset_closedBall).circleIntegrable (by positivity)
    rw [circleIntegral.integral_congr (by positivity) hsph, circleIntegral.integral_add hi1 hi2,
      circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv _ (by positivity),
      circleIntegral_eq_zero_of_differentiable_on_off_countable (by positivity)
        Set.countable_empty hgc fun z hz => hgd.differentiableAt (isOpen_ball.mem_nhds
          (ball_subset_ball (by linarith) hz.1))]
    rw [add_zero]
    field_simp

end Azurite.DLMF

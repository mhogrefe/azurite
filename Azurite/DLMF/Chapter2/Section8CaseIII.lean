/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section8CaseII

/-!
# DLMF §2.8(iv): Case III: Simple Pole, 2.8.24–2.8.34

For `d²W/dξ² = (u²/(4ξ) + (ν² − 1)/(4ξ²) + ψ(ξ)/ξ) W` (2.8.24) on `(α₁, α₂) ∋ 0`:

* Bessel pairs (`besselPair_pos`, `besselPair_neg`): for `ξ > 0`, `a = ξ^{1/2} 𝓕_ν(uξ^{1/2})`,
  `b = ξ 𝓕_{ν+1}(uξ^{1/2})` with `(𝓕_ν, 𝓕_{ν+1}) = (I_ν, I_{ν+1})` or `(K_ν, −K_{ν+1})`;
  for `ξ < 0`, `a = |ξ|^{1/2} 𝓕_ν(u|ξ|^{1/2})`, `b = −|ξ| 𝓕_{ν+1}(u|ξ|^{1/2})` with
  `(J_ν, J_{ν+1})` or `(Y_ν, Y_{ν+1})` — given only the recurrences 10.29.2 / 10.6.2 — all
  satisfy the same system
  `a′ = ((ν+1)/(2ξ)) a + (u/(2ξ)) b`, `b′ = (u/2) a + ((1−ν)/(2ξ)) b` (`IsCaseIIIPair`).
* 2.8.25–2.8.26, 2.8.29–2.8.30 as formal expansions (`CaseIIIData.dlmf_2_8_25_formal`): for any
  such pair, `W = a ∑_{s<n} A_s/u^{2s} + b ∑_{s<n−1} B_s/u^{2s+1}` satisfies 2.8.24 up to the single
  residual `a · u^{2−2n} (A″_{n−1} + (ν+1)A′_{n−1}/ξ − ψA_{n−1}/ξ)`.
* 2.8.27, 2.8.31 (`dlmf_2_8_27`, `dlmf_2_8_31`): DLMF's one-sided formulas for `B_s` both equal
  `−A_s′ + 2∫_0^1 g(ξσ²) dσ`, `g = ψA_s − (ν + ½)A_s′`, which is `C^∞` through `ξ = 0`.
* 2.8.28 (`caseIIIA`, `caseIIIB`, `dlmf_2_8_28`): the `C^∞` coefficient chain with
  `ξB_s′ + ½B_s = ψA_s − (ν+1)A_s′ − ξA_s″` and `A_{s+1}′ = (ν−1)B_s′ − ξB_s″ + ψB_s`.
* 2.8.33–2.8.34 (`envJ`, `envY`, `envJ_envY_continuous`): the envelopes are continuous, given
  `J_ν(X) + Y_ν(X) = 0` (2.8.32) with `J_ν(X) ≥ 0`.

Not formalized: the error terms of 2.8.25–2.8.26, 2.8.29–2.8.30, 2.8.35–2.8.36 (Olver, Ch. 12),
which need the theory of Bessel functions (DLMF Ch. 10), and the existence of `X_ν` (2.8.32).
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace Azurite.DLMF

variable {I : Set ℝ}

/-! ### Bessel pairs -/

/-- The first-order system satisfied by `a = |ξ|^{1/2} 𝓕_ν`, `b = ±|ξ| 𝓕_{ν+1}` at `ξ`. -/
def IsCaseIIIPair (ν u : ℝ) (a b : ℝ → ℝ) (x : ℝ) : Prop :=
  HasDerivAt a ((ν + 1) / (2 * x) * a x + u / (2 * x) * b x) x ∧
    HasDerivAt b (u / 2 * a x + (1 - ν) / (2 * x) * b x) x

/-- `ξ > 0`, modified Bessel functions: if `𝓕₀′ = 𝓕₁ + (ν/t)𝓕₀` and `𝓕₁′ = 𝓕₀ − ((ν+1)/t)𝓕₁`
(DLMF 10.29.2 for `(I_ν, I_{ν+1})` and `(K_ν, −K_{ν+1})`), then
`(ξ^{1/2}𝓕₀(uξ^{1/2}), ξ𝓕₁(uξ^{1/2}))` is a Case III pair. -/
theorem besselPair_pos {F₀ F₁ : ℝ → ℝ} {ν u : ℝ} (hu : 0 < u)
    (h0 : ∀ t, 0 < t → HasDerivAt F₀ (F₁ t + ν / t * F₀ t) t)
    (h1 : ∀ t, 0 < t → HasDerivAt F₁ (F₀ t - (ν + 1) / t * F₁ t) t) {x : ℝ} (hx : 0 < x) :
    IsCaseIIIPair ν u (fun y => Real.sqrt y * F₀ (u * Real.sqrt y))
      (fun y => y * F₁ (u * Real.sqrt y)) x := by
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have hr : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hrr : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have ht : 0 < u * Real.sqrt x := mul_pos hu hr
  have hT := hs.const_mul u
  have hF0 := (h0 _ ht).comp x hT
  have hF1 := (h1 _ ht).comp x hT
  set r := Real.sqrt x
  set p := F₀ (u * r)
  set q := F₁ (u * r)
  constructor
  · refine (hs.mul hF0).congr_deriv ?_
    show 1 / (2 * r) * p + r * ((q + ν / (u * r) * p) * (u * (1 / (2 * r)))) =
      (ν + 1) / (2 * x) * (r * p) + u / (2 * x) * (x * q)
    rw [← hrr]
    field_simp
    ring
  · refine ((hasDerivAt_id x).mul hF1).congr_deriv ?_
    show 1 * q + x * ((p - (ν + 1) / (u * r) * q) * (u * (1 / (2 * r)))) =
      u / 2 * (r * p) + (1 - ν) / (2 * x) * (x * q)
    rw [← hrr]
    field_simp
    ring

/-- `ξ < 0`, Bessel functions: if `𝓕₀′ = −𝓕₁ + (ν/t)𝓕₀` and `𝓕₁′ = 𝓕₀ − ((ν+1)/t)𝓕₁`
(DLMF 10.6.2 for `(J_ν, J_{ν+1})`, `(Y_ν, Y_{ν+1})`), then
`(|ξ|^{1/2}𝓕₀(u|ξ|^{1/2}), −|ξ|𝓕₁(u|ξ|^{1/2}))` is a Case III pair. -/
theorem besselPair_neg {F₀ F₁ : ℝ → ℝ} {ν u : ℝ} (hu : 0 < u)
    (h0 : ∀ t, 0 < t → HasDerivAt F₀ (-F₁ t + ν / t * F₀ t) t)
    (h1 : ∀ t, 0 < t → HasDerivAt F₁ (F₀ t - (ν + 1) / t * F₁ t) t) {x : ℝ} (hx : x < 0) :
    IsCaseIIIPair ν u (fun y => Real.sqrt (-y) * F₀ (u * Real.sqrt (-y)))
      (fun y => y * F₁ (u * Real.sqrt (-y))) x := by
  have hs : HasDerivAt (fun y => Real.sqrt (-y)) (-(1 / (2 * Real.sqrt (-x)))) x := by
    have := (Real.hasDerivAt_sqrt (by linarith : -x ≠ 0)).comp x (hasDerivAt_neg x)
    convert this using 1 <;> first | rfl | ring
  have hr : 0 < Real.sqrt (-x) := Real.sqrt_pos.mpr (by linarith)
  have hrr : Real.sqrt (-x) * Real.sqrt (-x) = -x := Real.mul_self_sqrt (by linarith)
  have ht : 0 < u * Real.sqrt (-x) := mul_pos hu hr
  have hT := hs.const_mul u
  have hF0 := (h0 _ ht).comp x hT
  have hF1 := (h1 _ ht).comp x hT
  have hx0 : x ≠ 0 := hx.ne
  set r := Real.sqrt (-x)
  set p := F₀ (u * r)
  set q := F₁ (u * r)
  have hxr : x = -(r * r) := by linarith
  constructor
  · refine (hs.mul hF0).congr_deriv ?_
    show -(1 / (2 * r)) * p + r * ((-q + ν / (u * r) * p) * (u * -(1 / (2 * r)))) =
      (ν + 1) / (2 * x) * (r * p) + u / (2 * x) * (x * q)
    rw [hxr]
    field_simp
    ring
  · refine ((hasDerivAt_id x).mul hF1).congr_deriv ?_
    show 1 * q + x * ((p - (ν + 1) / (u * r) * q) * (u * -(1 / (2 * r)))) =
      u / 2 * (r * p) + (1 - ν) / (2 * x) * (x * q)
    rw [hxr]
    field_simp
    ring

/-! ### The formal expansions -/

/-- Hypotheses on the coefficients for `n` terms: `A₀ = 1`, derivatives, and the relations 2.8.27
(`ξB_s′ + ½B_s = ψA_s − (ν+1)A_s′ − ξA_s″`) and 2.8.28 (`A_{s+1}′ = (ν−1)B_s′ − ξB_s″ + ψB_s`). -/
structure CaseIIIData (I : Set ℝ) (ψ : ℝ → ℝ) (ν : ℝ) (A A' A'' B B' B'' : ℕ → ℝ → ℝ) (n : ℕ) :
    Prop where
  A_zero : ∀ x, A 0 x = 1
  A_deriv : ∀ s < n, ∀ x ∈ I, HasDerivAt (A s) (A' s x) x
  A'_deriv : ∀ s < n, ∀ x ∈ I, HasDerivAt (A' s) (A'' s x) x
  B_deriv : ∀ s, s + 1 < n → ∀ x ∈ I, HasDerivAt (B s) (B' s x) x
  B'_deriv : ∀ s, s + 1 < n → ∀ x ∈ I, HasDerivAt (B' s) (B'' s x) x
  Beq : ∀ s, s + 1 < n → ∀ x ∈ I,
    x * B' s x + B s x / 2 = ψ x * A s x - (ν + 1) * A' s x - x * A'' s x
  Aeq : ∀ s, s + 1 < n → ∀ x ∈ I,
    A' (s + 1) x = (ν - 1) * B' s x - x * B'' s x + ψ x * B s x

/-- `∑_{s<n−1} B_s/u^{2s+1}`. -/
noncomputable def sumB3 (B : ℕ → ℝ → ℝ) (u : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (n - 1), B s x / u ^ (2 * s + 1)

theorem hasDerivAt_sumB3 {B B' : ℕ → ℝ → ℝ} {u : ℝ} {n : ℕ} {x : ℝ}
    (h : ∀ s, s + 1 < n → HasDerivAt (B s) (B' s x) x) :
    HasDerivAt (sumB3 B u n) (sumB3 B' u n x) x := by
  have := HasDerivAt.fun_sum (u := Finset.range (n - 1))
    (A := fun s y => B s y / u ^ (2 * s + 1)) (A' := fun s => B' s x / u ^ (2 * s + 1))
    fun s hs => (h s (by have := Finset.mem_range.mp hs; omega)).div_const _
  exact this

namespace CaseIIIData

variable {ψ : ℝ → ℝ} {ν : ℝ} {A A' A'' B B' B'' : ℕ → ℝ → ℝ} {n : ℕ}
  (D : CaseIIIData I ψ ν A A' A'' B B' B'' n)
include D

/-- The coefficient of `a` (times `ξ`). -/
theorem coeff_a {u : ℝ} (hu : 0 < u) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ I) :
    x * sumA A'' u n x + (ν + 1) * sumA A' u n x - ψ x * sumA A u n x +
        u * x * sumB3 B' u n x + u / 2 * sumB3 B u n x =
      (x * A'' (n - 1) x + (ν + 1) * A' (n - 1) x - ψ x * A (n - 1) x) / u ^ (2 * (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [sumA, sumB3, Nat.add_sub_cancel, Finset.sum_range_succ]
  have hz : ∀ s ∈ Finset.range m, x * (A'' s x / u ^ (2 * s)) + (ν + 1) * (A' s x / u ^ (2 * s)) -
      ψ x * (A s x / u ^ (2 * s)) + u * x * (B' s x / u ^ (2 * s + 1)) +
        u / 2 * (B s x / u ^ (2 * s + 1)) = 0 := by
    intro s hs
    have h := D.Beq s (by have := Finset.mem_range.mp hs; omega) x hx
    have hus : u ^ (2 * s) ≠ 0 := pow_ne_zero _ hu.ne'
    calc _ = (x * B' s x + B s x / 2 - (ψ x * A s x - (ν + 1) * A' s x - x * A'' s x)) /
          u ^ (2 * s) := by rw [pow_succ]; field_simp; ring
      _ = 0 := by rw [h, sub_self, zero_div]
  have hsum := Finset.sum_eq_zero hz
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  field_simp
  field_simp at hsum
  linear_combination (u ^ (2 * m)) * hsum

/-- The coefficient of `b` (times `ξ`) vanishes. -/
theorem coeff_b {u : ℝ} (hu : 0 < u) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ I) :
    x * sumB3 B'' u n x + (1 - ν) * sumB3 B' u n x + u * sumA A' u n x -
      ψ x * sumB3 B u n x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hA0 : A' 0 x = 0 := by
    have h := D.A_deriv 0 (by omega) x hx
    rw [show A 0 = fun _ => 1 from funext D.A_zero] at h
    exact h.unique (hasDerivAt_const x 1)
  simp only [sumA, sumB3, Nat.add_sub_cancel]
  rw [Finset.sum_range_succ', hA0, zero_div, add_zero, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun s hs => ?_
  have h := D.Aeq s (by have := Finset.mem_range.mp hs; omega) x hx
  have hus : u ^ (2 * s + 1) ≠ 0 := pow_ne_zero _ hu.ne'
  calc _ = (x * B'' s x + (1 - ν) * B' s x + A' (s + 1) x - ψ x * B s x) / u ^ (2 * s + 1) := by
        rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, pow_succ]; field_simp; ring
    _ = 0 := by rw [h]; ring

/-- **DLMF 2.8.25–2.8.26, 2.8.29–2.8.30** as formal expansions: for any Case III pair `(a, b)`
(`besselPair_pos`, `besselPair_neg`), `W = a ∑_{s<n} A_s/u^{2s} + b ∑_{s<n−1} B_s/u^{2s+1}`
satisfies 2.8.24 up to the single residual
`a · u^{2−2n} (A″_{n−1} + (ν+1)A′_{n−1}/ξ − ψA_{n−1}/ξ)`. -/
theorem dlmf_2_8_25_formal (hn : 1 ≤ n) {a b : ℝ → ℝ} {u : ℝ} (hu : 0 < u) {x : ℝ}
    (hx : x ∈ I) (hx0 : x ≠ 0) (hab : IsCaseIIIPair ν u a b x) :
    HasDerivAt (fun y => a y * sumA A u n y + b y * sumB3 B u n y)
      (a x * (sumA A' u n x + (ν + 1) / (2 * x) * sumA A u n x + u / 2 * sumB3 B u n x) +
        b x * (sumB3 B' u n x + u / (2 * x) * sumA A u n x +
          (1 - ν) / (2 * x) * sumB3 B u n x)) x ∧
    HasDerivAt (fun y => a y * (sumA A' u n y + (ν + 1) / (2 * y) * sumA A u n y +
          u / 2 * sumB3 B u n y) +
        b y * (sumB3 B' u n y + u / (2 * y) * sumA A u n y + (1 - ν) / (2 * y) * sumB3 B u n y))
      ((u ^ 2 / (4 * x) + (ν ^ 2 - 1) / (4 * x ^ 2) + ψ x / x) *
          (a x * sumA A u n x + b x * sumB3 B u n x) +
        a x * ((A'' (n - 1) x + (ν + 1) / x * A' (n - 1) x - ψ x / x * A (n - 1) x) /
          u ^ (2 * (n - 1)))) x := by
  obtain ⟨ha, hb⟩ := hab
  have hP := hasDerivAt_sumA (u := u) fun s hs => D.A_deriv s hs x hx
  have hP' := hasDerivAt_sumA (u := u) fun s hs => D.A'_deriv s hs x hx
  have hQ := hasDerivAt_sumB3 (u := u) fun s hs => D.B_deriv s hs x hx
  have hQ' := hasDerivAt_sumB3 (u := u) fun s hs => D.B'_deriv s hs x hx
  have hinv : ∀ k : ℝ, HasDerivAt (fun y : ℝ => k / (2 * y)) (-(k / (2 * x ^ 2))) x := by
    intro k
    have := ((hasDerivAt_id x).const_mul (2 : ℝ)).inv (mul_ne_zero two_ne_zero hx0) |>.const_mul k
    refine this.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
    · simp only [id]; field_simp
    · exact Eventually.of_forall fun y => by simp [div_eq_mul_inv]
  constructor
  · refine ((ha.mul hP).add (hb.mul hQ)).congr_deriv ?_
    ring
  · have hX := (hP'.add ((hinv (ν + 1)).mul hP)).add (hQ.const_mul (u / 2))
    have hY := (hQ'.add ((hinv u).mul hP)).add ((hinv (1 - ν)).mul hQ)
    refine ((ha.mul hX).add (hb.mul hY)).congr_deriv ?_
    simp only [Pi.add_apply, Pi.mul_apply]
    have e1 := D.coeff_a hu hn hx
    have e2 := D.coeff_b hu hn hx
    have hun : u ^ (2 * (n - 1)) ≠ 0 := pow_ne_zero _ hu.ne'
    linear_combination (norm := skip) (a x / x) * e1 + (b x / x) * e2
    field_simp
    ring

end CaseIIIData

/-! ### 2.8.27, 2.8.28, 2.8.31: the coefficients -/

/-- `B` from `A` by 2.8.27 / 2.8.31: `B = −A′ + 2∫_0^1 (ψA − (ν + ½)A′)(ξσ²) dσ`. -/
noncomputable def caseIIIBOf (ψ : ℝ → ℝ) (ν : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv A x + 2 * regB (fun v => ψ v * A v - (ν + 1 / 2) * deriv A v) x

/-- **DLMF 2.8.27–2.8.28**: `A₀ = 1`, `B_s` by 2.8.27, and
`A_{s+1} = νB_s − ξB_s′ + ∫_{x₀}^{ξ} ψB_s + c_s` (constants of integration arbitrary). -/
noncomputable def caseIIIA (ψ : ℝ → ℝ) (ν x₀ : ℝ) (c : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | s + 1 => fun x => ν * caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s) x -
      x * deriv (caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s)) x +
      (∫ t in x₀..x, ψ t * caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s) t) + c s

/-- `B_s` of 2.8.27. -/
noncomputable def caseIIIB (ψ : ℝ → ℝ) (ν x₀ : ℝ) (c : ℕ → ℝ) (s : ℕ) : ℝ → ℝ :=
  caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s)

theorem caseIIIBOf_smooth (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    {ψ A : ℝ → ℝ} (ν : ℝ) (hψ : ContDiffOn ℝ ∞ ψ I) (hA : ContDiffOn ℝ ∞ A I) :
    ContDiffOn ℝ ∞ (fun v => ψ v * A v - (ν + 1 / 2) * deriv A v) I ∧
      ContDiffOn ℝ ∞ (caseIIIBOf ψ ν A) I := by
  have hd : ContDiffOn ℝ ∞ (deriv A) I := hA.deriv_of_isOpen hI (m := ∞) (by simp)
  have hg : ContDiffOn ℝ ∞ (fun v => ψ v * A v - (ν + 1 / 2) * deriv A v) I :=
    (hψ.mul hA).sub (contDiffOn_const.mul hd)
  exact ⟨hg, hd.neg.add (contDiffOn_const.mul (regPhi_smooth hI hIc h0 0 hg))⟩

/-- **DLMF 2.8.27–2.8.28**: for `ψ` of class `C^∞` on `(α₁, α₂) ∋ 0, x₀`, all `A_s`, `B_s` are
`C^∞`, `ξB_s′ + ½B_s = ψA_s − (ν+1)A_s′ − ξA_s″` and `A_{s+1}′ = (ν−1)B_s′ − ξB_s″ + ψB_s`. -/
theorem dlmf_2_8_28 (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) {ψ : ℝ → ℝ}
    (ν : ℝ) {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hψ : ContDiffOn ℝ ∞ ψ I) (c : ℕ → ℝ) (s : ℕ) :
    ContDiffOn ℝ ∞ (caseIIIA ψ ν x₀ c s) I ∧ ContDiffOn ℝ ∞ (caseIIIB ψ ν x₀ c s) I ∧
      (∀ x ∈ I, x * deriv (caseIIIB ψ ν x₀ c s) x + caseIIIB ψ ν x₀ c s x / 2 =
        ψ x * caseIIIA ψ ν x₀ c s x - (ν + 1) * deriv (caseIIIA ψ ν x₀ c s) x -
          x * deriv (deriv (caseIIIA ψ ν x₀ c s)) x) ∧
      ∀ x ∈ I, deriv (caseIIIA ψ ν x₀ c (s + 1)) x =
        (ν - 1) * deriv (caseIIIB ψ ν x₀ c s) x - x * deriv (deriv (caseIIIB ψ ν x₀ c s)) x +
          ψ x * caseIIIB ψ ν x₀ c s x := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hA : ∀ s, ContDiffOn ℝ ∞ (caseIIIA ψ ν x₀ c s) I := by
    intro s
    induction s with
    | zero => exact contDiffOn_const
    | succ s ih =>
      have hB := (caseIIIBOf_smooth hI hIc h0 ν hψ ih).2
      have hd : ContDiffOn ℝ ∞ (deriv (caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s))) I :=
        hB.deriv_of_isOpen hI (m := ∞) (by simp)
      have hprod : ContDiffOn ℝ ∞ (fun t => ψ t * caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s) t) I :=
        hψ.mul hB
      have hG : ContDiffOn ℝ ∞
          (fun x => ∫ t in x₀..x, ψ t * caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s) t) I := by
        rw [contDiffOn_infty_iff_deriv_of_isOpen hI]
        have hGd : ∀ x ∈ I, HasDerivAt
            (fun x => ∫ t in x₀..x, ψ t * caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s) t)
            (ψ x * caseIIIBOf ψ ν (caseIIIA ψ ν x₀ c s) x) x := fun x hx =>
          integral_hasDerivAt_right
            ((hprod.continuousOn.mono (hIc.uIcc_subset hx₀ hx)).intervalIntegrable)
            (hprod.continuousOn.stronglyMeasurableAtFilter hI x hx)
            (hprod.continuousOn.continuousAt (hI.mem_nhds hx))
        exact ⟨fun x hx => (hGd x hx).differentiableAt.differentiableWithinAt,
          hprod.congr fun x hx => (hGd x hx).deriv⟩
      exact (((contDiffOn_const.mul hB).sub (contDiffOn_id.mul hd)).add hG).add contDiffOn_const
  obtain ⟨hg, hB⟩ := caseIIIBOf_smooth hI hIc h0 ν hψ (hA s)
  refine ⟨hA s, hB, fun x hx => ?_, fun x hx => ?_⟩
  · -- `B = −A′ + 2R`, `R + 2ξR′ = g`
    set g := fun v => ψ v * caseIIIA ψ ν x₀ c s v - (ν + 1 / 2) * deriv (caseIIIA ψ ν x₀ c s) v
    have hgd : ContDiffOn ℝ ∞ (deriv g) I := hg.deriv_of_isOpen hI (m := ∞) (by simp)
    have hR := regB_ode hI hIc h0 (fun v hv => ((hg.differentiableOn hne).differentiableAt
      (hI.mem_nhds hv)).hasDerivAt) hgd.continuousOn hx
    have hAd : ContDiffOn ℝ ∞ (deriv (caseIIIA ψ ν x₀ c s)) I :=
      (hA s).deriv_of_isOpen hI (m := ∞) (by simp)
    have h1 : HasDerivAt (deriv (caseIIIA ψ ν x₀ c s))
        (deriv (deriv (caseIIIA ψ ν x₀ c s)) x) x :=
      ((hAd.differentiableOn hne).differentiableAt (hI.mem_nhds hx)).hasDerivAt
    have h2 : HasDerivAt (regB g) (deriv (regB g) x) x :=
      (((regPhi_smooth hI hIc h0 0 hg).differentiableOn hne).differentiableAt
        (hI.mem_nhds hx)).hasDerivAt
    have hBd : HasDerivAt (caseIIIB ψ ν x₀ c s)
        (-deriv (deriv (caseIIIA ψ ν x₀ c s)) x + 2 * deriv (regB g) x) x :=
      h1.neg.add (h2.const_mul 2)
    rw [hBd.deriv]
    simp only [caseIIIB, caseIIIBOf]
    linear_combination hR
  · have hd : ContDiffOn ℝ ∞ (deriv (caseIIIB ψ ν x₀ c s)) I :=
      hB.deriv_of_isOpen hI (m := ∞) (by simp)
    have h0' : HasDerivAt (caseIIIB ψ ν x₀ c s) (deriv (caseIIIB ψ ν x₀ c s) x) x :=
      ((hB.differentiableOn hne).differentiableAt (hI.mem_nhds hx)).hasDerivAt
    have h1 : HasDerivAt (deriv (caseIIIB ψ ν x₀ c s)) (deriv (deriv (caseIIIB ψ ν x₀ c s)) x)
        x := ((hd.differentiableOn hne).differentiableAt (hI.mem_nhds hx)).hasDerivAt
    have hprod : ContinuousOn (fun t => ψ t * caseIIIB ψ ν x₀ c s t) I :=
      hψ.continuousOn.mul hB.continuousOn
    have h2 : HasDerivAt (fun x => ∫ t in x₀..x, ψ t * caseIIIB ψ ν x₀ c s t)
        (ψ x * caseIIIB ψ ν x₀ c s x) x :=
      integral_hasDerivAt_right ((hprod.mono (hIc.uIcc_subset hx₀ hx)).intervalIntegrable)
        (hprod.stronglyMeasurableAtFilter hI x hx) (hprod.continuousAt (hI.mem_nhds hx))
    have h3 : HasDerivAt (fun x => ν * caseIIIB ψ ν x₀ c s x -
        x * deriv (caseIIIB ψ ν x₀ c s) x +
        (∫ t in x₀..x, ψ t * caseIIIB ψ ν x₀ c s t) + c s)
        (ν * deriv (caseIIIB ψ ν x₀ c s) x - (1 * deriv (caseIIIB ψ ν x₀ c s) x +
          x * deriv (deriv (caseIIIB ψ ν x₀ c s)) x) + ψ x * caseIIIB ψ ν x₀ c s x) x :=
      (((h0'.const_mul ν).sub ((hasDerivAt_id x).mul h1)).add h2).add_const (c s)
    rw [show caseIIIA ψ ν x₀ c (s + 1) = fun x => ν * caseIIIB ψ ν x₀ c s x -
      x * deriv (caseIIIB ψ ν x₀ c s) x +
      (∫ t in x₀..x, ψ t * caseIIIB ψ ν x₀ c s t) + c s from rfl, h3.deriv]
    ring

/-- **DLMF 2.8.27** (`ξ > 0`): `B_s = −A_s′ + ξ^{−1/2} ∫_0^ξ (ψA_s − (ν+½)A_s′) v^{−1/2} dv`. -/
theorem dlmf_2_8_27 (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) {ψ A : ℝ → ℝ}
    (ν : ℝ) (hψ : ContDiffOn ℝ ∞ ψ I) (hA : ContDiffOn ℝ ∞ A I) {ξ : ℝ} (hξ : ξ ∈ I)
    (hpos : 0 < ξ) :
    caseIIIBOf ψ ν A ξ = -deriv A ξ + 1 / Real.sqrt ξ *
      ∫ v in (0 : ℝ)..ξ, (ψ v * A v - (ν + 1 / 2) * deriv A v) / Real.sqrt v := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨hg, -⟩ := caseIIIBOf_smooth hI hIc h0 ν hψ hA
  have hgd : ContDiffOn ℝ ∞ (deriv fun v => ψ v * A v - (ν + 1 / 2) * deriv A v) I :=
    hg.deriv_of_isOpen hI (m := ∞) (by simp)
  rw [caseIIIBOf, dlmf_2_8_17_pos hI hIc h0 (fun v hv => ((hg.differentiableOn hne).differentiableAt
    (hI.mem_nhds hv)).hasDerivAt) hgd.continuousOn hξ hpos]
  have hs : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hpos
  field_simp

/-- **DLMF 2.8.31** (`ξ < 0`): `B_s = −A_s′ + |ξ|^{−1/2} ∫_ξ^0 (ψA_s − (ν+½)A_s′) |v|^{−1/2} dv`. -/
theorem dlmf_2_8_31 (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) {ψ A : ℝ → ℝ}
    (ν : ℝ) (hψ : ContDiffOn ℝ ∞ ψ I) (hA : ContDiffOn ℝ ∞ A I) {ξ : ℝ} (hξ : ξ ∈ I)
    (hneg : ξ < 0) :
    caseIIIBOf ψ ν A ξ = -deriv A ξ + 1 / Real.sqrt |ξ| *
      ∫ v in ξ..0, (ψ v * A v - (ν + 1 / 2) * deriv A v) / Real.sqrt |v| := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨hg, -⟩ := caseIIIBOf_smooth hI hIc h0 ν hψ hA
  have hgd : ContDiffOn ℝ ∞ (deriv fun v => ψ v * A v - (ν + 1 / 2) * deriv A v) I :=
    hg.deriv_of_isOpen hI (m := ∞) (by simp)
  rw [caseIIIBOf, dlmf_2_8_17_neg hI hIc h0 (fun v hv => ((hg.differentiableOn hne).differentiableAt
    (hI.mem_nhds hv)).hasDerivAt) hgd.continuousOn hξ hneg, abs_of_neg hneg]
  have hs : 0 < Real.sqrt (-ξ) := Real.sqrt_pos.mpr (by linarith)
  have hint : (∫ v in ξ..0, (ψ v * A v - (ν + 1 / 2) * deriv A v) / Real.sqrt |v|) =
      ∫ v in ξ..0, (ψ v * A v - (ν + 1 / 2) * deriv A v) / Real.sqrt (-v) := by
    refine integral_congr_ae (Eventually.of_forall fun v hv => ?_)
    rw [uIoc_of_le hneg.le] at hv
    rcases hv.2.lt_or_eq with h | h
    · rw [abs_of_neg h]
    · rw [h]; simp
  rw [hint]
  field_simp

/-! ### 2.8.32–2.8.34: the envelopes of `J_ν`, `Y_ν` -/

/-- **DLMF 2.8.33–2.8.34**: `envJ(x) = √2 J(x)` for `x ≤ X`, `(J² + Y²)^{1/2}` for `x ≥ X`, `X` the
smallest positive root of `J + Y = 0` (2.8.32). -/
noncomputable def envJ (J Y : ℝ → ℝ) (X x : ℝ) : ℝ :=
  if x ≤ X then Real.sqrt 2 * J x else Real.sqrt (J x ^ 2 + Y x ^ 2)

/-- **DLMF 2.8.33–2.8.34**: `envY(x) = √2 |Y(x)|` for `x ≤ X`, `(J² + Y²)^{1/2}` for `x ≥ X`. -/
noncomputable def envY (J Y : ℝ → ℝ) (X x : ℝ) : ℝ :=
  if x ≤ X then Real.sqrt 2 * |Y x| else Real.sqrt (J x ^ 2 + Y x ^ 2)

/-- The envelopes are continuous, given that `X` is a root of 2.8.32 (`J(X) + Y(X) = 0`) at which
`J(X) ≥ 0` (only `envJ` needs the sign). -/
theorem envJ_envY_continuous {J Y : ℝ → ℝ} (hJ : Continuous J) (hY : Continuous Y) {X : ℝ}
    (hX : J X + Y X = 0) (hpos : 0 ≤ J X) :
    Continuous (envJ J Y X) ∧ Continuous (envY J Y X) := by
  have hYX : Y X = -J X := by linarith
  have key : Real.sqrt (J X ^ 2 + Y X ^ 2) = Real.sqrt 2 * |J X| := by
    rw [hYX, neg_sq, show J X ^ 2 + J X ^ 2 = 2 * J X ^ 2 by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq_eq_abs]
  have hs : Continuous fun x => Real.sqrt (J x ^ 2 + Y x ^ 2) :=
    Real.continuous_sqrt.comp ((hJ.pow 2).add (hY.pow 2))
  constructor
  · exact (continuous_const.mul hJ).if_le hs continuous_id continuous_const
      fun x hx => by simp only [Pi.mul_apply]; rw [hx, key, abs_of_nonneg hpos]
  · exact (continuous_const.mul hY.abs).if_le hs continuous_id continuous_const
      fun x hx => by simp only [Pi.mul_apply]; rw [hx, key, hYX, abs_neg]

end Azurite.DLMF

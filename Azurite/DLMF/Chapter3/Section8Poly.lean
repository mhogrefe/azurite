/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section11Division
import Azurite.DLMF.Chapter1.Section11LowDegree
import Azurite.DLMF.Chapter3.Section8AbelRuffini
import Azurite.DLMF.Chapter3.Section8Newton

/-!
# DLMF §3.8(iv): Zeros of polynomials

* 3.8.8 (`dlmf_3_8_8`): a polynomial `p(z) = aₙzⁿ + ⋯ + a₀`, `aₙ ≠ 0`, has `n` zeros in `ℂ`
  counting multiplicity: `p = aₙ ∏ (z − ζ)` over the multiset of roots, whose size is `n`, and
  the multiplicities (`rootMultiplicity`) add up to `n`. The multiplicity is that of §3.8(i)
  (`rootMultiplicity_eq_iff_isZeroOfMultiplicity`).
* "Explicit formulas for the zeros are available if `n ≤ 4`; see §§1.11(iii) and 4.43": every
  zero of a polynomial of degree `≤ 4` whose coefficients are expressible by radicals is itself
  expressible by radicals (`dlmf_3_8_iv_radicals`, from the formulas of §1.11(iii):
  `quadratic_rad`, `cubic_rad`, `quartic_rad`); in particular for rational coefficients
  (`dlmf_3_8_iv_radicals_rat`). §4.43 (trigonometric solution of cubics) is not formalized.
* "No explicit general formulas exist when `n ≥ 5`" (`dlmf_3_8_iv_abel_ruffini`): for every
  `n ≥ 5` there is `p ∈ ℚ[z]` of degree `n` with a zero not expressible by radicals — the
  Abel–Ruffini theorem, from the vendored `Section8AbelRuffini` (`x⁵ − 4x + 2`).
* Deflation (`dlmf_3_8_iv_deflation`): if `p(ζ) = 0`, Horner's scheme (§1.11(i)) gives
  `p = (z − ζ) q` with `deg q = n − 1`, and the zeros of `p` are `ζ` together with those of `q`.
  The "final iteration on the original polynomial" is a numerical recommendation: zeros of `q`
  are zeros of `p`, so Newton's rule for `p` may be applied to them (§3.8(ii)).
* Example `z⁴ − 1` (`dlmf_3_8_iv_example`): the zeros are `±1, ±i`; Newton's rule is 3.8.9,
  `φ(z) = (3z⁴ + 1)/(4z³)` (`dlmf_3_8_9`); from `z₀ = 1.5` the iterates decrease to `1`
  quadratically (`dlmf_3_8_iv_example_converges`).
* Table 3.8.2 (`dlmf_table_3_8_2`), certified exactly in `ℚ` by `decide +kernel`. The printed
  `z₀, …, z₄, z₆` are correctly rounded. **Erratum**: `z₅ = 1.00000 00001 8904956…`, so the
  printed `1.00000 00001 891` should be `1.00000 00001 890`.
-/

open Polynomial Finset Filter Topology Set

namespace Azurite.DLMF

/-! ### 3.8.8 -/

/-- The derivatives of `z ↦ p(z)` are those of the polynomial. -/
theorem iteratedDeriv_polyEval {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : 𝕜[X]) (k : ℕ) :
    iteratedDeriv k (fun z => p.eval z) = fun z => (derivative^[k] p).eval z := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have : deriv (fun z => p.eval z) = fun z => (derivative p).eval z := funext fun z =>
      Polynomial.deriv p
    rw [this, ih]

/-- The multiplicity of §3.8(i) is the multiplicity of a root of a polynomial. -/
theorem rootMultiplicity_eq_iff_isZeroOfMultiplicity {p : ℂ[X]} (hp : p ≠ 0) (ζ : ℂ) (m : ℕ) :
    p.rootMultiplicity ζ = m ↔ IsZeroOfMultiplicity (fun z => p.eval z) ζ m := by
  simp only [IsZeroOfMultiplicity, iteratedDeriv_polyEval]
  have hlt := fun n => lt_rootMultiplicity_iff_isRoot_iterate_derivative (t := ζ) (n := n) hp
  simp only [IsRoot] at hlt
  constructor
  · rintro rfl
    refine ⟨fun k hk => (hlt k).mp hk k le_rfl, fun h => ?_⟩
    exact lt_irrefl _ ((hlt _).mpr fun j hj => by
      rcases hj.lt_or_eq with hj | rfl
      · exact (hlt j).mp hj j le_rfl
      · exact h)
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ ?_
    · by_contra hc
      push Not at hc
      exact h2 ((hlt m).mp hc m le_rfl)
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact Nat.zero_le _
      · have := (hlt (m - 1)).mpr (fun j hj => h1 j (by omega))
        omega

/-- **DLMF 3.8.8**: `p(z) = aₙzⁿ + ⋯ + a₀` with `aₙ ≠ 0` has `n` zeros in `ℂ`, counting each
zero according to its multiplicity: `p = aₙ ∏ (z − ζ)` over the roots (with repetitions), there
are `n` of them, and the multiplicities of the distinct zeros add up to `n`. -/
theorem dlmf_3_8_8 (p : ℂ[X]) (hp : p ≠ 0) :
    p.roots.card = p.natDegree ∧
      C p.leadingCoeff * (p.roots.map fun ζ => X - C ζ).prod = p ∧
      ∑ ζ ∈ p.roots.toFinset, p.rootMultiplicity ζ = p.natDegree ∧
      ∀ ζ, p.eval ζ = 0 ↔ ζ ∈ p.roots := by
  have hcard := IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := p)
  refine ⟨hcard, C_leadingCoeff_mul_prod_multiset_X_sub_C hcard, ?_, fun ζ => ?_⟩
  · rw [← hcard, ← Multiset.toFinset_sum_count_eq]
    exact sum_congr rfl fun ζ _ => (count_roots p).symm
  · rw [mem_roots hp, IsRoot]

/-! ### `n ≤ 4`: explicit formulas (§1.11(iii)) -/

/-- Shorthand: `z` is expressible by radicals over `ℚ`. -/
abbrev IsRad (z : ℂ) : Prop := z ∈ solvableByRad ℚ ℂ

theorem isRad_ofNat (n : ℕ) [n.AtLeastTwo] : IsRad (OfNat.ofNat n : ℂ) := by
  simp

/-- Closure of `IsRad` under the field operations. -/
macro "rad_mem" : tactic => `(tactic| aesop (add safe apply [add_mem, mul_mem, sub_mem,
  div_mem, neg_mem, pow_mem, IntermediateField.natCast_mem, isRad_ofNat, one_mem, zero_mem]))

theorem exists_isRad_root {y : ℂ} (hy : IsRad y) {n : ℕ} (hn : 0 < n) :
    ∃ x, x ^ n = y ∧ IsRad x := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hn
  exact ⟨x, hx, solvableByRad.rad_mem hn.ne' (hx ▸ hy)⟩

theorem isRad_rho : IsRad (Complex.exp (2 * Real.pi * Complex.I / 3)) := by
  refine solvableByRad.rad_mem (n := 3) (by norm_num) ?_
  have h := dlmf_1_11_15.2.2
  have : Complex.exp (2 * Real.pi * Complex.I / 3) ^ 3 = 1 := by
    linear_combination (Complex.exp (2 * Real.pi * Complex.I / 3) - 1) * h
  rw [this]
  exact one_mem _

/-- Quadratics: 1.11.11. -/
theorem quadratic_rad {b c : ℂ} (hb : IsRad b) (hc : IsRad c) :
    ∃ z₁ z₂, IsRad z₁ ∧ IsRad z₂ ∧ ∀ z, z ^ 2 + b * z + c = (z - z₁) * (z - z₂) := by
  obtain ⟨s, hs, hsr⟩ := exists_isRad_root (y := b ^ 2 - 4 * 1 * c) (by rad_mem) two_pos
  refine ⟨(-b + s) / (2 * 1), (-b - s) / (2 * 1), by rad_mem, by rad_mem, fun z => ?_⟩
  have := (dlmf_1_11_11 one_ne_zero hs).1 z
  linear_combination this

/-- Cubics: 1.11.12–1.11.15 (with the case `A = 0`, where `p = 0`, handled directly). -/
theorem cubic_rad {a b c : ℂ} (ha : IsRad a) (hb : IsRad b) (hc : IsRad c) :
    ∃ z₁ z₂ z₃, IsRad z₁ ∧ IsRad z₂ ∧ IsRad z₃ ∧
      ∀ z, z ^ 3 + a * z ^ 2 + b * z + c = (z - z₁) * (z - z₂) * (z - z₃) := by
  have hP : IsRad (cubicP a b) := by unfold cubicP; rad_mem
  have hQ : IsRad (cubicQ a b c) := by unfold cubicQ; rad_mem
  have hρ := isRad_rho
  obtain ⟨s, hs, hsr⟩ := exists_isRad_root (y := -3 * cubicD (cubicP a b) (cubicQ a b c))
    (by unfold cubicD; rad_mem) two_pos
  obtain ⟨A, hA, hAr⟩ := exists_isRad_root (y := -27 / 2 * cubicQ a b c + 3 / 2 * s)
    (by rad_mem) three_pos
  by_cases hA0 : A ≠ 0
  · exact ⟨_, _, _, by rad_mem, by rad_mem, by rad_mem, dlmf_1_11_iii_cubic_roots hs hA hA0⟩
  · push Not at hA0
    subst hA0
    have hs9 : s = 9 * cubicQ a b c := by linear_combination (-2 / 3 : ℂ) * hA
    have hP0 : cubicP a b = 0 := by
      have h3 : cubicP a b ^ 3 = 0 := by
        unfold cubicD at hs
        rw [hs9] at hs
        linear_combination -hs / 12
      exact pow_eq_zero_iff (by norm_num) |>.mp h3
    obtain ⟨C', hC, hCr⟩ := exists_isRad_root (y := -cubicQ a b c) (by rad_mem) three_pos
    have hf := cubic_factor (p := cubicP a b) (q := cubicQ a b c) (A := 3 * C') (B := 0)
      dlmf_1_11_15.2.2 (by rw [hP0]; ring) (by linear_combination 27 * hC)
    set ρ := Complex.exp (2 * Real.pi * Complex.I / 3)
    refine ⟨(3 * C' + 0) / 3 - a / 3, (ρ * (3 * C') + ρ ^ 2 * 0) / 3 - a / 3,
      (ρ ^ 2 * (3 * C') + ρ * 0) / 3 - a / 3, ?_, ?_, ?_, fun z => ?_⟩
    rotate_left 3
    · have h1 := hf (z + a / 3)
      have h2 := dlmf_1_11_iii_cubic_reduce a b c (z + a / 3)
      simp only [add_sub_cancel_right] at h2
      rw [h2, h1]
      ring
    all_goals rad_mem

/-- Quartics: 1.11.16–1.11.20. -/
theorem quartic_rad {a b c d : ℂ} (ha : IsRad a) (hb : IsRad b) (hc : IsRad c) (hd : IsRad d) :
    ∃ z₁ z₂ z₃ z₄, IsRad z₁ ∧ IsRad z₂ ∧ IsRad z₃ ∧ IsRad z₄ ∧
      ∀ z, z ^ 4 + a * z ^ 3 + b * z ^ 2 + c * z + d =
        (z - z₁) * (z - z₂) * (z - z₃) * (z - z₄) := by
  set p := quarticP a b
  set q := quarticQ a b c
  set r := quarticR a b c d
  have hp : IsRad p := by simp only [p, quarticP]; rad_mem
  have hq : IsRad q := by simp only [q, quarticQ]; rad_mem
  have hr : IsRad r := by simp only [r, quarticR]; rad_mem
  obtain ⟨θ₁, θ₂, θ₃, h₁, h₂, h₃, hθ⟩ := cubic_rad (a := -2 * p) (b := p ^ 2 - 4 * r)
    (c := q ^ 2) (by rad_mem) (by rad_mem) (by rad_mem)
  have hθ' : ∀ z, z ^ 3 - 2 * p * z ^ 2 + (p ^ 2 - 4 * r) * z + q ^ 2 =
      (z - θ₁) * (z - θ₂) * (z - θ₃) := fun z => by linear_combination hθ z
  obtain ⟨t₁, ht₁, ht₁r⟩ := exists_isRad_root (y := -θ₁) (by rad_mem) two_pos
  obtain ⟨t₂, ht₂, ht₂r⟩ := exists_isRad_root (y := -θ₂) (by rad_mem) two_pos
  obtain ⟨t₃, ht₃, -⟩ := exists_isRad_root (y := -θ₃) (by rad_mem) two_pos
  obtain ⟨s₃, hs₃, hprod⟩ := dlmf_1_11_20 hθ' ht₁ ht₂ ht₃
  have hs₃r : IsRad s₃ := solvableByRad.rad_mem two_ne_zero (hs₃ ▸ by rad_mem)
  have hw := dlmf_1_11_19 hθ' ht₁ ht₂ hs₃ hprod
  refine ⟨(t₁ + t₂ + s₃) / 2 - a / 4, (t₁ - t₂ - s₃) / 2 - a / 4,
    (-t₁ + t₂ - s₃) / 2 - a / 4, (-t₁ - t₂ + s₃) / 2 - a / 4,
    by rad_mem, by rad_mem, by rad_mem, by rad_mem, fun z => ?_⟩
  have h1 := hw (z + a / 4)
  have h2 := dlmf_1_11_16 a b c d (z + a / 4)
  simp only [add_sub_cancel_right] at h2
  rw [h2, h1]
  ring

/-- **DLMF §3.8(iv)**: "Explicit formulas for the zeros are available if `n ≤ 4`": every zero of
a nonzero polynomial of degree `≤ 4` whose coefficients are expressible by radicals is itself
expressible by radicals (by the formulas of §1.11(iii)). -/
theorem dlmf_3_8_iv_radicals {p : ℂ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 4)
    (hc : ∀ i, IsRad (p.coeff i)) {z : ℂ} (hz : p.eval z = 0) : IsRad z := by
  have hlc : p.coeff p.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hp
  rw [eval_eq_sum_range] at hz
  generalize hn : p.natDegree = n at hz hlc hdeg
  set e := p.coeff
  have he : ∀ i, IsRad (e i) := hc
  interval_cases n <;> simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero,
    mul_one, pow_one] at hz
  · exact absurd hz hlc
  · have : z = -e 0 / e 1 := by field_simp; linear_combination hz
    rw [this]; rad_mem
  · obtain ⟨z₁, z₂, h₁, h₂, hf⟩ := quadratic_rad (b := e 1 / e 2) (c := e 0 / e 2)
      (by rad_mem) (by rad_mem)
    have h := hf z
    have h0 : z ^ 2 + e 1 / e 2 * z + e 0 / e 2 = 0 := by field_simp; linear_combination hz
    rw [h0, eq_comm, mul_eq_zero, sub_eq_zero, sub_eq_zero] at h
    rcases h with rfl | rfl <;> assumption
  · obtain ⟨z₁, z₂, z₃, h₁, h₂, h₃, hf⟩ := cubic_rad (a := e 2 / e 3) (b := e 1 / e 3)
      (c := e 0 / e 3) (by rad_mem) (by rad_mem) (by rad_mem)
    have h := hf z
    have h0 : z ^ 3 + e 2 / e 3 * z ^ 2 + e 1 / e 3 * z + e 0 / e 3 = 0 := by
      field_simp; linear_combination hz
    rw [h0, eq_comm, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero] at h
    rcases h with (rfl | rfl) | rfl <;> assumption
  · obtain ⟨z₁, z₂, z₃, z₄, h₁, h₂, h₃, h₄, hf⟩ := quartic_rad (a := e 3 / e 4)
      (b := e 2 / e 4) (c := e 1 / e 4) (d := e 0 / e 4) (by rad_mem) (by rad_mem)
      (by rad_mem) (by rad_mem)
    have h := hf z
    have h0 : z ^ 4 + e 3 / e 4 * z ^ 3 + e 2 / e 4 * z ^ 2 + e 1 / e 4 * z + e 0 / e 4 = 0 := by
      field_simp; linear_combination hz
    rw [h0, eq_comm, mul_eq_zero, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero,
      sub_eq_zero, sub_eq_zero] at h
    rcases h with ((rfl | rfl) | rfl) | rfl <;> assumption

/-- `dlmf_3_8_iv_radicals` for rational coefficients. -/
theorem dlmf_3_8_iv_radicals_rat {p : ℚ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 4) {z : ℂ}
    (hz : aeval z p = 0) : IsRad z := by
  refine dlmf_3_8_iv_radicals (p := p.map (algebraMap ℚ ℂ))
    ((Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hp)
    (by rwa [natDegree_map]) (fun i => ?_) (by rwa [eval_map_algebraMap])
  rw [coeff_map]
  exact IntermediateField.algebraMap_mem _ _

/-! ### `n ≥ 5`: Abel–Ruffini -/

/-- **DLMF §3.8(iv)**: "No explicit general formulas exist when `n ≥ 5`": for every `n ≥ 5`
there is a polynomial with rational coefficients of degree `n` having a zero that is not
expressible by radicals (Abel–Ruffini; `(x⁵ − 4x + 2) xⁿ⁻⁵`). -/
theorem dlmf_3_8_iv_abel_ruffini {n : ℕ} (hn : 5 ≤ n) :
    ∃ p : ℚ[X], p.natDegree = n ∧ ∃ z : ℂ, aeval z p = 0 ∧ ¬ IsRad z := by
  open AbelRuffiniArchive in
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Φ ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
  rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  refine ⟨Φ ℚ 4 2 * X ^ (n - 5), ?_, x, ?_, not_solvable_by_rad' x hx⟩
  · rw [(monic_Phi 4 2).natDegree_mul (monic_X_pow _), natDegree_Phi, natDegree_X_pow]
    omega
  · have hx' : aeval x (Φ ℚ 4 2) = 0 := by rwa [aeval_def]
    rw [map_mul, hx', zero_mul]

/-! ### Deflation -/

/-- **DLMF §3.8(iv)**, deflation: if `p(ζ) = 0` then Horner's scheme for `p(ζ)` (§1.11(i))
yields `p = (z − ζ) q`, `q = b_n z^{n−1} + ⋯ + b₁`, of degree `n − 1`; the zeros of `p` are `ζ`
together with the zeros of `q`, and every zero of `q` is a zero of `p`. -/
theorem dlmf_3_8_iv_deflation {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) {ζ : K}
    (hζ : p.eval ζ = 0) :
    let q := ∑ k ∈ range p.natDegree, C (horner p.coeff ζ p.natDegree (k + 1)) * X ^ k
    p = (X - C ζ) * q ∧ q.natDegree = p.natDegree - 1 ∧ p.roots = ζ ::ₘ q.roots ∧
      ∀ z, q.eval z = 0 → p.eval z = 0 := by
  intro q
  have hf := dlmf_1_11_2_poly p ζ
  rw [← dlmf_1_11_4_poly, hζ, C_0, add_zero] at hf
  have hq0 : q ≠ 0 := by rintro h; apply hp; rw [hf]; simp [q, h]
  refine ⟨hf, ?_, ?_, fun z hz => ?_⟩
  · conv_rhs => rw [hf]
    rw [natDegree_mul (X_sub_C_ne_zero ζ) hq0, natDegree_X_sub_C]
    omega
  · conv_lhs => rw [hf]
    rw [roots_mul (by rw [← hf]; exact hp), roots_X_sub_C, Multiset.singleton_add]
  · rw [hf, eval_mul, hz, mul_zero]

/-! ### Example: `z⁴ − 1` -/

/-- `z⁴ − 1`. -/
noncomputable def quartEx {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) : 𝕜 := z ^ 4 - 1

theorem hasDerivAt_quartEx {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    HasDerivAt quartEx (4 * z ^ 3) z := by
  have : HasDerivAt (fun z : 𝕜 => z ^ 4 - 1) (4 * z ^ 3) z := by
    simpa using (hasDerivAt_pow 4 z).sub_const 1
  exact this

/-- **DLMF 3.8.9**: Newton's rule for `z⁴ − 1` is `φ(z) = (3z⁴ + 1)/(4z³)` (also at `z = 0`,
with Lean's `1/0 = 0`). -/
theorem dlmf_3_8_9 {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    newtonStep quartEx z = (3 * z ^ 4 + 1) / (4 * z ^ 3) := by
  rw [newtonStep, (hasDerivAt_quartEx z).deriv, quartEx]
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · field_simp
    ring

/-- **Example** (DLMF §3.8(iv)): the zeros of `z⁴ − 1` are `±1` and `±i`. -/
theorem dlmf_3_8_iv_example (z : ℂ) :
    quartEx z = 0 ↔ z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I := by
  have h : quartEx z = (z - 1) * (z + 1) * (z - Complex.I) * (z + Complex.I) := by
    rw [quartEx]
    linear_combination (z ^ 2 - 1) * Complex.I_sq
  rw [h]
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  tauto

/-- **Example** (DLMF §3.8(iv)): from `z₀ = 1.5`, Newton's rule 3.8.9 decreases monotonically to
the zero `1`, quadratically. -/
theorem dlmf_3_8_iv_example_converges :
    (∀ n, (newtonStep (quartEx (𝕜 := ℝ)))^[n] (3 / 2) ∈ Set.Icc 1 (3 / 2)) ∧
      (∀ n, (newtonStep (quartEx (𝕜 := ℝ)))^[n + 1] (3 / 2) ≤
        (newtonStep (quartEx (𝕜 := ℝ)))^[n] (3 / 2)) ∧
      Tendsto (fun n => (newtonStep (quartEx (𝕜 := ℝ)))^[n] (3 / 2)) atTop (𝓝 1) ∧
      ∃ K ≥ 0, ∀ᶠ n in atTop, |(newtonStep (quartEx (𝕜 := ℝ)))^[n + 1] (3 / 2) - 1| ≤
        K * |(newtonStep (quartEx (𝕜 := ℝ)))^[n] (3 / 2) - 1| ^ 2 := by
  have hI : uIcc (1 : ℝ) (3 / 2) = Set.Icc 1 (3 / 2) := uIcc_of_le (by norm_num)
  have hd : ∀ x : ℝ, deriv quartEx x = 4 * x ^ 3 := fun x => (hasDerivAt_quartEx x).deriv
  have hdd : ∀ x : ℝ, deriv (deriv quartEx) x = 12 * x ^ 2 := fun x => by
    rw [show deriv (quartEx (𝕜 := ℝ)) = fun x => 4 * x ^ 3 from funext hd]
    have := ((hasDerivAt_pow 3 x).const_mul 4).deriv
    rw [this]
    ring
  have hcd : ∀ x : ℝ, ContDiffAt ℝ 2 quartEx x := fun x => by
    unfold quartEx; fun_prop
  obtain ⟨h1, h2, h3, h4⟩ := dlmf_3_8_ii_a (f := quartEx) (ξ := 1) (x₀ := 3 / 2)
    (fun x _ => hcd x) (by norm_num [quartEx]) (by rw [hdd]; norm_num [quartEx])
    (fun x hx => by rw [hI] at hx; rw [hd]; have := hx.1; positivity)
    (fun x hx => by rw [hdd, hdd]; positivity)
  rw [hI] at h1
  refine ⟨h1, fun n => ?_, h3, h4⟩
  have := h2 n
  rw [uIcc_of_le (h1 n).1] at this
  exact this.2

/-! ### Table 3.8.2 -/

/-- 3.8.9 in `ℚ`. -/
def quartPhiQ (x : ℚ) : ℚ := (3 * x ^ 4 + 1) / (4 * x ^ 3)

theorem quartPhiQ_iterate (n : ℕ) (x : ℚ) :
    (((quartPhiQ^[n] x : ℚ)) : ℝ) = (newtonStep (quartEx (𝕜 := ℝ)))^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, dlmf_3_8_9, quartPhiQ]
    push_cast
    rfl

/-- Table 3.8.2 as printed (13 decimals). -/
def tab382 : ℕ → ℚ
  | 0 => 15 / 10
  | 1 => 11990740740741 / 10 ^ 13
  | 2 => 10443168969414 / 10 ^ 13
  | 3 => 10027420038676 / 10 ^ 13
  | 4 => 10000112265490 / 10 ^ 13
  | 5 => 10000000001891 / 10 ^ 13
  | _ => 1

/-- The correctly rounded `z₅`. -/
def tab382z5 : ℚ := 10000000001890 / 10 ^ 13

theorem tab382_check :
    (∀ n ∈ ({0, 1, 2, 3, 4, 6} : Finset ℕ),
      |quartPhiQ^[n] (3 / 2) - tab382 n| < 5 / 10 ^ 14) ∧
      5 / 10 ^ 14 < |quartPhiQ^[5] (3 / 2) - tab382 5| ∧
      |quartPhiQ^[5] (3 / 2) - tab382z5| < 5 / 10 ^ 14 := by
  decide +kernel

/-- **Table 3.8.2**: Newton's rule for `z⁴ − 1 = 0` from `z₀ = 1.5`. The printed `z₀, …, z₄` and
`z₆` are correctly rounded to 13 decimals. **Erratum**: the printed `z₅ = 1.00000 00001 891` is
off by one unit in the last place; the correctly rounded value is `1.00000 00001 890`. -/
theorem dlmf_table_3_8_2 :
    (∀ n ∈ ({0, 1, 2, 3, 4, 6} : Finset ℕ),
      |(newtonStep (quartEx (𝕜 := ℝ)))^[n] (3 / 2) - tab382 n| < 5 / 10 ^ 14) ∧
      5 / 10 ^ 14 < |(newtonStep (quartEx (𝕜 := ℝ)))^[5] (3 / 2) - tab382 5| ∧
      |(newtonStep (quartEx (𝕜 := ℝ)))^[5] (3 / 2) - tab382z5| < 5 / 10 ^ 14 := by
  obtain ⟨h1, h2, h3⟩ := tab382_check
  have e : ∀ n, (newtonStep (quartEx (𝕜 := ℝ)))^[n] (3 / 2) = ((quartPhiQ^[n] (3 / 2) : ℚ) : ℝ) :=
    fun n => by rw [quartPhiQ_iterate]; norm_num
  have c : ∀ x y : ℚ, (|(x : ℝ) - y| : ℝ) = ((|x - y| : ℚ) : ℝ) := fun x y => by push_cast; rfl
  have b : ((5 / 10 ^ 14 : ℚ) : ℝ) = 5 / 10 ^ 14 := by norm_num
  refine ⟨fun n hn => ?_, ?_, ?_⟩
  · rw [e, ← b, c]; exact_mod_cast h1 n hn
  · rw [e, ← b, c]; exact_mod_cast h2
  · rw [e, ← b, c]; exact_mod_cast h3

end Azurite.DLMF

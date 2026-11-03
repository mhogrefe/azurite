/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3Newton

/-!
# DLMF §3.3(v): inverse interpolation

* Inverse interpolation: `inverse_interpolation` (general `n`: the Newton form in the divided
  differences `[f₀, …, f_k] x` of any `x(·)` with `x(f_k) = x_k` is the interpolation polynomial
  of the points `(f_k, x_k)`, and reproduces the `x_k`), `dlmf_3_3_39` (`n = 2`),
  `divDiff_congr` (divided differences depend only on the values at the nodes).
* Solving `f(z) = 0`: `inverse_interpolation_zero`, the error `a − x(0)` of the approximate zero
  as the §3.3(i) remainder of the inverse function (3.3.5).
* Example (first negative zero of `Ai`): the arithmetic on DLMF's printed numbers is proved
  exactly: `dlmf_3_3_40_zero` (`x = −2.33823 2462`), `dlmf_3_3_41` (with the corrected factor
  `x + 2.2`; erratum), `dlmf_3_3_42` (derivative), `dlmf_3_3_v_newton_x3`
  (`x₃ = −2.33934 0514`), `dlmf_3_3_v_newton_final` (`x = −2.33810 7373`; sign erratum),
  `dlmf_3_3_v_correct_digits` (4, 9 and 8 correct digits, given `a₁ = −2.33810 7410…`). The
  values `Ai(x_k)`, `a₁`, the coefficients of 3.3.40 as divided differences of `Ai` data, and the
  second inverse-interpolation step need certified `Ai`, not yet available (deferred; see
  `docs/dlmf_plan.md`).
-/

open Polynomial Finset Lagrange

namespace Azurite.DLMF

/-! ### Inverse interpolation -/

section Field

variable {F : Type*} [Field F]

/-- Divided differences depend only on the values at the nodes. -/
theorem divDiff_congr : ∀ {n : ℕ} (z : Fin (n + 1) → F) {g h : F → F},
    (∀ i, g (z i) = h (z i)) → divDiff n z g = divDiff n z h
  | 0, z, g, h, hgh => hgh 0
  | n + 1, z, g, h, hgh => by
    rw [divDiff, divDiff, divDiff_congr _ fun i => hgh i.succ,
      divDiff_congr _ fun i => hgh i.castSucc]

/-- **Inverse interpolation** (§3.3(v), 3.3.39 for general `n`): interchanging the roles of the
points and the function values, the polynomial
`x(f) = ∑_{k=0}^{n} (f − f₀)⋯(f − f_{k−1}) [f₀, …, f_k] x` (with `[f₀, …, f_k] x` the divided
differences of any `x(·)` with `x(f_k) = x_k`) is the interpolation polynomial of the points
`(f_k, x_k)`; in particular `x(f_k) = x_k`. -/
theorem inverse_interpolation (fv xv : ℕ → F) (n : ℕ) (hfv : Set.InjOn fv (Set.Iic n))
    (g : F → F) (hg : ∀ k ≤ n, g (fv k) = xv k) (φ : F) :
    ∑ k ∈ range (n + 1), (∏ j ∈ range k, (φ - fv j)) * divDiff k (fun i : Fin (k + 1) => fv i) g =
        (interpolate univ (fun i : Fin (n + 1) => fv i) (fun k => xv k)).eval φ ∧
      ∀ k ≤ n, ∑ k' ∈ range (n + 1), (∏ j ∈ range k', (fv k - fv j)) *
        divDiff k' (fun i : Fin (k' + 1) => fv i) g = xv k := by
  have hcongr : (interpolate univ (fun i : Fin (n + 1) => fv i) (fun k => g (fv k))) =
      interpolate univ (fun i : Fin (n + 1) => fv i) (fun k => xv k) := by
    congr 1; funext k; exact hg k (Nat.lt_succ_iff.mp k.2)
  refine ⟨by rw [← newton_interpolate fv g φ n hfv, hcongr], fun k hk => ?_⟩
  rw [← newton_interpolate fv g (fv k) n hfv, hcongr]
  have := (lagrange_unique _ (injective_of_injOn_Iic hfv) fun k => xv k).2.1
    ⟨k, Nat.lt_succ_of_le hk⟩
  simpa using this

/-- **DLMF 3.3.39**: `x(f) = [f₀] x + (f − f₀)[f₀, f₁] x + (f − f₀)(f − f₁)[f₀, f₁, f₂] x`, the
inverse interpolation polynomial through `(f₀, x₀)`, `(f₁, x₁)`, `(f₂, x₂)`. -/
theorem dlmf_3_3_39 (fv xv : ℕ → F) (hfv : Set.InjOn fv (Set.Iic 2)) (g : F → F)
    (hg : ∀ k ≤ 2, g (fv k) = xv k) (φ : F) :
    (interpolate univ (fun i : Fin 3 => fv i) (fun k => xv k)).eval φ =
      divDiff 0 (fun i : Fin 1 => fv i) g + (φ - fv 0) * divDiff 1 (fun i : Fin 2 => fv i) g +
        (φ - fv 0) * (φ - fv 1) * divDiff 2 (fun i : Fin 3 => fv i) g := by
  rw [← (inverse_interpolation fv xv 2 hfv g hg φ).1]
  simp only [sum_range_succ, range_zero, sum_empty, prod_range_succ, prod_empty]
  ring

end Field

/-- **Solving `f(z) = 0`** by inverse interpolation (§3.3(v)): if `g` inverts `f` at the nodes
(`g(f_k) = x_k`) and at the zero (`g(0) = a`), then `a − x(0)` is the interpolation error of `g`
at `0`, `a − x(0) = g^{(n+1)}(η)/(n+1)! ∏ (0 − f_k)` for some `η` in the smallest closed interval
containing `0` and the `f_k` (3.3.5 applied to `g`). -/
theorem inverse_interpolation_zero {n : ℕ} (fv : Fin (n + 1) → ℝ) (hfv : Function.Injective fv)
    (xv : Fin (n + 1) → ℝ) (g : ℝ → ℝ) (hg : ∀ k, g (fv k) = xv k) {a : ℝ} (ha : g 0 = a)
    {U : Set ℝ} (hU : IsOpen U) (hd : ∀ k ≤ n, DifferentiableOn ℝ (iteratedDeriv k g) U)
    (hI : Set.Icc ((insert 0 (univ.image fv)).min' (insert_nonempty _ _))
      ((insert 0 (univ.image fv)).max' (insert_nonempty _ _)) ⊆ U) :
    ∃ η ∈ Set.Icc ((insert 0 (univ.image fv)).min' (insert_nonempty _ _))
      ((insert 0 (univ.image fv)).max' (insert_nonempty _ _)),
      a - (interpolate univ fv xv).eval 0 =
        iteratedDeriv (n + 1) g η / (n + 1).factorial * ∏ k, (0 - fv k) := by
  obtain ⟨η, hη, hR⟩ := dlmf_3_3_5 fv hfv g hU hd 0 hI
  refine ⟨η, hη, ?_⟩
  have hx : interpolate univ fv xv = interpolate univ fv (fun k => g (fv k)) := by
    congr 1; funext k; exact (hg k).symm
  rw [hx, ← ha, ← eval_nodal (s := univ) (v := fv), ← hR, lagrangeRem]

/-! ### Example: the first negative zero of `Ai`

The Airy-function values `f_k = Ai(x_k)` and the zero `a₁` are not yet available in Azurite (the
AzFloat Airy functions need `Γ(1/3)`); the steps below are the exact arithmetic on the numbers
DLMF prints. -/

/-- 3.3.40 at `f = 0`: `x = −2.33823 2462` (to the printed ten digits). -/
theorem dlmf_3_3_40_zero :
    |(-2.2 + 1.440111973 * (0 - 0.0961453780) +
        0.0886585832 * (0 - 0.0961453780) * (0 - 0.0267063331)) - (-2.338232462 : ℝ)| <
      5e-10 := by
  rw [abs_lt]; constructor <;> norm_num

/-- The direct Newton polynomial 3.3.41, with the node `x₀ = −2.2` in its first factor. -/
noncomputable def airyNewton2 (x : ℝ) : ℝ :=
  0.0961453780 + 0.6943904495 * (x + 2.2) - 0.0300714275 * ((x + 2.2) * (x + 2.3))

/-- **DLMF 3.3.41** (corrected, see errata): the first factor must be `x + 2.2 = x − x₀`. The
corrected polynomial reproduces `f₀` at `x₀` and `f₁` at `x₁` (to the printed digits); DLMF's
literal `x + 2.1` gives `f₀ − 0.06943…` at `x₀`. -/
theorem dlmf_3_3_41 :
    airyNewton2 (-2.2) = 0.0961453780 ∧ |airyNewton2 (-2.3) - 0.0267063331| ≤ 5e-11 ∧
      (0.0961453780 + 0.6943904495 * ((-2.2 : ℝ) + 2.1) -
        0.0300714275 * ((-2.2 + 2.2) * (-2.2 + 2.3))) ≠ 0.0961453780 := by
  unfold airyNewton2
  refine ⟨by norm_num, by rw [abs_le]; constructor <;> norm_num, by norm_num⟩

/-- **DLMF 3.3.42**: `f′(x) = 0.55906 90257 − 0.06014 28550 x` is the derivative of 3.3.41 (the
exact constant term is `0.55906 902575`). -/
theorem dlmf_3_3_42 (x : ℝ) :
    HasDerivAt airyNewton2 (0.55906902575 - 0.0601428550 * x) x ∧
      |(0.55906902575 : ℝ) - 0.5590690257| ≤ 5e-11 := by
  refine ⟨?_, by rw [abs_le]; constructor <;> norm_num⟩
  have h1 : HasDerivAt (fun y : ℝ => y + 2.2) 1 x := (hasDerivAt_id' x).add_const _
  have h2 : HasDerivAt (fun y : ℝ => y + 2.3) 1 x := (hasDerivAt_id' x).add_const _
  have := ((h1.const_mul 0.6943904495).const_add 0.0961453780).sub
    ((h1.mul h2).const_mul 0.0300714275)
  convert this using 1
  · funext y; simp only [airyNewton2, Pi.sub_apply, Pi.mul_apply]
  · ring

/-- Newton's rule from `x = −2.5` with 3.3.41–3.3.42 gives `x₃ = −2.33934 0514`. -/
theorem dlmf_3_3_v_newton_x3 :
    |(-2.5 - airyNewton2 (-2.5) / (0.5590690257 - 0.0601428550 * (-2.5))) -
      (-2.339340514 : ℝ)| < 5e-10 := by
  unfold airyNewton2; rw [abs_lt]; constructor <;> norm_num

/-- The Newton polynomial with the new point `x₃ = −2.33934 0514` and
`[x₀, x₁, x₂, x₃] f = −0.26608 28233` (as printed). -/
noncomputable def airyNewton3 (x : ℝ) : ℝ :=
  airyNewton2 x + -0.2660828233 * ((x + 2.2) * (x + 2.3) * (x + 2.4))

theorem airyNewton3_hasDerivAt (x : ℝ) :
    HasDerivAt airyNewton3 (0.55906902575 - 0.0601428550 * x +
      -0.2660828233 * ((x + 2.3) * (x + 2.4) + (x + 2.2) * (x + 2.4) + (x + 2.2) * (x + 2.3)))
      x := by
  have h1 : HasDerivAt (fun y : ℝ => y + 2.2) 1 x := (hasDerivAt_id' x).add_const _
  have h2 : HasDerivAt (fun y : ℝ => y + 2.3) 1 x := (hasDerivAt_id' x).add_const _
  have h3 : HasDerivAt (fun y : ℝ => y + 2.4) 1 x := (hasDerivAt_id' x).add_const _
  have := (dlmf_3_3_42 x).1.add (((h1.mul h2).mul h3).const_mul (-0.2660828233))
  convert this using 1
  · funext y; simp only [airyNewton3, Pi.add_apply, Pi.mul_apply]
  · simp only [Pi.mul_apply]; ring

/-- Recomputing `f′` and applying Newton's rule from `x₃` gives `x = −2.33810 7373` (DLMF prints
`2.33810 7373`, without the minus sign; see errata). -/
theorem dlmf_3_3_v_newton_final :
    |((-2.339340514 : ℝ) - airyNewton3 (-2.339340514) /
        (0.55906902575 - 0.0601428550 * (-2.339340514) +
          -0.2660828233 * ((-2.339340514 + 2.3) * (-2.339340514 + 2.4) +
            (-2.339340514 + 2.2) * (-2.339340514 + 2.4) +
            (-2.339340514 + 2.2) * (-2.339340514 + 2.3)))) - (-2.338107373)| < 5e-10 := by
  unfold airyNewton3 airyNewton2; rw [abs_lt]; constructor <;> norm_num

/-- The numbers of correct digits, given `a₁ = −2.33810 7410…` (i.e.
`−2.33810 7411 < a₁ ≤ −2.33810 7410`): `−2.33823 2462` has 4 correct digits, `−2.33810 7409` has
9, and `−2.33810 7373` has 8 (`d` correct digits: error `< ½ · 10^{1−d}`, but not `< ½ · 10^{−d}`,
for numbers of size between 1 and 10). -/
theorem dlmf_3_3_v_correct_digits {a₁ : ℝ} (h1 : -2.3381074110 < a₁) (h2 : a₁ ≤ -2.3381074100) :
    (5e-5 ≤ |(-2.338232462 : ℝ) - a₁| ∧ |(-2.338232462 : ℝ) - a₁| < 5e-4) ∧
      (5e-10 ≤ |(-2.338107409 : ℝ) - a₁| ∧ |(-2.338107409 : ℝ) - a₁| < 5e-9) ∧
      (5e-9 ≤ |(-2.338107373 : ℝ) - a₁| ∧ |(-2.338107373 : ℝ) - a₁| < 5e-8) := by
  rw [abs_of_neg (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

end Azurite.DLMF

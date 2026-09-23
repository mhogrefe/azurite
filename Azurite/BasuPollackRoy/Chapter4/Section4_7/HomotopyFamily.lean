/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.NonsingularProjectiveZero

/-!
# BPR §4.7, Proposition 4.106: the homotopy family

To bound the number of non-singular projective zeros of homogeneous polynomials `P₁, …, P_k` of
degrees `d₁, …, d_k`, BPR deforms `P₁, …, P_k` to the *diagonal system*

`Dᵢ = (Xᵢ − X₀)(Xᵢ − 2 X₀) ⋯ (Xᵢ − dᵢ X₀)`,

whose non-singular projective zeros are exactly the grid `{1, …, d₁} × ⋯ × {1, …, d_k}` (in the
affine chart `X₀ ≠ 0`), giving the count `d₁ ⋯ d_k`. The deformation is the pencil

`Hᵢ,λ,µ = λ Pᵢ + µ Dᵢ`, with `(λ : µ) ∈ ℙ₁(C)`,

so that `S₍₁:₀₎ = (P₁, …, P_k)` and `S₍₀:₁₎ = (D₁, …, D_k)`.

This file sets up the polynomials `diagFactor`, `homotopyPoly` and records their homogeneity
(each `Hᵢ,λ,µ` is homogeneous of degree `dᵢ`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- The **diagonal factor** `Dᵢ = ∏_{n=1}^{d} (X_{i+1} − n · X₀)`, a homogeneous polynomial of
degree `d` in the `k + 1` homogeneous coordinates `X₀, …, X_k`. The variable `X_{i+1}` is the
`(i+1)`-st coordinate (`Fin.succ i`), `X₀` the `0`-th. -/
noncomputable def diagFactor (d : ℕ) (i : Fin k) : MvPolynomial (Fin (k + 1)) (Ri R) :=
  ∏ n ∈ Finset.Icc 1 d, (X i.succ - C ((n : ℕ) : Ri R) * X 0)

/-- The **diagonal system** `S₍₀:₁₎ = (D₁, …, D_k)` with `Dᵢ` of degree `dᵢ`. -/
noncomputable def diagSystem (d : Fin k → ℕ) (i : Fin k) : MvPolynomial (Fin (k + 1)) (Ri R) :=
  diagFactor (d i) i

/-- The **homotopy pencil** `Hᵢ,λ,µ = λ Pᵢ + µ Dᵢ`. For `(λ, µ) = (1, 0)` it is `Pᵢ`; for
`(λ, µ) = (0, 1)` it is the diagonal factor `Dᵢ`. -/
noncomputable def homotopyPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (lam mu : Ri R) (i : Fin k) : MvPolynomial (Fin (k + 1)) (Ri R) :=
  C lam * P i + C mu * diagFactor (d i) i

set_option linter.unusedSectionVars false in
/-- Each linear factor `X_{i+1} − n · X₀` is homogeneous of degree `1`. -/
theorem diagLinearFactor_isHomogeneous (n : ℕ) (i : Fin k) :
    (X i.succ - C ((n : ℕ) : Ri R) * X 0 : MvPolynomial (Fin (k + 1)) (Ri R)).IsHomogeneous 1 := by
  have h1 : (C ((n : ℕ) : Ri R) * X 0 : MvPolynomial (Fin (k + 1)) (Ri R)).IsHomogeneous 1 := by
    have := (MvPolynomial.isHomogeneous_C (Fin (k + 1)) ((n : Ri R))).mul
      (isHomogeneous_X (Ri R) (0 : Fin (k + 1)))
    rwa [zero_add] at this
  exact (isHomogeneous_X (Ri R) i.succ).sub h1

set_option linter.unusedSectionVars false in
/-- The diagonal factor `Dᵢ` is homogeneous of degree `d`. -/
theorem diagFactor_isHomogeneous (d : ℕ) (i : Fin k) :
    (diagFactor (R := R) d i).IsHomogeneous d := by
  rw [diagFactor]
  have h := MvPolynomial.IsHomogeneous.prod (Finset.Icc 1 d) (fun n => X i.succ - C ((n : ℕ) : Ri R) * X 0)
    (fun _ => 1) (fun n _ => diagLinearFactor_isHomogeneous n i)
  simpa using h

set_option linter.unusedSectionVars false in
/-- The homotopy pencil `Hᵢ,λ,µ = λ Pᵢ + µ Dᵢ` is homogeneous of degree `dᵢ` whenever `Pᵢ` is. -/
theorem homotopyPoly_isHomogeneous (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (lam mu : Ri R) (i : Fin k) :
    (homotopyPoly P d lam mu i).IsHomogeneous (d i) := by
  rw [homotopyPoly]
  apply IsHomogeneous.add
  · simpa using (isHomogeneous_C _ lam).mul (hP i)
  · simpa using (isHomogeneous_C _ mu).mul (diagFactor_isHomogeneous (d i) i)

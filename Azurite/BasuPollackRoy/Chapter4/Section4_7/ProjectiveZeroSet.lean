/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.Multihomogeneous
import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveSpace

/-!
# BPR §4.7: zeros of multihomogeneous polynomials in a product of projective spaces

Let `R` be a real closed field and `C = R[i] = Ri R`. A point of the product
`∏ᵢ ℙ_{k_i}(C)` is a tuple `x = (x̄₁, …, x̄_m)` of lines. For a multihomogeneous polynomial `P`, the
condition `P(x) = 0` is well defined: if `xᵢ` and `yᵢ` are two choices of homogeneous coordinates
for the same point (so `xᵢ = λᵢ yᵢ`, `λᵢ ≠ 0`), then `P` vanishes at one choice iff at the other,
because rescaling block `i` by `λᵢ` multiplies the value by `∏ᵢ λᵢ^{d_i} ≠ 0`
(`IsMultihomogeneous.eval_blockScale`).

An **algebraic set** of `∏ᵢ ℙ_{k_i}(C)` is a set of the form
`Zer(𝒫, ∏ᵢ ℙ_{k_i}(C)) = {x | ⋀_{P ∈ 𝒫} P(x) = 0}` for a finite set `𝒫` of multihomogeneous
polynomials.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  {m : ℕ} {k : Fin m → ℕ}

/-- **Evaluation at a choice of homogeneous coordinates.** Given a coordinate vector `v i` for each
block `i`, evaluate `P` at the combined assignment `⟨i, j⟩ ↦ v i j`. -/
noncomputable def evalCoords (P : MvPolynomial ((i : Fin m) × Fin (k i + 1)) (Ri R))
    (v : (i : Fin m) → (Fin (k i + 1) → Ri R)) : Ri R :=
  MvPolynomial.eval (fun s => v s.1 s.2) P

set_option linter.unusedSectionVars false in
/-- **Well-definedness of `P(x) = 0`.** For a multihomogeneous `P`, vanishing at a tuple of
homogeneous coordinates depends only on the point of `∏ᵢ ℙ_{k_i}(C)` it represents, not on the
choice of coordinates: if `v i` and `w i` span the same line for every `i`, then `P` vanishes at
`v` iff it vanishes at `w`. -/
theorem evalCoords_eq_zero_iff_of_mkLine_eq
    {P : MvPolynomial ((i : Fin m) × Fin (k i + 1)) (Ri R)} {d : Fin m → ℕ}
    (hP : IsMultihomogeneous P d) {v w : (i : Fin m) → (Fin (k i + 1) → Ri R)}
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (h : ∀ i, mkLine (v i) (hv i) = mkLine (w i) (hw i)) :
    evalCoords P v = 0 ↔ evalCoords P w = 0 := by
  -- a nonzero scalar `c i` with `v i = c i • w i` for each block
  choose c hc hvw using fun i => (mkLine_eq_mkLine_iff (v i) (w i) (hv i) (hw i)).mp (h i)
  -- rewrite the `v`-assignment as the `w`-assignment with block `i` scaled by `c i`
  have hrw : (fun s : (i : Fin m) × Fin (k i + 1) => v s.1 s.2)
      = fun s => c s.1 * w s.1 s.2 := by
    funext s
    have := congrFun (hvw s.1) s.2
    rw [this, Pi.smul_apply, smul_eq_mul]
  rw [evalCoords, evalCoords, hrw, hP.eval_blockScale c (fun s => w s.1 s.2),
    mul_eq_zero, or_iff_right]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hc i)

/-- **Vanishing of `P` at a point of `∏ᵢ ℙ_{k_i}(C)`.** `P(x) = 0`, where `x` is evaluated at the
canonical representatives `(x i).rep` of its lines. By
`evalCoords_eq_zero_iff_of_mkLine_eq` this is independent of the choice of representatives when `P`
is multihomogeneous. -/
noncomputable def ProjVanishes (P : MvPolynomial ((i : Fin m) × Fin (k i + 1)) (Ri R))
    (x : (i : Fin m) → complexProjectiveSpace R (k i)) : Prop :=
  evalCoords P (fun i => (x i).rep) = 0

/-- **BPR §4.7 (algebraic set in a product of projective spaces).**
`Zer(𝒫, ∏ᵢ ℙ_{k_i}(C)) = {x | ⋀_{P ∈ 𝒫} P(x) = 0}` for a finite set `𝒫` of (multihomogeneous)
polynomials. -/
def projZerOfFinset (Ps : Finset (MvPolynomial ((i : Fin m) × Fin (k i + 1)) (Ri R))) :
    Set ((i : Fin m) → complexProjectiveSpace R (k i)) :=
  {x | ∀ P ∈ Ps, ProjVanishes P x}

/-- **BPR §4.7 (algebraic set, predicate form).** A subset of `∏ᵢ ℙ_{k_i}(C)` is *algebraic* if it is
the common zero set `Zer(𝒫, ∏ᵢ ℙ_{k_i}(C))` of some finite set `𝒫` of multihomogeneous
polynomials. -/
def IsAlgebraicSet (S : Set ((i : Fin m) → complexProjectiveSpace R (k i))) : Prop :=
  ∃ Ps : Finset (MvPolynomial ((i : Fin m) × Fin (k i + 1)) (Ri R)),
    (∀ P ∈ Ps, ∃ dd, IsMultihomogeneous P dd) ∧ S = projZerOfFinset Ps

end Azurite.BPR.Chapter4

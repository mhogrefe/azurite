import Azurite.BasuPollackRoy.Chapter2.Section2_1.Notation_2_18
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# BPR §4.7: complex projective space

Let `R` be a real closed field and `C = R[i] = Ri R`. The **complex projective space of dimension
`k`**, `ℙ_k(C)`, is the set of lines of `Cᵏ⁺¹` through the origin — that is, the projectivization
of the `C`-vector space `Cᵏ⁺¹`. We model it by Mathlib's `Projectivization`, whose points are
exactly the one-dimensional subspaces of `Cᵏ⁺¹` (nonzero vectors up to a nonzero scalar).
-/

namespace Azurite.BPR.Chapter4

variable (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR §4.7 (complex projective space).** `ℙ_k(C)`, the complex projective space of dimension
`k` over `C = R[i] = Ri R`: the set of lines of `Cᵏ⁺¹` through the origin, realized as the
projectivization of the `C`-vector space `Fin (k+1) → C`. -/
abbrev complexProjectiveSpace (k : ℕ) : Type _ :=
  Projectivization (Ri R) (Fin (k + 1) → Ri R)

variable {R} {k : ℕ}

/-- **Homogeneous coordinates.** A nonzero `(k+1)`-tuple `x = (x₀, x₁, …, x_k)` of elements of `C`
defines the line `x̄ = (x₀ : x₁ : ⋯ : x_k)` through the origin, a point of `ℙ_k(C)`. -/
noncomputable def mkLine (x : Fin (k + 1) → Ri R) (hx : x ≠ 0) : complexProjectiveSpace R k :=
  Projectivization.mk (Ri R) x hx

set_option linter.unusedSectionVars false in
/-- **BPR §4.7 (homogeneous coordinates agree up to a scalar).**
`(x₀ : ⋯ : x_k) = (y₀ : ⋯ : y_k)` if and only if there is a nonzero `λ ∈ C` with `xᵢ = λ yᵢ`. -/
theorem mkLine_eq_mkLine_iff (x y : Fin (k + 1) → Ri R) (hx : x ≠ 0) (hy : y ≠ 0) :
    mkLine x hx = mkLine y hy ↔ ∃ c : Ri R, c ≠ 0 ∧ x = c • y := by
  rw [mkLine, mkLine, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a : Ri R), a.ne_zero, by rw [← Units.smul_def]; exact ha.symm⟩
  · rintro ⟨c, hc, hxy⟩
    exact ⟨Units.mk0 c hc, by rw [Units.smul_def, Units.val_mk0]; exact hxy.symm⟩

end Azurite.BPR.Chapter4

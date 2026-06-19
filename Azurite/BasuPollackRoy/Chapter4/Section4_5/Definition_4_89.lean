import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87

/-!
# BPR §4.5, Definition 4.89: separating elements

An element `a` of `A = K[X₁, …, X_k] / Ideal(𝒫, K)` is *separating* for `𝒫` if it takes distinct
values at distinct elements of `Zer(𝒫, Cᵏ)`.

The value of `a ∈ A` at a point `x ∈ Zer(𝒫, Cᵏ)` is `evalBar (inclExt a) x` (`valueAt`): the
image of `a` in `Ā` evaluated at `x`. Equivalently, it is the value at `x` of any polynomial
representative of `a` (`valueAt_mk`), which is well defined since `Ideal(𝒫, K) ⊆ Ideal(𝒫, C)`
vanishes on `Zer(𝒫, Cᵏ)`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]

/-- The value at `x ∈ Zer(𝒫, Cᵏ)` of an element `a ∈ A`: the image of `a` in `Ā`, evaluated at
`x`. -/
noncomputable def valueAt (Ps : Finset (MvPolynomial (Fin k) K)) (a : quotPolys Ps)
    (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps) : C :=
  evalBar C Ps x hx (inclExt C Ps a)

/-- The value of `a ∈ A` at `x` is the value at `x` of any polynomial representative of `a`. -/
theorem valueAt_mk (Ps : Finset (MvPolynomial (Fin k) K)) (p : MvPolynomial (Fin k) K)
    (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps) :
    valueAt C Ps (Ideal.Quotient.mk _ p) x hx = MvPolynomial.aeval x p := by
  rw [valueAt, inclExt_mk, evalBar_mk, MvPolynomial.aeval_map_algebraMap]

/-- **BPR Definition 4.89 (separating element).** An element `a` of `A` is *separating* for `𝒫` if
it has distinct values at distinct elements of `Zer(𝒫, Cᵏ)` — equivalently, if the map
`x ↦ a(x)` on `Zer(𝒫, Cᵏ)` is injective. -/
def IsSeparating (Ps : Finset (MvPolynomial (Fin k) K)) (a : quotPolys Ps) : Prop :=
  ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps) (y : Fin k → C) (hy : y ∈ zerOfFinset C Ps),
    valueAt C Ps a x hx = valueAt C Ps a y hy → x = y

end Azurite.BPR.Chapter4

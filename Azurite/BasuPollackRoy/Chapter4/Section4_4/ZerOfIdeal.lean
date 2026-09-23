import Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_61
import Mathlib.RingTheory.Nullstellensatz

/-!
# BPR §4.4: zero set of an ideal over an extension field

If `I ⊆ K[X₁, …, X_k]` is an ideal and `L` is a field containing `K`, the set of common zeros
of `I` in `Lᵏ` is
`Zer(I, Lᵏ) = {x ∈ Lᵏ | ∀ P ∈ I, P(x) = 0}` (`zerOfIdeal`, = Mathlib's `MvPolynomial.zeroLocus`).
When `L = K` this is the algebraic sets contained in `Kᵏ`.

Theorem 4.61 implies that every such set is the zero set of a *finite* set of polynomials:
`Zer(I, Lᵏ) = {x ∈ Lᵏ | ⋀_{P ∈ 𝒫} P(x) = 0}` for a finite `𝒫` (`zerOfIdeal_idealOfPolys`,
`exists_finset_zerOfIdeal`). So this notion of algebraic set agrees with the one in Chapter 1
(`K = ℂ`) and Chapter 2 (`K = ℝ`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]

/-- **BPR `Zer(I, Lᵏ)`**: the set of common zeros in `Lᵏ` of an ideal `I ⊆ K[X₁, …, X_k]`,
where `L` is a field extension of `K`. This is Mathlib's `MvPolynomial.zeroLocus`. -/
def zerOfIdeal (I : Ideal (MvPolynomial (Fin k) K)) : Set (Fin k → L) :=
  MvPolynomial.zeroLocus L I

@[simp]
theorem mem_zerOfIdeal {I : Ideal (MvPolynomial (Fin k) K)} {x : Fin k → L} :
    x ∈ zerOfIdeal I ↔ ∀ P ∈ I, MvPolynomial.aeval x P = 0 :=
  Iff.rfl

/-- The zero set of `Ideal(𝒫, K)` is the common zero set of the finite generating family `𝒫`:
`Zer(Ideal(𝒫, K), Lᵏ) = {x ∈ Lᵏ | ⋀_{P ∈ 𝒫} P(x) = 0}`. -/
theorem zerOfIdeal_idealOfPolys (P : Finset (MvPolynomial (Fin k) K)) :
    zerOfIdeal (L := L) (idealOfPolys P) = {x : Fin k → L | ∀ p ∈ P, MvPolynomial.aeval x p = 0} := by
  ext x
  simp only [mem_zerOfIdeal, Set.mem_ofPred_eq]
  constructor
  · intro h p hp
    exact h p (Ideal.subset_span (Finset.mem_coe.mpr hp))
  · intro h p hp
    exact aeval_eq_zero_of_mem_idealOfPolys hp x h

/-- **Note (Theorem 4.61).** Every set of the form `Zer(I, Lᵏ)` is the common zero set of a
*finite* set of polynomials: there is a finite `𝒫` with
`Zer(I, Lᵏ) = {x ∈ Lᵏ | ⋀_{P ∈ 𝒫} P(x) = 0}`. Hence every algebraic set in `Kᵏ` (the case
`L = K`) is of the form `Zer(𝒫, Kᵏ)` for a finite `𝒫`. -/
theorem exists_finset_zerOfIdeal (I : Ideal (MvPolynomial (Fin k) K)) :
    ∃ P : Finset (MvPolynomial (Fin k) K),
      zerOfIdeal (L := L) I = {x : Fin k → L | ∀ p ∈ P, MvPolynomial.aeval x p = 0} := by
  obtain ⟨P, hP⟩ := theorem_4_61 I
  exact ⟨P, by rw [hP, zerOfIdeal_idealOfPolys]⟩

end Azurite.BPR.Chapter4

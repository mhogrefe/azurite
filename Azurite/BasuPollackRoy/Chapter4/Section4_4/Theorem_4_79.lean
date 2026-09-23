import Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_78

/-!
# BPR Theorem 4.79: radical = vanishing ideal

For a finite `𝒫 ⊂ K[X₁, …, X_k]` (with `K` of characteristic zero and `C` algebraically closed),
the radical of `Ideal(𝒫, K)` coincides with the set of polynomials vanishing on `Zer(𝒫, C^k)`:
`√Ideal(𝒫, K) = {P | ∀ x ∈ Zer(𝒫, C^k), P(x) = 0}`. This follows from Theorem 4.78.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {K : Type*} [Field K]

/-- **BPR Theorem 4.79.** The radical of `Ideal(𝒫, K)` is exactly the set of polynomials
vanishing on `Zer(𝒫, C^k)` (with `K` of characteristic zero and `C` algebraically closed). -/
theorem theorem_4_79 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C] {k : ℕ}
    (Ps : Finset (MvPolynomial (Fin k) K)) :
    ((idealOfPolys Ps).radical : Set (MvPolynomial (Fin k) K)) =
      {P | ∀ x ∈ zerOfFinset C Ps, MvPolynomial.aeval x P = 0} := by
  ext P
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  constructor
  · -- `P ∈ √I ⟹ P^n ∈ I ⟹ (P(x))^n = 0 ⟹ P(x) = 0` on `Zer(𝒫)`.
    intro hP x hx
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hP
    have hz : MvPolynomial.aeval x (P ^ n) = 0 := aeval_eq_zero_of_mem_idealOfPolys hn x hx
    rw [map_pow] at hz
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0; rw [pow_zero] at hz; exact absurd hz one_ne_zero
    · exact pow_eq_zero_iff hn0.ne' |>.mp hz
  · -- `P` vanishes on `Zer(𝒫) ⟹ P^n ∈ I` (Theorem 4.78) `⟹ P ∈ √I`.
    intro hP
    exact Ideal.mem_radical_iff.mpr (theorem_4_78 Ps P hP)

end Azurite.BPR.Chapter4

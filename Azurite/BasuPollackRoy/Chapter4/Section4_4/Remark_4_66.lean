import Azurite.BasuPollackRoy.Chapter4.Section4_4.Reduction
import Azurite.BasuPollackRoy.Chapter4.Section4_4.IdealOfPolynomials

/-!
# BPR Remark 4.66: reduction stays in the ideal

If `P` is reducible to `Q` modulo `𝒢`, then `P − Q ∈ Ideal(𝒢, K)` (`remark_4_66`). In
particular, if `P` is reducible to `0` modulo `𝒢`, then `P ∈ Ideal(𝒢, K)`, i.e.
`P = ∑_{G ∈ 𝒢} A_G G` for some coefficients `A_G` (`remark_4_66_repr`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- A single reduction step changes `P` by an element of `Ideal(𝒢, K)`: if `Q` is a reduction
of `P` modulo `𝒢`, then `P − Q ∈ Ideal.span 𝒢`. -/
theorem sub_mem_span_of_isReduction (m : MonomialOrder (Fin k))
    (𝒢 : Finset (MvPolynomial (Fin k) K)) {P Q : MvPolynomial (Fin k) K}
    (h : IsReduction m 𝒢 P Q) : P - Q ∈ Ideal.span (↑𝒢 : Set _) := by
  obtain ⟨G, hG, α, _, rfl⟩ := h
  by_cases hle : m.degree G ≤ α
  · rw [Red_of_le m P G hle, sub_sub_cancel]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr hG))
  · rw [Red_of_not_le m P G hle, sub_self]
    exact Submodule.zero_mem _

/-- **BPR Remark 4.66.** If `P` is reducible to `Q` modulo `𝒢`, then
`P − Q ∈ Ideal(𝒢, K)`. -/
theorem remark_4_66 (m : MonomialOrder (Fin k)) (𝒢 : Finset (MvPolynomial (Fin k) K))
    {P Q : MvPolynomial (Fin k) K} (h : ReducibleTo m 𝒢 P Q) :
    P - Q ∈ Ideal.span (↑𝒢 : Set _) := by
  induction h with
  | refl => rw [sub_self]; exact Submodule.zero_mem _
  | tail _ hbc ih =>
    have := Submodule.add_mem _ ih (sub_mem_span_of_isReduction m 𝒢 hbc)
    rwa [sub_add_sub_cancel] at this

/-- **BPR Remark 4.66 (reduction to zero).** If `P` is reducible to `0` modulo `𝒢`, then
`P ∈ Ideal(𝒢, K)`, hence `P = ∑_{G ∈ 𝒢} A_G G` for some coefficients `A_G ∈ K[X₁, …, X_k]`. -/
theorem remark_4_66_repr (m : MonomialOrder (Fin k)) (𝒢 : Finset (MvPolynomial (Fin k) K))
    {P : MvPolynomial (Fin k) K} (h : ReducibleTo m 𝒢 P 0) :
    ∃ A : MvPolynomial (Fin k) K → MvPolynomial (Fin k) K, ∑ G ∈ 𝒢, A G * G = P := by
  have hP : P ∈ idealOfPolys 𝒢 := by
    have := remark_4_66 m 𝒢 h
    rwa [sub_zero] at this
  exact (mem_idealOfPolys_iff 𝒢 P).mp hP

/-- Strengthened reduction-to-standard-representation helper carrying the degree-non-increasing
invariant. If `P` is reducible to `Q` modulo `𝒢`, then `lmon(Q) ≼ lmon(P)` and `P − Q` has a
representation `∑ A_G G` in which every term `A_G G` has leading monomial `≼ lmon(P)`. -/
theorem reduction_standard_repr (m : MonomialOrder (Fin k))
    (𝒢 : Finset (MvPolynomial (Fin k) K)) {P Q : MvPolynomial (Fin k) K}
    (h : ReducibleTo m 𝒢 P Q) :
    m.toSyn (m.degree Q) ≤ m.toSyn (m.degree P) ∧
    ∃ A : MvPolynomial (Fin k) K → MvPolynomial (Fin k) K,
      (P - Q = ∑ G ∈ 𝒢, A G * G) ∧
      (∀ G ∈ 𝒢, m.toSyn (m.degree (A G * G)) ≤ m.toSyn (m.degree P)) := by
  unfold ReducibleTo at h
  induction h with
  | refl =>
    refine ⟨le_refl _, fun _ => 0, ?_, ?_⟩
    · simp
    · intro G _
      simp
  | @tail b c hcd hstep ih =>
    obtain ⟨hdeg_b, A, hrepr, hbound⟩ := ih
    obtain ⟨G₀, hG₀, α, hα, rfl⟩ := hstep
    classical
    by_cases hle : m.degree G₀ ≤ α
    · rw [Red_of_le m b G₀ hle]
      set β := α - m.degree G₀ with hβ
      set d := b.coeff α / m.leadingCoeff G₀ with hd
      set T := (monomial β d : MvPolynomial (Fin k) K) * G₀ with hT
      -- b.coeff α ≠ 0 since α ∈ b.support
      have hcoeff : b.coeff α ≠ 0 := by
        rwa [← MvPolynomial.mem_support_iff]
      -- degree bound for T
      have hdegT : m.toSyn (m.degree T) ≤ m.toSyn (m.degree P) := by
        by_cases hG0 : G₀ = 0
        · subst hG0
          simp [hT]
        · have hlc : m.leadingCoeff G₀ ≠ 0 :=
            fun hc => hG0 (MonomialOrder.leadingCoeff_eq_zero_iff.mp hc)
          have hd0 : d ≠ 0 := div_ne_zero hcoeff hlc
          have hmon0 : (monomial β d : MvPolynomial (Fin k) K) ≠ 0 := by
            rwa [Ne, MvPolynomial.monomial_eq_zero]
          have hdeg_mul : m.degree T = β + m.degree G₀ := by
            rw [hT, MonomialOrder.degree_mul hmon0 hG0]
            congr 1
            rw [MonomialOrder.degree_monomial, ite_eq_right hd0]
          have hβadd : β + m.degree G₀ = α := by
            rw [hβ, tsub_add_cancel_of_le hle]
          rw [hdeg_mul, hβadd]
          calc m.toSyn α ≤ m.toSyn (m.degree b) := MonomialOrder.le_degree hα
            _ ≤ m.toSyn (m.degree P) := hdeg_b
      refine ⟨?_, fun G => A G + (if G = G₀ then (monomial β d : MvPolynomial (Fin k) K) else 0),
        ?_, ?_⟩
      · -- conjunct 1: degree of b - T
        refine le_trans MonomialOrder.degree_sub_le ?_
        exact sup_le hdeg_b hdegT
      · -- conjunct 2: representation
        have hbtT : P - (b - T) = (P - b) + T := by ring
        rw [hbtT]
        have : ∀ G, (A G + (if G = G₀ then (monomial β d : MvPolynomial (Fin k) K) else 0)) * G
            = A G * G + (if G = G₀ then T else 0) := by
          intro G
          rw [add_mul]
          by_cases hGG₀ : G = G₀
          · subst hGG₀; simp [hT]
          · simp [hGG₀]
        simp only [this, Finset.sum_add_distrib]
        rw [← hrepr, Finset.sum_ite_eq' 𝒢 G₀ (fun _ => T), ite_eq_left hG₀]
      · -- conjunct 3: degree bound
        intro G hG
        rw [add_mul]
        by_cases hGG₀ : G = G₀
        · subst hGG₀
          rw [ite_eq_left rfl]
          refine le_trans MonomialOrder.degree_add_le ?_
          rw [← hT]
          exact sup_le (hbound G hG) hdegT
        · rw [ite_eq_right hGG₀, zero_mul, add_zero]
          exact hbound G hG
    · rw [Red_of_not_le m b G₀ hle]
      exact ⟨hdeg_b, A, hrepr, hbound⟩

/-- **BPR Remark 4.66 (degree-bounded standard representation).** If `P` is reducible to `0`
modulo `𝒢`, then `P = ∑_{G ∈ 𝒢} A_G G` with every term `A_G G` satisfying
`lmon(A_G G) ≼ lmon(P)` (in the monomial-order sense). -/
theorem remark_4_66_repr_degree (m : MonomialOrder (Fin k))
    (𝒢 : Finset (MvPolynomial (Fin k) K)) {P : MvPolynomial (Fin k) K}
    (h : ReducibleTo m 𝒢 P 0) :
    ∃ A : MvPolynomial (Fin k) K → MvPolynomial (Fin k) K,
      (∑ G ∈ 𝒢, A G * G = P) ∧
      (∀ G ∈ 𝒢, m.toSyn (m.degree (A G * G)) ≤ m.toSyn (m.degree P)) := by
  obtain ⟨_, A, hrepr, hbound⟩ := reduction_standard_repr m 𝒢 h
  rw [sub_zero] at hrepr
  exact ⟨A, hrepr.symm, fun G hG => hbound G hG⟩

end Azurite.BPR.Chapter4

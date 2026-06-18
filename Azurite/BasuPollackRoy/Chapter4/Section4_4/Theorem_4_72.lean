import Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_77

/-!
# BPR Theorem 4.72: Weak Hilbert's Nullstellensatz

For a finite `𝒫 = {P₁, …, P_s} ⊂ K[X₁, …, X_k]` (with `K` of characteristic zero and `C`
algebraically closed), `Zer(𝒫, C^k) = ∅` if and only if `1 ∈ Ideal(𝒫, K)`, i.e. there are
`A₁, …, A_s` with `A₁ P₁ + ⋯ + A_s P_s = 1`.

The forward direction is Proposition 4.77: if `Zer(𝒫) = ∅` then the geometric alternative is
impossible (a finite mapping onto `C^{k'}` is surjective, so its source `Zer(𝒫)` would be
non-empty), leaving `1 ∈ Ideal(𝒫)`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

/-- A finite-mapping chain transfers non-emptiness of the (bottom) target zero set back to the
(top) source zero set: each step is surjective onto the next. -/
private theorem chain_source_nonempty {C : Type*} [Field C] [Algebra K C] {k' : ℕ} :
    (d : ℕ) → (Ps : Finset (MvPolynomial (Fin (k' + d)) K)) →
      (T : Finset (MvPolynomial (Fin k') K)) → IsFiniteMappingChain C k' d Ps T →
        (zerOfFinset C T).Nonempty → (zerOfFinset C Ps).Nonempty
  | 0, _, _, h, hT => by rw [isFiniteMappingChain_zero] at h; subst h; exact hT
  | d + 1, _, T, h, hT => by
      rw [isFiniteMappingChain_succ] at h
      obtain ⟨Q, hfm, hchain⟩ := h
      obtain ⟨y, hy⟩ := chain_source_nonempty d Q T hchain hT
      obtain ⟨x, hx, -⟩ := hfm.1 hy
      exact ⟨x, hx⟩

/-- **BPR Theorem 4.72 (Weak Hilbert's Nullstellensatz).** For `𝒫 ⊂ K[X₁, …, X_k]` with `K` of
characteristic zero and `C` algebraically closed, `Zer(𝒫, C^k) = ∅` iff there exist
`A : K[X₁, …, X_k]` (one per member) with `∑_{P ∈ 𝒫} A_P · P = 1` — that is, `1 ∈ Ideal(𝒫, K)`. -/
theorem theorem_4_72 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C] {k : ℕ}
    (Ps : Finset (MvPolynomial (Fin k) K)) :
    zerOfFinset C Ps = ∅ ↔
      ∃ A : MvPolynomial (Fin k) K → MvPolynomial (Fin k) K, ∑ p ∈ Ps, A p * p = 1 := by
  rw [← mem_idealOfPolys_iff]
  constructor
  · -- `Zer(𝒫) = ∅ ⟹ 1 ∈ Ideal(𝒫)`, via Proposition 4.77.
    intro hempty
    rcases proposition_4_77 (C := C) Ps with h | ⟨k', d, hk, σ, T, _, hT, hchain⟩
    · exact h
    · exfalso
      subst hk
      -- The chain is a finite mapping onto `Zer T = C^{k'}` (non-empty), so `Zer(𝒫.image σ)` is
      -- non-empty; pulling back through `σ` gives a point of `Zer(𝒫)`, contradicting emptiness.
      have hTne : (zerOfFinset C T).Nonempty := by
        rw [hT]; exact ⟨fun _ => 0, Set.mem_univ _⟩
      obtain ⟨x, hx⟩ := chain_source_nonempty d (Ps.image σ) T hchain hTne
      have hbridge : ((MvPolynomial.aeval x).comp σ.toAlgHom) =
          MvPolynomial.aeval (fun i => MvPolynomial.aeval x (σ (X i))) := by
        apply MvPolynomial.algHom_ext; intro i; simp
      have hmem : (fun i => MvPolynomial.aeval x (σ (X i))) ∈ zerOfFinset C Ps := by
        intro p hp
        have hpx : MvPolynomial.aeval x (σ p) = 0 := hx (σ p) (Finset.mem_image_of_mem σ hp)
        have : MvPolynomial.aeval (fun i => MvPolynomial.aeval x (σ (X i))) p = 0 := by
          rw [← hbridge]; exact hpx
        exact this
      rw [hempty] at hmem
      exact (Set.notMem_empty _) hmem
  · -- `1 ∈ Ideal(𝒫) ⟹ Zer(𝒫) = ∅`: any common zero would make `1` vanish.
    intro h1
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have h0 : MvPolynomial.aeval x (1 : MvPolynomial (Fin k) K) = 0 :=
      aeval_eq_zero_of_mem_idealOfPolys h1 x (fun p hp => hx p hp)
    simp at h0

end Azurite.BPR.Chapter4

import Azurite.BasuPollackRoy.Chapter3.Section3_2.Convex
import Azurite.BasuPollackRoy.Chapter3.Section3_2.Proposition_3_6
import Azurite.BasuPollackRoy.Chapter2.Section2_5.PNormIsSemialgebraic

/-! # BPR §3.2, Proposition 3.7 — convex semialgebraic sets are semialgebraically connected

If `C` is semialgebraic and convex then `C` is semialgebraically connected. Given a hypothetical
splitting `C = F₁ ⊔ F₂` into non-empty sets closed in `C`, pick `x₁ ∈ F₁`, `x₂ ∈ F₂`. The affine path
`λ ↦ (1 − λ) x₁ + λ x₂` is a continuous semialgebraic map `[0,1] → C` (using convexity), so pulling
the splitting back along it disconnects the interval `[0,1]` — contradicting Proposition 3.6. -/

namespace Azurite.BPR

open MvPolynomial

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [IsRealClosed R] in
/-- **A polynomial map is a semialgebraic function** on any semialgebraic domain (the multi-output
analog of `polyFun_isSemialgebraicFunction_on`). -/
theorem isSemialgebraicFunction_polynomialMap {A : Set (Fin k → R)} (hA : IsSemialgebraicSet A)
    (P : Fin ℓ → MvPolynomial (Fin k) R) :
    IsSemialgebraicFunction A (polynomialMap P) := by
  show IsSemialgebraicSet (funGraph A (polynomialMap P))
  have heq : funGraph A (polynomialMap P)
      = {z : Fin (k + ℓ) → R | z ∘ Fin.castAdd ℓ ∈ A}
        ∩ ⋂ j ∈ (Finset.univ : Finset (Fin ℓ)),
            {z : Fin (k + ℓ) → R |
              eval z (X (Fin.natAdd k j) - rename (Fin.castAdd ℓ) (P j)) = 0} := by
    ext z
    simp only [funGraph, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_univ,
      forall_true_left, map_sub, eval_X, eval_rename, sub_eq_zero, polynomialMap, funext_iff,
      Function.comp_apply]
  rw [heq]
  exact (IsSemialgebraicSet.comap (Fin.castAdd ℓ) hA).inter
    (IsSemialgebraicSet.iInter_finset _ fun j _ => IsSemialgebraicSet.eqZero _)

/-- **BPR Proposition 3.7.** A convex set is semialgebraically connected. (BPR states this for
semialgebraic convex `C`, but the proof never uses semialgebraicity of `C` itself — only of the
hypothetical splitting, which is part of the definition of semialgebraic connectedness.) -/
theorem proposition_3_7 {C : Set (Fin k → R)} (hCconv : IsConvex C) :
    IsSemialgebraicallyConnected C := by
  rintro ⟨F₁, F₂, hF₁ne, hF₂ne, hF₁sa, hF₂sa, hF₁cl, hF₂cl, hdisj, hunion⟩
  obtain ⟨x₁, hx₁⟩ := hF₁ne
  obtain ⟨x₂, hx₂⟩ := hF₂ne
  have hx₁C : x₁ ∈ C := hunion ▸ Set.mem_union_left _ hx₁
  have hx₂C : x₂ ∈ C := hunion ▸ Set.mem_union_right _ hx₂
  -- the affine path `λ ↦ (1 − λ) x₁ + λ x₂`, as a polynomial map
  set P : Fin k → MvPolynomial (Fin 1) R := fun j => (1 - X 0) * MvPolynomial.C (x₁ j) + X 0 * MvPolynomial.C (x₂ j) with hP
  have hpath : ∀ v : Fin 1 → R, polynomialMap P v = (1 - v 0) • x₁ + (v 0) • x₂ := by
    intro v; funext j
    simp only [polynomialMap, hP, map_add, map_mul, map_sub, eval_X, eval_C, map_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- the interval `[0,1]` and the path's properties
  set I : Set (Fin 1 → R) := {v | v 0 ∈ Set.Icc (0 : R) 1} with hI
  have hIsa : IsSemialgebraicSet I := by
    have he : I = {v : Fin 1 → R | eval v (X 0) ≥ 0} ∩ {v : Fin 1 → R | eval v (X 0 - MvPolynomial.C 1) ≤ 0} := by
      ext v
      simp only [hI, Set.mem_Icc, Set.mem_inter_iff, Set.mem_ofPred_eq, eval_X, map_sub, eval_C,
        ge_iff_le, sub_nonpos]
    rw [he]; exact (IsSemialgebraicSet.geZero _).inter (IsSemialgebraicSet.leZero (X 0 - MvPolynomial.C 1))
  have hφsa : IsSemialgebraicFunction I (polynomialMap P) :=
    isSemialgebraicFunction_polynomialMap hIsa P
  have hφcont : ContinuousOn (polynomialMap P) I := (continuous_polynomialMap P).continuousOn
  have hφmaps : Set.MapsTo (polynomialMap P) I C := fun v hv => by
    rw [hpath]; exact hCconv hx₁C hx₂C (v 0) hv
  -- pull the splitting back to `[0,1]`, contradicting Proposition 3.6
  refine isSemialgebraicallyConnected_interval (R := R) Set.ordConnected_Icc
    ⟨I ∩ polynomialMap P ⁻¹' F₁, I ∩ polynomialMap P ⁻¹' F₂, ⟨constPt 0, ?_, ?_⟩,
      ⟨constPt 1, ?_, ?_⟩, (proposition_2_83 hφsa).2 hF₁sa, (proposition_2_83 hφsa).2 hF₂sa,
      isClosedIn_preimage hφcont hφmaps hF₁cl, isClosedIn_preimage hφcont hφmaps hF₂cl, ?_, ?_⟩
  · exact ⟨le_refl 0, zero_le_one⟩
  · rw [Set.mem_preimage, hpath]
    simpa [constPt] using hx₁
  · exact ⟨zero_le_one, le_refl 1⟩
  · rw [Set.mem_preimage, hpath]
    simpa [constPt] using hx₂
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro v ⟨⟨_, hv₁⟩, _, hv₂⟩
    rw [Set.mem_preimage] at hv₁ hv₂
    exact absurd (hdisj ▸ Set.mem_inter hv₁ hv₂) (Set.notMem_empty _)
  · ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro (⟨hvI, _⟩ | ⟨hvI, _⟩) <;> exact hvI
    · intro hvI
      rcases (hunion ▸ hφmaps hvI : polynomialMap P v ∈ F₁ ∪ F₂) with h | h
      · exact Or.inl ⟨hvI, h⟩
      · exact Or.inr ⟨hvI, h⟩

end Azurite.BPR

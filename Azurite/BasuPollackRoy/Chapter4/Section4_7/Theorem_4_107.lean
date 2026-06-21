import Azurite.BasuPollackRoy.Chapter4.Section4_7.Proposition_4_106

/-!
# BPR §4.7, Theorem 4.107: affine weak Bézout

Affine polynomials `P₁, …, P_k ∈ C[X₁, …, X_k]` of degrees `d₁, …, d_k` have at most `d₁ ⋯ d_k`
non-singular zeros (`theorem_4_107`). The proof homogenizes each `Pᵢ` to a degree-`dᵢ` homogeneous
polynomial in `k + 1` variables, identifies the affine non-singular zeros with the projective ones
(via the Note `isNonsingularZero_dehom_iff_isNonsingularProjectiveZero`), and applies the projective
weak Bézout bound (Proposition 4.106).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

set_option linter.unusedSectionVars false

/-! ### Part A: multivariate homogenization -/

/-- **Homogenization.** Given `p ∈ C[X₁, …, X_k]` and a target degree `n`, the homogenization
`Phom p n ∈ C[X₀, X₁, …, X_k]` adds a new variable `X₀` (index `0`) and raises each monomial of `p`
to total degree `n`: the monomial `c·∏ⱼ Xⱼ^{mⱼ}` becomes `c·X₀^{n − |m|}·∏ⱼ X_{j+1}^{mⱼ}`. -/
noncomputable def Phom (p : MvPolynomial (Fin k) (Ri R)) (n : ℕ) :
    MvPolynomial (Fin (k + 1)) (Ri R) :=
  ∑ m ∈ p.support, MvPolynomial.monomial (Finsupp.cons (n - (m.sum fun _ e => e)) m) (p.coeff m)

/-- The degree of `Finsupp.cons a m` is `a + m.degree` (sum over the new variable plus the rest). -/
theorem degree_cons (a : ℕ) (m : Fin k →₀ ℕ) :
    (Finsupp.cons a m).degree = a + m.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  simp [Finsupp.cons_zero, Finsupp.cons_succ]

/-- `Phom p n` is homogeneous of degree `n`, provided `p.totalDegree ≤ n`. -/
theorem isHomogeneous_Phom {p : MvPolynomial (Fin k) (Ri R)} {n : ℕ} (hdeg : p.totalDegree ≤ n) :
    (Phom p n).IsHomogeneous n := by
  refine IsHomogeneous.sum _ _ _ (fun m hm => ?_)
  refine isHomogeneous_monomial _ ?_
  -- `(Finsupp.cons (n - |m|) m).degree = n`.
  rw [degree_cons]
  have hmd : m.degree = m.sum fun _ e => e := rfl
  have hmle : (m.sum fun _ e => e) ≤ n := by
    refine le_trans ?_ hdeg
    rw [← hmd]; exact MvPolynomial.le_totalDegree hm
  rw [hmd]
  omega

/-- Dehomogenizing a single homogenized monomial recovers the monomial: applying `X₀ ↦ 1`,
`X_{j+1} ↦ Xⱼ` to `monomial (Finsupp.cons a m) c` gives `monomial m c`. -/
theorem aeval_cons_one_monomial_cons (a : ℕ) (m : Fin k →₀ ℕ) (c : Ri R) :
    aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (monomial (Finsupp.cons a m) c)
      = monomial m c := by
  rw [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp)]
  rw [Fin.prod_univ_succ]
  simp only [Finsupp.cons_zero, Finsupp.cons_succ, Fin.cons_zero, Fin.cons_succ, one_pow, one_mul]
  rw [MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq,
    Finsupp.prod_fintype _ _ (fun i => by simp)]

/-- **Dehomogenization recovers the original.** Applying `X₀ ↦ 1`, `X_{j+1} ↦ Xⱼ` to `Phom p n`
gives back `p`. -/
theorem dehom_Phom (p : MvPolynomial (Fin k) (Ri R)) (n : ℕ) :
    aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (Phom p n) = p := by
  rw [Phom, map_sum]
  conv_rhs => rw [p.as_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  exact aeval_cons_one_monomial_cons _ m (p.coeff m)

/-! ### Part C: affine weak Bézout -/

/-- **BPR Theorem 4.107 (affine weak Bézout).** Affine polynomials `P₁, …, P_k ∈ C[X₁, …, X_k]` of
degrees `d₁, …, d_k ≥ 1` have at most `d₁ ⋯ d_k` non-singular zeros. The proof homogenizes each `Pᵢ`
to a degree-`dᵢ` homogeneous polynomial `Phom (P i) (d i)`, identifies the affine non-singular zeros
with the projective ones (via `isNonsingularZero_dehom_iff_isNonsingularProjectiveZero` and
`dehom_Phom`) along the injection `x ↦ (1 : x₁ : ⋯ : x_k)`, and applies Proposition 4.106. -/
theorem theorem_4_107 (P : Fin k → MvPolynomial (Fin k) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hdeg : ∀ i, (P i).totalDegree ≤ d i) :
    {x : Fin k → Ri R | IsNonsingularZero P x}.ncard ≤ ∏ i, d i := by
  classical
  -- homogenize.
  set Qhom : Fin k → MvPolynomial (Fin (k + 1)) (Ri R) := fun i => Phom (P i) (d i) with hQhom
  have hQhomdeg : ∀ i, (Qhom i).IsHomogeneous (d i) := fun i => isHomogeneous_Phom (hdeg i)
  -- the affine↔projective correspondence.
  set φ : (Fin k → Ri R) → complexProjectiveSpace R k :=
    fun x => mkLine (Fin.cons 1 x) (cons_one_ne_zero x) with hφ
  have hφinj : Function.Injective φ := mkLine_cons_one_injective
  have hiff : ∀ x : Fin k → Ri R,
      IsNonsingularZero P x ↔ IsNonsingularProjectiveZero Qhom (φ x) := by
    intro x
    have hdehom : (fun i => aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (Qhom i)) = P := by
      funext i; rw [hQhom]; exact dehom_Phom (P i) (d i)
    have := isNonsingularZero_dehom_iff_isNonsingularProjectiveZero Qhom d hQhomdeg x
    rw [hdehom] at this
    exact this
  -- bound finite subsets of the affine zero set.
  apply ncard_le_of_forall_finset_card_le
  intro G hG
  -- image under `φ` is a finset of projective non-singular zeros, of equal cardinality.
  have hGimgsub : (↑(G.image φ) : Set (complexProjectiveSpace R k))
      ⊆ {x | IsNonsingularProjectiveZero Qhom x} := by
    intro y hy
    rw [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨x, hxG, rfl⟩ := hy
    have hx : IsNonsingularZero P x := hG hxG
    exact (hiff x).mp hx
  have hcard : (G.image φ).card = G.card := Finset.card_image_of_injective G hφinj
  rw [← hcard]
  exact proposition_4_106_finsetCard Qhom d hd hQhomdeg (G.image φ) hGimgsub

end Azurite.BPR.Chapter4

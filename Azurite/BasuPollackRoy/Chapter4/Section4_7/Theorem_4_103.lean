import Azurite.BasuPollackRoy.Chapter4.Section4_7.Elimination
import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveZeroSet
import Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_68
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# BPR §4.7, Theorem 4.103 (projective weak Bézout / projection of an algebraic set)

The projection of an algebraic subset of `ℙ_{k₀}(C) × ℙ_{k₁}(C)` onto the second factor `ℙ_{k₁}(C)`
is again algebraic. We wire the affine-cone elimination core (`Elimination.elimination`) to the
projective-space API of §4.7.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

namespace Theorem_4_103

/-! ### The variable-split equivalence `Σ → ⊕`. -/

/-- The variable-split equivalence: the sigma index `(i : Fin 2) × Fin (k i + 1)` is identified with
the sum `Fin (k 0 + 1) ⊕ Fin (k 1 + 1)`, block `0` going to `inl` and block `1` to `inr`. -/
def σequiv (k : Fin 2 → ℕ) :
    ((i : Fin 2) × Fin (k i + 1)) ≃ Fin (k 0 + 1) ⊕ Fin (k 1 + 1) where
  toFun s :=
    Fin.cases (motive := fun i => Fin (k i + 1) → Fin (k 0 + 1) ⊕ Fin (k 1 + 1))
      Sum.inl
      (fun i' j => Sum.inr (Fin.cast (by rw [Fin.eq_zero i']; rfl) j))
      s.1 s.2
  invFun := Sum.elim (fun j => ⟨0, j⟩) (fun j => ⟨1, j⟩)
  left_inv := by
    rintro ⟨i, j⟩
    fin_cases i <;> rfl
  right_inv := by
    rintro (j | j) <;> rfl

@[simp] theorem σequiv_symm_inl (k : Fin 2 → ℕ) (j : Fin (k 0 + 1)) :
    (σequiv k).symm (Sum.inl j) = ⟨0, j⟩ := rfl

@[simp] theorem σequiv_symm_inr (k : Fin 2 → ℕ) (j : Fin (k 1 + 1)) :
    (σequiv k).symm (Sum.inr j) = ⟨1, j⟩ := rfl

@[simp] theorem σequiv_apply_zero (k : Fin 2 → ℕ) (j : Fin (k 0 + 1)) :
    σequiv k ⟨0, j⟩ = Sum.inl j := rfl

theorem σequiv_apply_one (k : Fin 2 → ℕ) (j : Fin (k 1 + 1)) :
    σequiv k ⟨1, j⟩ = Sum.inr j := by
  apply (σequiv k).symm.injective
  rw [Equiv.symm_apply_apply, σequiv_symm_inr]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The vector reconstruction: given block-coordinate functions `a` (block 0) and `b` (block 1),
the assignment `s ↦ (Sum.elim a b) (σequiv s)` recovers the block-indexed assignment
`s ↦ v s.1 s.2` where `v 0 = a`, `v 1 = b`. -/
theorem sumElim_σequiv (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R) (b : Fin (k 1 + 1) → Ri R)
    (v : (i : Fin 2) → (Fin (k i + 1) → Ri R)) (ha : v 0 = a) (hb : v 1 = b) :
    (fun s : (i : Fin 2) × Fin (k i + 1) => (Sum.elim a b) (σequiv k s)) = fun s => v s.1 s.2 := by
  funext s
  obtain ⟨i, j⟩ := s
  revert j
  refine Fin.cases ?_ (fun i' j => ?_) i
  · intro j
    rw [σequiv_apply_zero, Sum.elim_inl, ha]
  · obtain rfl : i' = 0 := Fin.eq_zero i'
    show Sum.elim a b (σequiv k ⟨1, j⟩) = v 1 j
    rw [σequiv_apply_one, Sum.elim_inr, hb]

/-! ### The split polynomial and the eval bridge. -/

variable {C : Type*} [CommRing C]

/-- **Eval bridge for `sumToIter`.** Evaluating the iterated polynomial `sumToIter P` first in the
inner variables at `b` and then in the outer variables at `a` equals evaluating `P` at the combined
assignment `Sum.elim a b`. -/
theorem eval_sumToIter {S₁ S₂ : Type*} (a : S₁ → C) (b : S₂ → C)
    (P : MvPolynomial (S₁ ⊕ S₂) C) :
    eval a (map (eval b) (sumToIter C S₁ S₂ P)) = eval (Sum.elim a b) P := by
  induction P using MvPolynomial.induction_on with
  | C r => rw [sumToIter_C, map_C, eval_C, eval_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, eval_add, hp, hq, eval_add]
  | mul_X p i hp =>
    cases i with
    | inl b₁ =>
      rw [map_mul, map_mul, eval_mul, hp, sumToIter_Xl, map_X, eval_X, eval_mul, eval_X,
        Sum.elim_inl]
    | inr c =>
      rw [map_mul, map_mul, eval_mul, hp, sumToIter_Xr, map_C, eval_C, eval_mul]
      simp only [eval_X, Sum.elim_inr]

/-- The split of a two-block polynomial `P` into an `X`-polynomial (block `0`) with `Y`-polynomial
(block `1`) coefficients: relabel the sigma variables to a sum, then iterate. -/
noncomputable def split (k : Fin 2 → ℕ)
    (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)) :
    MvPolynomial (Fin (k 0 + 1)) (MvPolynomial (Fin (k 1 + 1)) (Ri R)) :=
  sumToIter (Ri R) (Fin (k 0 + 1)) (Fin (k 1 + 1)) (rename (σequiv k) P)

/-- **Coefficient dictionary for `sumToIter`.** The `γ₁`-coefficient of the `γ₀`-coefficient of the
iterated polynomial `sumToIter P` equals the coefficient of `P` at the combined exponent
`γ₀.sumElim γ₁`. -/
theorem coeff_sumToIter {S₁ S₂ : Type*} (P : MvPolynomial (S₁ ⊕ S₂) C) (γ₀ : S₁ →₀ ℕ)
    (γ₁ : S₂ →₀ ℕ) :
    ((sumToIter C S₁ S₂ P).coeff γ₀).coeff γ₁ = P.coeff (γ₀.sumElim γ₁) := by
  classical
  induction P using MvPolynomial.induction_on generalizing γ₀ γ₁ with
  | C r =>
    have key : (0 : S₁ ⊕ S₂ →₀ ℕ) = γ₀.sumElim γ₁ ↔ (0 : S₁ →₀ ℕ) = γ₀ ∧ (0 : S₂ →₀ ℕ) = γ₁ := by
      rw [eq_comm, eq_comm (a := (0 : S₁ →₀ ℕ)), eq_comm (a := (0 : S₂ →₀ ℕ))]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · ext a; have := Finsupp.ext_iff.mp h (Sum.inl a); simpa [Finsupp.sumElim_inl] using this
        · ext b; have := Finsupp.ext_iff.mp h (Sum.inr b); simpa [Finsupp.sumElim_inr] using this
      · rintro ⟨h1, h2⟩; subst h1; subst h2; ext x; cases x <;> simp
    simp only [sumToIter_C, coeff_C, apply_ite (coeff γ₁), coeff_zero]
    split_ifs with h0 h1 h2 <;> simp_all
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, coeff_add, hp, hq]
  | mul_X p i hp =>
    cases i with
    | inl b =>
      have hmem : b ∈ γ₀.support ↔ (Sum.inl b : S₁ ⊕ S₂) ∈ (γ₀.sumElim γ₁).support := by
        simp [Finsupp.mem_support_iff]
      have hsub : (γ₀ - Finsupp.single b 1).sumElim γ₁
          = γ₀.sumElim γ₁ - Finsupp.single (Sum.inl b) 1 := by
        ext x
        cases x with
        | inl a => simp [Finsupp.sumElim_inl, Finsupp.single_apply, Sum.inl.injEq]
        | inr a => simp [Finsupp.sumElim_inr]
      rw [map_mul, sumToIter_Xl, coeff_mul_X', coeff_mul_X', apply_ite (coeff γ₁), coeff_zero]
      split_ifs with h1 h2 h2
      · rw [hp, hsub]
      · exact absurd (hmem.1 h1) h2
      · exact absurd (hmem.2 h2) h1
      · rfl
    | inr c =>
      rw [map_mul, sumToIter_Xr]
      have e : coeff γ₀ ((sumToIter C S₁ S₂) p * MvPolynomial.C (X c))
          = coeff γ₀ ((sumToIter C S₁ S₂) p) * X c := by rw [mul_comm, coeff_C_mul, mul_comm]
      have hmem : c ∈ γ₁.support ↔ (Sum.inr c : S₁ ⊕ S₂) ∈ (γ₀.sumElim γ₁).support := by
        simp [Finsupp.mem_support_iff]
      have hsub : γ₀.sumElim (γ₁ - Finsupp.single c 1)
          = γ₀.sumElim γ₁ - Finsupp.single (Sum.inr c) 1 := by
        ext x
        cases x with
        | inl a => simp [Finsupp.sumElim_inl]
        | inr a => simp [Finsupp.sumElim_inr, Finsupp.single_apply, Sum.inr.injEq]
      rw [e, coeff_mul_X', coeff_mul_X']
      split_ifs with h1 h2 h2
      · rw [hp, hsub]
      · exact absurd (hmem.1 h1) h2
      · exact absurd (hmem.2 h2) h1
      · rfl

/-- **The eval-coords bridge.** Evaluating the split polynomial first in the inner (block-1) variables
at `v 1` and then in the outer (block-0) variables at `v 0` recovers `evalCoords P v`. -/
theorem eval_split (k : Fin 2 → ℕ) (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R))
    (v : (i : Fin 2) → (Fin (k i + 1) → Ri R)) :
    eval (v 0) (map (eval (v 1)) (split k P)) = evalCoords P v := by
  rw [split, eval_sumToIter, eval_rename, evalCoords]
  congr 1
  rw [Function.comp_def]
  exact congrArg _ (sumElim_σequiv k (v 0) (v 1) v rfl rfl)

/-! ### Multihomogeneity translation. -/

omit [IsRealClosed R] in
/-- **Coefficient dictionary for `split`.** The inner (block-1) `γ₁`-coefficient of the outer
(block-0) `γ₀`-coefficient of `split P` equals the coefficient of `P` at the sigma-exponent obtained
by relabeling `γ₀.sumElim γ₁` through `σequiv.symm`. -/
theorem coeff_coeff_split (k : Fin 2 → ℕ)
    (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R))
    (γ₀ : Fin (k 0 + 1) →₀ ℕ) (γ₁ : Fin (k 1 + 1) →₀ ℕ) :
    ((split k P).coeff γ₀).coeff γ₁
      = P.coeff (Finsupp.mapDomain (σequiv k).symm (γ₀.sumElim γ₁)) := by
  rw [split, coeff_sumToIter]
  have hmap : Finsupp.mapDomain (σequiv k) (Finsupp.mapDomain (σequiv k).symm (γ₀.sumElim γ₁))
      = γ₀.sumElim γ₁ := by
    rw [← Finsupp.mapDomain_comp]
    simp only [Equiv.self_comp_symm, Finsupp.mapDomain_id]
  conv_lhs => rw [← hmap]
  exact coeff_rename_mapDomain (σequiv k) (σequiv k).injective P _

/-- The block-0 exponent of the relabeled sigma-monomial recovers `γ₀`. -/
theorem mapDomain_symm_inl (k : Fin 2 → ℕ) (γ₀ : Fin (k 0 + 1) →₀ ℕ) (γ₁ : Fin (k 1 + 1) →₀ ℕ)
    (j : Fin (k 0 + 1)) :
    Finsupp.mapDomain (σequiv k).symm (γ₀.sumElim γ₁) ⟨0, j⟩ = γ₀ j := by
  have h : (σequiv k).symm (Sum.inl j) = ⟨0, j⟩ := σequiv_symm_inl k j
  rw [← h, Finsupp.mapDomain_apply (σequiv k).symm.injective, Finsupp.sumElim_inl]

/-- The block-1 exponent of the relabeled sigma-monomial recovers `γ₁`. -/
theorem mapDomain_symm_inr (k : Fin 2 → ℕ) (γ₀ : Fin (k 0 + 1) →₀ ℕ) (γ₁ : Fin (k 1 + 1) →₀ ℕ)
    (j : Fin (k 1 + 1)) :
    Finsupp.mapDomain (σequiv k).symm (γ₀.sumElim γ₁) ⟨1, j⟩ = γ₁ j := by
  have h : (σequiv k).symm (Sum.inr j) = ⟨1, j⟩ := σequiv_symm_inr k j
  rw [← h, Finsupp.mapDomain_apply (σequiv k).symm.injective, Finsupp.sumElim_inr]

omit [IsRealClosed R] in
/-- **Block-0 homogeneity of `split P`.** If `P` is multihomogeneous of multidegree `dd`, then
`split P` is homogeneous of degree `dd 0` in the block-0 variables. -/
theorem split_isHomogeneous {k : Fin 2 → ℕ}
    {P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)} {dd : Fin 2 → ℕ}
    (hP : IsMultihomogeneous P dd) : (split k P).IsHomogeneous (dd 0) := by
  intro γ₀ hγ₀
  -- find a nonzero inner coefficient of `coeff γ₀ (split k P)`
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁, ((split k P).coeff γ₀).coeff γ₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hγ₀ (MvPolynomial.ext _ _ (fun γ₁ => by rw [h γ₁, coeff_zero]))
  rw [coeff_coeff_split] at hγ₁
  set c := Finsupp.mapDomain (σequiv k).symm (γ₀.sumElim γ₁) with hc
  have hcmem : c ∈ P.support := MvPolynomial.mem_support_iff.mpr hγ₁
  rw [Finsupp.weight_apply]
  simp only [smul_eq_mul, mul_one, Pi.one_apply]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl),
    show (∑ j : Fin (k 0 + 1), γ₀ j) = ∑ j, c ⟨0, j⟩ from
      Finset.sum_congr rfl fun j _ => (mapDomain_symm_inl k γ₀ γ₁ j).symm]
  exact hP 0 c hcmem

omit [IsRealClosed R] in
/-- **Block-1 homogeneity of the coefficients of `split P`.** If `P` is multihomogeneous of
multidegree `dd`, then every block-0 coefficient of `split P` is homogeneous of degree `dd 1` in the
block-1 variables. -/
theorem coeff_split_isHomogeneous {k : Fin 2 → ℕ}
    {P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)} {dd : Fin 2 → ℕ}
    (hP : IsMultihomogeneous P dd) (γ₀ : Fin (k 0 + 1) →₀ ℕ) :
    ((split k P).coeff γ₀).IsHomogeneous (dd 1) := by
  intro γ₁ hγ₁
  rw [coeff_coeff_split] at hγ₁
  set c := Finsupp.mapDomain (σequiv k).symm (γ₀.sumElim γ₁) with hc
  have hcmem : c ∈ P.support := MvPolynomial.mem_support_iff.mpr hγ₁
  rw [Finsupp.weight_apply]
  simp only [smul_eq_mul, mul_one, Pi.one_apply]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl),
    show (∑ j : Fin (k 1 + 1), γ₁ j) = ∑ j, c ⟨1, j⟩ from
      Finset.sum_congr rfl fun j _ => (mapDomain_symm_inr k γ₀ γ₁ j).symm]
  exact hP 1 c hcmem

/-! ### Renaming the elimination output into single-block (`Fin 1`) form. -/

/-- The single-block index equivalence `Fin (n+1) ≃ (i : Fin 1) × Fin (n+1)`. -/
def e1 (n : ℕ) : Fin (n + 1) ≃ ((_ : Fin 1) × Fin (n + 1)) where
  toFun j := ⟨0, j⟩
  invFun s := s.2
  left_inv _ := rfl
  right_inv := by rintro ⟨i, j⟩; obtain rfl : i = 0 := Subsingleton.elim _ _; rfl

@[simp] theorem e1_apply (n : ℕ) (j : Fin (n + 1)) : e1 n j = ⟨0, j⟩ := rfl

omit [IsRealClosed R] in
/-- Renaming a `Y`-homogeneous polynomial of degree `m` along `e1` makes it multihomogeneous of
multidegree `(fun _ => m) : Fin 1 → ℕ`. -/
theorem rename_e1_isMultihomogeneous {n m : ℕ} {Q : MvPolynomial (Fin (n + 1)) (Ri R)}
    (hQ : Q.IsHomogeneous m) :
    IsMultihomogeneous (rename (e1 n) Q) (fun _ : Fin 1 => m) := by
  classical
  intro i γ hγ
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [MvPolynomial.support_rename_of_injective (e1 n).injective] at hγ
  obtain ⟨γ', hγ'mem, rfl⟩ := Finset.mem_image.mp hγ
  have hdeg : (Finsupp.weight 1) γ' = m := hQ (MvPolynomial.mem_support_iff.mp hγ'mem)
  rw [Finsupp.weight_apply] at hdeg
  simp only [smul_eq_mul, mul_one, Pi.one_apply] at hdeg
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdeg
  rw [show (∑ j : Fin (n + 1), Finsupp.mapDomain (e1 n) γ' ⟨0, j⟩) = ∑ j : Fin (n + 1), γ' j from
    Finset.sum_congr rfl fun j _ => by
      rw [show (⟨0, j⟩ : (i : Fin 1) × Fin (n + 1)) = e1 n j from rfl,
        Finsupp.mapDomain_apply (e1 n).injective]]
  exact hdeg

/-- `ProjVanishes` of the single-block renamed polynomial reduces to ordinary evaluation at the
representative of the (single) projective coordinate. -/
theorem projVanishes_rename_e1 {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) (Ri R))
    (y : (i : Fin 1) → complexProjectiveSpace R n) :
    ProjVanishes (k := fun _ : Fin 1 => n) (rename (e1 n) Q) y ↔ eval (y 0).rep Q = 0 := by
  rw [ProjVanishes, evalCoords, eval_rename]
  refine Iff.of_eq (congrArg (· = 0) ?_)
  refine congrArg (eval · Q) ?_
  funext j
  rfl

/-! ### Projective wiring. -/

/-- The two-block coordinate vector with block `0` equal to `a` and block `1` equal to `b`. -/
def blockVec (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R) (b : Fin (k 1 + 1) → Ri R) :
    (i : Fin 2) → (Fin (k i + 1) → Ri R) :=
  Fin.cases a (fun i' => (Fin.eq_zero i' ▸ b : Fin (k (Fin.succ i') + 1) → Ri R))

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem blockVec_zero (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R)
    (b : Fin (k 1 + 1) → Ri R) : blockVec k a b 0 = a := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem blockVec_one (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R)
    (b : Fin (k 1 + 1) → Ri R) : blockVec k a b 1 = b := rfl

omit [IsRealClosed R] in
/-- Each block of a block vector built from nonzero vectors is nonzero. -/
theorem blockVec_ne_zero (k : Fin 2 → ℕ) (a : Fin (k 0 + 1) → Ri R) (b : Fin (k 1 + 1) → Ri R)
    (i : Fin 2) (ha : a ≠ 0) (hb : b ≠ 0) : blockVec k a b i ≠ 0 := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · exact ha
  · obtain rfl : i' = 0 := Fin.eq_zero i'
    exact hb

/-- The split evaluation at `(a, b)` equals `evalCoords P` at the block vector `blockVec a b`. -/
theorem eval_split_blockVec {k : Fin 2 → ℕ}
    (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)) (a : Fin (k 0 + 1) → Ri R)
    (b : Fin (k 1 + 1) → Ri R) :
    eval a (map (eval b) (split k P)) = evalCoords P (blockVec k a b) := by
  rw [← eval_split k P (blockVec k a b), blockVec_zero, blockVec_one]

/-- `ProjVanishes P x` unfolds, via the split, to the two-stage evaluation of `split P`. -/
theorem projVanishes_iff_eval_split {k : Fin 2 → ℕ}
    (P : MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R))
    (x : (i : Fin 2) → complexProjectiveSpace R (k i)) :
    ProjVanishes P x ↔
      eval (x 0).rep (map (eval (x 1).rep) (split k P)) = 0 := by
  rw [ProjVanishes, ← eval_split k P (fun i => (x i).rep)]

/-- **Rep-independence transfer for block 0.** Fixing the block-1 coordinate `y₁` (a line) and a
finite multihomogeneous family `Ps`, the existence of a block-0 line `x₀` whose representative makes
all `split`-evaluations vanish is equivalent to the existence of an arbitrary nonzero block-0 vector
`z` doing the same. -/
theorem exists_line_iff_exists_nonzero {k : Fin 2 → ℕ}
    (Ps : Finset (MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)))
    (hPs : ∀ P ∈ Ps, ∃ dd : Fin 2 → ℕ, IsMultihomogeneous P dd)
    (y₁ : complexProjectiveSpace R (k 1)) :
    (∃ x₀ : complexProjectiveSpace R (k 0),
        ∀ P ∈ Ps, eval (x₀).rep (map (eval y₁.rep) (split k P)) = 0)
      ↔ (∃ z : Fin (k 0 + 1) → Ri R, z ≠ 0 ∧
          ∀ P ∈ Ps, eval z (map (eval y₁.rep) (split k P)) = 0) := by
  constructor
  · rintro ⟨x₀, hx₀⟩
    exact ⟨x₀.rep, x₀.rep_nonzero, hx₀⟩
  · rintro ⟨z, hz, hzvan⟩
    refine ⟨mkLine z hz, fun P hP => ?_⟩
    obtain ⟨dd, hdd⟩ := hPs P hP
    have hzP : eval z (map (eval y₁.rep) (split k P)) = 0 := hzvan P hP
    -- transfer the vanishing from `z` to `(mkLine z hz).rep` via rep-independence.
    rw [eval_split_blockVec]
    rw [eval_split_blockVec] at hzP
    -- the two block vectors agree on block 1 and span the same line on block 0.
    have hmk : ∀ i : Fin 2,
        mkLine (blockVec k (mkLine z hz).rep y₁.rep i)
          (blockVec_ne_zero k _ y₁.rep i (mkLine z hz).rep_nonzero y₁.rep_nonzero)
        = mkLine (blockVec k z y₁.rep i)
          (blockVec_ne_zero k z y₁.rep i hz y₁.rep_nonzero) := by
      refine Fin.cases ?_ (fun i' => ?_)
      · exact Projectivization.mk_rep (mkLine z hz)
      · obtain rfl : i' = 0 := Fin.eq_zero i'
        rfl
    rw [evalCoords_eq_zero_iff_of_mkLine_eq hdd _ _ hmk]
    exact hzP

/-- The two-block projective point with block `0` equal to `x₀` and block `1` equal to `y₁`. -/
def blockVecPt (k : Fin 2 → ℕ) (x₀ : complexProjectiveSpace R (k 0))
    (y₁ : complexProjectiveSpace R (k 1)) : (i : Fin 2) → complexProjectiveSpace R (k i) :=
  Fin.cases x₀ (fun i' => (Fin.eq_zero i' ▸ y₁ : complexProjectiveSpace R (k (Fin.succ i'))))

omit [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] theorem blockVecPt_zero (k : Fin 2 → ℕ) (x₀ : complexProjectiveSpace R (k 0))
    (y₁ : complexProjectiveSpace R (k 1)) : blockVecPt k x₀ y₁ 0 = x₀ := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] theorem blockVecPt_one (k : Fin 2 → ℕ) (x₀ : complexProjectiveSpace R (k 0))
    (y₁ : complexProjectiveSpace R (k 1)) : blockVecPt k x₀ y₁ 1 = y₁ := rfl

end Theorem_4_103

open Theorem_4_103

/-- **Workhorse for BPR Theorem 4.103.** The projection onto the second factor of the algebraic set
`Zer(𝒫, ℙ_{k₀}(C) × ℙ_{k₁}(C))` is the zero set of an explicit finite family of multihomogeneous
polynomials (the maximal minors of the elimination matrix). -/
theorem projection_isAlgebraic {k : Fin 2 → ℕ}
    (Ps : Finset (MvPolynomial ((i : Fin 2) × Fin (k i + 1)) (Ri R)))
    (hPs : ∀ P ∈ Ps, ∃ dd : Fin 2 → ℕ, IsMultihomogeneous P dd) :
    ∃ Qs : Finset (MvPolynomial ((_ : Fin 1) × Fin (k 1 + 1)) (Ri R)),
      (∀ Q ∈ Qs, ∃ dd : Fin 1 → ℕ, IsMultihomogeneous Q dd) ∧
      (fun x : (i : Fin 2) → complexProjectiveSpace R (k i) => (fun _ : Fin 1 => x 1)) ''
          projZerOfFinset Ps
        = projZerOfFinset (k := fun _ : Fin 1 => k 1) Qs := by
  classical
  haveI : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  haveI : CharZero R := inferInstance
  haveI : CharZero (Ri R) := charZero_of_injective_algebraMap (algebraMap R (Ri R)).injective
  -- index the finite family `Ps`
  set s := Ps.card with hs
  set enum : Fin s ≃ Ps := Ps.equivFin.symm with henum
  -- the split family and its multidegrees
  set p : Fin s → MvPolynomial (Fin (k 0 + 1)) (MvPolynomial (Fin (k 1 + 1)) (Ri R)) :=
    fun i => split k (enum i).1 with hp
  -- multidegrees of each member
  have hmh : ∀ i, ∃ dd : Fin 2 → ℕ, IsMultihomogeneous (enum i).1 dd := fun i =>
    hPs (enum i).1 (enum i).2
  choose dd hdd using hmh
  -- block-0 homogeneity
  have hpd : ∀ i, (p i).IsHomogeneous (dd i 0) := fun i => split_isHomogeneous (hdd i)
  -- block-1 homogeneity of coefficients
  have hpe : ∀ i γ, ((p i).coeff γ).IsHomogeneous (dd i 1) := fun i γ =>
    coeff_split_isHomogeneous (hdd i) γ
  -- apply the elimination core
  obtain ⟨coreQs, hcoreHom, hcoreSpec⟩ :=
    Elimination.elimination (C := Ri R) (k₁ := k 0) (k₂ := k 1) (s := s)
      (fun i => dd i 0) p hpd (fun i => dd i 1) hpe
  -- rename the core output to single-block form
  refine ⟨coreQs.image (rename (e1 (k 1))), ?_, ?_⟩
  · -- multihomogeneity of each renamed minor
    intro Q hQ
    rw [Finset.mem_image] at hQ
    obtain ⟨Q₀, hQ₀mem, rfl⟩ := hQ
    obtain ⟨m, hm⟩ := hcoreHom Q₀ hQ₀mem
    exact ⟨fun _ => m, rename_e1_isMultihomogeneous hm⟩
  · -- the set equality
    ext y
    simp only [Set.mem_image, projZerOfFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxvan, rfl⟩
      intro Q hQ
      rw [Finset.mem_image] at hQ
      obtain ⟨Q₀, hQ₀mem, rfl⟩ := hQ
      rw [projVanishes_rename_e1]
      -- the core spec at `y₁ = (x 1).rep`: a common nonzero zero exists (namely `(x 0).rep`)
      have hexists : ∃ z : Fin (k 0 + 1) → Ri R, z ≠ 0 ∧
          ∀ i, eval z (map (eval (x 1).rep) (p i)) = 0 := by
        refine ⟨(x 0).rep, (x 0).rep_nonzero, fun i => ?_⟩
        have := hxvan (enum i).1 (enum i).2
        rw [projVanishes_iff_eval_split] at this
        exact this
      exact (hcoreSpec (x 1).rep).mpr hexists Q₀ hQ₀mem
    · intro hyvan
      -- from the renamed vanishing, each core minor vanishes at `(y 0).rep`
      have hcore0 : ∀ Q₀ ∈ coreQs, eval (y 0).rep Q₀ = 0 := by
        intro Q₀ hQ₀mem
        have := hyvan (rename (e1 (k 1)) Q₀) (Finset.mem_image_of_mem _ hQ₀mem)
        rwa [projVanishes_rename_e1] at this
      -- the core spec produces a common nonzero zero `z`
      obtain ⟨z, hz, hzvan⟩ := (hcoreSpec (y 0).rep).mp hcore0
      -- translate `∀ i` to `∀ P ∈ Ps`
      have hzvan' : ∀ P ∈ Ps, eval z (map (eval (y 0).rep) (split k P)) = 0 := by
        intro P hP
        have hi := hzvan (enum.symm ⟨P, hP⟩)
        rw [hp] at hi
        simp only [Equiv.apply_symm_apply] at hi
        exact hi
      -- promote `z` to a line `x₀` via rep-independence
      obtain ⟨x₀, hx₀⟩ := (exists_line_iff_exists_nonzero Ps hPs (y 0)).mpr ⟨z, hz, hzvan'⟩
      -- assemble the preimage point `x = (x₀, y 0)`
      refine ⟨blockVecPt k x₀ (y 0), fun P hP => ?_, ?_⟩
      · rw [projVanishes_iff_eval_split, blockVecPt_zero, blockVecPt_one]
        exact hx₀ P hP
      · funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [blockVecPt_one]

/-- **BPR Theorem 4.103 (a weak Bézout theorem).** If `V ⊆ ℙ_{k₀}(C) × ℙ_{k₁}(C)` is algebraic, then
its projection onto the second factor `ℙ_{k₁}(C)` is algebraic. -/
theorem theorem_4_103 {k : Fin 2 → ℕ}
    (V : Set ((i : Fin 2) → complexProjectiveSpace R (k i))) (hV : IsAlgebraicSet V) :
    IsAlgebraicSet (k := fun _ : Fin 1 => k 1)
      ((fun x : (i : Fin 2) → complexProjectiveSpace R (k i) => fun _ : Fin 1 => x 1) '' V) := by
  obtain ⟨Ps, hPs, rfl⟩ := hV
  exact projection_isAlgebraic Ps hPs

end Azurite.BPR.Chapter4

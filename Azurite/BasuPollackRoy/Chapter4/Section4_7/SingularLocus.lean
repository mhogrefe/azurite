import Azurite.BasuPollackRoy.Chapter4.Section4_7.HomotopyFamily
import Azurite.BasuPollackRoy.Chapter4.Section4_7.JacobianRank
import Azurite.BasuPollackRoy.Chapter4.Section4_7.Theorem_4_103

/-!
# BPR §4.7, Proposition 4.106: the singular locus of the homotopy system is algebraic

For the homotopy system `S_{(λ:µ)} = (H_{1,λ,µ}, …, H_{k,λ,µ})` with `H_{i,λ,µ} = λ Pᵢ + µ Dᵢ`, the
set of pairs `(x, (λ:µ)) ∈ ℙ_k(C) × ℙ_1(C)` such that `x` is a *singular* projective zero of
`S_{(λ:µ)}` (a common zero whose projective Jacobian has rank `< k`) is an algebraic subset of the
product `ℙ_k(C) × ℙ_1(C)`. By Theorem 4.103 its projection `Δ` onto `ℙ_1(C)` (the discriminant
locus of the pencil) is therefore algebraic.

We model the product over the two-block index `kk = ![k, 1]` (block `0` = `ℙ_k(C)`, block `1` =
`ℙ_1(C)` carrying the pencil coordinates `λ = X⟨1,0⟩`, `µ = X⟨1,1⟩`). To avoid working with `pderiv`
inside the sigma ring, the Jacobian *entries* are encoded directly as multihomogeneous polynomials
`entryPoly` whose block-0 partials of `P` and `D` are renamed in, and the singular condition is the
simultaneous vanishing of the homotopy polynomials and of all maximal minors of the entry matrix.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

namespace SingularLocus

/-- The two-block multidegree index: block `0` is `ℙ_k(C)`, block `1` is `ℙ_1(C)`. -/
abbrev kk (k : ℕ) : Fin 2 → ℕ := ![k, 1]

/-- The sigma variable index for the two-block product `ℙ_k(C) × ℙ_1(C)`. -/
abbrev Sig (k : ℕ) : Type := (i : Fin 2) × Fin (kk k i + 1)

/-- The block-`0` variable embedding `Fin (k+1) → Sig`, `j ↦ ⟨0, j⟩`. -/
def emb0 (k : ℕ) : Fin (k + 1) → Sig k := fun j => ⟨0, j⟩

theorem emb0_injective (k : ℕ) : Function.Injective (emb0 k) := by
  intro a b h
  simpa [emb0] using (Sigma.mk.inj_iff.mp h).2

/-- The common-zero polynomial `H_{i,λ,µ} = λ Pᵢ + µ Dᵢ` lifted into the sigma ring. -/
noncomputable def Hpoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin k) : MvPolynomial (Sig k) (Ri R) :=
  X (⟨1, 0⟩ : Sig k) * rename (emb0 k) (P i)
    + X (⟨1, 1⟩ : Sig k) * rename (emb0 k) (diagFactor (d i) i)

/-- The `(i, j)` Jacobian entry polynomial `λ ∂Pᵢ/∂Xⱼ + µ ∂Dᵢ/∂Xⱼ` lifted into the sigma ring. -/
noncomputable def entryPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i : Fin k) (j : Fin (k + 1)) : MvPolynomial (Sig k) (Ri R) :=
  X (⟨1, 0⟩ : Sig k) * rename (emb0 k) (pderiv j (P i))
    + X (⟨1, 1⟩ : Sig k) * rename (emb0 k) (pderiv j (diagFactor (d i) i))

/-- The maximal minor obtained by deleting block-`0` column `c` from the entry matrix. -/
noncomputable def minorPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (c : Fin (k + 1)) : MvPolynomial (Sig k) (Ri R) :=
  (Matrix.of fun i a : Fin k => entryPoly P d i (c.succAbove a)).det

/-- The defining family of the singular locus: the homotopy polynomials together with all maximal
minors of the Jacobian entry matrix. -/
noncomputable def Ps (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ) :
    Finset (MvPolynomial (Sig k) (Ri R)) :=
  (Finset.univ.image (Hpoly P d)) ∪ (Finset.univ.image (fun c => minorPoly P d c))

/-! ### Generic multihomogeneity helpers (stated over an arbitrary block structure)

To keep elaboration from repeatedly unfolding `Sig k`/`kk` we state the multihomogeneity algebra
generically over an arbitrary block index `(i : Fin m) × Fin (κ i + 1)`. -/

section Generic

variable {A : Type*} [CommSemiring A] {m : ℕ} {κ : Fin m → ℕ}

theorem isMultihomogeneous_zero (d : Fin m → ℕ) :
    IsMultihomogeneous (0 : MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A) d := by
  intro i c hc
  simp [MvPolynomial.support_zero] at hc

theorem IsMultihomogeneous.of_support_subset
    {P Q : MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A} {d : Fin m → ℕ}
    (h : Q.support ⊆ P.support) (hP : IsMultihomogeneous P d) : IsMultihomogeneous Q d :=
  fun i c hc => hP i c (h hc)

theorem isMultihomogeneous_one :
    IsMultihomogeneous (1 : MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A) (fun _ : Fin m => 0) := by
  classical
  intro i c hc
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hc
  obtain rfl : (0 : (i : Fin m) × Fin (κ i + 1) →₀ ℕ) = c := by
    by_contra h; rw [if_neg h] at hc; exact hc rfl
  simp

theorem IsMultihomogeneous.sum {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A) (d : Fin m → ℕ)
    (h : ∀ i ∈ s, IsMultihomogeneous (f i) d) :
    IsMultihomogeneous (∑ i ∈ s, f i) d := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isMultihomogeneous_zero d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsMultihomogeneous.prod {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial ((i : Fin m) × Fin (κ i + 1)) A) (D : ι → (Fin m → ℕ))
    (h : ∀ i ∈ s, IsMultihomogeneous (f i) (D i)) :
    IsMultihomogeneous (∏ i ∈ s, f i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact isMultihomogeneous_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The determinant of a matrix of multihomogeneous entries, with the multidegree constant along
each row, is multihomogeneous of the summed multidegree. -/
theorem isMultihomogeneous_det {B : Type*} [CommRing B] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) (MvPolynomial ((i : Fin m) × Fin (κ i + 1)) B))
    (D : Fin n → (Fin m → ℕ)) (hN : ∀ i a, IsMultihomogeneous (N i a) (D i)) :
    IsMultihomogeneous N.det (∑ i, D i) := by
  classical
  rw [Matrix.det_apply']
  apply IsMultihomogeneous.sum
  intro σ _
  -- the product `∏ i, N (σ i) i` is multihomog of `∑ i, D (σ i) = ∑ i, D i`
  have hprod : IsMultihomogeneous (∏ i, N (σ i) i) (∑ i, D (σ i)) :=
    IsMultihomogeneous.prod Finset.univ (fun i => N (σ i) i) (fun i => D (σ i))
      (fun i _ => hN (σ i) i)
  have hsum : (∑ i, D (σ i)) = ∑ i, D i := Equiv.sum_comp σ D
  rw [hsum] at hprod
  -- multiplying by the sign constant only shrinks support
  refine IsMultihomogeneous.of_support_subset (fun c hc => ?_) hprod
  have hsign : (↑↑(Equiv.Perm.sign σ) : MvPolynomial ((i : Fin m) × Fin (κ i + 1)) B)
      = C (↑↑(Equiv.Perm.sign σ) : B) :=
    (map_intCast (C : B →+* MvPolynomial ((i : Fin m) × Fin (κ i + 1)) B) _).symm
  rw [MvPolynomial.mem_support_iff] at hc ⊢
  rw [hsign, MvPolynomial.coeff_C_mul] at hc
  exact fun h0 => hc (by rw [h0, mul_zero])

end Generic

set_option linter.unusedSectionVars false in
/-- Renaming a homogeneous polynomial of degree `n` along `emb0` yields a multihomogeneous
polynomial of multidegree `![n, 0]`. -/
theorem rename_emb0_isMultihomogeneous {n : ℕ} {Q : MvPolynomial (Fin (k + 1)) (Ri R)}
    (hQ : Q.IsHomogeneous n) :
    IsMultihomogeneous (rename (emb0 k) Q) (![n, 0]) := by
  classical
  intro i c hc
  rw [MvPolynomial.support_rename_of_injective (emb0_injective k)] at hc
  obtain ⟨c', hc'mem, rfl⟩ := Finset.mem_image.mp hc
  have hdeg : (Finsupp.weight 1) c' = n := hQ (MvPolynomial.mem_support_iff.mp hc'mem)
  rw [Finsupp.weight_apply] at hdeg
  simp only [smul_eq_mul, mul_one, Pi.one_apply] at hdeg
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdeg
  fin_cases i
  · -- block 0
    show ∑ j : Fin (k + 1), Finsupp.mapDomain (emb0 k) c' ⟨0, j⟩ = n
    rw [show (∑ j : Fin (k + 1), Finsupp.mapDomain (emb0 k) c' ⟨0, j⟩) = ∑ j : Fin (k + 1), c' j from
      Finset.sum_congr rfl fun j _ => by
        rw [show (⟨0, j⟩ : Sig k) = emb0 k j from rfl,
          Finsupp.mapDomain_apply (emb0_injective k)]]
    exact hdeg
  · -- block 1
    show ∑ j : Fin (1 + 1), Finsupp.mapDomain (emb0 k) c' ⟨1, j⟩ = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨a, ha⟩
    simp [emb0] at ha

/-! ### Multihomogeneity of the defining polynomials -/

set_option linter.unusedSectionVars false in
theorem Hpoly_isMultihomogeneous (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (i : Fin k) :
    IsMultihomogeneous (Hpoly P d i) (![d i, 1]) := by
  rw [Hpoly]
  apply IsMultihomogeneous.add
  · have hX : IsMultihomogeneous (X (⟨1, 0⟩ : Sig k) : MvPolynomial (Sig k) (Ri R)) (![0, 1]) := by
      have := isMultihomogeneous_X (A := Ri R) (⟨1, 0⟩ : Sig k)
      convert this using 1
      funext i; fin_cases i <;> simp
    have := hX.mul (rename_emb0_isMultihomogeneous (hP i))
    convert this using 1
    funext i; fin_cases i <;> simp
  · have hX : IsMultihomogeneous (X (⟨1, 1⟩ : Sig k) : MvPolynomial (Sig k) (Ri R)) (![0, 1]) := by
      have := isMultihomogeneous_X (A := Ri R) (⟨1, 1⟩ : Sig k)
      convert this using 1
      funext i; fin_cases i <;> simp
    have := hX.mul (rename_emb0_isMultihomogeneous (diagFactor_isHomogeneous (d i) i))
    convert this using 1
    funext i; fin_cases i <;> simp

set_option linter.unusedSectionVars false in
theorem entryPoly_isMultihomogeneous (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (i : Fin k) (j : Fin (k + 1)) :
    IsMultihomogeneous (entryPoly P d i j) (![d i - 1, 1]) := by
  rw [entryPoly]
  apply IsMultihomogeneous.add
  · have hX : IsMultihomogeneous (X (⟨1, 0⟩ : Sig k) : MvPolynomial (Sig k) (Ri R)) (![0, 1]) := by
      have := isMultihomogeneous_X (A := Ri R) (⟨1, 0⟩ : Sig k)
      convert this using 1
      funext i; fin_cases i <;> simp
    have := hX.mul (rename_emb0_isMultihomogeneous ((hP i).pderiv (i := j)))
    convert this using 1
    funext i; fin_cases i <;> simp
  · have hX : IsMultihomogeneous (X (⟨1, 1⟩ : Sig k) : MvPolynomial (Sig k) (Ri R)) (![0, 1]) := by
      have := isMultihomogeneous_X (A := Ri R) (⟨1, 1⟩ : Sig k)
      convert this using 1
      funext i; fin_cases i <;> simp
    have := hX.mul (rename_emb0_isMultihomogeneous ((diagFactor_isHomogeneous (d i) i).pderiv (i := j)))
    convert this using 1
    funext i; fin_cases i <;> simp

set_option linter.unusedSectionVars false in
theorem minorPoly_isMultihomogeneous (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (c : Fin (k + 1)) :
    IsMultihomogeneous (minorPoly P d c) (∑ i, (![d i - 1, 1] : Fin 2 → ℕ)) := by
  rw [minorPoly]
  apply isMultihomogeneous_det
  intro i a
  simp only [Matrix.of_apply]
  exact entryPoly_isMultihomogeneous P d hP i (c.succAbove a)

/-! ### Evaluation bridges -/

set_option linter.unusedSectionVars false in
/-- Evaluating a renamed block-`0` polynomial at a sigma assignment reduces to evaluating the
original at the block-`0` representative. -/
theorem eval_rename_emb0 (xp : (i : Fin 2) → complexProjectiveSpace R (kk k i))
    (Q : MvPolynomial (Fin (k + 1)) (Ri R)) :
    eval (fun s : Sig k => (xp s.1).rep s.2) (rename (emb0 k) Q)
      = eval (xp 0).rep Q := by
  rw [eval_rename]
  rfl

set_option linter.unusedSectionVars false in
theorem aeval_eq_eval (x : Fin (k + 1) → Ri R) (Q : MvPolynomial (Fin (k + 1)) (Ri R)) :
    aeval x Q = eval x Q :=
  DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval x) Q

set_option linter.unusedSectionVars false in
theorem evalCoords_Hpoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (xp : (i : Fin 2) → complexProjectiveSpace R (kk k i)) (i : Fin k) :
    evalCoords (Hpoly P d i) (fun i => (xp i).rep)
      = aeval (xp 0).rep (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i) := by
  rw [evalCoords, Hpoly, homotopyPoly]
  rw [aeval_eq_eval]
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  rw [eval_rename_emb0, eval_rename_emb0, eval_C, eval_C,
    show eval (fun s : Sig k => (xp s.1).rep s.2) (X (⟨1, 0⟩ : Sig k)) = (xp 1).rep 0 from
      eval_X _, show eval (fun s : Sig k => (xp s.1).rep s.2) (X (⟨1, 1⟩ : Sig k)) = (xp 1).rep 1 from
      eval_X _]
  rfl

set_option linter.unusedSectionVars false in
theorem evalCoords_entryPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (xp : (i : Fin 2) → complexProjectiveSpace R (kk k i)) (i : Fin k) (j : Fin (k + 1)) :
    evalCoords (entryPoly P d i j) (fun i => (xp i).rep)
      = (projJacobian (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1)) (xp 0)) i j := by
  have hpderiv : pderiv j (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i)
      = C ((xp 1).rep 0) * pderiv j (P i)
        + C ((xp 1).rep 1) * pderiv j (diagFactor (d i) i) := by
    rw [homotopyPoly, map_add, pderiv_C_mul, pderiv_C_mul]
  rw [evalCoords, entryPoly, projJacobian, Matrix.of_apply, hpderiv, aeval_eq_eval]
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul]
  rw [eval_rename_emb0, eval_rename_emb0, eval_C, eval_C,
    show eval (fun s : Sig k => (xp s.1).rep s.2) (X (⟨1, 0⟩ : Sig k)) = (xp 1).rep 0 from
      eval_X _, show eval (fun s : Sig k => (xp s.1).rep s.2) (X (⟨1, 1⟩ : Sig k)) = (xp 1).rep 1 from
      eval_X _]
  rfl

set_option linter.unusedSectionVars false in
theorem evalCoords_minorPoly (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (xp : (i : Fin 2) → complexProjectiveSpace R (kk k i)) (c : Fin (k + 1)) :
    evalCoords (minorPoly P d c) (fun i => (xp i).rep)
      = ((projJacobian (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1)) (xp 0)).submatrix
          id c.succAbove).det := by
  rw [evalCoords, minorPoly]
  rw [RingHom.map_det (eval (fun s : Sig k => (xp s.1).rep s.2))]
  congr 1
  ext i a
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply,
    id_eq]
  have := evalCoords_entryPoly P d xp i (c.succAbove a)
  rw [evalCoords] at this
  exact this

end SingularLocus

open SingularLocus

/-- **BPR Proposition 4.106 (the singular locus).** The set of pairs `(x, (λ:µ)) ∈ ℙ_k(C) × ℙ_1(C)`
such that `x` is a *singular* projective zero of the homotopy system `S_{(λ:µ)}` (a common zero whose
projective Jacobian has rank `< k`). -/
def singularLocus (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ) :
    Set ((i : Fin 2) → complexProjectiveSpace R ((![k, 1] : Fin 2 → ℕ) i)) :=
  {xp | (∀ i, aeval (xp 0).rep (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i) = 0)
        ∧ (projJacobian (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1)) (xp 0)).rank < k}

theorem singularLocus_eq_projZerOfFinset (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    singularLocus P d = projZerOfFinset (Ps P d) := by
  ext xp
  simp only [singularLocus, Set.mem_setOf_eq, projZerOfFinset, Ps]
  constructor
  · rintro ⟨hzero, hrank⟩ Q hQ
    rw [Finset.mem_union] at hQ
    rcases hQ with hQ | hQ
    · -- `Q` is a homotopy polynomial
      rw [Finset.mem_image] at hQ
      obtain ⟨i, _, rfl⟩ := hQ
      rw [ProjVanishes, evalCoords_Hpoly]
      exact hzero i
    · -- `Q` is a maximal minor
      rw [Finset.mem_image] at hQ
      obtain ⟨c, _, rfl⟩ := hQ
      rw [ProjVanishes, evalCoords_minorPoly]
      have hP' : ∀ i, (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i).IsHomogeneous (d i) :=
        fun i => homotopyPoly_isHomogeneous P d hP _ _ i
      have hx : ∀ i, aeval (xp 0).rep (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i) = 0 := hzero
      exact (projJacobian_rank_lt_iff_forall_det_eq_zero hP' hx).mp hrank c
  · intro h
    have hP' : ∀ i, (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i).IsHomogeneous (d i) :=
      fun i => homotopyPoly_isHomogeneous P d hP _ _ i
    have hzero : ∀ i, aeval (xp 0).rep (homotopyPoly P d ((xp 1).rep 0) ((xp 1).rep 1) i) = 0 := by
      intro i
      have := h (Hpoly P d i)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      rwa [ProjVanishes, evalCoords_Hpoly] at this
    refine ⟨hzero, ?_⟩
    rw [projJacobian_rank_lt_iff_forall_det_eq_zero hP' hzero]
    intro c
    have := h (minorPoly P d c)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩))
    rwa [ProjVanishes, evalCoords_minorPoly] at this

/-- **BPR Proposition 4.106.** The singular locus of the homotopy system is an algebraic subset of
`ℙ_k(C) × ℙ_1(C)`. -/
theorem singularLocus_isAlgebraic (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    IsAlgebraicSet (singularLocus P d) := by
  refine ⟨Ps P d, ?_, singularLocus_eq_projZerOfFinset P d hP⟩
  intro Q hQ
  rw [Ps, Finset.mem_union] at hQ
  rcases hQ with hQ | hQ
  · rw [Finset.mem_image] at hQ
    obtain ⟨i, _, rfl⟩ := hQ
    exact ⟨_, Hpoly_isMultihomogeneous P d hP i⟩
  · rw [Finset.mem_image] at hQ
    obtain ⟨c, _, rfl⟩ := hQ
    exact ⟨_, minorPoly_isMultihomogeneous P d hP c⟩

/-- **BPR Proposition 4.106 (the discriminant locus `Δ`).** The projection of the singular locus
onto the pencil factor `ℙ_1(C)` is algebraic. -/
theorem delta_isAlgebraic (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    IsAlgebraicSet (k := fun _ : Fin 1 => (1 : ℕ))
      ((fun xp : (i : Fin 2) → complexProjectiveSpace R ((![k, 1] : Fin 2 → ℕ) i) =>
        fun _ : Fin 1 => xp 1) '' singularLocus P d) :=
  theorem_4_103 (k := ![k, 1]) (singularLocus P d) (singularLocus_isAlgebraic P d hP)

end Azurite.BPR.Chapter4

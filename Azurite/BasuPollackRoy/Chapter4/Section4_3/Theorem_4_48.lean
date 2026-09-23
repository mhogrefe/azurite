import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_47
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_10

/-!
# BPR Theorem 4.48: `sDisc_k(M)` is a sum of squares of minors

For a symmetric matrix `M`, the `k`-th subdiscriminant `sDisc_k(M)` is the sum of the
squares of the `(p−k) × (p−k)` minors of `A_k`. This is immediate from
Proposition 4.47 (`Newt_k(M) = A_k A_kᵀ`) and the Cauchy–Binet formula
(Proposition 4.10): `det(A_k A_kᵀ) = ∑_I (det A_k[·,I])²`, the sum over `(p−k)`-element
column subsets `I`.

The columns of `A_k` are indexed by the basis `E` (`STri p`); to enumerate the minors
we reindex them by `Fin (card (STri p)) = Fin (p(p+1)/2)` via `AkFin` (the same matrix,
columns ordered), so the minors of `AkFin` are exactly those of `A_k`.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open Matrix Finset

section

variable {p : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- `A_k` with its `p(p+1)/2` columns enumerated by `Fin (card (STri p))` (an arbitrary
ordering of the basis `E`); the `(p−k) × (p−k)` minors are unchanged. -/
noncomputable def AkFin (k : ℕ) (M : Matrix (Fin p) (Fin p) R) :
    Matrix (Fin (p - k)) (Fin (Fintype.card (STri p))) R :=
  (Ak k M).submatrix id (Fintype.equivFin (STri p)).symm

/-- **Theorem 4.48.** `sDisc_k(M)` is the sum of the squares of the `(p−k) × (p−k)`
minors of `A_k`. -/
theorem theorem_4_48 (k : ℕ) (M : Matrix (Fin p) (Fin p) R) (hM : M.IsSymm) :
    sDiscOfMatrix k M =
      ∑ I ∈ (Finset.univ : Finset (Fin (Fintype.card (STri p)))).powersetCard (p - k),
        if h : I.card = p - k then
          ((AkFin k M).submatrix id (I.orderEmbOfFin h)).det ^ 2
        else 0 := by
  classical
  -- Step 1: reduce `sDisc_k(M)` to `det (AkFin · AkFinᵀ)`.
  have hAk : Ak k M * (Ak k M)ᵀ = AkFin k M * (AkFin k M)ᵀ := by
    set e := Fintype.equivFin (STri p)
    have ht : (AkFin k M)ᵀ = (Ak k M)ᵀ.submatrix e.symm id := by
      rw [AkFin, Matrix.transpose_submatrix]
    rw [ht, AkFin, Matrix.submatrix_mul_equiv (Ak k M) ((Ak k M)ᵀ) id e.symm id,
      Matrix.submatrix_id_id]
  have hreduce : sDiscOfMatrix k M = (AkFin k M * (AkFin k M)ᵀ).det := by
    rw [sDiscOfMatrix, proposition_4_47 k M hM, hAk]
  rw [hreduce]
  -- Step 2: Cauchy–Binet.
  rw [proposition_4_10 (AkFin k M) ((AkFin k M)ᵀ)]
  -- Step 3: each product is a square.
  refine Finset.sum_congr rfl ?_
  intro I hI
  by_cases h : I.card = p - k
  · rw [dite_eq_left h, dite_eq_left h]
    have htr : ((AkFin k M)ᵀ.submatrix (I.orderEmbOfFin h) id).det =
        ((AkFin k M).submatrix id (I.orderEmbOfFin h)).det := by
      rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    rw [htr, sq]
  · rw [dite_eq_right h, dite_eq_right h]

end

/-! ### Explicit expression over `ℤ[m_{j,ℓ}]`: sum of powers of 2 times squares

The minor of `A_k` over a column set `J` carries a factor `√2` for each off-diagonal
column, so its square is `2^(#off-diagonal columns)` times the square of the
corresponding *rationalized* minor — a determinant of entries of powers of `M`, hence an
element of `ℤ[m_{j,ℓ}]`. We prove this directly over any commutative ring (so in
particular over `ℤ[m_{j,ℓ}]`, the generic symmetric matrix): the trace expansion
`Tr(M^a M^b) = ∑_q w_q (M^a)_q (M^b)_q` with `w_q ∈ {1,2}` gives
`Newt_k(M) = R · diag(w) · Rᵀ` for the rationalized matrix `R`, and weighted
Cauchy–Binet turns `det` into `∑_J (∏_{c∈J} w_c) (minor R[·,J])² = ∑_J 2^{d_J} (minor)²`.
-/

section PowersOfTwo

variable {p : ℕ} {D : Type*} [CommRing D]

/-- The **rationalized** `A_k`: the `(i, (j,ℓ))`-entry is the `(j,ℓ)`-entry of `M^{i-1}`
itself — the component of `M^{i-1}` along `E_{j,ℓ}` with the `√2` factor dropped, hence a
polynomial in the entries of `M` (an element of `ℤ[m_{j,ℓ}]` for the generic matrix). -/
def RAk (k : ℕ) (M : Matrix (Fin p) (Fin p) D) : Matrix (Fin (p - k)) (STri p) D :=
  Matrix.of fun i q => (M ^ (i : ℕ)) q.val.1 q.val.2

/-- `RAk` with columns enumerated by `Fin (card (STri p))`. -/
noncomputable def RAkFin (k : ℕ) (M : Matrix (Fin p) (Fin p) D) :
    Matrix (Fin (p - k)) (Fin (Fintype.card (STri p))) D :=
  (RAk k M).submatrix id (Fintype.equivFin (STri p)).symm

/-- The number of off-diagonal columns (`j ≠ ℓ`) in a set `J` of column indices; the
exponent of `2` attached to the corresponding rationalized minor. -/
noncomputable def offDiagCard (J : Finset (Fin (Fintype.card (STri p)))) : ℕ :=
  (J.filter fun c => ((Fintype.equivFin (STri p)).symm c).val.1
    ≠ ((Fintype.equivFin (STri p)).symm c).val.2).card

/-- The column weight: `1` on diagonal columns, `2` on off-diagonal columns. -/
private noncomputable def wtF : Fin (Fintype.card (STri p)) → D :=
  fun c => if ((Fintype.equivFin (STri p)).symm c).val.1
      = ((Fintype.equivFin (STri p)).symm c).val.2 then 1 else 2

/-- Combinatorial identity: a symmetric double sum over `Fin p × Fin p` collapses to a
weighted sum over the upper-triangular index set `STri p`. -/
private lemma sum_prod_eq_sum_STri (g : Fin p → Fin p → D) (hg : ∀ x y, g x y = g y x) :
    (∑ xy : Fin p × Fin p, g xy.1 xy.2) =
      ∑ q : STri p, (if q.val.1 = q.val.2 then (1 : D) else 2) * g q.val.1 q.val.2 := by
  classical
  -- LHS splits into the `x ≤ y` and `¬ x ≤ y` parts.
  have hLHS : (∑ xy : Fin p × Fin p, g xy.1 xy.2) =
      (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => xy.1 ≤ xy.2), g xy.1 xy.2) +
        (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => ¬ xy.1 ≤ xy.2), g xy.1 xy.2) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun xy : Fin p × Fin p => xy.1 ≤ xy.2)
      (fun xy => g xy.1 xy.2)).symm
  -- The `¬ x ≤ y` part reindexes (via swap, using symmetry of `g`) to the `x < y` part.
  have hswap : (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => ¬ xy.1 ≤ xy.2),
        g xy.1 xy.2) =
      (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => xy.1 < xy.2), g xy.1 xy.2) := by
    refine Finset.sum_nbij' (fun xy => (xy.2, xy.1)) (fun xy => (xy.2, xy.1)) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at *; exact ha
    · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at *; exact ha
    · intro a _; rfl
    · intro a _; rfl
    · intro a _; exact hg a.1 a.2
  -- RHS: convert the subtype sum to a filter sum over `x ≤ y`, then split the `if`.
  rw [← Finset.sum_subtype (Finset.univ.filter (fun xy : Fin p × Fin p => xy.1 ≤ xy.2))
    (fun x => by simp) (fun xy => (if xy.1 = xy.2 then (1 : D) else 2) * g xy.1 xy.2)]
  have key : (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => xy.1 ≤ xy.2),
        (if xy.1 = xy.2 then (1 : D) else 2) * g xy.1 xy.2) =
      (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => xy.1 ≤ xy.2), g xy.1 xy.2) +
        (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => xy.1 ≤ xy.2),
          (if xy.1 < xy.2 then g xy.1 xy.2 else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun xy hxy => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    rcases eq_or_lt_of_le hxy with h | h
    · simp [h]
    · simp [ne_of_lt h, h]; ring
  have key2 : (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => xy.1 ≤ xy.2),
        (if xy.1 < xy.2 then g xy.1 xy.2 else 0)) =
      (∑ xy ∈ Finset.univ.filter (fun xy : Fin p × Fin p => xy.1 < xy.2), g xy.1 xy.2) := by
    rw [← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro xy _
    simp [lt_iff_le_and_ne]
  rw [hLHS, hswap, key, key2]

/-- Trace expansion for a product of two symmetric matrices. -/
private lemma trace_expansion (A B : Matrix (Fin p) (Fin p) D) (hA : A.IsSymm)
    (hB : B.IsSymm) :
    (A * B).trace =
      ∑ q : STri p,
        (if q.val.1 = q.val.2 then (1 : D) else 2) * (A q.val.1 q.val.2 * B q.val.1 q.val.2) := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [← Fintype.sum_prod_type (fun xy : Fin p × Fin p => A xy.1 xy.2 * B xy.2 xy.1)]
  rw [← sum_prod_eq_sum_STri (fun x y => A x y * B x y)
    (fun x y => by rw [hA.apply, hB.apply])]
  refine Finset.sum_congr rfl (fun xy _ => ?_)
  rw [hB.apply xy.2 xy.1]

/-- Matrix factorization: `Newt_k(M) = RAk · diag(w) · RAkᵀ`. -/
private lemma traceNewt_eq (k : ℕ) (M : Matrix (Fin p) (Fin p) D) (hM : M.IsSymm) :
    traceNewtMatrix k M = RAkFin k M * Matrix.diagonal wtF * (RAkFin k M)ᵀ := by
  classical
  set e := Fintype.equivFin (STri p) with he
  ext i i'
  -- LHS: `Tr(M^{i+i'}) = Tr(M^i M^i')`, then the trace expansion over `STri p`.
  rw [traceNewtMatrix, Matrix.of_apply, pow_add,
    trace_expansion (M ^ (i : ℕ)) (M ^ (i' : ℕ)) (hM.pow _) (hM.pow _)]
  -- Reindex the `STri p` sum by `e` to a sum over `Fin (card (STri p))`.
  rw [← Equiv.sum_comp e.symm
    (fun q : STri p => (if q.val.1 = q.val.2 then (1 : D) else 2) *
      ((M ^ (i : ℕ)) q.val.1 q.val.2 * (M ^ (i' : ℕ)) q.val.1 q.val.2))]
  -- RHS: expand the matrix product entrywise.
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, RAkFin, RAk, Matrix.submatrix_apply,
    Matrix.of_apply, id_eq, wtF, ← he]
  ring

/-- **Subdiscriminant as a sum of products of powers of 2 by squares.** Over any
commutative ring (in particular `ℤ[m_{j,ℓ}]`), `sDisc_k(M)` of a symmetric `M` is the sum
over `(p−k)`-element column sets `J` of `2^{d_J}` times the square of the corresponding
`(p−k) × (p−k)` minor of the rationalized matrix `RAk`, where `d_J` is the number of
off-diagonal columns in `J`. -/
theorem sDiscOfMatrix_eq_sum_pow_two_mul_sq (k : ℕ) (M : Matrix (Fin p) (Fin p) D)
    (hM : M.IsSymm) :
    sDiscOfMatrix k M =
      ∑ J ∈ (Finset.univ : Finset (Fin (Fintype.card (STri p)))).powersetCard (p - k),
        if h : J.card = p - k then
          2 ^ offDiagCard J * ((RAkFin k M).submatrix id (J.orderEmbOfFin h)).det ^ 2
        else 0 := by
  classical
  rw [sDiscOfMatrix, traceNewt_eq k M hM,
    proposition_4_10 (RAkFin k M * Matrix.diagonal wtF) ((RAkFin k M)ᵀ)]
  refine Finset.sum_congr rfl (fun J hJ => ?_)
  by_cases h : J.card = p - k
  · rw [dite_eq_left h, dite_eq_left h]
    set f := J.orderEmbOfFin h with hf
    -- Transpose factor equals the minor of `RAkFin`.
    have htr : ((RAkFin k M)ᵀ.submatrix (⇑f) id).det
        = ((RAkFin k M).submatrix id (⇑f)).det := by
      rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    -- The `diag wtF` factor pulls out of the submatrix as a column-rescaling diagonal.
    have hfac : (RAkFin k M * Matrix.diagonal wtF).submatrix id (⇑f)
        = (RAkFin k M).submatrix id (⇑f) * Matrix.diagonal (wtF ∘ f) := by
      ext a b
      simp [Matrix.submatrix_apply, Matrix.mul_diagonal]
    rw [htr, hfac, Matrix.det_mul, Matrix.det_diagonal]
    -- The product of column weights along `J` is `2 ^ offDiagCard J`.
    have hprod : (∏ j, (wtF ∘ f) j) = (2 : D) ^ offDiagCard J := by
      have : (∏ j, (wtF ∘ f) j) = ∏ c ∈ J, (wtF c : D) := by
        simp only [Function.comp_apply]
        rw [← Finset.prod_image (f := wtF) (g := (⇑f)) f.injective.injOn]
        congr 1
        rw [← Finset.coe_inj, Finset.coe_image, Finset.coe_univ, Set.image_univ]
        exact Finset.range_orderEmbOfFin J h
      rw [this, offDiagCard]
      -- Split the product over `J` by the *diagonal* predicate (works in any ring, even
      -- if `2 = 1`): diagonal columns contribute `1`, off-diagonal columns contribute `2`.
      rw [← Finset.prod_filter_mul_prod_filter_not J
        (fun c => ((Fintype.equivFin (STri p)).symm c).val.1
          = ((Fintype.equivFin (STri p)).symm c).val.2) wtF]
      -- Diagonal part: every factor is `1`.
      rw [Finset.prod_congr rfl (g := fun _ => (1 : D)) (fun c hc => ?_)]
      rotate_left
      · simp only [Finset.mem_filter] at hc
        simp only [wtF, ite_eq_left hc.2]
      rw [Finset.prod_const_one, one_mul]
      -- Off-diagonal part: every factor is `2`; the index set matches `offDiagCard`.
      rw [Finset.prod_congr rfl (g := fun _ => (2 : D)) (fun c hc => ?_)]
      rotate_left
      · simp only [Finset.mem_filter] at hc
        simp only [wtF, ite_eq_right hc.2]
      rw [Finset.prod_const]
    rw [hprod, sq]
    ring
  · rw [dite_eq_right h, dite_eq_right h]

/-- **Consequence.** Over any commutative ring `D`, the `k`-th subdiscriminant of the
characteristic polynomial of a symmetric matrix is a sum of products of powers of `2` by
squares of elements of `D`. -/
theorem sDiscOfMatrix_isSumOfPowTwoMulSq (k : ℕ) (M : Matrix (Fin p) (Fin p) D)
    (hM : M.IsSymm) :
    ∃ (n : ℕ) (a : Fin n → ℕ) (d : Fin n → D),
      sDiscOfMatrix k M = ∑ i, 2 ^ a i * d i ^ 2 := by
  classical
  rw [sDiscOfMatrix_eq_sum_pow_two_mul_sq k M hM]
  set S := (Finset.univ : Finset (Fin (Fintype.card (STri p)))).powersetCard (p - k) with hS
  set e := Fintype.equivFin (S : Type _) with he
  refine ⟨Fintype.card S,
    fun i => offDiagCard (e.symm i).1,
    fun i => ((RAkFin k M).submatrix id
      ((e.symm i).1.orderEmbOfFin (Finset.mem_powersetCard.mp (e.symm i).2).2)).det, ?_⟩
  rw [Equiv.sum_comp e.symm (fun x : S => 2 ^ offDiagCard x.1 *
    ((RAkFin k M).submatrix id
      (x.1.orderEmbOfFin (Finset.mem_powersetCard.mp x.2).2)).det ^ 2)]
  rw [← Finset.sum_attach S (fun J => if h : J.card = p - k then
    2 ^ offDiagCard J * ((RAkFin k M).submatrix id (J.orderEmbOfFin h)).det ^ 2 else 0)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [dite_eq_left (Finset.mem_powersetCard.mp x.2).2]

/-- **Example (2 × 2).** For a symmetric `2 × 2` matrix `!![a, b; b, c]`, the
subdiscriminant `sDisc₀` equals the sum of the squares of the `2 × 2` minors of
`A₀ = !![1, 1, 0; a, c, √2·b]`, namely `(c − a)² + (√2 b)² + (√2 b)²`. (This is also the
discriminant `(a + c)² − 4(ac − b²)` of the characteristic polynomial
`X² − (a + c) X + (ac − b²)` — see the `ring`-equal forms below — so it checks
Theorem 4.48 in this case.) -/
theorem sDiscOfMatrix_two_example (a b c : D) :
    sDiscOfMatrix 0 (!![a, b; b, c]) = (c - a) ^ 2 + 2 * b ^ 2 + 2 * b ^ 2 := by
  unfold sDiscOfMatrix traceNewtMatrix
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Fin.isValue]
  norm_num [pow_zero, pow_one, pow_two, Matrix.trace_fin_two, Matrix.trace_one,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

end PowersOfTwo

end Azurite.BPR.Chapter4

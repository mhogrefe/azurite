import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMatrixListProd
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# BPR §8.1: BPR-exact bound on coefficient bitsize of a matrix list product

For a list of matrices `M_1, …, M_m ∈ Matrix(ν, ν, ℤ[Y_1, …, Y_k])` with the
coefficients of `M_l (i, j)` bounded in bitsize by `τ_l` and the totalDegree of
`M_l (i, j)` bounded by `p_l`, every coefficient of any entry of the product
satisfies BPR's exact bitsize bound:

  `bit ≤ τ_1 + ⋯ + τ_m + k · (bit(p_1 + 1) + ⋯ + bit(p_m + 1)) + m · bit(n)`

where `n = Fintype.card ν`. The main theorem is
`Matrix.bitsize_coeff_mvList_prod_le_bpr_exact`.

The proof is by induction on `k`. The infrastructure built up in this file:

* `Matrix.polyCoeff` — `Polynomial.coeff d` applied entrywise to a matrix of
  polynomials.
* `Matrix.polyCoeff_mul` — binary matrix-polynomial coefficient convolution.
* `Matrix.polyCoeff_list_prod` — list-version of the above, indexed by
  `Finset.Nat.antidiagonalTuple`.
* `Matrix.map_list_prod` / `coeff_cons_of_mvList_prod` — ring-hom transport of
  a matrix list product, used to peel off the first variable via
  `MvPolynomial.finSuccEquiv`.
* `Matrix.bitsize_list_prod_per_matrix_le` — per-matrix bitsize bound for an
  integer matrix list product (the `k = 0` base case).

The inductive step `k → k+1` peels off the first variable via
`MvPolynomial.finSuccEquiv`, expands the resulting matrix-polynomial coefficient
via `Matrix.polyCoeff_list_prod`, applies the IH to each summand, and finally
bounds the cardinality of the relevant filtered `antidiagonalTuple` to absorb
the extra `k → k+1` summand.
-/

namespace Azurite.BPR

open Matrix MvPolynomial Polynomial Finset.Nat

/-! ## Matrix-polynomial coefficient (binary convolution) -/

section PolyCoeff

variable {ν : Type _} [Fintype ν] [DecidableEq ν] {R : Type _} [CommSemiring R]

/-- Apply `Polynomial.coeff d` entrywise to a matrix of polynomials. -/
def Matrix.polyCoeff (d : ℕ) (M : Matrix ν ν (Polynomial R)) : Matrix ν ν R :=
  M.map (fun p => p.coeff d)

omit [Fintype ν] [DecidableEq ν] in
@[simp]
theorem Matrix.polyCoeff_apply (d : ℕ) (M : Matrix ν ν (Polynomial R)) (i j : ν) :
    Matrix.polyCoeff d M i j = (M i j).coeff d := rfl

omit [DecidableEq ν] in
/-- Matrix-polynomial convolution at a single index. -/
theorem Matrix.polyCoeff_mul (d : ℕ) (M N : Matrix ν ν (Polynomial R)) :
    Matrix.polyCoeff d (M * N) =
      ∑ x ∈ Finset.antidiagonal d, Matrix.polyCoeff x.1 M * Matrix.polyCoeff x.2 N := by
  ext i j
  show ((M * N) i j).coeff d = _
  rw [Matrix.mul_apply, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_mul]
  rw [Finset.sum_comm, _root_.Matrix.sum_apply i j]
  apply Finset.sum_congr rfl
  intro x _
  show ∑ s, (M i s).coeff x.1 * (N s j).coeff x.2 =
       (Matrix.polyCoeff x.1 M * Matrix.polyCoeff x.2 N) i j
  rw [Matrix.mul_apply]
  rfl

end PolyCoeff

/-! ## List version of matrix-polynomial coefficient convolution -/

section PolyCoeffListProd

variable {ν : Type _} [Fintype ν] [DecidableEq ν] {R : Type _} [CommSemiring R]

/-- The list of matrix coefficient images `polyCoeff (ds l) (Ms.get l)` for each
    position in the list. -/
def Matrix.polyCoeffList (Ms : List (Matrix ν ν (Polynomial R)))
    (ds : Fin Ms.length → ℕ) : List (Matrix ν ν R) :=
  List.ofFn (fun l : Fin Ms.length => Matrix.polyCoeff (ds l) (Ms.get l))

omit [Fintype ν] [DecidableEq ν] in
@[simp]
theorem Matrix.polyCoeffList_nil :
    Matrix.polyCoeffList (R := R) (ν := ν) [] (fun _ => 0) = [] := by
  unfold Matrix.polyCoeffList; rfl

omit [Fintype ν] [DecidableEq ν] in
theorem Matrix.polyCoeffList_cons (M : Matrix ν ν (Polynomial R))
    (rest : List (Matrix ν ν (Polynomial R))) (ds : Fin (M :: rest).length → ℕ) :
    Matrix.polyCoeffList (M :: rest) ds =
      Matrix.polyCoeff (ds 0) M ::
        Matrix.polyCoeffList rest (fun l => ds l.succ) := by
  unfold Matrix.polyCoeffList
  rw [List.ofFn_succ]
  rfl

/-- The X^d-coefficient of a matrix-polynomial list product equals the sum,
    over tuples summing to `d`, of products of coefficient matrices. -/
theorem Matrix.polyCoeff_list_prod (d : ℕ)
    (Ms : List (Matrix ν ν (Polynomial R))) :
    Matrix.polyCoeff d Ms.prod =
      ∑ ds ∈ antidiagonalTuple Ms.length d,
        (Matrix.polyCoeffList Ms ds).prod := by
  induction Ms generalizing d with
  | nil =>
    rw [List.prod_nil]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      show Matrix.polyCoeff 0 (1 : Matrix ν ν (Polynomial R)) =
        ∑ ds ∈ antidiagonalTuple 0 0, (Matrix.polyCoeffList [] ds).prod
      rw [antidiagonalTuple_zero_zero, Finset.sum_singleton]
      ext i j
      show (1 : Matrix ν ν (Polynomial R)).map (fun p => p.coeff 0) i j =
           (Matrix.polyCoeffList [] ![]).prod i j
      rw [show Matrix.polyCoeffList ([] : List (Matrix ν ν (Polynomial R)))
              ![] = ([] : List (Matrix ν ν R)) from rfl, List.prod_nil]
      show (1 : Matrix ν ν (Polynomial R)).map (fun p => p.coeff 0) i j =
           (1 : Matrix ν ν R) i j
      rw [Matrix.one_apply, Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hd)
      show Matrix.polyCoeff d'.succ (1 : Matrix ν ν (Polynomial R)) =
        ∑ ds ∈ antidiagonalTuple 0 d'.succ, (Matrix.polyCoeffList [] ds).prod
      rw [antidiagonalTuple_zero_succ, Finset.sum_empty]
      ext i j
      show ((1 : Matrix ν ν (Polynomial R)).map (fun p => p.coeff d'.succ)) i j =
           (0 : Matrix ν ν R) i j
      rw [Matrix.zero_apply, Matrix.map_apply, Matrix.one_apply]
      split_ifs
      · show (1 : Polynomial R).coeff d'.succ = 0
        rw [Polynomial.coeff_one]; simp
      · show (0 : Polynomial R).coeff d'.succ = 0
        rw [Polynomial.coeff_zero]
  | cons M rest ih =>
    rw [List.prod_cons, Matrix.polyCoeff_mul]
    conv_lhs =>
      rw [show (∑ x ∈ Finset.antidiagonal d,
                Matrix.polyCoeff x.1 M * Matrix.polyCoeff x.2 rest.prod) =
              ∑ x ∈ Finset.antidiagonal d, Matrix.polyCoeff x.1 M *
                (∑ ds' ∈ antidiagonalTuple rest.length x.2,
                  (Matrix.polyCoeffList rest ds').prod) from by
            apply Finset.sum_congr rfl
            intro x _
            rw [ih x.2]]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sigma (Finset.antidiagonal d)
          (fun x : ℕ × ℕ => antidiagonalTuple rest.length x.2)
          (fun p => Matrix.polyCoeff p.1.1 M * (Matrix.polyCoeffList rest p.2).prod)]
    refine Finset.sum_bij'
      (i := fun p _ => Fin.cons p.1.1 p.2)
      (j := fun ds _ => ⟨(ds 0, ∑ l : Fin rest.length, ds l.succ), Fin.tail ds⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_sigma] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Finset.mem_antidiagonal] at hp1
      rw [mem_antidiagonalTuple] at hp2
      change Fin.cons p.1.1 p.2 ∈ antidiagonalTuple (rest.length + 1) d
      rw [mem_antidiagonalTuple, Fin.sum_cons]
      omega
    · intro ds hds
      change ds ∈ antidiagonalTuple (rest.length + 1) d at hds
      rw [mem_antidiagonalTuple] at hds
      rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_antidiagonal]
        rw [Fin.sum_univ_succ] at hds
        exact hds
      · rw [mem_antidiagonalTuple]
        rfl
    · intro p hp
      ext <;> simp [Fin.tail_cons, Fin.cons_succ, Fin.cons_zero]
      rw [Finset.mem_sigma] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Finset.mem_antidiagonal] at hp1
      rw [mem_antidiagonalTuple] at hp2
      omega
    · intro ds _
      show Fin.cons (ds 0) (Fin.tail ds) = ds
      exact Fin.cons_self_tail ds
    · intro p _
      show Matrix.polyCoeff p.1.1 M * (Matrix.polyCoeffList rest p.2).prod =
        (Matrix.polyCoeffList (M :: rest) (Fin.cons p.1.1 p.2)).prod
      rw [Matrix.polyCoeffList_cons, List.prod_cons]
      simp only [Fin.cons_zero, Fin.cons_succ]

end PolyCoeffListProd

/-! ## Ring-hom transport for matrix list products -/

section FinSuccEquivTransport

variable {ν : Type _} [Fintype ν] [DecidableEq ν]

/-- Ring-hom transport of a matrix list product. -/
theorem Matrix.map_list_prod {R S : Type _} [Semiring R] [Semiring S] (f : R →+* S)
    (Ms : List (Matrix ν ν R)) :
    (Ms.prod).map f = (Ms.map (Matrix.map · f)).prod := by
  have h := MonoidHom.map_list_prod f.mapMatrix.toMonoidHom Ms
  show f.mapMatrix.toMonoidHom Ms.prod = _
  rw [h]
  rfl

/-- Transport the `(Fin (k+1)) →₀ ℕ`-coefficient of an entry of a matrix list
    product into the polynomial-`X^d` coefficient (in the `MvPolynomial (Fin k) ℤ`
    coefficient ring) of the corresponding matrix list product after
    entrywise `finSuccEquiv`. -/
theorem coeff_cons_of_mvList_prod {k : ℕ}
    (Ms : List (Matrix ν ν (MvPolynomial (Fin (k + 1)) ℤ)))
    (i j : ν) (d : ℕ) (r : Fin k →₀ ℕ) :
    ((Ms.prod) i j).coeff (Finsupp.cons d r) =
      (Matrix.polyCoeff d
        ((Ms.map (Matrix.map · (MvPolynomial.finSuccEquiv ℤ k).toRingHom)).prod)
          i j).coeff r := by
  rw [show ((Ms.prod) i j).coeff (Finsupp.cons d r) =
        (((MvPolynomial.finSuccEquiv ℤ k) ((Ms.prod) i j)).coeff d).coeff r from
        (MvPolynomial.finSuccEquiv_coeff_coeff r ((Ms.prod) i j) d).symm]
  have h_map :
      MvPolynomial.finSuccEquiv ℤ k ((Ms.prod) i j) =
        ((Ms.map (Matrix.map · (MvPolynomial.finSuccEquiv ℤ k).toRingHom)).prod) i j := by
    have h_rh :=
      Matrix.map_list_prod (MvPolynomial.finSuccEquiv ℤ k).toRingHom Ms
    have h_entry : ((Ms.prod).map (MvPolynomial.finSuccEquiv ℤ k).toRingHom) i j =
        (MvPolynomial.finSuccEquiv ℤ k) ((Ms.prod) i j) := rfl
    rw [← h_entry, h_rh]
  rw [h_map]
  rfl

end FinSuccEquivTransport

/-! ## Per-matrix total-degree bound for a matrix list product -/

/-- The total degree of an entry of a matrix list product over
    `MvPolynomial (Fin k) ℤ` is bounded by `ps.sum`, where each `p_l` bounds
    every entry of `M_l`. -/
theorem Matrix.totalDegree_mvList_prod_le_per_matrix
    {k : ℕ} {ν : Type _} [Fintype ν] [DecidableEq ν] :
    ∀ (Ms : List (Matrix ν ν (MvPolynomial (Fin k) ℤ))) (ps : List ℕ),
      Ms ≠ [] →
      List.Forall₂ (fun M p => ∀ i j, (M i j).totalDegree ≤ p) Ms ps →
      ∀ i j, ((Ms.prod) i j).totalDegree ≤ ps.sum := by
  intro Ms ps h_ne h_p
  induction h_p with
  | nil => exact absurd rfl h_ne
  | @cons M p_head rest ps_rest hM_head h_rest ih =>
    intro i j
    by_cases h_rest_nil : rest = []
    · subst h_rest_nil
      cases h_rest
      rw [List.prod_cons, List.prod_nil, mul_one]
      have := hM_head i j
      show (M i j).totalDegree ≤ (p_head :: ([] : List ℕ)).sum
      simp; omega
    · have ih_rest := ih h_rest_nil
      rw [List.prod_cons, Matrix.mul_apply]
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
      apply Finset.sup_le
      intro s _
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have h1 : (M i s).totalDegree ≤ p_head := hM_head i s
      have h2 : (rest.prod s j).totalDegree ≤ ps_rest.sum := ih_rest s j
      show (M i s).totalDegree + (rest.prod s j).totalDegree ≤
        (p_head :: ps_rest).sum
      rw [show (p_head :: ps_rest).sum = p_head + ps_rest.sum from rfl]
      omega

/-! ## Integer base case: per-matrix bitsize bound -/

/-- A refinement of `Matrix.bitsize_list_prod_le` that allows each matrix in the
    list to have its own bitsize bound `τ_l`, matching BPR's per-matrix bound
    for `A = ℤ`. We use `List.Forall₂` to avoid length-juggling. -/
theorem Matrix.bitsize_list_prod_per_matrix_le {ν : Type _} [Fintype ν] [DecidableEq ν] :
    ∀ (Ms : List (Matrix ν ν ℤ)) (τs : List ℕ),
      Ms ≠ [] →
      List.Forall₂ (fun M τ => ∀ i j, (M i j).natAbs.size ≤ τ) Ms τs →
      ∀ i j, ((Ms.prod) i j).natAbs.size ≤
        τs.sum + Ms.length * Nat.size (Fintype.card ν) := by
  intro Ms τs h_ne hMs
  induction hMs with
  | nil => exact absurd rfl h_ne
  | @cons M τ_head rest τs_rest hM_head h_rest ih =>
    intro i j
    by_cases h_rest_nil : rest = []
    · subst h_rest_nil
      cases h_rest
      rw [List.prod_cons, List.prod_nil, mul_one]
      have h := hM_head i j
      show (M i j).natAbs.size ≤
        ((τ_head :: ([] : List ℕ)).sum +
          (M :: ([] : List (Matrix ν ν ℤ))).length * Nat.size (Fintype.card ν))
      simp
      omega
    · have ih_rest := ih h_rest_nil
      rw [List.prod_cons]
      have h_bound := Matrix.bitsize_mul_le
        (M := M) (N := rest.prod)
        (τ := τ_head) (σ := τs_rest.sum + rest.length * Nat.size (Fintype.card ν))
        hM_head ih_rest i j
      refine h_bound.trans ?_
      show τ_head + (τs_rest.sum + rest.length * Nat.size (Fintype.card ν)) +
             Nat.size (Fintype.card ν) ≤
           (τ_head :: τs_rest).sum + (M :: rest).length * Nat.size (Fintype.card ν)
      rw [show (τ_head :: τs_rest).sum = τ_head + τs_rest.sum from rfl,
          show (M :: rest).length = rest.length + 1 from rfl]
      have : (rest.length + 1) * Nat.size (Fintype.card ν) =
        rest.length * Nat.size (Fintype.card ν) + Nat.size (Fintype.card ν) := by ring
      omega

/-! ## Auxiliary lemmas for the inductive step -/

variable {ν : Type _} [Fintype ν] [DecidableEq ν]

/-- `totalDegree` of an `X^d`-coefficient under `finSuccEquiv` is bounded by the
    original `totalDegree`. -/
private lemma totalDegree_coeff_finSuccEquiv_le
    {k : ℕ} (p : MvPolynomial (Fin (k+1)) ℤ) (d : ℕ) :
    ((MvPolynomial.finSuccEquiv ℤ k p).coeff d).totalDegree ≤ p.totalDegree := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro α hα
  have h_ne : ((MvPolynomial.finSuccEquiv ℤ k p).coeff d).coeff α ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hα
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at h_ne
  have h_cons_mem : Finsupp.cons d α ∈ p.support := MvPolynomial.mem_support_iff.mpr h_ne
  have h_total : ((Finsupp.cons d α).sum fun _ e => e) ≤ p.totalDegree :=
    MvPolynomial.le_totalDegree h_cons_mem
  rw [Finsupp.sum_cons] at h_total
  exact le_trans (Nat.le_add_left _ d) h_total

/-- A coefficient of `finSuccEquiv` past the original `totalDegree` vanishes. -/
private lemma coeff_finSuccEquiv_eq_zero_of_totalDegree_lt
    {k : ℕ} (p : MvPolynomial (Fin (k+1)) ℤ) {d : ℕ} (h : p.totalDegree < d) :
    (MvPolynomial.finSuccEquiv ℤ k p).coeff d = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree _ _) h

/-- Bitsize of a `Nat` product is bounded by the sum of bitsizes. -/
private lemma Nat.size_mul_le' (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have ha' : a < 2 ^ a.size := Nat.lt_size_self _
  have hb' : b < 2 ^ b.size := Nat.lt_size_self _
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_pos_right ha' hb |>.trans_le (Nat.mul_le_mul le_rfl hb'.le)

/-- For `m ≥ 1`: the bitsize of a `Finset.prod` of `(p_l + 1)` is bounded by the sum of
    bitsizes. (For `m = 0` the LHS equals `1` while the RHS is `0`.) -/
private lemma Nat.size_prod_succ_le {m : ℕ} (hm : 0 < m) (ps : Fin m → ℕ) :
    Nat.size (∏ l, (ps l + 1)) ≤ ∑ l, Nat.size (ps l + 1) := by
  induction m with
  | zero => exact absurd hm (lt_irrefl 0)
  | succ m ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      simp
    have ih' : Nat.size (∏ l : Fin m, (ps l.succ + 1)) ≤
        ∑ l : Fin m, Nat.size (ps l.succ + 1) := ih hm0 (fun l => ps l.succ)
    have h_mul : Nat.size ((ps 0 + 1) * ∏ l : Fin m, (ps l.succ + 1)) ≤
        Nat.size (ps 0 + 1) + Nat.size (∏ l : Fin m, (ps l.succ + 1)) :=
      Nat.size_mul_le' _ _
    omega

/-- Cardinality bound on the antidiagonalTuple filtered by per-coordinate bounds. -/
private lemma card_antidiagonalTuple_filter_le {m d : ℕ} (ps : Fin m → ℕ) :
    ((Finset.Nat.antidiagonalTuple m d).filter (fun ds => ∀ l, ds l ≤ ps l)).card ≤
      ∏ l, (ps l + 1) := by
  calc ((Finset.Nat.antidiagonalTuple m d).filter (fun ds => ∀ l, ds l ≤ ps l)).card
      ≤ (Fintype.piFinset (fun l : Fin m => Finset.range (ps l + 1))).card := by
        apply Finset.card_le_card
        intro ds hds
        rw [Finset.mem_filter] at hds
        rw [Fintype.mem_piFinset]
        intro l
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (hds.2 l)
    _ = ∏ l, (ps l + 1) := by
        rw [Fintype.card_piFinset]
        apply Finset.prod_congr rfl
        intro l _; rw [Finset.card_range]

/-! ## Main theorem: BPR-exact bound via k-induction -/

/-- **BPR §8.1 (unnumbered lemma), k-induction form.** The coefficient bitsize
    of an entry of a matrix list product over `ℤ[Y_1, …, Y_k]` is bounded by
    BPR's exact bound. -/
theorem Matrix.bitsize_coeff_mvList_prod_le_bpr_exact :
    ∀ (k : ℕ) (Ms : List (Matrix ν ν (MvPolynomial (Fin k) ℤ)))
      (τs ps : List ℕ),
    Ms ≠ [] →
    List.Forall₂ (fun M τ => ∀ i j r, ((M i j).coeff r).natAbs.size ≤ τ) Ms τs →
    List.Forall₂ (fun M p => ∀ i j, (M i j).totalDegree ≤ p) Ms ps →
    ∀ i j r, (((Ms.prod) i j).coeff r).natAbs.size ≤
      τs.sum + k * (ps.map fun p => Nat.size (p + 1)).sum +
        Ms.length * Nat.size (Fintype.card ν) := by
  intro k
  induction k with
  | zero =>
    -- Base case: `k = 0`. The polynomial term vanishes; every `r : Fin 0 →₀ ℕ`
    -- is the unique zero, and the `r = 0` coefficient is `MvPolynomial.constantCoeff`.
    -- Transport via the ring hom `constantCoeff : MvPolynomial (Fin 0) ℤ →+* ℤ`
    -- to land in `Matrix.bitsize_list_prod_per_matrix_le`.
    intro Ms τs ps h_ne h_τ _ i j r
    have hr : r = 0 := by ext i; exact i.elim0
    subst hr
    rw [show ((Ms.prod i j).coeff (0 : Fin 0 →₀ ℕ)).natAbs.size =
            (MvPolynomial.constantCoeff (Ms.prod i j)).natAbs.size from rfl]
    have h_transport :
        MvPolynomial.constantCoeff (Ms.prod i j) =
          ((Ms.map (Matrix.map · MvPolynomial.constantCoeff)).prod) i j := by
      have h := Matrix.map_list_prod MvPolynomial.constantCoeff Ms
      have h_entry : ((Ms.prod).map MvPolynomial.constantCoeff) i j =
          MvPolynomial.constantCoeff (Ms.prod i j) := rfl
      rw [← h_entry, h]
    rw [h_transport]
    have h_τ_int : List.Forall₂
        (fun (M_int : Matrix ν ν ℤ) τ => ∀ i j, (M_int i j).natAbs.size ≤ τ)
        (Ms.map (Matrix.map · MvPolynomial.constantCoeff)) τs := by
      apply List.Forall₂.flip
      have := h_τ.flip
      rw [List.forall₂_map_right_iff]
      apply this.imp
      intro τ M h_bound i' j'
      have h := h_bound i' j' 0
      simpa using h
    have h_Ms_ne :
        Ms.map (Matrix.map · MvPolynomial.constantCoeff) ≠ [] := by
      simp [List.map_eq_nil_iff, h_ne]
    have h_bound := Matrix.bitsize_list_prod_per_matrix_le
      (Ms.map (Matrix.map · MvPolynomial.constantCoeff)) τs h_Ms_ne h_τ_int i j
    refine h_bound.trans ?_
    rw [List.length_map]
    omega
  | succ k ih =>
    intro Ms τs ps h_ne h_τ h_p i j r
    -- Decompose `r : Fin (k+1) →₀ ℕ` as `Finsupp.cons (r 0) r.tail`, then peel
    -- off the first variable via `finSuccEquiv` and expand the resulting
    -- polynomial coefficient via `polyCoeff_list_prod`.
    rw [← Finsupp.cons_tail r]
    rw [coeff_cons_of_mvList_prod Ms i j (r 0) r.tail]
    rw [show ((Matrix.polyCoeff (r 0)
              ((Ms.map (Matrix.map · (MvPolynomial.finSuccEquiv ℤ k).toRingHom)).prod)) i j)
        = (∑ ds ∈ Finset.Nat.antidiagonalTuple
              (Ms.map (Matrix.map · (MvPolynomial.finSuccEquiv ℤ k).toRingHom)).length (r 0),
            (Matrix.polyCoeffList
              (Ms.map (Matrix.map · (MvPolynomial.finSuccEquiv ℤ k).toRingHom)) ds).prod) i j
        from by rw [Matrix.polyCoeff_list_prod]]
    rw [_root_.Matrix.sum_apply i j]
    rw [MvPolynomial.coeff_sum]
    set fe := (MvPolynomial.finSuccEquiv ℤ k).toRingHom
    set B := τs.sum + k * (ps.map fun p => Nat.size (p + 1)).sum +
      Ms.length * Nat.size (Fintype.card ν) with hB_def
    -- Per-summand bound: for any tuple `ds`, the summand bitsize is ≤ B (the IH bound).
    have h_summand_bound : ∀ ds ∈ Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0),
        ((((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod) i j).coeff r.tail).natAbs.size
          ≤ B := by
      intro ds _
      have h_Ms_inner_len :
          (Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).length = Ms.length := by
        unfold Matrix.polyCoeffList
        rw [List.length_ofFn, List.length_map]
      have h_Ms_inner_ne : Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds ≠ [] := by
        intro he
        have hL : (Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).length = 0 := by
          rw [he]; rfl
        rw [h_Ms_inner_len] at hL
        exact h_ne (List.length_eq_zero_iff.mp hL)
      have h_τ_inner : List.Forall₂
          (fun M' τ => ∀ i' j' r', ((M' i' j').coeff r').natAbs.size ≤ τ)
          (Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds) τs := by
        rw [List.forall₂_iff_get]
        refine ⟨h_Ms_inner_len.trans h_τ.length_eq, fun l h₁ h₂ i' j' r' => ?_⟩
        have hl_Ms : l < Ms.length := by
          have := h₁
          unfold Matrix.polyCoeffList at this
          rwa [List.length_ofFn, List.length_map] at this
        simp only [Matrix.polyCoeffList, List.get_eq_getElem, List.getElem_ofFn,
          Matrix.polyCoeff_apply, List.getElem_map, Matrix.map_apply]
        show (MvPolynomial.coeff r' (((MvPolynomial.finSuccEquiv ℤ k) (Ms[l] i' j')).coeff
              (ds ⟨l, by rw [List.length_map]; exact hl_Ms⟩))).natAbs.size ≤ τs[l]
        rw [MvPolynomial.finSuccEquiv_coeff_coeff]
        exact (List.forall₂_iff_get.mp h_τ).2 l hl_Ms h₂ i' j' _
      have h_p_inner : List.Forall₂
          (fun M' p => ∀ i' j', (M' i' j').totalDegree ≤ p)
          (Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds) ps := by
        rw [List.forall₂_iff_get]
        refine ⟨h_Ms_inner_len.trans h_p.length_eq, fun l h₁ h₂ i' j' => ?_⟩
        have hl_Ms : l < Ms.length := by
          have := h₁
          unfold Matrix.polyCoeffList at this
          rwa [List.length_ofFn, List.length_map] at this
        simp only [Matrix.polyCoeffList, List.get_eq_getElem, List.getElem_ofFn,
          Matrix.polyCoeff_apply, List.getElem_map, Matrix.map_apply]
        show (((MvPolynomial.finSuccEquiv ℤ k) (Ms[l] i' j')).coeff
              (ds ⟨l, by rw [List.length_map]; exact hl_Ms⟩)).totalDegree ≤ ps[l]
        exact (totalDegree_coeff_finSuccEquiv_le _ _).trans
          ((List.forall₂_iff_get.mp h_p).2 l hl_Ms h₂ i' j')
      have h_ih := ih (Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds) τs ps
        h_Ms_inner_ne h_τ_inner h_p_inner i j r.tail
      refine h_ih.trans ?_
      rw [hB_def, h_Ms_inner_len]
    -- Define `p_fn : Fin (Ms.map fe).length → ℕ` using `ps`.
    have h_ps_len : ps.length = Ms.length := h_p.length_eq.symm
    have h_map_len : (Ms.map (Matrix.map · fe)).length = Ms.length :=
      List.length_map _
    let p_fn : Fin (Ms.map (Matrix.map · fe)).length → ℕ := fun l =>
      ps.get ⟨l.val, by rw [h_ps_len, ← h_map_len]; exact l.isLt⟩
    -- Show: any tuple `ds` with some `ds l > p_fn l` gives a zero summand.
    have h_zero : ∀ ds ∈ Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0),
        (∃ l, ds l > p_fn l) →
        MvPolynomial.coeff r.tail
          ((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod i j) = 0 := by
      intro ds _ ⟨l, hl_gt⟩
      have hl_Ms : l.val < Ms.length := by rw [← h_map_len]; exact l.isLt
      have h_mat_zero : Matrix.polyCoeff (ds l) ((Ms.map (Matrix.map · fe)).get l) = 0 := by
        funext i' j'
        rw [Matrix.polyCoeff_apply, Matrix.zero_apply]
        rcases l with ⟨l, hl⟩
        simp only [List.get_eq_getElem, List.getElem_map, Matrix.map_apply]
        change ((MvPolynomial.finSuccEquiv ℤ k) (Ms[l] i' j')).coeff (ds ⟨l, hl⟩) = 0
        apply coeff_finSuccEquiv_eq_zero_of_totalDegree_lt
        exact lt_of_le_of_lt
          ((List.forall₂_iff_get.mp h_p).2 l hl_Ms (by rw [h_ps_len]; exact hl_Ms) i' j')
          hl_gt
      have h_zero_in : (0 : Matrix ν ν (MvPolynomial (Fin k) ℤ)) ∈
          Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds := by
        unfold Matrix.polyCoeffList
        rw [List.mem_ofFn]
        exact ⟨l, h_mat_zero⟩
      rw [List.prod_eq_zero h_zero_in, Matrix.zero_apply, MvPolynomial.coeff_zero]
    -- Reduce the sum to its filtered subset (the rest are zero).
    rw [show
      (∑ ds ∈ Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0),
        MvPolynomial.coeff r.tail
          ((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod i j))
      = ∑ ds ∈ (Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0)).filter
          (fun ds => ∀ l, ds l ≤ p_fn l),
        MvPolynomial.coeff r.tail
          ((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod i j) from by
      apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro ds hds h_not_in
      rw [Finset.mem_filter, not_and_or] at h_not_in
      rcases h_not_in with h | h
      · exact absurd hds h
      · push Not at h
        exact h_zero ds hds h]
    have h_filtered_bound := Int.size_finset_sum_le
      (s := (Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0)).filter
        (fun ds => ∀ l, ds l ≤ p_fn l))
      (f := fun ds => MvPolynomial.coeff r.tail
        ((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod i j))
      (B := B)
      (fun ds hds => h_summand_bound ds (Finset.mem_filter.mp hds).1)
    refine h_filtered_bound.trans ?_
    -- Bound filtered.card by `∏ (p_fn l + 1)` and then by `2^(∑ bit(p_fn l + 1))`.
    have h_card_le := card_antidiagonalTuple_filter_le
      (m := (Ms.map (Matrix.map · fe)).length) (d := r 0) (ps := p_fn)
    have hm_pos : 0 < (Ms.map (Matrix.map · fe)).length := by
      rw [h_map_len]
      exact Nat.pos_of_ne_zero (fun h => h_ne (List.length_eq_zero_iff.mp h))
    have h_card_size_le :
        Nat.size ((Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0)).filter
          (fun ds => ∀ l, ds l ≤ p_fn l)).card
        ≤ ∑ l, Nat.size (p_fn l + 1) :=
      (Nat.size_le_size h_card_le).trans (Nat.size_prod_succ_le hm_pos p_fn)
    -- Convert the Fin sum over `p_fn` to the List sum `(ps.map (fun p => bit(p+1))).sum`.
    have list_map_sum_via_get : (ps.map (fun p => Nat.size (p + 1))).sum =
        ∑ l : Fin ps.length, Nat.size (ps.get l + 1) := by
      conv_lhs => rw [show ps = List.ofFn ps.get from (List.ofFn_get ps).symm]
      rw [List.map_ofFn, List.sum_ofFn]
      rfl
    have h_sum_fin_eq_list :
        (∑ l, Nat.size (p_fn l + 1)) = (ps.map (fun p => Nat.size (p + 1))).sum := by
      rw [list_map_sum_via_get]
      have h_len_eq : (Ms.map (Matrix.map · fe)).length = ps.length :=
        h_map_len.trans h_ps_len.symm
      apply Finset.sum_bij (fun l _ => Fin.cast h_len_eq l)
      · intros; exact Finset.mem_univ _
      · intro l₁ _ l₂ _ heq
        have := congrArg Fin.val heq
        exact Fin.ext this
      · intro l _; exact ⟨Fin.cast h_len_eq.symm l, Finset.mem_univ _, by ext; rfl⟩
      · intro l _
        show Nat.size (p_fn l + 1) = Nat.size (ps.get _ + 1)
        rfl
    have h_step : B + ∑ l, Nat.size (p_fn l + 1) ≤
        τs.sum + (k + 1) * (ps.map fun p => Nat.size (p + 1)).sum +
          Ms.length * Nat.size (Fintype.card ν) := by
      rw [h_sum_fin_eq_list, hB_def]
      have : (k + 1) * (ps.map fun p => Nat.size (p + 1)).sum =
        k * (ps.map fun p => Nat.size (p + 1)).sum +
          (ps.map fun p => Nat.size (p + 1)).sum := by ring
      omega
    exact le_trans (Nat.add_le_add_left h_card_size_le _) h_step

end Azurite.BPR

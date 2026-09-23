/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

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

open _root_.Azurite.BPR.Matrix _root_.Azurite.BPR.MvPolynomial Polynomial Finset.Nat

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
private lemma totalDegree_coeff_finSuccEquiv_le {R : Type _} [CommSemiring R]
    {k : ℕ} (p : MvPolynomial (Fin (k+1)) R) (d : ℕ) :
    ((MvPolynomial.finSuccEquiv R k p).coeff d).totalDegree ≤ p.totalDegree := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro α hα
  have h_ne : ((MvPolynomial.finSuccEquiv R k p).coeff d).coeff α ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hα
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at h_ne
  have h_cons_mem : Finsupp.cons d α ∈ p.support := MvPolynomial.mem_support_iff.mpr h_ne
  have h_total : ((Finsupp.cons d α).sum fun _ e => e) ≤ p.totalDegree :=
    MvPolynomial.le_totalDegree h_cons_mem
  rw [Finsupp.sum_cons] at h_total
  exact le_trans (Nat.le_add_left _ d) h_total

/-- A coefficient of `finSuccEquiv` past the original `totalDegree` vanishes. -/
private lemma coeff_finSuccEquiv_eq_zero_of_totalDegree_lt {R : Type _} [CommSemiring R]
    {k : ℕ} (p : MvPolynomial (Fin (k+1)) R) {d : ℕ} (h : p.totalDegree < d) :
    (MvPolynomial.finSuccEquiv R k p).coeff d = 0 := by
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

/-- Sharper variant: `bit(∏(p_l + 1) - 1) ≤ ∑ bit(p_l)`. Used together with
    `Int.size_finset_sum_le'` to match BPR's exact `bit(p_i)` (rather than the
    slacker `bit(p_i + 1)`). The key step is `p + 1 ≤ 2 ^ bit(p)`. -/
private lemma Nat.size_prod_succ_sub_one_le {m : ℕ} (ps : Fin m → ℕ) :
    Nat.size ((∏ l, (ps l + 1)) - 1) ≤ ∑ l, Nat.size (ps l) := by
  rw [Nat.size_le]
  have h_prod_le : ∏ l, (ps l + 1) ≤ 2 ^ (∑ l, Nat.size (ps l)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ, pow_add]
      have h_first : ps 0 + 1 ≤ 2 ^ Nat.size (ps 0) := by
        have : ps 0 < 2 ^ Nat.size (ps 0) := Nat.lt_size_self _
        omega
      have h_rest := ih (fun l => ps l.succ)
      calc (ps 0 + 1) * ∏ l : Fin m, (ps l.succ + 1)
          ≤ 2 ^ Nat.size (ps 0) * ∏ l : Fin m, (ps l.succ + 1) :=
            Nat.mul_le_mul_right _ h_first
        _ ≤ 2 ^ Nat.size (ps 0) * 2 ^ (∑ l : Fin m, Nat.size (ps l.succ)) :=
            Nat.mul_le_mul_left _ h_rest
  have h_2pow_pos : 0 < 2 ^ (∑ l, Nat.size (ps l)) := Nat.two_pow_pos _
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
      τs.sum + k * (ps.map fun p => Nat.size p).sum +
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
      simpa [MvPolynomial.constantCoeff_eq] using h
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
    set B := τs.sum + k * (ps.map fun p => Nat.size p).sum +
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
        show ((((MvPolynomial.finSuccEquiv ℤ k) (Ms[l] i' j')).coeff
              (ds ⟨l, by rw [List.length_map]; exact hl_Ms⟩)).coeff r').natAbs.size ≤ τs[l]
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
        ((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod i j).coeff r.tail = 0 := by
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
      rw [List.prod_eq_zero h_zero_in, Matrix.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    -- Reduce the sum to its filtered subset (the rest are zero).
    rw [show
      (∑ ds ∈ Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0),
        ((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod i j).coeff r.tail)
      = ∑ ds ∈ (Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0)).filter
          (fun ds => ∀ l, ds l ≤ p_fn l),
        ((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod i j).coeff r.tail from by
      apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro ds hds h_not_in
      rw [Finset.mem_filter, not_and_or] at h_not_in
      rcases h_not_in with h | h
      · exact absurd hds h
      · push Not at h
        exact h_zero ds hds h]
    have h_filtered_bound := Int.size_finset_sum_le'
      (s := (Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0)).filter
        (fun ds => ∀ l, ds l ≤ p_fn l))
      (f := fun ds => ((Matrix.polyCoeffList (Ms.map (Matrix.map · fe)) ds).prod i j).coeff r.tail)
      (B := B)
      (fun ds hds => h_summand_bound ds (Finset.mem_filter.mp hds).1)
    refine h_filtered_bound.trans ?_
    -- Sharper bound: bit(card - 1) ≤ ∑ bit(p_l) (no `+ 1` per coordinate).
    have h_card_le := card_antidiagonalTuple_filter_le
      (m := (Ms.map (Matrix.map · fe)).length) (d := r 0) (ps := p_fn)
    have h_card_sub_le :
        ((Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0)).filter
          (fun ds => ∀ l, ds l ≤ p_fn l)).card - 1 ≤
        (∏ l, (p_fn l + 1)) - 1 := by omega
    have h_card_size_le :
        Nat.size (((Finset.Nat.antidiagonalTuple (Ms.map (Matrix.map · fe)).length (r 0)).filter
          (fun ds => ∀ l, ds l ≤ p_fn l)).card - 1)
        ≤ ∑ l, Nat.size (p_fn l) :=
      (Nat.size_le_size h_card_sub_le).trans (Nat.size_prod_succ_sub_one_le p_fn)
    -- Convert the Fin sum over `p_fn` to the List sum `(ps.map (fun p => bit(p))).sum`.
    have list_map_sum_via_get : (ps.map (fun p => Nat.size p)).sum =
        ∑ l : Fin ps.length, Nat.size (ps.get l) := by
      conv_lhs => rw [show ps = List.ofFn ps.get from (List.ofFn_get ps).symm]
      rw [List.map_ofFn, List.sum_ofFn]
      rfl
    have h_sum_fin_eq_list :
        (∑ l, Nat.size (p_fn l)) = (ps.map (fun p => Nat.size p)).sum := by
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
        show Nat.size (p_fn l) = Nat.size (ps.get _)
        rfl
    have h_step : B + ∑ l, Nat.size (p_fn l) ≤
        τs.sum + (k + 1) * (ps.map fun p => Nat.size p).sum +
          Ms.length * Nat.size (Fintype.card ν) := by
      rw [h_sum_fin_eq_list, hB_def]
      have : (k + 1) * (ps.map fun p => Nat.size p).sum =
        k * (ps.map fun p => Nat.size p).sum +
          (ps.map fun p => Nat.size p).sum := by ring
      omega
    exact le_trans (Nat.add_le_add_left h_card_size_le _) h_step

/-! ## BPR Remark 8.10: polynomial-list analog (the `n = 1` special case)

For a list of multivariate polynomials, BPR's bound drops the `m · bit(n)` term.
The proof mirrors the matrix theorem above but operates directly on polynomials,
using a polynomial-list coefficient convolution `coeff_list_prod`
(analogous to `Matrix.polyCoeff_list_prod`) and an integer base case
`Int.bitsize_list_prod_le` (analogous to `Matrix.bitsize_list_prod_per_matrix_le`,
but without the `m · bit(n)` cost since scalar multiplication has no
"middle-dimension" sum to pay for).
-/

section CoeffListProd

variable {R : Type _} [CommSemiring R]

/-- The `X^d`-coefficient of a polynomial list product equals the sum, over
    tuples summing to `d`, of products of single coefficients. -/
theorem coeff_list_prod (d : ℕ) (Ps : List (Polynomial R)) :
    (Ps.prod).coeff d =
      ∑ ds ∈ antidiagonalTuple Ps.length d,
        ∏ l : Fin Ps.length, (Ps.get l).coeff (ds l) := by
  induction Ps generalizing d with
  | nil =>
    rw [List.prod_nil]
    show (1 : Polynomial R).coeff d =
      ∑ ds ∈ antidiagonalTuple 0 d,
        ∏ l : Fin 0, (([] : List (Polynomial R)).get l).coeff (ds l)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rw [antidiagonalTuple_zero_zero, Finset.sum_singleton, Polynomial.coeff_one]
      simp
    · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hd)
      rw [antidiagonalTuple_zero_succ, Finset.sum_empty, Polynomial.coeff_one]
      simp
  | cons P rest ih =>
    rw [List.prod_cons, Polynomial.coeff_mul]
    conv_lhs =>
      rw [show (∑ x ∈ Finset.antidiagonal d, P.coeff x.1 * (rest.prod).coeff x.2) =
              ∑ x ∈ Finset.antidiagonal d, P.coeff x.1 *
                (∑ ds' ∈ antidiagonalTuple rest.length x.2,
                  ∏ l : Fin rest.length, (rest.get l).coeff (ds' l)) from by
            apply Finset.sum_congr rfl
            intro x _
            rw [ih x.2]]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sigma (Finset.antidiagonal d)
          (fun x : ℕ × ℕ => antidiagonalTuple rest.length x.2)
          (fun p =>
            P.coeff p.1.1 * ∏ l : Fin rest.length, (rest.get l).coeff (p.2 l))]
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
      · rw [mem_antidiagonalTuple]; rfl
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
      show P.coeff p.1.1 * ∏ l : Fin rest.length, (rest.get l).coeff (p.2 l) =
        ∏ l : Fin (rest.length + 1), ((P :: rest).get l).coeff
          ((Fin.cons p.1.1 p.2 : Fin (rest.length + 1) → ℕ) l)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rfl

end CoeffListProd

/-! ## Integer base case: bitsize of a list product of integers -/

/-- Per-element bitsize bound for a (non-empty) list product of integers. The
    bound is `τs.sum` (no `m · bit(n)` term as in the matrix case). -/
theorem Int.bitsize_list_prod_le :
    ∀ (Ps : List ℤ) (τs : List ℕ),
      Ps ≠ [] →
      List.Forall₂ (fun P τ => P.natAbs.size ≤ τ) Ps τs →
      Ps.prod.natAbs.size ≤ τs.sum := by
  intro Ps τs h_ne hPs
  induction hPs with
  | nil => exact absurd rfl h_ne
  | @cons P τ_head rest τs_rest hP_head h_rest ih =>
    by_cases h_rest_nil : rest = []
    · subst h_rest_nil
      cases h_rest
      rw [List.prod_cons, List.prod_nil, mul_one]
      show P.natAbs.size ≤ (τ_head :: ([] : List ℕ)).sum
      simp; omega
    · have ih_rest := ih h_rest_nil
      rw [List.prod_cons]
      refine (Int.size_mul_le P rest.prod τ_head τs_rest.sum hP_head ih_rest).trans ?_
      show τ_head + τs_rest.sum ≤ (τ_head :: τs_rest).sum
      rw [show (τ_head :: τs_rest).sum = τ_head + τs_rest.sum from rfl]

/-! ## Main theorem: BPR Remark 8.10 (polynomial analog of the matrix theorem) -/

/-- **BPR §8.1 Remark 8.10.** Multiplying a non-empty list of `m` polynomials
    `P_l ∈ ℤ[Y_1, …, Y_k]`, with `P_l` having total degree bounded by `p_l`
    (in `Y`) and coefficient bitsizes bounded by `τ_l`, produces coefficients
    bounded by `(τ_1 + ⋯ + τ_m) + k · (bit(p_1) + ⋯ + bit(p_m))`. This is
    BPR's exact bound. -/
theorem MvPolynomial.bitsize_coeff_list_prod_le_bpr_exact :
    ∀ (k : ℕ) (Ps : List (MvPolynomial (Fin k) ℤ)) (τs ps : List ℕ),
    Ps ≠ [] →
    List.Forall₂ (fun P τ => ∀ r, (P.coeff r).natAbs.size ≤ τ) Ps τs →
    List.Forall₂ (fun P p => P.totalDegree ≤ p) Ps ps →
    ∀ r, ((Ps.prod).coeff r).natAbs.size ≤
      τs.sum + k * (ps.map fun p => Nat.size p).sum := by
  intro k
  induction k with
  | zero =>
    intro Ps τs ps h_ne h_τ _ r
    have hr : r = 0 := by ext i; exact i.elim0
    subst hr
    rw [show ((Ps.prod).coeff (0 : Fin 0 →₀ ℕ)).natAbs.size =
            (MvPolynomial.constantCoeff (Ps.prod)).natAbs.size from rfl]
    have h_transport :
        MvPolynomial.constantCoeff (Ps.prod) =
          (Ps.map MvPolynomial.constantCoeff).prod := by
      simpa using MonoidHom.map_list_prod
        MvPolynomial.constantCoeff.toMonoidHom Ps
    rw [h_transport]
    have h_τ_int : List.Forall₂
        (fun (P_int : ℤ) τ => P_int.natAbs.size ≤ τ)
        (Ps.map MvPolynomial.constantCoeff) τs := by
      apply List.Forall₂.flip
      have := h_τ.flip
      rw [List.forall₂_map_right_iff]
      apply this.imp
      intro τ P h_bound
      have h := h_bound 0
      show (MvPolynomial.constantCoeff P).natAbs.size ≤ τ
      rw [MvPolynomial.constantCoeff_eq]; exact h
    have h_Ps_int_ne : Ps.map MvPolynomial.constantCoeff ≠ [] := by
      simp [List.map_eq_nil_iff, h_ne]
    refine (Int.bitsize_list_prod_le _ _ h_Ps_int_ne h_τ_int).trans ?_
    omega
  | succ k ih =>
    intro Ps τs ps h_ne h_τ h_p r
    -- Decompose r = cons (r 0) r.tail; transport via finSuccEquiv.
    rw [← Finsupp.cons_tail r]
    rw [show ((Ps.prod).coeff (Finsupp.cons (r 0) r.tail)) =
            (((MvPolynomial.finSuccEquiv ℤ k) (Ps.prod)).coeff (r 0)).coeff r.tail from
            (MvPolynomial.finSuccEquiv_coeff_coeff r.tail Ps.prod (r 0)).symm]
    set fe := (MvPolynomial.finSuccEquiv ℤ k).toRingHom
    have h_transport : MvPolynomial.finSuccEquiv ℤ k (Ps.prod) = (Ps.map fe).prod := by
      exact map_list_prod fe Ps
    rw [h_transport]
    -- Expand the polynomial X^(r 0)-coefficient of a list product.
    rw [coeff_list_prod, MvPolynomial.coeff_sum]
    set B := τs.sum + k * (ps.map fun p => Nat.size p).sum with hB_def
    -- Define `p_fn : Fin (Ps.map fe).length → ℕ` via `ps` (used in filter and bound).
    have h_ps_len : ps.length = Ps.length := h_p.length_eq.symm
    have h_map_len : (Ps.map fe).length = Ps.length := List.length_map _
    let p_fn : Fin (Ps.map fe).length → ℕ := fun l =>
      ps.get ⟨l.val, by rw [h_ps_len, ← h_map_len]; exact l.isLt⟩
    -- Per-summand bound: each `ds`-summand has bitsize ≤ B (via IH).
    have h_summand_bound : ∀ ds ∈ Finset.Nat.antidiagonalTuple (Ps.map fe).length (r 0),
        ((∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff r.tail).natAbs.size
          ≤ B := by
      intro ds _
      let Ps_inner : List (MvPolynomial (Fin k) ℤ) :=
        List.ofFn (fun l : Fin (Ps.map fe).length =>
          ((Ps.map fe).get l).coeff (ds l))
      have h_Ps_inner_len : Ps_inner.length = Ps.length := by
        show (List.ofFn _).length = _
        rw [List.length_ofFn, h_map_len]
      have h_Ps_inner_ne : Ps_inner ≠ [] := by
        intro he
        have hL : Ps_inner.length = 0 := by rw [he]; rfl
        rw [h_Ps_inner_len] at hL
        exact h_ne (List.length_eq_zero_iff.mp hL)
      have h_prod_eq : Ps_inner.prod =
          ∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l) := by
        show (List.ofFn _).prod = _
        exact List.prod_ofFn
      rw [← h_prod_eq]
      -- Per-element coefficient and degree Forall₂ for Ps_inner.
      have h_τ_inner : List.Forall₂
          (fun P' τ => ∀ r', (P'.coeff r').natAbs.size ≤ τ) Ps_inner τs := by
        rw [List.forall₂_iff_get]
        refine ⟨h_Ps_inner_len.trans h_τ.length_eq, fun l h₁ h₂ r' => ?_⟩
        have hl_Ps : l < Ps.length := by rwa [h_Ps_inner_len] at h₁
        have hl_map : l < (Ps.map fe).length := by rwa [h_map_len]
        simp only [Ps_inner, List.get_eq_getElem, List.getElem_ofFn,
          List.getElem_map]
        show ((((MvPolynomial.finSuccEquiv ℤ k) (Ps[l])).coeff
              (ds ⟨l, hl_map⟩)).coeff r').natAbs.size ≤ τs[l]
        rw [MvPolynomial.finSuccEquiv_coeff_coeff]
        exact (List.forall₂_iff_get.mp h_τ).2 l hl_Ps h₂ _
      have h_p_inner : List.Forall₂
          (fun P' p => P'.totalDegree ≤ p) Ps_inner ps := by
        rw [List.forall₂_iff_get]
        refine ⟨h_Ps_inner_len.trans h_p.length_eq, fun l h₁ h₂ => ?_⟩
        have hl_Ps : l < Ps.length := by rwa [h_Ps_inner_len] at h₁
        have hl_map : l < (Ps.map fe).length := by rwa [h_map_len]
        simp only [Ps_inner, List.get_eq_getElem, List.getElem_ofFn,
          List.getElem_map]
        show (((MvPolynomial.finSuccEquiv ℤ k) (Ps[l])).coeff
              (ds ⟨l, hl_map⟩)).totalDegree ≤ ps[l]
        exact (totalDegree_coeff_finSuccEquiv_le _ _).trans
          ((List.forall₂_iff_get.mp h_p).2 l hl_Ps h₂)
      have h_ih := ih Ps_inner τs ps h_Ps_inner_ne h_τ_inner h_p_inner r.tail
      exact h_ih
    -- Zero-summand argument.
    have h_zero : ∀ ds ∈ Finset.Nat.antidiagonalTuple (Ps.map fe).length (r 0),
        (∃ l, ds l > p_fn l) →
        (∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff r.tail = 0 := by
      intro ds _ ⟨l, hl_gt⟩
      have hl_Ps : l.val < Ps.length := by rw [← h_map_len]; exact l.isLt
      have h_factor_zero : ((Ps.map fe).get l).coeff (ds l) = 0 := by
        rcases l with ⟨l, hl⟩
        simp only [List.get_eq_getElem, List.getElem_map]
        change ((MvPolynomial.finSuccEquiv ℤ k) (Ps[l])).coeff (ds ⟨l, hl⟩) = 0
        apply coeff_finSuccEquiv_eq_zero_of_totalDegree_lt
        exact lt_of_le_of_lt
          ((List.forall₂_iff_get.mp h_p).2 l hl_Ps (by rw [h_ps_len]; exact hl_Ps))
          hl_gt
      rw [Finset.prod_eq_zero (Finset.mem_univ l) h_factor_zero]
      simp
    -- Reduce sum to filtered subset.
    rw [show
      (∑ ds ∈ Finset.Nat.antidiagonalTuple (Ps.map fe).length (r 0),
        (∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff r.tail)
      = ∑ ds ∈ (Finset.Nat.antidiagonalTuple (Ps.map fe).length (r 0)).filter
          (fun ds => ∀ l, ds l ≤ p_fn l),
        (∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff r.tail from by
      apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro ds hds h_not_in
      rw [Finset.mem_filter, not_and_or] at h_not_in
      rcases h_not_in with h | h
      · exact absurd hds h
      · push Not at h
        exact h_zero ds hds h]
    have h_filtered_bound := Int.size_finset_sum_le'
      (s := (Finset.Nat.antidiagonalTuple (Ps.map fe).length (r 0)).filter
        (fun ds => ∀ l, ds l ≤ p_fn l))
      (f := fun ds => (∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff r.tail)
      (B := B) (fun ds hds => h_summand_bound ds (Finset.mem_filter.mp hds).1)
    refine h_filtered_bound.trans ?_
    have h_card_le := card_antidiagonalTuple_filter_le
      (m := (Ps.map fe).length) (d := r 0) (ps := p_fn)
    -- Sharper bound: bit(card - 1) ≤ ∑ bit(p_l) (no `+ 1` per coordinate).
    have h_card_sub_le :
        ((Finset.Nat.antidiagonalTuple (Ps.map fe).length (r 0)).filter
          (fun ds => ∀ l, ds l ≤ p_fn l)).card - 1 ≤
        (∏ l, (p_fn l + 1)) - 1 := by omega
    have h_card_size_le :
        Nat.size (((Finset.Nat.antidiagonalTuple (Ps.map fe).length (r 0)).filter
          (fun ds => ∀ l, ds l ≤ p_fn l)).card - 1) ≤
          ∑ l, Nat.size (p_fn l) :=
      (Nat.size_le_size h_card_sub_le).trans (Nat.size_prod_succ_sub_one_le p_fn)
    -- Convert Fin sum to List sum.
    have list_map_sum_via_get :
        (ps.map (fun p => Nat.size p)).sum =
        ∑ l : Fin ps.length, Nat.size (ps.get l) := by
      conv_lhs => rw [show ps = List.ofFn ps.get from (List.ofFn_get ps).symm]
      rw [List.map_ofFn, List.sum_ofFn]
      rfl
    have h_sum_fin_eq_list :
        (∑ l, Nat.size (p_fn l)) =
        (ps.map (fun p => Nat.size p)).sum := by
      rw [list_map_sum_via_get]
      have h_len_eq : (Ps.map fe).length = ps.length :=
        h_map_len.trans h_ps_len.symm
      apply Finset.sum_bij (fun l _ => Fin.cast h_len_eq l)
      · intros; exact Finset.mem_univ _
      · intro l₁ _ l₂ _ heq
        exact (Fin.cast_inj _).mp heq
      · intro l _; exact ⟨Fin.cast h_len_eq.symm l, Finset.mem_univ _, by ext; rfl⟩
      · intro l _
        show Nat.size (p_fn l) = Nat.size (ps.get _)
        rfl
    have h_step : B + ∑ l, Nat.size (p_fn l) ≤
        τs.sum + (k + 1) * (ps.map fun p => Nat.size p).sum := by
      rw [h_sum_fin_eq_list, hB_def]
      have : (k + 1) * (ps.map fun p => Nat.size p).sum =
        k * (ps.map fun p => Nat.size p).sum +
          (ps.map fun p => Nat.size p).sum := by ring
      omega
    exact le_trans (Nat.add_le_add_left h_card_size_le _) h_step

/-! ## BPR equation (8.2): products of polynomials in `ℤ[Y, X]` (two variable blocks) -/

set_option maxHeartbeats 800000 in
/-- **BPR §8.1 equation (8.2).** For a non-empty list of `m` polynomials in
    `ℤ[Y_1, …, Y_ℓ][X_1, …, X_k]`, with uniform degree-in-`X` bound `p`,
    degree-in-`Y` bound `q`, and uniform integer-coefficient bitsize bound `τ`,
    every integer coefficient of the product is bounded by

      `m · (τ + k · bit(p) + ℓ · bit(q))`.

    This is BPR's exact bound. Encoded with `Y` as the outer variable block
    and `X` as the inner block: `MvPolynomial (Fin ℓ) (MvPolynomial (Fin k) ℤ)`.
    The proof is by induction on `ℓ`, with the base case `ℓ = 0` reducing to
    `MvPolynomial.bitsize_coeff_list_prod_le_bpr_exact` (Remark 8.10). -/
theorem MvPolynomial.bitsize_coeff_list_prod_le_bpr_8_2 :
    ∀ (ℓ k : ℕ) (Ps : List (MvPolynomial (Fin ℓ) (MvPolynomial (Fin k) ℤ)))
      (τ p q : ℕ),
    Ps ≠ [] →
    (∀ P ∈ Ps, ∀ y x, ((P.coeff y).coeff x).natAbs.size ≤ τ) →
    (∀ P ∈ Ps, P.totalDegree ≤ q) →
    (∀ P ∈ Ps, ∀ y, (P.coeff y).totalDegree ≤ p) →
    ∀ y x, (((Ps.prod).coeff y).coeff x).natAbs.size ≤
      Ps.length * (τ + k * Nat.size p + ℓ * Nat.size q) := by
  intro ℓ
  induction ℓ with
  | zero =>
    -- Base case: `ℓ = 0`. The polynomial-in-Y term vanishes; every `y : Fin 0 →₀ ℕ`
    -- is `0`, and `P.coeff 0 = constantCoeff P`. Transport via the ring hom
    -- `constantCoeff : MvPolynomial (Fin 0) R →+* R` to reduce to Remark 8.10
    -- applied to the inner-X polynomial list with uniform bounds.
    intro k Ps τ p q h_ne h_τ _ h_pX y x
    have hy : y = 0 := by ext i; exact i.elim0
    subst hy
    -- (Ps.prod).coeff 0 = constantCoeff (Ps.prod) = (Ps.map constantCoeff).prod.
    rw [show ((Ps.prod).coeff (0 : Fin 0 →₀ ℕ)) =
            MvPolynomial.constantCoeff (Ps.prod) from rfl]
    rw [show MvPolynomial.constantCoeff (Ps.prod) =
            (Ps.map MvPolynomial.constantCoeff).prod from by
        simpa using MonoidHom.map_list_prod
          MvPolynomial.constantCoeff.toMonoidHom Ps]
    -- Build Forall₂ relations for Remark 8.10 with uniform bounds τ_l = τ, p_l = p.
    set Ps' : List (MvPolynomial (Fin k) ℤ) :=
      Ps.map MvPolynomial.constantCoeff with hPs'_def
    have h_Ps'_ne : Ps' ≠ [] := by simp [Ps', List.map_eq_nil_iff, h_ne]
    have h_τ' : List.Forall₂
        (fun (P : MvPolynomial (Fin k) ℤ) τ_l => ∀ r, (P.coeff r).natAbs.size ≤ τ_l)
        Ps' (List.replicate Ps'.length τ) := by
      apply List.forall₂_iff_get.mpr
      refine ⟨by rw [List.length_replicate], fun l h₁ h₂ r => ?_⟩
      have hl_Ps : l < Ps.length := by
        rw [show Ps'.length = Ps.length from by simp [Ps']] at h₁
        exact h₁
      show ((Ps'.get ⟨l, h₁⟩).coeff r).natAbs.size ≤
        (List.replicate Ps'.length τ).get ⟨l, h₂⟩
      simp only [List.get_eq_getElem, List.getElem_replicate]
      simp only [Ps', List.getElem_map]
      show ((MvPolynomial.constantCoeff (Ps[l])).coeff r).natAbs.size ≤ τ
      change ((Ps[l].coeff 0).coeff r).natAbs.size ≤ τ
      exact h_τ Ps[l] (List.getElem_mem _) 0 r
    have h_p' : List.Forall₂
        (fun (P : MvPolynomial (Fin k) ℤ) p_l => P.totalDegree ≤ p_l)
        Ps' (List.replicate Ps'.length p) := by
      apply List.forall₂_iff_get.mpr
      refine ⟨by rw [List.length_replicate], fun l h₁ h₂ => ?_⟩
      have hl_Ps : l < Ps.length := by
        rw [show Ps'.length = Ps.length from by simp [Ps']] at h₁
        exact h₁
      show (Ps'.get ⟨l, h₁⟩).totalDegree ≤
        (List.replicate Ps'.length p).get ⟨l, h₂⟩
      simp only [List.get_eq_getElem, List.getElem_replicate]
      simp only [Ps', List.getElem_map]
      show (MvPolynomial.constantCoeff (Ps[l])).totalDegree ≤ p
      change (Ps[l].coeff 0).totalDegree ≤ p
      exact h_pX Ps[l] (List.getElem_mem _) 0
    have h_bound := MvPolynomial.bitsize_coeff_list_prod_le_bpr_exact
      k Ps' (List.replicate Ps'.length τ) (List.replicate Ps'.length p)
      h_Ps'_ne h_τ' h_p' x
    refine h_bound.trans ?_
    -- Convert τs.sum = m·τ and (ps.map ...).sum = m·bit(p).
    rw [List.sum_replicate, smul_eq_mul, show Ps'.length = Ps.length from by simp [Ps']]
    rw [show (List.replicate Ps.length p).map (fun p => Nat.size p) =
            List.replicate Ps.length (Nat.size p) from List.map_replicate]
    rw [List.sum_replicate, smul_eq_mul]
    ring_nf
    omega
  | succ ℓ ih =>
    intro k Ps τ p q h_ne h_τ h_q h_pX y x
    -- Decompose y = cons (y 0) y.tail; transport via finSuccEquiv on the outer
    -- MvPolynomial layer (whose base ring is MvPolynomial (Fin k) ℤ).
    rw [← Finsupp.cons_tail y]
    -- Apply finSuccEquiv_coeff_coeff with R = MvPolynomial (Fin k) ℤ.
    rw [show ((Ps.prod).coeff (Finsupp.cons (y 0) y.tail)) =
            (((MvPolynomial.finSuccEquiv (MvPolynomial (Fin k) ℤ) ℓ)
                (Ps.prod)).coeff (y 0)).coeff y.tail from
            (MvPolynomial.finSuccEquiv_coeff_coeff
              y.tail Ps.prod (y 0)).symm]
    -- Ring-hom transport: `finSuccEquiv (Ps.prod) = (Ps.map fe).prod`.
    set fe := (MvPolynomial.finSuccEquiv (MvPolynomial (Fin k) ℤ) ℓ).toRingHom
      with hfe_def
    rw [show MvPolynomial.finSuccEquiv (MvPolynomial (Fin k) ℤ) ℓ (Ps.prod) =
            (Ps.map fe).prod from by
        exact map_list_prod fe Ps]
    -- Expand the polynomial Y_(ℓ+1)^(y 0)-coefficient of the list product, then
    -- distribute the outer y.tail- and x-coefficient extractions through the sum.
    rw [coeff_list_prod, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
    set B := Ps.length * (τ + k * Nat.size p + ℓ * Nat.size q) with hB_def
    -- Per-summand bound via IH at ℓ.
    have h_summand_bound : ∀ ds ∈ Finset.Nat.antidiagonalTuple (Ps.map fe).length (y 0),
        (((∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff y.tail).coeff x).natAbs.size
          ≤ B := by
      intro ds _
      have h_len_eq : (Ps.map fe).length = Ps.length := List.length_map _
      -- Define `Ps_inner` directly indexed over `Fin Ps.length`.
      let Ps_inner : List (MvPolynomial (Fin ℓ) (MvPolynomial (Fin k) ℤ)) :=
        List.ofFn (n := Ps.length) (fun l =>
          (fe (Ps.get l)).coeff (ds (Fin.cast h_len_eq.symm l)))
      have h_Ps_inner_len : Ps_inner.length = Ps.length := List.length_ofFn
      have h_Ps_inner_ne : Ps_inner ≠ [] := by
        intro he
        have hL : Ps_inner.length = 0 := by rw [he]; rfl
        rw [h_Ps_inner_len] at hL
        exact h_ne (List.length_eq_zero_iff.mp hL)
      -- Key identity: Ps_inner.prod = ∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l).
      have h_prod_eq : Ps_inner.prod =
          ∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l) := by
        show (List.ofFn _).prod = _
        rw [List.prod_ofFn]
        -- Both products are over ∏ on different Fin types; relate via cast.
        apply Finset.prod_bij (fun l _ => Fin.cast h_len_eq.symm l)
        · intros; exact Finset.mem_univ _
        · intro l₁ _ l₂ _ heq; exact (Fin.cast_inj _).mp heq
        · intro l _; exact ⟨Fin.cast h_len_eq l, Finset.mem_univ _, by ext; rfl⟩
        · intro l _
          simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]
      rw [← h_prod_eq]
      have h_get_eq : ∀ (l : ℕ) (hl_Ps : l < Ps.length)
          (hl_map : l < (Ps.map fe).length)
          (hl : l < Ps_inner.length),
          Ps_inner.get ⟨l, hl⟩ =
            ((MvPolynomial.finSuccEquiv (MvPolynomial (Fin k) ℤ) ℓ)
              (Ps[l]'hl_Ps)).coeff (ds ⟨l, hl_map⟩) := by
        intro l hl_Ps hl_map hl
        show (List.ofFn _).get _ = _
        rw [List.get_ofFn]
        simp only [Fin.cast_mk]
        rfl
      have h_τ_inner : ∀ P ∈ Ps_inner, ∀ y' x',
          ((P.coeff y').coeff x').natAbs.size ≤ τ := by
        intro P hP y' x'
        rw [List.mem_iff_get] at hP
        obtain ⟨⟨l, hl⟩, rfl⟩ := hP
        have hl_Ps : l < Ps.length := h_Ps_inner_len ▸ hl
        have hl_map : l < (Ps.map fe).length := h_len_eq.symm ▸ hl_Ps
        rw [h_get_eq l hl_Ps hl_map hl]
        rw [MvPolynomial.finSuccEquiv_coeff_coeff]
        exact h_τ (Ps[l]'hl_Ps) (List.getElem_mem _) _ x'
      have h_q_inner : ∀ P ∈ Ps_inner, P.totalDegree ≤ q := by
        intro P hP
        rw [List.mem_iff_get] at hP
        obtain ⟨⟨l, hl⟩, rfl⟩ := hP
        have hl_Ps : l < Ps.length := h_Ps_inner_len ▸ hl
        have hl_map : l < (Ps.map fe).length := h_len_eq.symm ▸ hl_Ps
        rw [h_get_eq l hl_Ps hl_map hl]
        exact (totalDegree_coeff_finSuccEquiv_le _ _).trans
          (h_q (Ps[l]'hl_Ps) (List.getElem_mem _))
      have h_pX_inner : ∀ P ∈ Ps_inner, ∀ y',
          (P.coeff y').totalDegree ≤ p := by
        intro P hP y'
        rw [List.mem_iff_get] at hP
        obtain ⟨⟨l, hl⟩, rfl⟩ := hP
        have hl_Ps : l < Ps.length := h_Ps_inner_len ▸ hl
        have hl_map : l < (Ps.map fe).length := h_len_eq.symm ▸ hl_Ps
        rw [h_get_eq l hl_Ps hl_map hl]
        rw [MvPolynomial.finSuccEquiv_coeff_coeff]
        exact h_pX (Ps[l]'hl_Ps) (List.getElem_mem _) _
      have h_ih := ih k Ps_inner τ p q h_Ps_inner_ne h_τ_inner h_q_inner h_pX_inner
        y.tail x
      refine h_ih.trans ?_
      rw [hB_def, h_Ps_inner_len]
    -- Define `q_fn : Fin (Ps.map fe).length → ℕ` (uniform q).
    have h_map_len : (Ps.map fe).length = Ps.length := List.length_map _
    let q_fn : Fin (Ps.map fe).length → ℕ := fun _ => q
    -- Zero-summand argument: if some `ds l > q` then the entire summand is 0.
    have h_zero : ∀ ds ∈ Finset.Nat.antidiagonalTuple (Ps.map fe).length (y 0),
        (∃ l, ds l > q) →
        ((∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff y.tail).coeff x = 0 := by
      intro ds _ ⟨l, hl_gt⟩
      have hl_Ps : l.val < Ps.length := by rw [← h_map_len]; exact l.isLt
      have h_factor_zero : ((Ps.map fe).get l).coeff (ds l) = 0 := by
        rcases l with ⟨l, hl⟩
        simp only [List.get_eq_getElem, List.getElem_map]
        change ((MvPolynomial.finSuccEquiv (MvPolynomial (Fin k) ℤ) ℓ)
          (Ps[l])).coeff (ds ⟨l, hl⟩) = 0
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [MvPolynomial.natDegree_finSuccEquiv]
        exact lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree _ _)
          (lt_of_le_of_lt (h_q Ps[l] (List.getElem_mem _)) hl_gt)
      rw [Finset.prod_eq_zero (Finset.mem_univ l) h_factor_zero]
      simp
    -- Reduce sum to filtered subset.
    rw [show
      (∑ ds ∈ Finset.Nat.antidiagonalTuple (Ps.map fe).length (y 0),
        ((∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff y.tail).coeff x)
      = ∑ ds ∈ (Finset.Nat.antidiagonalTuple (Ps.map fe).length (y 0)).filter
          (fun ds => ∀ l, ds l ≤ q_fn l),
        ((∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff y.tail).coeff x from by
      apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro ds hds h_not_in
      rw [Finset.mem_filter, not_and_or] at h_not_in
      rcases h_not_in with h | h
      · exact absurd hds h
      · push Not at h
        exact h_zero ds hds h]
    -- Apply sharper Int.size_finset_sum_le' to filtered sum.
    have h_filtered_bound := Int.size_finset_sum_le'
      (s := (Finset.Nat.antidiagonalTuple (Ps.map fe).length (y 0)).filter
        (fun ds => ∀ l, ds l ≤ q_fn l))
      (f := fun ds => ((∏ l : Fin (Ps.map fe).length, ((Ps.map fe).get l).coeff (ds l)).coeff y.tail).coeff x)
      (B := B) (fun ds hds => h_summand_bound ds (Finset.mem_filter.mp hds).1)
    refine h_filtered_bound.trans ?_
    have h_card_le := card_antidiagonalTuple_filter_le
      (m := (Ps.map fe).length) (d := y 0) (ps := q_fn)
    have h_card_sub_le :
        ((Finset.Nat.antidiagonalTuple (Ps.map fe).length (y 0)).filter
          (fun ds => ∀ l, ds l ≤ q_fn l)).card - 1 ≤
        (∏ l, (q_fn l + 1)) - 1 := by omega
    have h_card_size_le :
        Nat.size (((Finset.Nat.antidiagonalTuple (Ps.map fe).length (y 0)).filter
          (fun ds => ∀ l, ds l ≤ q_fn l)).card - 1) ≤
          ∑ l, Nat.size (q_fn l) :=
      (Nat.size_le_size h_card_sub_le).trans (Nat.size_prod_succ_sub_one_le q_fn)
    have h_sum_const : (∑ l : Fin (Ps.map fe).length, Nat.size (q_fn l)) =
        (Ps.map fe).length * Nat.size q := by
      simp [q_fn, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [h_sum_const] at h_card_size_le
    rw [hB_def]
    have h_target_expand :
        Ps.length * (τ + k * Nat.size p + (ℓ + 1) * Nat.size q) =
        Ps.length * (τ + k * Nat.size p + ℓ * Nat.size q) +
          Ps.length * Nat.size q := by ring
    rw [h_target_expand]
    have h_step :
        (Ps.map fe).length * Nat.size q ≤ Ps.length * Nat.size q := by
      rw [h_map_len]
    exact le_trans (Nat.add_le_add_left h_card_size_le _)
      (Nat.add_le_add_left h_step _)

end Azurite.BPR

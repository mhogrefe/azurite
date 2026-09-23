import Azurite.BasuPollackRoy.Chapter8.Section8_3.SignedSubresultant

/-!
# BPR §8.3.3: Structure Theorem for Signed Subresultants — row-operation toolkit

Ring-level analogues of BPR Lemma 8.28 for the polynomial determinant `pdetRing`,
which the structure theorem (Proposition 8.39) invokes repeatedly:

* `pdetRing_update_add_smul` — adding a `D`-multiple of one row to another (distinct)
  row leaves `pdet` unchanged;
* `pdetRing_update_smul` — scaling a row by `s : D` multiplies `pdet` by `s`;
* `pdetRing_update_neg` — negating a row negates `pdet`.

(Reversal of the family, the third use of Lemma 8.28, is `pdetRing_comp_perm`.)
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {D : Type*} [CommRing D]

/-- **BPR Lemma 8.32.** If `m ≥ 2` and every polynomial of the family has degree
    `< n - 1`, then `pdet_{m,n}(𝒫) = 0`: the first coefficient column of every minor
    (the `X^{n-1}`-coefficients) is zero. -/
theorem pdetRing_eq_zero_of_degree_lt {m n : ℕ} (hm : 2 ≤ m) (P : Fin m → D[X])
    (hdeg : ∀ r, (P r).degree < (↑(n - 1) : WithBot ℕ)) : pdetRing n P = 0 := by
  rw [pdetRing]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [pdetMinorRing]
  have hzero : ∀ r, pdetMinorMatRing n P (i : ℕ) r (⟨0, by omega⟩ : Fin m) = 0 := by
    intro r
    rw [pdetMinorMatRing, pdetColIdx, ite_eq_left (by show 0 + 1 < m; omega)]
    exact Polynomial.coeff_eq_zero_of_degree_lt (hdeg r)
  rw [Matrix.det_eq_zero_of_column_eq_zero _ hzero, zero_smul]

/-- **Ring Lemma 8.28 (row addition).** Adding a `D`-multiple of one row of the family
    to another, distinct row does not change the polynomial determinant. -/
theorem pdetRing_update_add_smul {m n : ℕ} (P : Fin m → D[X]) {i j : Fin m} (hij : i ≠ j)
    (c : D) : pdetRing n (Function.update P i (P i + c • P j)) = pdetRing n P := by
  rw [pdetRing, pdetRing]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  rw [pdetMinorRing, pdetMinorRing]
  have hmat : pdetMinorMatRing n (Function.update P i (P i + c • P j)) (k : ℕ)
      = (pdetMinorMatRing n P (k : ℕ)).updateRow i
          ((pdetMinorMatRing n P (k : ℕ)) i + c • (pdetMinorMatRing n P (k : ℕ)) j) := by
    ext r c'
    by_cases hr : r = i
    · subst hr
      simp [pdetMinorMatRing, Matrix.updateRow_apply, Function.update_self,
        Polynomial.coeff_add, Polynomial.coeff_smul]
    · simp [pdetMinorMatRing, Matrix.updateRow_apply, hr]
  rw [hmat, Matrix.det_updateRow_add_smul_self (pdetMinorMatRing n P (k : ℕ)) hij c]

/-- Adding a `D`-linear combination of other (distinct from `j`) rows of the family to
    row `j` does not change the polynomial determinant (iterated ring Lemma 8.28). -/
theorem pdetRing_update_add_combination {m n : ℕ} (P : Fin m → D[X]) (j : Fin m)
    (s : Finset (Fin m)) (lam : Fin m → D) :
    j ∉ s → pdetRing n (Function.update P j (P j + ∑ i ∈ s, lam i • P i)) = pdetRing n P := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simp [Function.update_eq_self]
  | insert a t ha ih =>
    intro hj
    rw [Finset.mem_insert, not_or] at hj
    rw [Finset.sum_insert ha]
    have key : Function.update P j (P j + (lam a • P a + ∑ i ∈ t, lam i • P i))
        = Function.update (Function.update P j (P j + ∑ i ∈ t, lam i • P i)) j
            ((Function.update P j (P j + ∑ i ∈ t, lam i • P i)) j
              + lam a • (Function.update P j (P j + ∑ i ∈ t, lam i • P i)) a) := by
      rw [Function.update_idem, Function.update_self, Function.update_of_ne (Ne.symm hj.1)]
      congr 1
      ring
    rw [key, pdetRing_update_add_smul _ hj.1 (lam a)]
    exact ih hj.2

/-- Index-function form of `pdetRing_update_add_combination`: adding
    `∑_{a ∈ t} lam a • P (idx a)` to row `j` (all `idx a ≠ j`) leaves `pdet` unchanged. -/
theorem pdetRing_update_add_combination' {m n : ℕ} {ι : Type*} (P : Fin m → D[X]) (j : Fin m)
    (t : Finset ι) (idx : ι → Fin m) (lam : ι → D) :
    (∀ a ∈ t, idx a ≠ j) →
      pdetRing n (Function.update P j (P j + ∑ a ∈ t, lam a • P (idx a))) = pdetRing n P := by
  classical
  induction t using Finset.induction with
  | empty => intro _; simp [Function.update_eq_self]
  | insert a s ha ih =>
    intro hj
    rw [Finset.forall_mem_insert] at hj
    rw [Finset.sum_insert ha]
    have key : Function.update P j (P j + (lam a • P (idx a) + ∑ b ∈ s, lam b • P (idx b)))
        = Function.update (Function.update P j (P j + ∑ b ∈ s, lam b • P (idx b))) j
            ((Function.update P j (P j + ∑ b ∈ s, lam b • P (idx b))) j
              + lam a • (Function.update P j (P j + ∑ b ∈ s, lam b • P (idx b))) (idx a)) := by
      rw [Function.update_idem, Function.update_self, Function.update_of_ne hj.1]
      congr 1; ring
    rw [key, pdetRing_update_add_smul _ hj.1.symm (lam a)]
    exact ih hj.2

/-- **Ring Lemma 8.28 (row scaling).** Scaling a row of the family by `s : D` multiplies
    the polynomial determinant by `s`. -/
theorem pdetRing_update_smul {m n : ℕ} (P : Fin m → D[X]) (j : Fin m) (s : D) :
    pdetRing n (Function.update P j (s • P j)) = s • pdetRing n P := by
  have hmr : ∀ k : ℕ, pdetMinorRing n (Function.update P j (s • P j)) k
      = s * pdetMinorRing n P k := by
    intro k
    rw [pdetMinorRing, pdetMinorRing]
    have hmat : pdetMinorMatRing n (Function.update P j (s • P j)) k
        = (pdetMinorMatRing n P k).updateRow j (s • (pdetMinorMatRing n P k) j) := by
      ext r c'
      by_cases hr : r = j
      · subst hr
        simp [pdetMinorMatRing, Matrix.updateRow_apply, Function.update_self,
          Polynomial.coeff_smul]
      · simp [pdetMinorMatRing, Matrix.updateRow_apply, hr]
    rw [hmat, Matrix.det_updateRow_smul (pdetMinorMatRing n P k) j s (pdetMinorMatRing n P k j),
      Matrix.updateRow_eq_self]
  rw [pdetRing, pdetRing]
  have hsum : s • (∑ k : Fin (n - m + 1), pdetMinorRing n P (k : ℕ) • (X : D[X]) ^ (k : ℕ))
      = ∑ k : Fin (n - m + 1), s • (pdetMinorRing n P (k : ℕ) • (X : D[X]) ^ (k : ℕ)) :=
    Finset.smul_sum
  rw [hsum]
  exact Finset.sum_congr rfl (fun k _ => by rw [hmr, mul_smul])

/-- **Ring Lemma 8.28 (row negation).** Negating a row of the family negates the
    polynomial determinant. -/
theorem pdetRing_update_neg {m n : ℕ} (P : Fin m → D[X]) (j : Fin m) :
    pdetRing n (Function.update P j (-P j)) = -pdetRing n P := by
  have h := pdetRing_update_smul (n := n) P j (-1 : D)
  rw [neg_one_smul, neg_one_smul] at h
  exact h

/-- Transport `pdetRing` across an equality of the (index) cardinality. -/
theorem pdetRing_congr_cast {m m' n : ℕ} (hm : m = m') (f : Fin m → D[X]) (g : Fin m' → D[X])
    (h : ∀ i : Fin m, f i = g (Fin.cast hm i)) : pdetRing n f = pdetRing n g := by
  subst hm
  exact congrArg (pdetRing n) (funext h)

/-- Negating the rows of the family indexed by a finite set `s` multiplies the
    polynomial determinant by `(-1)^{|s|}`. -/
theorem pdetRing_neg_rows {m n : ℕ} (P : Fin m → D[X]) (s : Finset (Fin m)) :
    pdetRing n (fun r => if r ∈ s then -(P r) else P r) = (-1 : ℤ) ^ s.card • pdetRing n P := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    have key : (fun r => if r ∈ insert a t then -(P r) else P r)
        = Function.update (fun r => if r ∈ t then -(P r) else P r) a
            (-((fun r => if r ∈ t then -(P r) else P r) a)) := by
      ext r
      by_cases hr : r = a
      · subst hr; simp [Finset.mem_insert, ha]
      · simp [Finset.mem_insert, hr]
    rw [key, pdetRing_update_neg, ih, Finset.card_insert_of_notMem ha, pow_succ, mul_neg_one,
      neg_smul]

end Azurite.BPR.Chapter8

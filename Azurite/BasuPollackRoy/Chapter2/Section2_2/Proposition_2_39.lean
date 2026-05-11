import Azurite.BasuPollackRoy.Chapter2.Section2_1.Factorization
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34

/-!
# BPR Proposition 2.39: monic with non-positive real part roots ⇒ `Var(P) = 0`

**Proposition 2.39 (BPR).** Let `P ∈ R[X]` be a monic polynomial over a real
closed field `R`. If all the roots of `P` (in the algebraic closure
`R[i] = Ri R`) have non-positive real part, then `Var(P) = 0`.

**Proof.** Using the factorization of `P` into products of linear factors
`X − a` (real root `a`) and quadratics `(X − c)² + d²` (complex conjugate
roots `c ± id`) from `Factorization.lean`, the assumption gives `a ≤ 0` and
`c ≤ 0`. Each such factor has non-negative coefficients, and products of
polynomials with non-negative coefficients have non-negative coefficients.
Hence all coefficients of `P` are non-negative, so `Var(P) = 0`.
-/

namespace Azurite.BPR.Proposition2_39

open Polynomial Azurite.BPR Azurite.BPR.Factorization

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Product of polynomials with non-negative coefficients has non-negative
    coefficients. -/
lemma coeff_mul_nonneg {A B : R[X]}
    (hA : ∀ i, 0 ≤ A.coeff i) (hB : ∀ i, 0 ≤ B.coeff i) (k : ℕ) :
    0 ≤ (A * B).coeff k := by
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hA _) (hB _))

/-- If `a ≤ 0`, the coefficients of `X − C a` are non-negative: the constant
    term is `-a ≥ 0`, the linear coefficient is `1`, higher coefficients are
    `0`. -/
lemma linearFactor_coeff_nonneg {a : R} (ha : a ≤ 0) :
    ∀ k, 0 ≤ (linearFactor a).coeff k := by
  intro k
  unfold linearFactor
  match k with
  | 0 =>
    rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_nonneg]
    exact ha
  | 1 =>
    rw [coeff_sub, coeff_X_one, coeff_C, if_neg one_ne_zero, sub_zero]
    exact zero_le_one
  | n + 2 =>
    rw [coeff_sub, coeff_X, coeff_C]
    simp

/-- If `c ≤ 0`, the coefficients of `(X − C c)² + C (d²)` are non-negative:
    - constant term is `c² + d² ≥ 0`
    - linear coefficient is `−2c ≥ 0` since `c ≤ 0`
    - `X²`-coefficient is `1`
    - higher coefficients are `0`. -/
lemma quadraticFactor_coeff_nonneg {c d : R} (hc : c ≤ 0) :
    ∀ k, 0 ≤ (quadraticFactor (c, d)).coeff k := by
  have hexpand : quadraticFactor (c, d) =
      X ^ 2 + C (-(2 * c)) * X + C (c ^ 2 + d ^ 2) := by
    show (X - C c) ^ 2 + C (d ^ 2) = _
    rw [show (X - C c : R[X]) = X + C (-c) from by rw [map_neg]; ring]
    rw [show (X + C (-c) : R[X]) ^ 2 =
        X ^ 2 + C (-c + -c) * X + C ((-c) * (-c)) from by
      rw [map_add, map_mul]; ring]
    rw [show (-c + -c : R) = -(2 * c) from by ring]
    rw [show ((-c) * (-c) : R) = c ^ 2 from by ring]
    rw [show C (c ^ 2 + d ^ 2) = C (c ^ 2) + C (d ^ 2) from map_add C _ _]
    ring
  intro k
  rw [hexpand, coeff_add, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  match k with
  | 0 =>
    simp only [Nat.reduceEqDiff, if_false, mul_zero, add_zero, if_true]
    positivity
  | 1 =>
    simp only [Nat.reduceEqDiff, if_false, mul_one, if_true, zero_add]
    linarith
  | 2 =>
    simp only [Nat.reduceEqDiff, if_false, mul_zero, add_zero, if_true]
    exact zero_le_one
  | n + 3 =>
    have h1 : (n + 3 = 2) = False := by simp
    have h2 : (1 = n + 3) = False := by simp
    have h3 : (n + 3 = 0) = False := by simp
    simp only [h1, h2, h3, if_false, mul_zero, add_zero, le_refl]

/-- The product of a multiset of linear factors `X − a` with all `a ≤ 0` has
    non-negative coefficients. -/
lemma linears_prod_coeff_nonneg {linears : Multiset R}
    (h : ∀ a ∈ linears, a ≤ 0) :
    ∀ k, 0 ≤ ((linears.map linearFactor).prod).coeff k := by
  induction linears using Multiset.induction with
  | empty =>
    intro k
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs <;> simp
  | cons a s ih =>
    intro k
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine coeff_mul_nonneg ?_ ?_ k
    · exact linearFactor_coeff_nonneg (h a (Multiset.mem_cons_self _ _))
    · exact ih (fun a' ha' => h a' (Multiset.mem_cons_of_mem ha'))

/-- The product of a multiset of quadratic factors `(X − c)² + d²` with all
    `c ≤ 0` has non-negative coefficients. -/
lemma quadratics_prod_coeff_nonneg {quadratics : Multiset (R × R)}
    (h : ∀ pq ∈ quadratics, pq.1 ≤ 0) :
    ∀ k, 0 ≤ ((quadratics.map quadraticFactor).prod).coeff k := by
  induction quadratics using Multiset.induction with
  | empty =>
    intro k
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs <;> simp
  | cons pq s ih =>
    intro k
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine coeff_mul_nonneg ?_ ?_ k
    · exact quadraticFactor_coeff_nonneg (h pq (Multiset.mem_cons_self _ _))
    · exact ih (fun pq' hpq' => h pq' (Multiset.mem_cons_of_mem hpq'))

/-- If every coefficient of `P` is non-negative, then `varPoly P = 0`. -/
lemma varPoly_eq_zero_of_coeff_nonneg {P : R[X]}
    (h : ∀ k, 0 ≤ P.coeff k) : varPoly P = 0 := by
  unfold varPoly
  apply Var_eq_zero_of_forall_nonneg
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨k, _, hk⟩ := hx
  rw [← hk]
  exact h k

/-- Helper: if `P` factors as a product of linear factors `X − a` with `a ≤ 0`
    and quadratic factors `(X − c)² + d²` with `c ≤ 0`, then `varPoly P = 0`. -/
theorem proposition_2_39_of_factorization
    {P : R[X]}
    {linears : Multiset R} {quadratics : Multiset (R × R)}
    (hfact : P = (linears.map linearFactor).prod *
                 (quadratics.map quadraticFactor).prod)
    (h_linears_nonpos : ∀ a ∈ linears, a ≤ 0)
    (h_quadratics_nonpos : ∀ pq ∈ quadratics, pq.1 ≤ 0) :
    varPoly P = 0 := by
  apply varPoly_eq_zero_of_coeff_nonneg
  intro k
  rw [hfact]
  exact coeff_mul_nonneg (linears_prod_coeff_nonneg h_linears_nonpos)
    (quadratics_prod_coeff_nonneg h_quadratics_nonpos) k

/-- **BPR Proposition 2.39.** Let `R` be a real closed field and `P ∈ R[X]`
    be a monic polynomial. If for every pair `a, b : R` such that
    `ι a + ι b · i` is a root of `P` (where `ι : R → Ri R` is the algebra
    map), we have `a ≤ 0`, then `varPoly P = 0`.

    The hypothesis says: every root of `P` in `Ri R = R[i]` has non-positive
    real part — since every element of `Ri R` is of the form `ι a + ι b · i`,
    the predicate form covers all roots. -/
theorem proposition_2_39
    {R : Type*} [Field R] [IsRealClosed R] [DecidableEq R] {P : R[X]}
    (hP : P.Monic)
    (h_nonpos : ∀ a b : R,
        aeval (algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) P = 0 →
        a ≤ 0) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    varPoly P = 0 := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  obtain ⟨linears, quadratics, _hqs_d, hfact⟩ := exists_factorization P
  rw [hP.leadingCoeff, map_one, one_mul] at hfact
  -- hfact : P = (linears.map linearFactor).prod * (quadratics.map quadraticFactor).prod
  refine proposition_2_39_of_factorization hfact ?_ ?_
  · intro a ha
    apply h_nonpos a 0
    rw [map_zero, zero_mul, add_zero, hfact, map_mul,
      aeval_linearFactor_prod_of_mem ha, zero_mul]
  · rintro ⟨c, d⟩ hpq
    apply h_nonpos c d
    rw [hfact, map_mul, aeval_quadraticFactor_prod_of_mem hpq, mul_zero]

end Azurite.BPR.Proposition2_39

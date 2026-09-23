import Azurite.BasuPollackRoy.Chapter2.Section2_1.Factorization
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_41
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_42
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_43

/-!
# BPR Proposition 2.40: monic with all roots in `ConeB` ⇒ `P` is normal

**Proposition 2.40 (BPR).** Let `P ∈ R[X]` be a monic polynomial over a real
closed field `R`. If every root of `P` (in `R[i] = Ri R`) lies in the cone
`𝓑 = {a + ib : |b| ≤ -√3 · a}`, then `P` is normal.

**Proof.** Factor `P` into linear factors `X − a` and quadratic factors
`(X − c)² + d² = quadFromRoots c d`. By Lemma 2.41 each `X − a` is normal
(since `(a, 0) ∈ 𝓑` gives `a ≤ 0`). By Lemma 2.42 each `quadFromRoots c d`
is normal (since `(c, d) ∈ 𝓑`). By Lemma 2.43 (product of normals is
normal), `P` is normal.
-/

namespace Azurite.BPR.Proposition2_40

open Polynomial Azurite.BPR Azurite.BPR.Factorization

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `quadraticFactor (c, d) = quadFromRoots c d`: the two BPR representations
    of the monic quadratic with complex-conjugate roots agree. -/
private lemma quadraticFactor_eq_quadFromRoots (c d : R) :
    quadraticFactor (c, d) = quadFromRoots c d := by
  show (X - C c) ^ 2 + C (d ^ 2) = X ^ 2 - C (2 * c) * X + C (c ^ 2 + d ^ 2)
  simp only [map_mul, map_add, map_pow, C_ofNat]
  ring

/-- The polynomial `1 : R[X]` is normal (base case for empty products). -/
lemma isNormal_one : IsNormal (1 : R[X]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [coeff_one]
    split_ifs
    · exact zero_le_one
    · exact le_refl 0
  · rw [leadingCoeff_one]; exact zero_lt_one
  · intro k
    simp only [coeff_one]
    split_ifs <;> simp
  · rintro j h hjh hj hh i hji hih
    rw [coeff_one] at hj hh
    split_ifs at hj with hj0
    · subst hj0
      split_ifs at hh with hh0
      · subst hh0; omega
      · exact absurd hh (lt_irrefl 0)
    · exact absurd hj (lt_irrefl 0)

/-- Product of linear factors `X − a` with all `a ≤ 0` is normal. -/
theorem isNormal_prod_linearFactor {linears : Multiset R}
    (h : ∀ a ∈ linears, a ≤ 0) :
    IsNormal (linears.map linearFactor).prod := by
  induction linears using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact isNormal_one
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine isNormal_mul ?_ (ih fun a' ha' => h a' (Multiset.mem_cons_of_mem ha'))
    unfold linearFactor
    exact isNormal_X_sub_C_iff.mpr (h a (Multiset.mem_cons_self _ _))

/-- Product of quadratic factors `(X − c)² + d²` with all pairs in `𝓑` is normal. -/
theorem isNormal_prod_quadraticFactor {quadratics : Multiset (R × R)}
    (h : ∀ pq ∈ quadratics, pq ∈ ConeB) :
    IsNormal (quadratics.map quadraticFactor).prod := by
  induction quadratics using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact isNormal_one
  | cons pq s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine isNormal_mul ?_ (ih fun pq' hpq' => h pq' (Multiset.mem_cons_of_mem hpq'))
    obtain ⟨c, d⟩ := pq
    rw [quadraticFactor_eq_quadFromRoots]
    exact (isNormal_quadFromRoots_iff c d).mpr (h (c, d) (Multiset.mem_cons_self _ _))

/-- **BPR Proposition 2.40** (factorization form). If `P` factors as a product
    of linear factors `X − a` with `a ≤ 0` and quadratic factors
    `quadraticFactor (c, d)` with `(c, d) ∈ 𝓑`, then `P` is normal. -/
theorem proposition_2_40_of_factorization
    {P : R[X]}
    {linears : Multiset R} {quadratics : Multiset (R × R)}
    (hfact : P = (linears.map linearFactor).prod *
                 (quadratics.map quadraticFactor).prod)
    (h_linears : ∀ a ∈ linears, a ≤ 0)
    (h_quadratics : ∀ pq ∈ quadratics, pq ∈ ConeB) :
    IsNormal P := by
  rw [hfact]
  exact isNormal_mul (isNormal_prod_linearFactor h_linears)
    (isNormal_prod_quadraticFactor h_quadratics)

/-- **BPR Proposition 2.40.** Let `R` be a real closed field and `P ∈ R[X]` be
    a monic polynomial. If for every `a, b : R` such that `ι a + ι b · i` is a
    root of `P` (in `Ri R`), the pair `(a, b)` lies in `𝓑`, then `P` is normal.

    Since every element of `Ri R` is of the form `ι a + ι b · i` by
    `Ri.repr_exists`, the predicate form covers all roots. -/
theorem proposition_2_40
    {R : Type*} [Field R] [IsRealClosed R] [DecidableEq R] {P : R[X]}
    (hP : P.Monic)
    (h_coneB : ∀ a b : R,
        aeval (algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) P = 0 →
        (a, b) ∈ ConeB) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    IsNormal P := by
  let : LinearOrder R := IsRealClosed.toLinearOrder
  let : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  have : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  obtain ⟨linears, quadratics, _hqs_d, hfact⟩ := exists_factorization P
  rw [hP.leadingCoeff, map_one, one_mul] at hfact
  refine proposition_2_40_of_factorization hfact ?_ ?_
  · intro a ha
    have hroot :
        aeval (algebraMap R (Ri R) a + algebraMap R (Ri R) 0 * Ri.i R) P = 0 := by
      rw [map_zero, zero_mul, add_zero, hfact, map_mul,
        aeval_linearFactor_prod_of_mem ha, zero_mul]
    exact (h_coneB a 0 hroot).1
  · rintro ⟨c, d⟩ hpq
    apply h_coneB c d
    rw [hfact, map_mul, aeval_quadraticFactor_prod_of_mem hpq, mul_zero]

end Azurite.BPR.Proposition2_40

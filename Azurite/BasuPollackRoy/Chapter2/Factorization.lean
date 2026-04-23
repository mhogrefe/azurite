import Azurite.BasuPollackRoy.Chapter2.Proposition_2_19

/-!
# Polynomial factorization over a real closed field

**Corollary of BPR Proposition 2.19.** Over a real closed field `R`, every
nonzero polynomial factors as
`P = C P.leadingCoeff · ∏ (X − aᵢ) · ∏ ((X − cⱼ)² + dⱼ²)` with `dⱼ ≠ 0`.

We state this via two multisets: `linears : Multiset R` listing the real roots
(with multiplicity) and `quadratics : Multiset (R × R)` listing pairs `(c, d)`
with `d ≠ 0` for each irreducible quadratic factor `(X − c)² + d²`.
-/

namespace Azurite.BPR.Factorization

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_11 Azurite.BPR.Proposition2_19

variable {R : Type*} [Field R]

/-- The linear factor corresponding to a real root. -/
noncomputable def linearFactor (a : R) : R[X] := X - C a

/-- The irreducible quadratic factor `(X − c)² + d²`. -/
noncomputable def quadraticFactor (cd : R × R) : R[X] := (X - C cd.1) ^ 2 + C (cd.2 ^ 2)

/-- Split a multiset of "linear-or-irreducible-quadratic" monic polynomials
    into two multisets: real roots (linears) and `(c, d)` pairs (quadratics). -/
lemma exists_split_multiset (m : Multiset R[X])
    (h : ∀ q ∈ m, (∃ a : R, q = linearFactor a) ∨
        (∃ c d : R, d ≠ 0 ∧ q = quadraticFactor (c, d))) :
    ∃ (linears : Multiset R) (quadratics : Multiset (R × R)),
      (∀ pq ∈ quadratics, pq.2 ≠ 0) ∧
      m.prod = (linears.map linearFactor).prod *
               (quadratics.map quadraticFactor).prod := by
  induction m using Multiset.induction with
  | empty => exact ⟨0, 0, by simp, by simp⟩
  | cons q m ih =>
    have h' : ∀ q' ∈ m, (∃ a : R, q' = linearFactor a) ∨
        (∃ c d : R, d ≠ 0 ∧ q' = quadraticFactor (c, d)) :=
      fun q' hq' => h q' (Multiset.mem_cons_of_mem hq')
    obtain ⟨ls, qs, hqs_d, heq⟩ := ih h'
    rcases h q (Multiset.mem_cons_self _ _) with ⟨a, ha⟩ | ⟨c, d, hd, hcd⟩
    · refine ⟨a ::ₘ ls, qs, hqs_d, ?_⟩
      rw [Multiset.prod_cons, ha, Multiset.map_cons, Multiset.prod_cons, heq,
          mul_assoc]
    · refine ⟨ls, (c, d) ::ₘ qs, ?_, ?_⟩
      · intro pq hpq
        rcases Multiset.mem_cons.mp hpq with h1 | h1
        · rw [h1]; exact hd
        · exact hqs_d _ h1
      · rw [Multiset.prod_cons, hcd, Multiset.map_cons, Multiset.prod_cons, heq]
        ring

/-- **Factorization over a real closed field.** Every polynomial `P` over a
    real closed field factors as `C P.leadingCoeff` times a product of real
    linear factors `X − aᵢ` and irreducible quadratic factors `(X − cⱼ)² + dⱼ²`
    with `dⱼ ≠ 0`. -/
theorem exists_factorization [IsRealClosed R] [DecidableEq R] (P : R[X]) :
    ∃ (linears : Multiset R) (quadratics : Multiset (R × R)),
      (∀ pq ∈ quadratics, pq.2 ≠ 0) ∧
      P = C P.leadingCoeff *
          (linears.map linearFactor).prod *
          (quadratics.map quadraticFactor).prod := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  by_cases hP : P = 0
  · refine ⟨0, 0, by simp, ?_⟩
    rw [hP, leadingCoeff_zero, map_zero, zero_mul, zero_mul]
  -- Normalized factors are monic irreducibles; each is linear or quadratic.
  have hfactors : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors P,
      (∃ a : R, q = linearFactor a) ∨
      (∃ c d : R, d ≠ 0 ∧ q = quadraticFactor (c, d)) := by
    intro q hq
    rw [Polynomial.mem_normalizedFactors_iff hP] at hq
    obtain ⟨hirr, hmon, _⟩ := hq
    rcases proposition_2_19_of_isRealClosed hirr hmon with hdeg | ⟨c, d, hd, hcd⟩
    · left
      refine ⟨-q.coeff 0, ?_⟩
      rw [linearFactor, show (X - C (-q.coeff 0) : R[X]) = X + C (q.coeff 0) from by
        rw [C_neg, sub_neg_eq_add]]
      exact hmon.eq_X_add_C hdeg
    · right
      exact ⟨c, d, hd, hcd⟩
  obtain ⟨ls, qs, hqs, heq⟩ := exists_split_multiset _ hfactors
  refine ⟨ls, qs, hqs, ?_⟩
  have hprod := Polynomial.leadingCoeff_mul_prod_normalizedFactors P
  rw [heq, ← mul_assoc] at hprod
  exact hprod.symm

/-! ## Root evaluation of the factor polynomials in `R[i]`

These lemmas record that each linear/quadratic factor vanishes at its
corresponding root in `Ri R`, and propagate the evaluation to the product
of factors via `Multiset.dvd_prod`. Downstream propositions (2.39, 2.40)
use these to translate a root-based hypothesis on `P` into a factor-based
hypothesis on the decomposition. -/

/-- The real root `a` is a root of `linearFactor a = X − C a` in `Ri R`. -/
theorem aeval_linearFactor_self (a : R) :
    aeval (algebraMap R (Ri R) a) (linearFactor a) = 0 := by
  unfold linearFactor
  rw [map_sub, aeval_X, aeval_C]
  exact sub_self _

/-- The complex root `c + di` is a root of `quadraticFactor (c, d) = (X − C c)² + C d²`
    in `Ri R`. -/
theorem aeval_quadraticFactor_root (c d : R) :
    aeval (algebraMap R (Ri R) c + algebraMap R (Ri R) d * Ri.i R)
      (quadraticFactor (c, d)) = 0 := by
  show aeval _ ((X - C c) ^ 2 + C (d ^ 2)) = 0
  rw [map_add, map_pow, map_sub, aeval_X, aeval_C, aeval_C]
  set ι := algebraMap R (Ri R)
  have hsub : (ι c + ι d * Ri.i R) - ι c = ι d * Ri.i R := by ring
  rw [hsub, mul_pow, Ri.i_sq]
  rw [show ι d ^ 2 * -1 + ι (d ^ 2) = ι d ^ 2 * -1 + ι d ^ 2 from by
    rw [map_pow]]
  ring

/-- If `a ∈ linears`, then `ι a` is a root of the product of linear factors. -/
theorem aeval_linearFactor_prod_of_mem {linears : Multiset R} {a : R}
    (ha : a ∈ linears) :
    aeval (algebraMap R (Ri R) a) ((linears.map linearFactor).prod) = 0 := by
  have hmem : linearFactor a ∈ linears.map linearFactor :=
    Multiset.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨Q, hQ⟩ := Multiset.dvd_prod hmem
  rw [hQ, map_mul, aeval_linearFactor_self, zero_mul]

/-- If `(c, d) ∈ quadratics`, then `ι c + ι d · i` is a root of the product of
    quadratic factors. -/
theorem aeval_quadraticFactor_prod_of_mem {quadratics : Multiset (R × R)}
    {c d : R} (hcd : (c, d) ∈ quadratics) :
    aeval (algebraMap R (Ri R) c + algebraMap R (Ri R) d * Ri.i R)
      ((quadratics.map quadraticFactor).prod) = 0 := by
  have hmem : quadraticFactor (c, d) ∈ quadratics.map quadraticFactor :=
    Multiset.mem_map.mpr ⟨(c, d), hcd, rfl⟩
  obtain ⟨Q, hQ⟩ := Multiset.dvd_prod hmem
  rw [hQ, map_mul, aeval_quadraticFactor_root, zero_mul]

end Azurite.BPR.Factorization

import Azurite.BasuPollackRoy.Chapter4.Section4_3.Corollary_4_45
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Remark_2_38
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula

/-!
# BPR §8.2.4 Proposition 8.24: signature of a quadratic form via Descartes' rule

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.2.4.

**Proposition 8.24.** Let `Φ` be a quadratic form with associated symmetric
matrix `M` of size `n`, with entries in a real closed field `R`, and let
`CharPol(M) = det(X·Idₙ − M) = Xⁿ + a_{n−1}Xⁿ⁻¹ + ⋯ + a₀` be its characteristic
polynomial. Then
`Sign(M) = Var(1, a_{n−1}, …, a₀) − Var((−1)ⁿ, (−1)ⁿ⁻¹a_{n−1}, …, a₀)`.

*Proof.* All roots of the characteristic polynomial of a symmetric matrix belong
to `R` (Theorem 4.43), so Descartes' rule of signs (Proposition 2.33) is exact
(Remark 2.38): the sign-variation count `Var(1, a_{n−1}, …, a₀)` of the
coefficient sequence equals the number of positive roots, and
`Var((−1)ⁿ, …, a₀)`—the variation count of the coefficients of `CharPol(M)(−X)`—
equals the number of positive roots of `CharPol(M)(−X)`, i.e. the number of
negative roots of `CharPol(M)`. By Corollary 4.45 the signature is the difference
of these two counts.

**Encoding.** The coefficient sign-variation count `Var(a₀, …, aₙ)` is BPR
Notation 2.34, formalized as `varPoly` (`Var` of the coefficient list); it is
invariant under reversal, so `varPoly (CharPol M)` is exactly BPR's
`Var(1, a_{n−1}, …, a₀)`. The second variation count `Var((−1)ⁿ, …, a₀)` is
`varPoly (CharPol(M).comp (−X))`, since the coefficient of `Xⁱ` in
`CharPol(M)(−X)` is `(−1)ⁱ aᵢ`. Thus the proposition reads
`Sign (quadraticForm M) = varPoly (M.charpoly) − varPoly (M.charpoly.comp (−X))`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial Azurite.BPR

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- **BPR Proposition 8.24.** The signature of the quadratic form of a symmetric
    matrix `M` over a real closed field equals the difference of the sign-variation
    counts of the coefficient sequences of `CharPol(M)` and `CharPol(M)(−X)`. -/
theorem proposition_8_24 (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm) :
    Sign (quadraticForm M)
      = (varPoly M.charpoly : ℤ) - varPoly (M.charpoly.comp (-Polynomial.X)) := by
  classical
  obtain ⟨_, hsign, hpartition⟩ := corollary_4_45 M hM
  -- `CharPol(M)` is monic of degree `n`, and (Theorem 4.43) all its roots are real.
  have hcharne : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Trichotomy partition of the root multiset.
  have hmulti : M.charpoly.roots.filter (0 < ·) + M.charpoly.roots.filter (· < 0)
      + M.charpoly.roots.filter (· = 0) = M.charpoly.roots := by
    ext x
    simp only [Multiset.count_add, Multiset.count_filter]
    rcases lt_trichotomy x 0 with h | h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg h.ne]; omega
    · subst h; simp
    · rw [if_pos h, if_neg (not_lt.mpr h.le), if_neg h.ne']; omega
  have hcard : M.charpoly.roots.card = n := by
    conv_lhs => rw [← hmulti]
    rw [Multiset.card_add, Multiset.card_add]
    exact hpartition
  have hcard1 : M.charpoly.roots.card = M.charpoly.natDegree := by rw [hcard, hdeg]
  -- The negated polynomial `Q = CharPol(M)(−X)`.
  set Q := M.charpoly.comp (-Polynomial.X) with hQ
  have hQne : Q ≠ 0 := by
    rw [hQ, Ne, Polynomial.comp_eq_zero_iff]
    push Not
    refine ⟨hcharne, fun _ => ?_⟩
    intro hX
    rw [Polynomial.coeff_neg, Polynomial.coeff_X_zero, neg_zero, map_zero] at hX
    exact Polynomial.X_ne_zero (neg_eq_zero.mp hX)
  have hQdeg : Q.natDegree = n := by
    rw [hQ, Polynomial.natDegree_comp]
    simp [hdeg]
  have hQroots : Q.roots = M.charpoly.roots.map (fun x => -x) := by
    rw [hQ]; exact Polynomial.roots_comp_neg_X M.charpoly
  have hQcard1 : Q.roots.card = Q.natDegree := by
    rw [hQroots, Multiset.card_map, hcard, hQdeg]
  have hIVP : HasIntermediateValueProperty R := hasIVP_of_isRealClosed
  -- Descartes is exact for both polynomials.
  have hvp1 : varPoly M.charpoly = posRoots M.charpoly :=
    Theorem2_35.varPoly_eq_posRoots_of_all_roots_real hIVP hcharne hcard1
  have hvp2 : varPoly Q = posRoots Q :=
    Theorem2_35.varPoly_eq_posRoots_of_all_roots_real hIVP hQne hQcard1
  -- `posRoots (CharPol M) = #positive roots`, `posRoots Q = #negative roots of CharPol M`.
  have hposM : posRoots M.charpoly = (M.charpoly.roots.filter (0 < ·)).card := rfl
  have hposQ : posRoots Q = (M.charpoly.roots.filter (· < 0)).card := by
    show (Q.roots.filter (fun x => 0 < x)).card = _
    rw [hQroots, Multiset.filter_map, Multiset.card_map]
    congr 1
    apply Multiset.filter_congr
    intro x _
    exact neg_pos
  -- Assemble via Corollary 4.45.
  rw [hsign, hvp1, hvp2, hposM, hposQ]

end Azurite.BPR.Chapter4

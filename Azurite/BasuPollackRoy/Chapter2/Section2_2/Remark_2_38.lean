import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_35

/-!
# BPR Remark 2.38: equality when all roots are real

When every root of `P` lies in the base field (i.e. `P.roots.card = natDegree P`),
Budan-Fourier collapses to an equality:
`Var(Der(P); a, b] = num(P; (a, b])` for every `a < b`.

The argument proceeds in three steps.

1. `Var(Der(P); −∞, +∞) = natDegree P`: the `≤` comes from `Var l ≤ length l - 1`
   applied to `Der(P)` (a list of length `p + 1`); the `≥` comes from
   `num(P; R) ≤ Var(Der(P); −∞, +∞)` via Budan-Fourier and
   `num(P; R) = natDegree P` by hypothesis.
2. Split both `num` and `Var` into the three sub-intervals `(−∞, a]`, `(a, b]`,
   `(b, +∞)` and sum the per-interval Budan-Fourier inequalities.
3. Since both sums equal `natDegree P` and each `num ≤ Var`, equality must hold
   componentwise — in particular on the middle interval.
-/

namespace Azurite.BPR.Theorem2_35

open Polynomial Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- Upper bound: `varNonzero l ≤ l.length − 1`. Each sign variation lives in
    one of the `length − 1` adjacent pairs. -/
private lemma varNonzero_le_length_sub_one :
    ∀ (l : List R), varNonzero l ≤ l.length - 1
  | [] => by simp
  | [_] => by simp [varNonzero]
  | a :: b :: rest => by
    rw [varNonzero_cons_cons]
    have ih := varNonzero_le_length_sub_one (b :: rest)
    simp only [List.length_cons] at ih ⊢
    split_ifs <;> omega

omit [IsStrictOrderedRing R] in
/-- Upper bound: `Var l ≤ l.length − 1`. Filtering zeros can only shrink the
    length, and `varNonzero` on the filtered list satisfies the bound. -/
private lemma Var_le_length_sub_one (l : List R) : Var l ≤ l.length - 1 := by
  unfold Var
  have hvn := varNonzero_le_length_sub_one (l.filter (· ≠ 0))
  have hlen := List.length_filter_le (fun x : R => decide (x ≠ 0)) l
  omega

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `(der P).length = natDegree P + 1`. -/
private lemma der_length (P : R[X]) : (der P).length = P.natDegree + 1 := by
  unfold der; simp

omit [IsStrictOrderedRing R] in
/-- Upper bound: `varAt (der P) a ≤ natDegree P`. -/
private lemma varAt_der_le_natDegree (P : R[X]) (a : ExtendedPoint R) :
    varAt (der P) a ≤ P.natDegree := by
  unfold varAt
  have h := Var_le_length_sub_one ((der P).map (ExtendedPoint.evalPoly · a))
  rw [List.length_map, der_length] at h
  omega

omit [IsStrictOrderedRing R] in
/-- Partition: for `a ≤ b`, the number of roots of `P` in `R` splits as the sum
    over `(−∞, a]`, `(a, b]`, `(b, +∞)`. -/
private lemma numRoots_triple_split (P : R[X]) {a b : R} (hab : a ≤ b) :
    numRoots P .negInf (.finite a) + numRoots P (.finite a) (.finite b) +
      numRoots P (.finite b) .posInf = numRoots P .negInf .posInf := by
  classical
  show (P.roots.filter (· ≤ a)).card +
      (P.roots.filter (fun r => a < r ∧ r ≤ b)).card +
      (P.roots.filter (b < ·)).card = P.roots.card
  rw [← Multiset.card_add, ← Multiset.card_add]
  congr 1
  ext r
  simp only [Multiset.count_add, Multiset.count_filter]
  by_cases h1 : r ≤ a
  · have h2 : ¬ (a < r ∧ r ≤ b) := fun ⟨h, _⟩ =>
      absurd (lt_of_lt_of_le h h1) (lt_irrefl a)
    have h3 : ¬ b < r := fun h =>
      absurd (lt_of_lt_of_le h h1) (not_lt.mpr hab)
    simp [h1, h2, h3]
  · push Not at h1
    by_cases h2 : r ≤ b
    · have h1' : ¬ r ≤ a := not_le.mpr h1
      have h2ab : a < r ∧ r ≤ b := ⟨h1, h2⟩
      have h3 : ¬ b < r := not_lt.mpr h2
      simp [h1', h2ab, h3]
    · push Not at h2
      have h1' : ¬ r ≤ a := not_le.mpr h1
      have h2' : ¬ (a < r ∧ r ≤ b) := fun ⟨_, h⟩ =>
        absurd (lt_of_lt_of_le h2 h) (lt_irrefl b)
      simp [h1', h2', h2]

/-- **BPR Remark 2.38.** When every root of `P ≠ 0` is real
    (`P.roots.card = natDegree P`), `Var(Der(P); a, b]` equals
    `num(P; (a, b])` for every `a < b`.

    Budan-Fourier provides only the inequality `num ≤ Var` with even
    difference, but under the hypothesis the three-way sum telescopes:
    the total `Var(Der(P); −∞, +∞)` equals `natDegree P = num(P; R)`,
    forcing equality in each sub-interval. -/
theorem var_eq_numRoots_of_all_roots_real
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0)
    (hroots_card : P.roots.card = P.natDegree) {a b : R} (hab : a < b) :
    varBetween (der P) (.finite a) (.finite b) =
      (numRoots P (.finite a) (.finite b) : ℤ) := by
  -- Total roots = natDegree.
  have hnum_total : (numRoots P .negInf .posInf : ℤ) = (P.natDegree : ℤ) := by
    show (P.roots.card : ℤ) = (P.natDegree : ℤ)
    exact_mod_cast hroots_card
  -- Total varBetween ≤ natDegree.
  have hvar_le : varBetween (der P) .negInf .posInf ≤ (P.natDegree : ℤ) := by
    unfold varBetween
    have h1 : (varAt (der P) .negInf : ℤ) ≤ (P.natDegree : ℤ) :=
      Int.ofNat_le.mpr (varAt_der_le_natDegree P .negInf)
    have h2 : (0 : ℤ) ≤ (varAt (der P) .posInf : ℤ) := Int.natCast_nonneg _
    linarith
  -- BF total: num ≤ Var.
  have hBF_total := (budan_fourier_negInf_posInf hIVP hP).1
  -- Hence varBetween total = natDegree.
  have hvar_total : varBetween (der P) .negInf .posInf = (P.natDegree : ℤ) := by
    linarith
  -- numRoots splits into three (as ℤ).
  have hnum_split : (numRoots P .negInf (.finite a) : ℤ) +
      (numRoots P (.finite a) (.finite b) : ℤ) +
      (numRoots P (.finite b) .posInf : ℤ) = (P.natDegree : ℤ) := by
    have h := numRoots_triple_split P hab.le
    have h' : ((numRoots P .negInf (.finite a) +
        numRoots P (.finite a) (.finite b) +
        numRoots P (.finite b) .posInf : ℕ) : ℤ) =
        ((numRoots P .negInf .posInf : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  -- varBetween splits into three.
  have hvar_split : varBetween (der P) .negInf (.finite a) +
      varBetween (der P) (.finite a) (.finite b) +
      varBetween (der P) (.finite b) .posInf = (P.natDegree : ℤ) := by
    have h1 := varBetween_split (der P) .negInf (.finite b) .posInf
    have h2 := varBetween_split (der P) .negInf (.finite a) (.finite b)
    linarith
  -- BF on each sub-interval.
  have hBF_L := (budan_fourier_negInf hIVP hP a).1
  have hBF_M := (budan_fourier_finite hIVP hP hab).1
  have hBF_R := (budan_fourier_posInf hIVP hP b).1
  -- Componentwise ≤ with equal sums forces componentwise equality.
  linarith

end Azurite.BPR.Theorem2_35

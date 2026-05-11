import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_25
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_35

/-!
# BPR Theorem 2.33: Descartes' Rule of Signs

For `P ∈ R[X]` over an ordered field `R`:

  1. `Var(P) ≥ pos(P)` — the sign-variation count of the coefficient
     sequence is an upper bound on the number of positive real roots,
     counted with multiplicity.
  2. `Var(P) − pos(P)` is even.

**Proof sketch (BPR).** The coefficient of degree `i` of `P` has the same
sign as the `i`-th derivative of `P` evaluated at `0` (since
`P^{(i)}(0) = i! · a_i`). At `+∞`, the leading coefficients of the
successive derivatives all have the same sign as `leadingCoeff P` — they
differ only by positive integer multiples — so there are no sign
variations at `+∞`. Hence

    `Var(P) = Var(Der(P); 0, +∞)`.

Both claims then follow from a sharper "variation change bounds the root
count with matching parity" statement for a derivative list on a half-open
interval, applied with `a = 0`, `b = +∞`.
-/

namespace Azurite.BPR.Theorem2_33

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_35

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Helpers: leading coefficients of iterated derivatives -/

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- For `k ≤ P.natDegree` with `P ≠ 0`, the coefficient at `P.natDegree - k`
    of the `k`-th derivative equals `P.natDegree.descFactorial k • P.leadingCoeff`.
    Consequence of `Polynomial.coeff_iterate_derivative`. -/
private lemma coeff_iterate_derivative_at_natDegree_sub
    (P : R[X]) {k : ℕ} (hk : k ≤ P.natDegree) :
    ((derivative)^[k] P).coeff (P.natDegree - k) =
      (P.natDegree.descFactorial k : R) * P.leadingCoeff := by
  have h := Polynomial.coeff_iterate_derivative (p := P) (k := k) (P.natDegree - k)
  rw [Nat.sub_add_cancel hk] at h
  rw [h, nsmul_eq_mul]
  rfl

/-- For `P ≠ 0` and `k ≤ P.natDegree`, the `k`-th iterated derivative has
    `natDegree = P.natDegree - k` and `leadingCoeff = P.natDegree.descFactorial k · P.leadingCoeff`. -/
private lemma natDegree_and_leadingCoeff_iterate_derivative
    {P : R[X]} (hP : P ≠ 0) {k : ℕ} (hk : k ≤ P.natDegree) :
    ((derivative)^[k] P).natDegree = P.natDegree - k ∧
    ((derivative)^[k] P).leadingCoeff =
      (P.natDegree.descFactorial k : R) * P.leadingCoeff := by
  -- Use `coeff_iterate_derivative_at_natDegree_sub` and the upper bound.
  have hcoeff := coeff_iterate_derivative_at_natDegree_sub P hk
  -- The coefficient is nonzero: descFactorial > 0 in char-0 and leadingCoeff ≠ 0.
  have hdesc_pos : (0 : R) < (P.natDegree.descFactorial k : R) := by
    have : 0 < P.natDegree.descFactorial k := Nat.descFactorial_pos.mpr hk
    exact_mod_cast this
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hne : ((derivative)^[k] P).coeff (P.natDegree - k) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (ne_of_gt hdesc_pos) hlc
  -- Hence natDegree ≥ P.natDegree - k.
  have hlb : P.natDegree - k ≤ ((derivative)^[k] P).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hne
  have hub : ((derivative)^[k] P).natDegree ≤ P.natDegree - k :=
    Polynomial.natDegree_iterate_derivative P k
  have hnd : ((derivative)^[k] P).natDegree = P.natDegree - k := le_antisymm hub hlb
  refine ⟨hnd, ?_⟩
  rw [Polynomial.leadingCoeff, hnd, hcoeff]

/-- For `P ≠ 0`, `k ≤ P.natDegree`, and `0 ≤ P.leadingCoeff`, the leading
    coefficient of the `k`-th iterated derivative is nonneg. -/
private lemma leadingCoeff_iterate_derivative_nonneg
    {P : R[X]} (hP : P ≠ 0) {k : ℕ} (hk : k ≤ P.natDegree)
    (h : 0 ≤ P.leadingCoeff) :
    0 ≤ ((derivative)^[k] P).leadingCoeff := by
  rw [(natDegree_and_leadingCoeff_iterate_derivative hP hk).2]
  have hdesc : 0 ≤ (P.natDegree.descFactorial k : R) := by
    exact_mod_cast Nat.zero_le _
  exact mul_nonneg hdesc h

/-- Dual of `leadingCoeff_iterate_derivative_nonneg`. -/
private lemma leadingCoeff_iterate_derivative_nonpos
    {P : R[X]} (hP : P ≠ 0) {k : ℕ} (hk : k ≤ P.natDegree)
    (h : P.leadingCoeff ≤ 0) :
    ((derivative)^[k] P).leadingCoeff ≤ 0 := by
  rw [(natDegree_and_leadingCoeff_iterate_derivative hP hk).2]
  have hdesc : 0 ≤ (P.natDegree.descFactorial k : R) := by
    exact_mod_cast Nat.zero_le _
  exact mul_nonpos_of_nonneg_of_nonpos hdesc h

/-! ### Helper: scaling each entry by a positive value preserves `Var` -/

/-- Scaling each entry of an index-mapped list by a positive value preserves
    the pairwise sign-variation count. Works on any list of indices `s`. -/
private lemma varNonzero_map_mul_pos :
    ∀ (s : List ℕ) (f g : ℕ → R) (_hg : ∀ i ∈ s, 0 < g i),
    varNonzero (s.map (fun i => g i * f i)) = varNonzero (s.map f)
  | [], _, _, _ => rfl
  | [_], _, _, _ => rfl
  | a :: b :: rest, f, g, hg => by
      simp only [List.map_cons]
      rw [varNonzero_cons_cons, varNonzero_cons_cons]
      have hga : 0 < g a := hg a List.mem_cons_self
      have hgb : 0 < g b := hg b (List.mem_cons_of_mem _ List.mem_cons_self)
      have ih := varNonzero_map_mul_pos (b :: rest) f g
        (fun i hi => hg i (List.mem_cons_of_mem _ hi))
      simp only [List.map_cons] at ih
      rw [ih]
      congr 1
      apply if_congr _ rfl rfl
      have heq : (g a * f a) * (g b * f b) = (g a * g b) * (f a * f b) := by ring
      rw [heq]
      have hab : 0 < g a * g b := mul_pos hga hgb
      constructor
      · intro h
        rcases mul_neg_iff.mp h with ⟨_, h⟩ | ⟨h', _⟩
        · exact h
        · exact absurd h' (not_lt.mpr hab.le)
      · intro h
        exact mul_neg_iff.mpr (Or.inl ⟨hab, h⟩)

/-- Scaling each entry of `(range (n+1)).map f` by a positive value at each
    index preserves `Var`. Used in `varAt_der_finite_zero` to absorb the
    factorial scaling factor `i! · aᵢ = P^{(i)}(0)`. -/
private lemma Var_map_range_scale_eq (n : ℕ) (f g : ℕ → R)
    (hg : ∀ i, i ≤ n → 0 < g i) :
    Var ((List.range (n + 1)).map (fun i => g i * f i)) =
      Var ((List.range (n + 1)).map f) := by
  unfold Var
  have h_ne_zero_iff : ∀ i ∈ List.range (n + 1),
      (decide (g i * f i ≠ 0)) = (decide (f i ≠ 0)) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hi)
    have hgi : g i ≠ 0 := ne_of_gt (hg i hi')
    simp [hgi]
  rw [List.filter_map, List.filter_map]
  simp only [Function.comp_def]
  rw [List.filter_congr h_ne_zero_iff]
  set s := (List.range (n + 1)).filter (fun i => decide (f i ≠ 0))
  have hs : ∀ i ∈ s, 0 < g i := by
    intro i hi
    have : i ∈ List.range (n + 1) := List.mem_of_mem_filter hi
    exact hg i (Nat.lt_succ_iff.mp (List.mem_range.mp this))
  exact varNonzero_map_mul_pos s f g hs

/-! ### The two main helpers -/

/-- At `+∞`, the signs of the successive derivatives `P, P', …, P^{(p)}`
    all agree with `sign(leadingCoeff P)`, so `Var(Der(P); +∞) = 0`. -/
lemma varAt_der_posInf (P : R[X]) : varAt (der P) .posInf = 0 := by
  rw [varAt_posInf, der, List.map_map]
  -- Goal: Var ((range (P.natDegree + 1)).map (leadingCoeff ∘ (derivative^[·] P))) = 0
  by_cases hP : P = 0
  · subst hP
    apply Var_eq_zero_of_forall_nonneg
    intro x hx
    simp only [List.mem_map, Function.comp_apply] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [Polynomial.iterate_derivative_zero, Polynomial.leadingCoeff_zero]
  -- P ≠ 0. Case split on the sign of leadingCoeff P.
  rcases le_or_gt 0 P.leadingCoeff with hlc | hlc
  · apply Var_eq_zero_of_forall_nonneg
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact leadingCoeff_iterate_derivative_nonneg hP (Nat.lt_succ_iff.mp hk) hlc
  · apply Var_eq_zero_of_forall_nonpos
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact leadingCoeff_iterate_derivative_nonpos hP (Nat.lt_succ_iff.mp hk) hlc.le

/-- At `0`, each value `P^{(i)}(0) = i! · a_i` has the same sign as the
    coefficient `a_i` (since `i!` is positive), so `Var(Der(P); 0) = Var(P)`. -/
lemma varAt_der_finite_zero (P : R[X]) :
    varAt (der P) (.finite 0) = varPoly P := by
  rw [varAt_finite, der, varPoly, List.map_map]
  -- Goal: Var ((range (p+1)).map (fun i => (deriv^[i] P).eval 0))
  --     = Var ((range (p+1)).map P.coeff)
  -- Use: (deriv^[i] P).eval 0 = (deriv^[i] P).coeff 0 = i! • P.coeff i
  have hshow : ((fun Q => Polynomial.eval (0 : R) Q) ∘ fun i => (derivative)^[i] P) =
      (fun i => (i.factorial : R) * P.coeff i) := by
    funext i
    simp only [Function.comp_apply]
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative,
        zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [hshow]
  exact Var_map_range_scale_eq P.natDegree P.coeff (fun i => (i.factorial : R))
    (fun i _ => by show (0 : R) < (i.factorial : R); exact_mod_cast Nat.factorial_pos i)

/-- The stepping-stone identity from the BPR proof sketch:
    `Var(P) = Var(Der(P); 0, +∞)`. Follows immediately from
    `varAt_der_finite_zero` (so `Var(Der(P); 0) = Var(P)`) and
    `varAt_der_posInf` (so `Var(Der(P); +∞) = 0`). -/
theorem varPoly_eq_varBetween_der (P : R[X]) :
    (varPoly P : ℤ) = varBetween (der P) (.finite 0) .posInf := by
  simp [varBetween, varAt_der_finite_zero, varAt_der_posInf]

omit [IsStrictOrderedRing R] in
/-- `posRoots P = numRoots P (0, +∞)`. Immediate from unfolding both sides. -/
private lemma posRoots_eq_numRoots (P : R[X]) :
    posRoots P = numRoots P (.finite 0) .posInf := rfl

/-- **BPR Theorem 2.33 (Descartes' rule of signs).** Over a real closed field,
    for `P ∈ R[X]`:

    1. `Var(P) ≥ pos(P)` — the number of sign variations in the coefficient
       sequence is an upper bound on the number of positive real roots
       counted with multiplicity;
    2. `Var(P) − pos(P)` is even.

    The BPR proof reduces via `varPoly_eq_varBetween_der` to the Budan-Fourier
    theorem on the half-open interval `(0, +∞)`. -/
theorem descartes_rule_of_signs (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) :
    posRoots P ≤ varPoly P ∧ Even ((varPoly P : ℤ) - posRoots P) := by
  by_cases hP : P = 0
  · subst hP
    refine ⟨?_, ?_⟩
    · simp [posRoots, varPoly]
    · simp [posRoots, varPoly]
  have hBF := budan_fourier_posInf hIVP hP 0
  rw [← posRoots_eq_numRoots P, ← varPoly_eq_varBetween_der P] at hBF
  exact ⟨by exact_mod_cast hBF.1, hBF.2⟩

end Azurite.BPR.Theorem2_33

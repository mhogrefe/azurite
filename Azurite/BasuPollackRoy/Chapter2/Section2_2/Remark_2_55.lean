import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Definition_2_53
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Jumps

/-!
# BPR Remark 2.55

Two structural identities for the Cauchy index `Ind(Q/P; a, b)` (BPR
Definition 2.53):

* **Remark 2.55(a).** Maximum-value characterisation: `Ind(Q/P; a, b)`
  attains its maximum `p = deg(P)` iff `P` and `Q` interlace on `(a, b)`
  in the precise BPR sense.

* **Remark 2.55(b).** Mod-`P` invariance: if `R = Rem(Q, P)` is the
  Euclidean remainder, then `Ind(R/P; a, b) = Ind(Q/P; a, b)` (assuming
  `P ≠ 0`).

The companion file `Definition_2_53.lean` holds only the bare definitions
`cauchyIndexOn`, `cauchyIndex` (BPR Definition 2.53).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
/-! ### BPR Remark 2.55(a)

When does `Ind(Q/P; a, b)` attain its maximum value `p = deg(P)`? Exactly
when `P` and `Q` interlace nicely on `(a, b)`: `q = p − 1`, leading
coefficients of `P` and `Q` share a sign, all roots of `P` and `Q` are
simple and lie in `(a, b)`, and between any two consecutive roots of `P`
there is exactly one root of `Q`.

#### Lemmas needed to finish the proof

**Already proven in this file:**
* `cauchyIndexOn_le_card_roots_toFinset`, `cauchyIndexOn_le_natDegree`
* `cauchyIndexOn_eq_natDegree_extract` (forward direction's structural part)

**Provided by Mathlib (need to be applied):**
* `Polynomial.eq_prod_roots_of_splits_id` — when `P` splits over `R`,
  `P = C lc_P · ∏_{r ∈ P.roots}(X − C r)`.
* `Polynomial.derivative_mul`, `Polynomial.derivative_prod` — Leibniz rule.
* `Polynomial.rootMultiplicity_mul` — `mult x (P · Q) = mult x P + mult x Q`.
* `Multiset.toFinset_card_eq_card_iff_nodup` — already used.

**Provided by `Proposition_2_21.lean` (already imported):**
* `proposition_2_21_right` — sign on the right of a root via the
  multiplicity-th derivative.
* The IVP for `ℝ` (or other real-closed fields) bridges this to the jump
  predicates.

**Need to be developed (Azurite-specific helpers):**

1. `factored_eval_at_root` — for a `P` with all simple real roots
   `r₁ < ⋯ < rₚ`, `P.eval rᵢ = 0` and
   `P.derivative.eval rᵢ = lc_P · ∏_{j ≠ i}(rᵢ − rⱼ)`.

2. `sign_alternating_product_eval` — with sorted distinct values
   `r₁ < ⋯ < rₚ` and any index `i`,
   `sign(∏_{j ≠ i}(rᵢ − rⱼ)) = (−1)^(p − i)`,
   because exactly `p − i` factors are negative (`r_j > r_i ⇔ j > i`).

3. `sign_derivative_at_simple_root` — combining (1) and (2):
   `sign(P.derivative.eval rᵢ) = sign(lc_P) · (−1)^(p − i)`.

4. `sign_eval_Q_at_P_root_of_interlacing` — under interlacing, for the
   `i`-th `P`-root `rᵢ` and `Q` having `p − 1` simple roots interlaced:
   `sign(Q.eval rᵢ) = sign(lc_Q) · (−1)^(p − i)`,
   since exactly `p − i` factors `(rᵢ − sⱼ)` are negative (`sⱼ > rᵢ ⇔ j ≥ i`).

5. `sign_QP_derivative_at_P_root` — combining (3) and (4):
   `sign((Q · P).derivative.eval rᵢ) = sign(lc_P) · sign(lc_Q)`,
   constant in `i`, hence `+1` exactly when `sign(lc_P) = sign(lc_Q)`.

6. `JumpsFromNegInfToPosInf_iff_sign_match` — at a simple `P`-root `rᵢ`
   that is not a `Q`-root, `JumpsFromNegInfToPosInf Q P rᵢ ↔
   sign((Q · P).derivative.eval rᵢ) = 1`. Direction (←) uses Prop. 2.21.

7. **Forward (with extraction in hand):** the extraction theorem already
   gives the simple-root and `(a, b)` containment for `P`. Combined with
   the `JumpsFromNegInfToPosInf` predicate at each `P`-root, lemma 6 gives
   the sign-match. From the per-`i` formula in (5), the `(−1)^(p−i)`
   factors fix the sign so `sign(lc_P) = sign(lc_Q)`. The interlacing
   pattern (and `q = p − 1`) follow by counting `Q`-roots between
   consecutive `P`-roots (each gap forces a sign change of `Q/P`, hence a
   `Q`-root by IVP/Prop. 2.20).

8. **Backward:** given the structural conditions, lemmas (3)–(6) directly
   yield `JumpsFromNegInfToPosInf Q P r` for every `r ∈ P.roots`. The
   counting then collapses to `pos = card P.roots.toFinset = P.natDegree`,
   `neg = 0`, hence `cauchyIndexOn Q P a b = P.natDegree`.

The bottleneck is lemmas (1)–(5): polynomial factorization plus a careful
sign-of-product induction over sorted roots. -/

/-- Interlacing condition (BPR Remark 2.55(a)): between any two roots of
    `P` with no other `P`-root in between, there is exactly one root of `Q`. -/
def Interlacing (P Q : R[X]) : Prop :=
  ∀ r₁ r₂ : R, r₁ < r₂ → P.IsRoot r₁ → P.IsRoot r₂ →
    (∀ r₃ : R, P.IsRoot r₃ → ¬ (r₁ < r₃ ∧ r₃ < r₂)) →
    ∃! s : R, Q.IsRoot s ∧ r₁ < s ∧ s < r₂

omit [IsStrictOrderedRing R] in
/-- The Cauchy index is bounded above by the number of distinct roots of `P`. -/
theorem cauchyIndexOn_le_card_roots_toFinset
    (Q P : R[X]) (a b : ExtendedPoint R) :
    cauchyIndexOn Q P a b ≤ (P.roots.toFinset.card : ℤ) := by
  classical
  show ((P.roots.toFinset.filter
      (fun x => x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
      ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          JumpsFromPosInfToNegInf Q P x)).card : ℤ) ≤ P.roots.toFinset.card
  have h_pos_le :
      ((P.roots.toFinset.filter (fun x => x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf Q P x)).card : ℤ) ≤ P.roots.toFinset.card := by
    exact_mod_cast Finset.card_filter_le _ _
  have h_neg_nn :
      0 ≤ ((P.roots.toFinset.filter (fun x => x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromPosInfToNegInf Q P x)).card : ℤ) := by
    exact_mod_cast Nat.zero_le _
  omega

omit [IsStrictOrderedRing R] in
/-- The Cauchy index is bounded above by `P.natDegree`. -/
theorem cauchyIndexOn_le_natDegree (Q P : R[X]) (a b : ExtendedPoint R) :
    cauchyIndexOn Q P a b ≤ (P.natDegree : ℤ) := by
  classical
  refine (cauchyIndexOn_le_card_roots_toFinset Q P a b).trans ?_
  by_cases hP : P = 0
  · simp [hP]
  · have h1 : P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    have h2 : Multiset.card P.roots ≤ P.natDegree := Polynomial.card_roots' P
    exact_mod_cast h1.trans h2

omit [IsStrictOrderedRing R] in
/-- When the Cauchy index equals `P.natDegree`, every distinct root of `P`
    must be in `(a, b)` and produce a `−∞ → +∞` jump (and none produce a
    `+∞ → −∞` jump). Furthermore `P.roots.toFinset.card = P.natDegree` and
    `P.roots.Nodup`, i.e. `P` has `natDegree`-many distinct simple real roots. -/
theorem cauchyIndexOn_eq_natDegree_extract
    (Q P : R[X]) (a b : ExtendedPoint R)
    (h : cauchyIndexOn Q P a b = (P.natDegree : ℤ)) :
    P.roots.toFinset.card = P.natDegree ∧
    Multiset.card P.roots = P.natDegree ∧
    P.roots.Nodup ∧
    (∀ r ∈ P.roots.toFinset, r ∈ ExtendedPoint.openInterval a b ∧
      JumpsFromNegInfToPosInf Q P r) ∧
    (∀ r ∈ P.roots.toFinset, ¬ JumpsFromPosInfToNegInf Q P r) := by
  classical
  have h_unfold : ((P.roots.toFinset.filter
      (fun x => x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
      ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          JumpsFromPosInfToNegInf Q P x)).card : ℤ) = P.natDegree := h
  -- Bounds: pos ≤ card P.roots.toFinset ≤ card P.roots ≤ P.natDegree, neg ≥ 0.
  have h_pos_le :
      (P.roots.toFinset.filter (fun x => x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf Q P x)).card ≤ P.roots.toFinset.card :=
    Finset.card_filter_le _ _
  have h_card_le_card_roots : P.roots.toFinset.card ≤ Multiset.card P.roots :=
    Multiset.toFinset_card_le _
  have h_card_roots_le_natDegree : Multiset.card P.roots ≤ P.natDegree := by
    by_cases hP : P = 0
    · simp [hP]
    · exact Polynomial.card_roots' P
  -- Extract equalities from the chain.
  have h_pos_eq : (P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧
      JumpsFromNegInfToPosInf Q P x)).card = P.natDegree := by
    omega
  have h_neg_zero : (P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧
      JumpsFromPosInfToNegInf Q P x)).card = 0 := by
    omega
  have h_toFinset_card : P.roots.toFinset.card = P.natDegree := by
    have h_pos_le' : (P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf Q P x)).card ≤ P.roots.toFinset.card :=
      h_pos_le
    omega
  have h_card_roots_eq : Multiset.card P.roots = P.natDegree := by omega
  have h_nodup : P.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    rw [h_toFinset_card, h_card_roots_eq]
  -- Each root in toFinset is in the filter (since the filter has full card).
  have h_filter_eq : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf Q P x) =
      P.roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    omega
  refine ⟨h_toFinset_card, h_card_roots_eq, h_nodup, ?_, ?_⟩
  · intro r hr
    have hr_in_filter : r ∈ P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf Q P x) := by
      rw [h_filter_eq]; exact hr
    exact (Finset.mem_filter.mp hr_in_filter).2
  · intro r hr h_jump_neg
    -- From h_neg_zero, the negative-jump filter is empty, contradiction.
    have hr_in_neg : r ∈ P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromPosInfToNegInf Q P x) := by
      refine Finset.mem_filter.mpr ⟨hr, ?_, h_jump_neg⟩
      have hr_full : r ∈ P.roots.toFinset.filter (fun x =>
          x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf Q P x) := by
        rw [h_filter_eq]; exact hr
      exact (Finset.mem_filter.mp hr_full).2.1
    have : P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromPosInfToNegInf Q P x) ≠ ∅ :=
      Finset.ne_empty_of_mem hr_in_neg
    have h_empty : P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromPosInfToNegInf Q P x) = ∅ :=
      Finset.card_eq_zero.mp h_neg_zero
    exact this h_empty

/-! #### Helper lemmas for Remark 2.55(a) -/

omit [IsStrictOrderedRing R] in
/-- For nonzero `P` with all roots real (counted with multiplicity), the
    derivative evaluated at a root has the explicit form
    `lc_P · ∏_{r' ∈ roots, r' ≠ r}(r − r')`. -/
private lemma derivative_eval_at_root_of_splits
    (P : R[X]) (h_split : Multiset.card P.roots = P.natDegree)
    {r : R} (hr : r ∈ P.roots) :
    P.derivative.eval r =
      P.leadingCoeff * (Multiset.map (r - ·) (P.roots.erase r)).prod := by
  classical
  have h_splits : P.Splits := Polynomial.splits_iff_card_roots.mpr h_split
  have h_eq : P =
      C P.leadingCoeff * (Multiset.map (fun a => X - C a) P.roots).prod :=
    h_splits.eq_prod_roots
  -- Take derivative of both sides.
  have h_deriv_eq : P.derivative =
      C P.leadingCoeff *
        (Multiset.map (fun a => X - C a) P.roots).prod.derivative := by
    conv_lhs => rw [h_eq]
    rw [Polynomial.derivative_C_mul]
  rw [h_deriv_eq, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_multiset_prod_X_sub_C_derivative hr]

/-- The sign of `∏_{r' ∈ s}(r − r')` over a multiset `s` not containing `r`
    is `(−1)` raised to the number of elements of `s` greater than `r`. -/
private lemma sign_prod_sub
    (r : R) (s : Multiset R) (h_ne : r ∉ s) :
    SignType.sign ((Multiset.map (r - ·) s).prod) =
      (-1 : SignType) ^ (Multiset.card (s.filter (r < ·))) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have h_a_ne : a ≠ r :=
      fun h => h_ne (h ▸ Multiset.mem_cons_self _ _)
    have h_s_ne : r ∉ s := fun h => h_ne (Multiset.mem_cons_of_mem h)
    rw [Multiset.map_cons, Multiset.prod_cons, sign_mul, ih h_s_ne]
    rcases lt_or_gt_of_ne h_a_ne.symm with h_ra | h_ra
    · -- r < a: factor (r − a) < 0, filter gains `a`.
      have h_sub_neg : r - a < 0 := sub_neg.mpr h_ra
      have h_sign : SignType.sign (r - a) = -1 := sign_eq_neg_one_iff.mpr h_sub_neg
      rw [h_sign, Multiset.filter_cons_of_pos _ h_ra, Multiset.card_cons,
        pow_succ]
      exact mul_comm _ _
    · -- r > a (i.e., a < r): factor (r − a) > 0, filter unchanged.
      have h_sub_pos : 0 < r - a := sub_pos.mpr h_ra
      have h_sign : SignType.sign (r - a) = 1 := sign_pos h_sub_pos
      rw [h_sign, Multiset.filter_cons_of_neg _ (not_lt.mpr h_ra.le), one_mul]

omit [Field R] [IsStrictOrderedRing R] in
/-- For any `r`, `(s.erase r).filter (r < ·) = s.filter (r < ·)` because
    `r < r` is false, so `r` is never selected by the filter anyway. -/
private lemma filter_lt_erase_self (s : Multiset R) (r : R) :
    (s.erase r).filter (r < ·) = s.filter (r < ·) := by
  classical
  ext a
  rw [Multiset.count_filter, Multiset.count_filter]
  by_cases h : r < a
  · simp only [ite_eq_left h]
    have h_ne : a ≠ r := fun heq => absurd h (heq ▸ lt_irrefl r)
    exact Multiset.count_erase_of_ne h_ne s
  · simp only [ite_eq_right h]

/-- For nonzero `P` with all simple real roots, the sign of `P'(r)` at a
    root `r` is `sign(lc_P) · (−1)^|{r' ∈ P.roots : r < r'}|`. -/
private lemma sign_derivative_at_simple_root
    {P : R[X]} (h_split : Multiset.card P.roots = P.natDegree)
    (h_nodup : P.roots.Nodup) {r : R} (hr : r ∈ P.roots) :
    SignType.sign (P.derivative.eval r) =
      SignType.sign P.leadingCoeff *
        (-1 : SignType) ^ (Multiset.card (P.roots.filter (r < ·))) := by
  classical
  have h_eval := derivative_eval_at_root_of_splits P h_split hr
  rw [h_eval, sign_mul]
  congr 1
  have h_r_notin : r ∉ P.roots.erase r := by
    intro h
    have h_count : Multiset.count r (P.roots.erase r) ≥ 1 := Multiset.one_le_count_iff_mem.mpr h
    have h_nodup' : Multiset.count r P.roots ≤ 1 := Multiset.nodup_iff_count_le_one.mp h_nodup r
    have h_erase_count : Multiset.count r (P.roots.erase r) =
        Multiset.count r P.roots - 1 := Multiset.count_erase_self _ _
    omega
  have h1 := sign_prod_sub r (P.roots.erase r) h_r_notin
  rw [h1, filter_lt_erase_self]

/-- For a polynomial `Q` with all simple real roots, the sign of `Q(r)` at
    any non-root `r` is `sign(lc_Q) · (−1)^|{s ∈ Q.roots : r < s}|`. -/
private lemma sign_eval_at_non_root
    {Q : R[X]} (h_split : Multiset.card Q.roots = Q.natDegree)
    {r : R} (hr : r ∉ Q.roots) :
    SignType.sign (Q.eval r) =
      SignType.sign Q.leadingCoeff *
        (-1 : SignType) ^ (Multiset.card (Q.roots.filter (r < ·))) := by
  classical
  have h_splits : Q.Splits := Polynomial.splits_iff_card_roots.mpr h_split
  have h_eq : Q =
      C Q.leadingCoeff * (Multiset.map (fun a => X - C a) Q.roots).prod :=
    h_splits.eq_prod_roots
  have h_map_eq :
      Multiset.map (Polynomial.eval r) (Multiset.map (fun a => X - C a) Q.roots) =
        Multiset.map (fun a => r - a) Q.roots := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a _
    simp [Function.comp]
  have h_eval : Q.eval r =
      Q.leadingCoeff * (Multiset.map (r - ·) Q.roots).prod := by
    conv_lhs => rw [h_eq]
    rw [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_multiset_prod, h_map_eq]
  rw [h_eval, sign_mul, sign_prod_sub r Q.roots hr]

omit [IsStrictOrderedRing R] in
/-- The number of `Q`-roots strictly greater than a `P`-root `rᵢ` equals
    the number of `P`-roots strictly greater than `rᵢ`. This is the key
    combinatorial consequence of interlacing.

    The proof builds an explicit bijection `f : {P-roots > r} → {Q-roots > r}`:
    for each `P`-root `r' > r`, `f r'` is the unique `Q`-root in the gap
    `(prev r', r')`, where `prev r'` is the max `P`-root strictly less than
    `r'` (well-defined since `r ∈ P.roots` and `r < r'`). -/
private lemma card_filter_gt_Q_eq_P
    (P Q : R[X]) (hP_ne : P ≠ 0) (hQ_ne : Q ≠ 0)
    (hP_card : Multiset.card P.roots = P.natDegree)
    (hP_nodup : P.roots.Nodup)
    (hQ_card : Multiset.card Q.roots = Q.natDegree)
    (hQ_nodup : Q.roots.Nodup)
    (hq : Q.natDegree + 1 = P.natDegree)
    (hint : Interlacing P Q)
    {r : R} (hr : r ∈ P.roots) :
    Multiset.card (Q.roots.filter (r < ·)) =
      Multiset.card (P.roots.filter (r < ·)) := by
  classical
  -- Convert Multiset.card to Finset.card using Nodup.
  have hP_filter_nodup : (P.roots.filter (r < ·)).Nodup := hP_nodup.filter _
  have hQ_filter_nodup : (Q.roots.filter (r < ·)).Nodup := hQ_nodup.filter _
  have hP_eq : Multiset.card (P.roots.filter (r < ·)) =
      (P.roots.toFinset.filter (r < ·)).card := by
    rw [show P.roots.toFinset.filter (r < ·) =
        (P.roots.filter (r < ·)).toFinset from ?_]
    · exact (Multiset.toFinset_card_of_nodup hP_filter_nodup).symm
    · ext a; simp [Multiset.mem_toFinset]
  have hQ_eq : Multiset.card (Q.roots.filter (r < ·)) =
      (Q.roots.toFinset.filter (r < ·)).card := by
    rw [show Q.roots.toFinset.filter (r < ·) =
        (Q.roots.filter (r < ·)).toFinset from ?_]
    · exact (Multiset.toFinset_card_of_nodup hQ_filter_nodup).symm
    · ext a; simp [Multiset.mem_toFinset]
  rw [hP_eq, hQ_eq]
  -- The previous-P-root function: max P-root strictly less than r'.
  -- Well-defined because `r ∈ P.roots` with `r < r'`, so the set is nonempty.
  set Pgt := P.roots.toFinset.filter (r < ·)
  set Qgt := Q.roots.toFinset.filter (r < ·)
  have hPgt_mem : ∀ {r'}, r' ∈ Pgt ↔ r' ∈ P.roots ∧ r < r' := by
    intro r'
    simp [Pgt, Multiset.mem_toFinset]
  have hQgt_mem : ∀ {q}, q ∈ Qgt ↔ q ∈ Q.roots ∧ r < q := by
    intro q
    simp [Qgt, Multiset.mem_toFinset]
  -- For r' ∈ Pgt, define `prev r'` as the max P-root < r'.
  have hPlt_nonempty : ∀ {r'}, r' ∈ Pgt →
      (P.roots.toFinset.filter (· < r')).Nonempty := by
    intro r' hr'
    refine ⟨r, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, ?_⟩⟩
    exact (hPgt_mem.mp hr').2
  let prev : ∀ r' ∈ Pgt, R := fun r' hr' =>
    (P.roots.toFinset.filter (· < r')).max' (hPlt_nonempty hr')
  have hprev_lt : ∀ r' (hr' : r' ∈ Pgt), prev r' hr' < r' := by
    intro r' hr'
    have h := (P.roots.toFinset.filter (· < r')).max'_mem (hPlt_nonempty hr')
    exact (Finset.mem_filter.mp h).2
  have hprev_mem : ∀ r' (hr' : r' ∈ Pgt), prev r' hr' ∈ P.roots := by
    intro r' hr'
    have h := (P.roots.toFinset.filter (· < r')).max'_mem (hPlt_nonempty hr')
    exact Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1
  have hprev_ge : ∀ r' (hr' : r' ∈ Pgt), r ≤ prev r' hr' := by
    intro r' hr'
    apply (P.roots.toFinset.filter (· < r')).le_max'
    refine Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, ?_⟩
    exact (hPgt_mem.mp hr').2
  have hprev_no_between : ∀ r' (hr' : r' ∈ Pgt) (r₃ : R), P.IsRoot r₃ →
      ¬ (prev r' hr' < r₃ ∧ r₃ < r') := by
    intro r' hr' r₃ hr₃ ⟨h_left, h_right⟩
    have hr₃_finset : r₃ ∈ P.roots.toFinset.filter (· < r') := by
      refine Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne).mpr hr₃),
          h_right⟩
    have h_le := (P.roots.toFinset.filter (· < r')).le_max'
      r₃ hr₃_finset
    exact absurd h_left (not_lt.mpr h_le)
  have hprev_isRoot : ∀ r' (hr' : r' ∈ Pgt), P.IsRoot (prev r' hr') := by
    intro r' hr'
    exact (Polynomial.mem_roots hP_ne).mp (hprev_mem r' hr')
  have hr'_isRoot : ∀ r' (hr' : r' ∈ Pgt), P.IsRoot r' := by
    intro r' hr'
    exact (Polynomial.mem_roots hP_ne).mp (hPgt_mem.mp hr').1
  -- Apply Interlacing to get the unique Q-root in (prev r', r').
  let f : ∀ r' ∈ Pgt, R := fun r' hr' =>
    (hint (prev r' hr') r' (hprev_lt r' hr') (hprev_isRoot r' hr')
      (hr'_isRoot r' hr') (hprev_no_between r' hr')).choose
  have hf_spec : ∀ r' (hr' : r' ∈ Pgt),
      Q.IsRoot (f r' hr') ∧ prev r' hr' < f r' hr' ∧ f r' hr' < r' := by
    intro r' hr'
    exact (hint (prev r' hr') r' (hprev_lt r' hr') (hprev_isRoot r' hr')
      (hr'_isRoot r' hr') (hprev_no_between r' hr')).choose_spec.1
  -- f maps into Qgt: f r' ∈ Q.roots and f r' > r.
  have hf_mem_Q : ∀ r' (hr' : r' ∈ Pgt), f r' hr' ∈ Q.roots := fun r' hr' =>
    (Polynomial.mem_roots hQ_ne).mpr (hf_spec r' hr').1
  have hf_gt_r : ∀ r' (hr' : r' ∈ Pgt), r < f r' hr' := fun r' hr' =>
    lt_of_le_of_lt (hprev_ge r' hr') (hf_spec r' hr').2.1
  have hf_into_Qgt : ∀ r' (hr' : r' ∈ Pgt), f r' hr' ∈ Qgt := fun r' hr' =>
    hQgt_mem.mpr ⟨hf_mem_Q r' hr', hf_gt_r r' hr'⟩
  -- f is injective: different r' give Q-roots in disjoint open intervals.
  have hf_inj : ∀ r₁' (h₁ : r₁' ∈ Pgt) r₂' (h₂ : r₂' ∈ Pgt),
      f r₁' h₁ = f r₂' h₂ → r₁' = r₂' := by
    intro r₁' h₁ r₂' h₂ hf_eq
    -- Suppose r₁' ≠ r₂'. WLOG r₁' < r₂'.
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
    · -- r₁' < r₂'. Then prev r₂' ≥ r₁' (since r₁' ∈ P.roots, r₁' < r₂').
      have hr₁'_in_filter : r₁' ∈ P.roots.toFinset.filter (· < r₂') := by
        refine Finset.mem_filter.mpr ⟨?_, h_lt⟩
        exact Multiset.mem_toFinset.mpr (hPgt_mem.mp h₁).1
      have h_prev_ge_r₁ : r₁' ≤ prev r₂' h₂ :=
        (P.roots.toFinset.filter (· < r₂')).le_max' _ hr₁'_in_filter
      -- f r₁' h₁ < r₁' (from hf_spec)
      have h_f_lt : f r₁' h₁ < r₁' := (hf_spec r₁' h₁).2.2
      -- f r₂' h₂ > prev r₂' h₂ ≥ r₁'
      have h_f_gt : prev r₂' h₂ < f r₂' h₂ := (hf_spec r₂' h₂).2.1
      have : f r₁' h₁ < f r₂' h₂ := lt_of_lt_of_le h_f_lt
        (le_trans h_prev_ge_r₁ h_f_gt.le)
      exact absurd hf_eq (ne_of_lt this)
    · -- Symmetric case.
      have hr₂'_in_filter : r₂' ∈ P.roots.toFinset.filter (· < r₁') := by
        refine Finset.mem_filter.mpr ⟨?_, h_lt⟩
        exact Multiset.mem_toFinset.mpr (hPgt_mem.mp h₂).1
      have h_prev_ge_r₂ : r₂' ≤ prev r₁' h₁ :=
        (P.roots.toFinset.filter (· < r₁')).le_max' _ hr₂'_in_filter
      have h_f_lt : f r₂' h₂ < r₂' := (hf_spec r₂' h₂).2.2
      have h_f_gt : prev r₁' h₁ < f r₁' h₁ := (hf_spec r₁' h₁).2.1
      have : f r₂' h₂ < f r₁' h₁ := lt_of_lt_of_le h_f_lt
        (le_trans h_prev_ge_r₂ h_f_gt.le)
      exact absurd hf_eq.symm (ne_of_lt this)
  -- Convert the injection `f : Pgt → Qgt` into the cardinality bound
  -- `|Pgt| ≤ |Qgt|`. We lift the dependent `f` to a non-dependent function
  -- using a default value outside `Pgt`.
  let f' : R → R := fun r' => if h : r' ∈ Pgt then f r' h else r'
  have h_Pgt_le_Qgt : Pgt.card ≤ Qgt.card := by
    apply Finset.card_le_card_of_injOn f'
    · intro r' hr'
      show f' r' ∈ Qgt
      have : f' r' = f r' hr' := dite_eq_left hr'
      rw [this]
      exact hf_into_Qgt r' hr'
    · intro r₁' h₁ r₂' h₂ h_eq
      simp only [Finset.mem_coe] at h₁ h₂
      have e₁ : f' r₁' = f r₁' h₁ := dite_eq_left h₁
      have e₂ : f' r₂' = f r₂' h₂ := dite_eq_left h₂
      rw [e₁, e₂] at h_eq
      exact hf_inj r₁' h₁ r₂' h₂ h_eq
  -- The dual side: build a parallel injection `g : Plt → Qle` where
  -- `Plt = {P-roots < r}` and `Qle = {Q-roots ≤ r}`. For `r' ∈ Plt`, let
  -- `next r'` be the min `P`-root strictly greater than `r'`; this exists
  -- since `r ∈ P.roots` with `r > r'`. By Interlacing on `(r', next r')`,
  -- there is a unique `Q`-root in this gap, lying below `next r' ≤ r`.
  set Plt := P.roots.toFinset.filter (· < r)
  set Qle := Q.roots.toFinset.filter (· ≤ r)
  have hPlt_mem : ∀ {r'}, r' ∈ Plt ↔ r' ∈ P.roots ∧ r' < r := by
    intro r'; simp [Plt, Multiset.mem_toFinset]
  have hQle_mem : ∀ {q}, q ∈ Qle ↔ q ∈ Q.roots ∧ q ≤ r := by
    intro q; simp [Qle, Multiset.mem_toFinset]
  have hPgt_nonempty_for_lt : ∀ {r'}, r' ∈ Plt →
      (P.roots.toFinset.filter (r' < ·)).Nonempty := by
    intro r' hr'
    refine ⟨r, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, ?_⟩⟩
    exact (hPlt_mem.mp hr').2
  let next_P : ∀ r' ∈ Plt, R := fun r' hr' =>
    (P.roots.toFinset.filter (r' < ·)).min' (hPgt_nonempty_for_lt hr')
  have hnext_gt : ∀ r' (hr' : r' ∈ Plt), r' < next_P r' hr' := by
    intro r' hr'
    have h := (P.roots.toFinset.filter (r' < ·)).min'_mem (hPgt_nonempty_for_lt hr')
    exact (Finset.mem_filter.mp h).2
  have hnext_mem : ∀ r' (hr' : r' ∈ Plt), next_P r' hr' ∈ P.roots := by
    intro r' hr'
    have h := (P.roots.toFinset.filter (r' < ·)).min'_mem (hPgt_nonempty_for_lt hr')
    exact Multiset.mem_toFinset.mp (Finset.mem_filter.mp h).1
  have hnext_le_r : ∀ r' (hr' : r' ∈ Plt), next_P r' hr' ≤ r := by
    intro r' hr'
    apply (P.roots.toFinset.filter (r' < ·)).min'_le
    refine Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, ?_⟩
    exact (hPlt_mem.mp hr').2
  have hnext_no_between : ∀ r' (hr' : r' ∈ Plt) (r₃ : R), P.IsRoot r₃ →
      ¬ (r' < r₃ ∧ r₃ < next_P r' hr') := by
    intro r' hr' r₃ hr₃ ⟨h_left, h_right⟩
    have hr₃_finset : r₃ ∈ P.roots.toFinset.filter (r' < ·) := by
      refine Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne).mpr hr₃),
          h_left⟩
    have h_ge := (P.roots.toFinset.filter (r' < ·)).min'_le r₃ hr₃_finset
    exact absurd h_right (not_lt.mpr h_ge)
  have hnext_isRoot : ∀ r' (hr' : r' ∈ Plt), P.IsRoot (next_P r' hr') := by
    intro r' hr'
    exact (Polynomial.mem_roots hP_ne).mp (hnext_mem r' hr')
  have hr'_isRoot_lt : ∀ r' (hr' : r' ∈ Plt), P.IsRoot r' := by
    intro r' hr'
    exact (Polynomial.mem_roots hP_ne).mp (hPlt_mem.mp hr').1
  let g : ∀ r' ∈ Plt, R := fun r' hr' =>
    (hint r' (next_P r' hr') (hnext_gt r' hr') (hr'_isRoot_lt r' hr')
      (hnext_isRoot r' hr') (hnext_no_between r' hr')).choose
  have hg_spec : ∀ r' (hr' : r' ∈ Plt),
      Q.IsRoot (g r' hr') ∧ r' < g r' hr' ∧ g r' hr' < next_P r' hr' := by
    intro r' hr'
    exact (hint r' (next_P r' hr') (hnext_gt r' hr') (hr'_isRoot_lt r' hr')
      (hnext_isRoot r' hr') (hnext_no_between r' hr')).choose_spec.1
  have hg_into_Qle : ∀ r' (hr' : r' ∈ Plt), g r' hr' ∈ Qle := by
    intro r' hr'
    refine hQle_mem.mpr ⟨(Polynomial.mem_roots hQ_ne).mpr (hg_spec r' hr').1, ?_⟩
    exact le_of_lt (lt_of_lt_of_le (hg_spec r' hr').2.2 (hnext_le_r r' hr'))
  have hg_inj : ∀ r₁' (h₁ : r₁' ∈ Plt) r₂' (h₂ : r₂' ∈ Plt),
      g r₁' h₁ = g r₂' h₂ → r₁' = r₂' := by
    intro r₁' h₁ r₂' h₂ hg_eq
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
    · -- r₁' < r₂'. Then next_P r₁' ≤ r₂'.
      have hr₂'_in_filter : r₂' ∈ P.roots.toFinset.filter (r₁' < ·) := by
        refine Finset.mem_filter.mpr ⟨?_, h_lt⟩
        exact Multiset.mem_toFinset.mpr (hPlt_mem.mp h₂).1
      have h_next_le_r₂ : next_P r₁' h₁ ≤ r₂' :=
        (P.roots.toFinset.filter (r₁' < ·)).min'_le _ hr₂'_in_filter
      have h_g₁_lt : g r₁' h₁ < next_P r₁' h₁ := (hg_spec r₁' h₁).2.2
      have h_g₂_gt : r₂' < g r₂' h₂ := (hg_spec r₂' h₂).2.1
      have : g r₁' h₁ < g r₂' h₂ :=
        lt_of_lt_of_le (lt_of_lt_of_le h_g₁_lt h_next_le_r₂) (le_of_lt h_g₂_gt)
      exact absurd hg_eq (ne_of_lt this)
    · -- Symmetric.
      have hr₁'_in_filter : r₁' ∈ P.roots.toFinset.filter (r₂' < ·) := by
        refine Finset.mem_filter.mpr ⟨?_, h_lt⟩
        exact Multiset.mem_toFinset.mpr (hPlt_mem.mp h₁).1
      have h_next_le_r₁ : next_P r₂' h₂ ≤ r₁' :=
        (P.roots.toFinset.filter (r₂' < ·)).min'_le _ hr₁'_in_filter
      have h_g₂_lt : g r₂' h₂ < next_P r₂' h₂ := (hg_spec r₂' h₂).2.2
      have h_g₁_gt : r₁' < g r₁' h₁ := (hg_spec r₁' h₁).2.1
      have : g r₂' h₂ < g r₁' h₁ :=
        lt_of_lt_of_le (lt_of_lt_of_le h_g₂_lt h_next_le_r₁) (le_of_lt h_g₁_gt)
      exact absurd hg_eq.symm (ne_of_lt this)
  let g' : R → R := fun r' => if h : r' ∈ Plt then g r' h else r'
  have h_Plt_le_Qle : Plt.card ≤ Qle.card := by
    apply Finset.card_le_card_of_injOn g'
    · intro r' hr'
      show g' r' ∈ Qle
      have : g' r' = g r' hr' := dite_eq_left hr'
      rw [this]
      exact hg_into_Qle r' hr'
    · intro r₁' h₁ r₂' h₂ h_eq
      simp only [Finset.mem_coe] at h₁ h₂
      have e₁ : g' r₁' = g r₁' h₁ := dite_eq_left h₁
      have e₂ : g' r₂' = g r₂' h₂ := dite_eq_left h₂
      rw [e₁, e₂] at h_eq
      exact hg_inj r₁' h₁ r₂' h₂ h_eq
  -- Total counts force equality: `|Pgt| + |Plt| + 1 = p` (Nodup, r ∈ P.roots),
  -- and `|Qgt| + |Qle| = p − 1`. Combined with the two `≤` inequalities,
  -- equality is forced in both.
  have hP_total : Pgt.card + Plt.card + 1 = P.natDegree := by
    have h_P_split : P.roots.toFinset =
        Pgt ∪ Plt ∪ {r} := by
      ext a
      simp only [Pgt, Plt, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton,
        Multiset.mem_toFinset]
      constructor
      · intro ha
        rcases lt_trichotomy r a with h | h | h
        · exact Or.inl (Or.inl ⟨ha, h⟩)
        · exact Or.inr h.symm
        · exact Or.inl (Or.inr ⟨ha, h⟩)
      · rintro ((⟨ha, _⟩ | ⟨ha, _⟩) | h_eq)
        · exact ha
        · exact ha
        · rw [h_eq]; exact hr
    have h_disj_PgtPlt : Disjoint Pgt Plt := by
      rw [Finset.disjoint_left]
      intro x hx_gt hx_lt
      have h1 := (Finset.mem_filter.mp hx_gt).2
      have h2 := (Finset.mem_filter.mp hx_lt).2
      exact absurd (lt_trans h1 h2) (lt_irrefl r)
    have h_disj_r : Disjoint (Pgt ∪ Plt) ({r} : Finset R) := by
      rw [Finset.disjoint_right]
      intro x hx hx_in
      have hxr : x = r := Finset.mem_singleton.mp hx
      rcases Finset.mem_union.mp hx_in with h | h
      · have := (Finset.mem_filter.mp h).2
        rw [hxr] at this
        exact absurd this (lt_irrefl r)
      · have := (Finset.mem_filter.mp h).2
        rw [hxr] at this
        exact absurd this (lt_irrefl r)
    have h_natDeg : P.natDegree = P.roots.toFinset.card :=
      ((Multiset.toFinset_card_of_nodup hP_nodup).trans hP_card).symm
    rw [h_natDeg, h_P_split,
      Finset.card_union_of_disjoint h_disj_r,
      Finset.card_union_of_disjoint h_disj_PgtPlt,
      Finset.card_singleton]
  have hQ_total : Qgt.card + Qle.card = Q.natDegree := by
    have h_Q_split : Q.roots.toFinset = Qgt ∪ Qle := by
      ext a
      simp only [Qgt, Qle, Finset.mem_union, Finset.mem_filter, Multiset.mem_toFinset]
      constructor
      · intro ha
        by_cases h : r < a
        · exact Or.inl ⟨ha, h⟩
        · exact Or.inr ⟨ha, not_lt.mp h⟩
      · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    have h_disj_QgtQle : Disjoint Qgt Qle := by
      rw [Finset.disjoint_left]
      intro x hx_gt hx_le
      exact absurd (Finset.mem_filter.mp hx_le).2
        (not_le.mpr (Finset.mem_filter.mp hx_gt).2)
    have h_natDeg_Q : Q.natDegree = Q.roots.toFinset.card :=
      ((Multiset.toFinset_card_of_nodup hQ_nodup).trans hQ_card).symm
    rw [h_natDeg_Q, h_Q_split,
      Finset.card_union_of_disjoint h_disj_QgtQle]
  -- From `|Pgt| + |Plt| + 1 = p`, `|Qgt| + |Qle| = p − 1`, and
  -- `|Pgt| ≤ |Qgt|`, `|Plt| ≤ |Qle|`, conclude equality.
  omega

omit [IsStrictOrderedRing R] in
/-- Under the structural conditions, no `P`-root is a `Q`-root.

    Proof outline: build the same `Pgt → Qgt` and `Plt → Qlt` injections as
    in `card_filter_gt_Q_eq_P`, but now noting that the second injection's
    image is strictly less than `r` (since `g r' < next_P r' ≤ r`). The
    cardinality bounds plus total counts force
    `count(r, Q.roots.toFinset) = 0`. -/
private lemma P_root_not_Q_root
    {P Q : R[X]} (hP_ne : P ≠ 0) (hQ_ne : Q ≠ 0)
    (hP_card : Multiset.card P.roots = P.natDegree)
    (hP_nodup : P.roots.Nodup)
    (hQ_card : Multiset.card Q.roots = Q.natDegree)
    (hQ_nodup : Q.roots.Nodup)
    (hq : Q.natDegree + 1 = P.natDegree)
    (hint : Interlacing P Q)
    {r : R} (hr : r ∈ P.roots) : r ∉ Q.roots := by
  classical
  intro hr_Q
  -- Repeat the injection construction from `card_filter_gt_Q_eq_P`, but
  -- now use the strict-less-than image for `g`.
  set Pgt := P.roots.toFinset.filter (r < ·)
  set Plt := P.roots.toFinset.filter (· < r)
  set Qgt := Q.roots.toFinset.filter (r < ·)
  set Qlt := Q.roots.toFinset.filter (· < r)
  set Qle := Q.roots.toFinset.filter (· ≤ r)
  have hPgt_mem : ∀ {r'}, r' ∈ Pgt ↔ r' ∈ P.roots ∧ r < r' := by
    intro r'; simp [Pgt, Multiset.mem_toFinset]
  have hPlt_mem : ∀ {r'}, r' ∈ Plt ↔ r' ∈ P.roots ∧ r' < r := by
    intro r'; simp [Plt, Multiset.mem_toFinset]
  have hQlt_mem : ∀ {q}, q ∈ Qlt ↔ q ∈ Q.roots ∧ q < r := by
    intro q; simp [Qlt, Multiset.mem_toFinset]
  have hQgt_mem : ∀ {q}, q ∈ Qgt ↔ q ∈ Q.roots ∧ r < q := by
    intro q; simp [Qgt, Multiset.mem_toFinset]
  -- f : Pgt → Qgt (same as in card_filter_gt_Q_eq_P).
  have hPlt_lt_nonempty : ∀ {r'}, r' ∈ Pgt →
      (P.roots.toFinset.filter (· < r')).Nonempty := by
    intro r' hr'
    refine ⟨r, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, ?_⟩⟩
    exact (hPgt_mem.mp hr').2
  let prev : ∀ r' ∈ Pgt, R := fun r' hr' =>
    (P.roots.toFinset.filter (· < r')).max' (hPlt_lt_nonempty hr')
  have hprev_lt : ∀ r' (hr' : r' ∈ Pgt), prev r' hr' < r' := fun r' hr' =>
    (Finset.mem_filter.mp ((P.roots.toFinset.filter
      (· < r')).max'_mem (hPlt_lt_nonempty hr'))).2
  have hprev_mem : ∀ r' (hr' : r' ∈ Pgt), prev r' hr' ∈ P.roots := fun r' hr' =>
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp
      ((P.roots.toFinset.filter (· < r')).max'_mem (hPlt_lt_nonempty hr'))).1
  have hprev_ge : ∀ r' (hr' : r' ∈ Pgt), r ≤ prev r' hr' := by
    intro r' hr'
    apply (P.roots.toFinset.filter (· < r')).le_max'
    refine Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, ?_⟩
    exact (hPgt_mem.mp hr').2
  have hprev_no_between : ∀ r' (hr' : r' ∈ Pgt) (r₃ : R), P.IsRoot r₃ →
      ¬ (prev r' hr' < r₃ ∧ r₃ < r') := by
    intro r' hr' r₃ hr₃ ⟨h_left, h_right⟩
    have hr₃_finset : r₃ ∈ P.roots.toFinset.filter (· < r') :=
      Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne).mpr hr₃), h_right⟩
    have h_le := (P.roots.toFinset.filter (· < r')).le_max' r₃ hr₃_finset
    exact absurd h_left (not_lt.mpr h_le)
  let f : ∀ r' ∈ Pgt, R := fun r' hr' =>
    (hint (prev r' hr') r' (hprev_lt r' hr')
      ((Polynomial.mem_roots hP_ne).mp (hprev_mem r' hr'))
      ((Polynomial.mem_roots hP_ne).mp (hPgt_mem.mp hr').1)
      (hprev_no_between r' hr')).choose
  have hf_spec : ∀ r' (hr' : r' ∈ Pgt),
      Q.IsRoot (f r' hr') ∧ prev r' hr' < f r' hr' ∧ f r' hr' < r' := fun r' hr' =>
    (hint (prev r' hr') r' (hprev_lt r' hr')
      ((Polynomial.mem_roots hP_ne).mp (hprev_mem r' hr'))
      ((Polynomial.mem_roots hP_ne).mp (hPgt_mem.mp hr').1)
      (hprev_no_between r' hr')).choose_spec.1
  have hf_into_Qgt : ∀ r' (hr' : r' ∈ Pgt), f r' hr' ∈ Qgt := fun r' hr' =>
    hQgt_mem.mpr ⟨(Polynomial.mem_roots hQ_ne).mpr (hf_spec r' hr').1,
      lt_of_le_of_lt (hprev_ge r' hr') (hf_spec r' hr').2.1⟩
  have hf_inj : ∀ r₁' (h₁ : r₁' ∈ Pgt) r₂' (h₂ : r₂' ∈ Pgt),
      f r₁' h₁ = f r₂' h₂ → r₁' = r₂' := by
    intro r₁' h₁ r₂' h₂ hf_eq
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
    · have h_prev_ge : r₁' ≤ prev r₂' h₂ :=
        (P.roots.toFinset.filter (· < r₂')).le_max' _
          (Finset.mem_filter.mpr
            ⟨Multiset.mem_toFinset.mpr (hPgt_mem.mp h₁).1, h_lt⟩)
      exact absurd hf_eq (ne_of_lt
        (lt_of_lt_of_le (hf_spec r₁' h₁).2.2
          (le_trans h_prev_ge (le_of_lt (hf_spec r₂' h₂).2.1))))
    · have h_prev_ge : r₂' ≤ prev r₁' h₁ :=
        (P.roots.toFinset.filter (· < r₁')).le_max' _
          (Finset.mem_filter.mpr
            ⟨Multiset.mem_toFinset.mpr (hPgt_mem.mp h₂).1, h_lt⟩)
      exact absurd hf_eq.symm (ne_of_lt
        (lt_of_lt_of_le (hf_spec r₂' h₂).2.2
          (le_trans h_prev_ge (le_of_lt (hf_spec r₁' h₁).2.1))))
  let f' : R → R := fun r' => if h : r' ∈ Pgt then f r' h else r'
  have h_Pgt_le_Qgt : Pgt.card ≤ Qgt.card := by
    apply Finset.card_le_card_of_injOn f'
    · intro r' hr'
      show f' r' ∈ Qgt
      have : f' r' = f r' hr' := dite_eq_left hr'
      rw [this]; exact hf_into_Qgt r' hr'
    · intro r₁' h₁ r₂' h₂ h_eq
      simp only [Finset.mem_coe] at h₁ h₂
      rw [show f' r₁' = f r₁' h₁ from dite_eq_left h₁,
        show f' r₂' = f r₂' h₂ from dite_eq_left h₂] at h_eq
      exact hf_inj r₁' h₁ r₂' h₂ h_eq
  -- Dual injection g : Plt → Qlt (strict — image is < r).
  have hPgt_gt_nonempty : ∀ {r'}, r' ∈ Plt →
      (P.roots.toFinset.filter (r' < ·)).Nonempty := by
    intro r' hr'
    refine ⟨r, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, ?_⟩⟩
    exact (hPlt_mem.mp hr').2
  let next_P : ∀ r' ∈ Plt, R := fun r' hr' =>
    (P.roots.toFinset.filter (r' < ·)).min' (hPgt_gt_nonempty hr')
  have hnext_gt : ∀ r' (hr' : r' ∈ Plt), r' < next_P r' hr' := fun r' hr' =>
    (Finset.mem_filter.mp ((P.roots.toFinset.filter
      (r' < ·)).min'_mem (hPgt_gt_nonempty hr'))).2
  have hnext_mem : ∀ r' (hr' : r' ∈ Plt), next_P r' hr' ∈ P.roots := fun r' hr' =>
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp
      ((P.roots.toFinset.filter (r' < ·)).min'_mem (hPgt_gt_nonempty hr'))).1
  have hnext_le_r : ∀ r' (hr' : r' ∈ Plt), next_P r' hr' ≤ r := by
    intro r' hr'
    apply (P.roots.toFinset.filter (r' < ·)).min'_le
    refine Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, ?_⟩
    exact (hPlt_mem.mp hr').2
  have hnext_no_between : ∀ r' (hr' : r' ∈ Plt) (r₃ : R), P.IsRoot r₃ →
      ¬ (r' < r₃ ∧ r₃ < next_P r' hr') := by
    intro r' hr' r₃ hr₃ ⟨h_left, h_right⟩
    have hr₃_finset : r₃ ∈ P.roots.toFinset.filter (r' < ·) :=
      Finset.mem_filter.mpr
        ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne).mpr hr₃), h_left⟩
    have h_ge := (P.roots.toFinset.filter (r' < ·)).min'_le r₃ hr₃_finset
    exact absurd h_right (not_lt.mpr h_ge)
  let g : ∀ r' ∈ Plt, R := fun r' hr' =>
    (hint r' (next_P r' hr') (hnext_gt r' hr')
      ((Polynomial.mem_roots hP_ne).mp (hPlt_mem.mp hr').1)
      ((Polynomial.mem_roots hP_ne).mp (hnext_mem r' hr'))
      (hnext_no_between r' hr')).choose
  have hg_spec : ∀ r' (hr' : r' ∈ Plt),
      Q.IsRoot (g r' hr') ∧ r' < g r' hr' ∧ g r' hr' < next_P r' hr' := fun r' hr' =>
    (hint r' (next_P r' hr') (hnext_gt r' hr')
      ((Polynomial.mem_roots hP_ne).mp (hPlt_mem.mp hr').1)
      ((Polynomial.mem_roots hP_ne).mp (hnext_mem r' hr'))
      (hnext_no_between r' hr')).choose_spec.1
  -- Key: image is in Qlt strictly (since g r' < next_P r' ≤ r).
  have hg_into_Qlt : ∀ r' (hr' : r' ∈ Plt), g r' hr' ∈ Qlt := by
    intro r' hr'
    refine hQlt_mem.mpr ⟨(Polynomial.mem_roots hQ_ne).mpr (hg_spec r' hr').1, ?_⟩
    exact lt_of_lt_of_le (hg_spec r' hr').2.2 (hnext_le_r r' hr')
  have hg_inj : ∀ r₁' (h₁ : r₁' ∈ Plt) r₂' (h₂ : r₂' ∈ Plt),
      g r₁' h₁ = g r₂' h₂ → r₁' = r₂' := by
    intro r₁' h₁ r₂' h₂ hg_eq
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
    · have h_next_le : next_P r₁' h₁ ≤ r₂' :=
        (P.roots.toFinset.filter (r₁' < ·)).min'_le _
          (Finset.mem_filter.mpr
            ⟨Multiset.mem_toFinset.mpr (hPlt_mem.mp h₂).1, h_lt⟩)
      exact absurd hg_eq (ne_of_lt
        (lt_of_lt_of_le (lt_of_lt_of_le (hg_spec r₁' h₁).2.2 h_next_le)
          (le_of_lt (hg_spec r₂' h₂).2.1)))
    · have h_next_le : next_P r₂' h₂ ≤ r₁' :=
        (P.roots.toFinset.filter (r₂' < ·)).min'_le _
          (Finset.mem_filter.mpr
            ⟨Multiset.mem_toFinset.mpr (hPlt_mem.mp h₁).1, h_lt⟩)
      exact absurd hg_eq.symm (ne_of_lt
        (lt_of_lt_of_le (lt_of_lt_of_le (hg_spec r₂' h₂).2.2 h_next_le)
          (le_of_lt (hg_spec r₁' h₁).2.1)))
  let g' : R → R := fun r' => if h : r' ∈ Plt then g r' h else r'
  have h_Plt_le_Qlt : Plt.card ≤ Qlt.card := by
    apply Finset.card_le_card_of_injOn g'
    · intro r' hr'
      show g' r' ∈ Qlt
      have : g' r' = g r' hr' := dite_eq_left hr'
      rw [this]; exact hg_into_Qlt r' hr'
    · intro r₁' h₁ r₂' h₂ h_eq
      simp only [Finset.mem_coe] at h₁ h₂
      rw [show g' r₁' = g r₁' h₁ from dite_eq_left h₁,
        show g' r₂' = g r₂' h₂ from dite_eq_left h₂] at h_eq
      exact hg_inj r₁' h₁ r₂' h₂ h_eq
  -- Cardinality contradiction.
  have hP_total : Pgt.card + Plt.card + 1 = P.natDegree := by
    have h_P_split : P.roots.toFinset = Pgt ∪ Plt ∪ {r} := by
      ext a
      simp only [Pgt, Plt, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton,
        Multiset.mem_toFinset]
      constructor
      · intro ha
        rcases lt_trichotomy r a with h | h | h
        · exact Or.inl (Or.inl ⟨ha, h⟩)
        · exact Or.inr h.symm
        · exact Or.inl (Or.inr ⟨ha, h⟩)
      · rintro ((⟨ha, _⟩ | ⟨ha, _⟩) | h_eq)
        · exact ha
        · exact ha
        · rw [h_eq]; exact hr
    have h_disj_PgtPlt : Disjoint Pgt Plt := by
      rw [Finset.disjoint_left]
      intro x hx_gt hx_lt
      exact absurd (lt_trans (Finset.mem_filter.mp hx_gt).2
        (Finset.mem_filter.mp hx_lt).2) (lt_irrefl r)
    have h_disj_r : Disjoint (Pgt ∪ Plt) ({r} : Finset R) := by
      rw [Finset.disjoint_right]
      intro x hx hx_in
      have hxr : x = r := Finset.mem_singleton.mp hx
      rcases Finset.mem_union.mp hx_in with h | h
      · have := (Finset.mem_filter.mp h).2; rw [hxr] at this
        exact absurd this (lt_irrefl r)
      · have := (Finset.mem_filter.mp h).2; rw [hxr] at this
        exact absurd this (lt_irrefl r)
    have h_natDeg : P.natDegree = P.roots.toFinset.card :=
      ((Multiset.toFinset_card_of_nodup hP_nodup).trans hP_card).symm
    rw [h_natDeg, h_P_split,
      Finset.card_union_of_disjoint h_disj_r,
      Finset.card_union_of_disjoint h_disj_PgtPlt,
      Finset.card_singleton]
  -- Q-side: include the (assumed) `r ∈ Q.roots` so card splits as
  -- `|Qgt| + 1 + |Qlt| = q = p − 1`.
  have hr_Q_finset : r ∈ Q.roots.toFinset := Multiset.mem_toFinset.mpr hr_Q
  have hQ_total : Qgt.card + Qlt.card + 1 = Q.natDegree := by
    have h_Q_split : Q.roots.toFinset = Qgt ∪ Qlt ∪ {r} := by
      ext a
      simp only [Qgt, Qlt, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton,
        Multiset.mem_toFinset]
      constructor
      · intro ha
        rcases lt_trichotomy r a with h | h | h
        · exact Or.inl (Or.inl ⟨ha, h⟩)
        · exact Or.inr h.symm
        · exact Or.inl (Or.inr ⟨ha, h⟩)
      · rintro ((⟨ha, _⟩ | ⟨ha, _⟩) | h_eq)
        · exact ha
        · exact ha
        · rw [h_eq]; exact hr_Q
    have h_disj_QgtQlt : Disjoint Qgt Qlt := by
      rw [Finset.disjoint_left]
      intro x hx_gt hx_lt
      exact absurd (lt_trans (Finset.mem_filter.mp hx_gt).2
        (Finset.mem_filter.mp hx_lt).2) (lt_irrefl r)
    have h_disj_r : Disjoint (Qgt ∪ Qlt) ({r} : Finset R) := by
      rw [Finset.disjoint_right]
      intro x hx hx_in
      have hxr : x = r := Finset.mem_singleton.mp hx
      rcases Finset.mem_union.mp hx_in with h | h
      · have := (Finset.mem_filter.mp h).2; rw [hxr] at this
        exact absurd this (lt_irrefl r)
      · have := (Finset.mem_filter.mp h).2; rw [hxr] at this
        exact absurd this (lt_irrefl r)
    have h_natDeg : Q.natDegree = Q.roots.toFinset.card :=
      ((Multiset.toFinset_card_of_nodup hQ_nodup).trans hQ_card).symm
    rw [h_natDeg, h_Q_split,
      Finset.card_union_of_disjoint h_disj_r,
      Finset.card_union_of_disjoint h_disj_QgtQlt,
      Finset.card_singleton]
  -- Combine: `|Pgt| + |Plt| + 1 = p`, `|Qgt| + |Qlt| + 1 = p − 1` (from r ∈ Q.roots),
  -- and `|Pgt| ≤ |Qgt|`, `|Plt| ≤ |Qlt|`. Then `p − 1 ≤ p − 2`, contradiction.
  omega

/-- **The composite "jump" lemma.** Under the structural conditions of
    Remark 2.55(a) plus the IVP for `R`, every `P`-root produces a
    `−∞ → +∞` jump of `Q/P`. -/
private lemma jumps_at_P_root
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X])
    (hP_ne : P ≠ 0) (hQ_ne : Q ≠ 0)
    (hP_card : Multiset.card P.roots = P.natDegree)
    (hP_nodup : P.roots.Nodup)
    (hQ_card : Multiset.card Q.roots = Q.natDegree)
    (hQ_nodup : Q.roots.Nodup)
    (hq : Q.natDegree + 1 = P.natDegree)
    (hsign : SignType.sign P.leadingCoeff = SignType.sign Q.leadingCoeff)
    (hint : Interlacing P Q)
    {r : R} (hr : r ∈ P.roots) :
    JumpsFromNegInfToPosInf Q P r := by
  classical
  -- (1) `r` is a simple root of `P`, not a root of `Q`.
  have h_mP_one : P.rootMultiplicity r = 1 := by
    have h_count : Multiset.count r P.roots = 1 := by
      have h_le : Multiset.count r P.roots ≤ 1 :=
        Multiset.nodup_iff_count_le_one.mp hP_nodup r
      have h_ge : 1 ≤ Multiset.count r P.roots :=
        Multiset.one_le_count_iff_mem.mpr hr
      omega
    rw [← Polynomial.count_roots]; exact h_count
  have hr_notQ : r ∉ Q.roots :=
    P_root_not_Q_root hP_ne hQ_ne hP_card hP_nodup hQ_card hQ_nodup hq hint hr
  have h_mQ_zero : Q.rootMultiplicity r = 0 := by
    by_contra h
    apply hr_notQ
    rw [Polynomial.mem_roots hQ_ne]
    exact (Polynomial.rootMultiplicity_pos hQ_ne).mp (Nat.pos_of_ne_zero h)
  -- (2) Multiplicity inequality and oddness.
  have h_gt : P.rootMultiplicity r > Q.rootMultiplicity r := by
    rw [h_mP_one, h_mQ_zero]; omega
  have h_odd : Odd (P.rootMultiplicity r - Q.rootMultiplicity r) := by
    rw [h_mP_one, h_mQ_zero]; decide
  -- (3) Sign analysis on `(Q * P)' (r) = Q(r) · P'(r)`.
  have hQP_ne : Q * P ≠ 0 := mul_ne_zero hQ_ne hP_ne
  have hQP_card_filter_eq :
      Multiset.card (Q.roots.filter (r < ·)) =
        Multiset.card (P.roots.filter (r < ·)) :=
    card_filter_gt_Q_eq_P P Q hP_ne hQ_ne hP_card hP_nodup hQ_card hQ_nodup
      hq hint hr
  have hP_eval_zero : P.eval r = 0 := (Polynomial.mem_roots hP_ne).mp hr
  have h_QP_deriv_eval :
      (Q * P).derivative.eval r = Q.eval r * P.derivative.eval r := by
    rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, hP_eval_zero, mul_zero, zero_add]
  have h_sign_P_deriv : SignType.sign (P.derivative.eval r) =
      SignType.sign P.leadingCoeff *
        (-1 : SignType) ^ (Multiset.card (P.roots.filter (r < ·))) :=
    sign_derivative_at_simple_root hP_card hP_nodup hr
  have h_sign_Q_eval : SignType.sign (Q.eval r) =
      SignType.sign Q.leadingCoeff *
        (-1 : SignType) ^ (Multiset.card (Q.roots.filter (r < ·))) :=
    sign_eval_at_non_root hQ_card hr_notQ
  -- The product simplifies to 1 under matching leading-coeff signs and
  -- equal filter counts, since `e * e = 1` for `e ∈ {-1, 1} ⊆ SignType`.
  have h_lc_ne : SignType.sign Q.leadingCoeff ≠ 0 := by
    rw [Ne, sign_eq_zero_iff, Polynomial.leadingCoeff_eq_zero]
    exact hQ_ne
  have h_sign_QP_deriv : SignType.sign ((Q * P).derivative.eval r) = 1 := by
    rw [h_QP_deriv_eval, sign_mul, h_sign_Q_eval, h_sign_P_deriv,
      hQP_card_filter_eq, hsign]
    -- Goal: `(sign Q.leadingCoeff * (-1)^k) * (sign Q.leadingCoeff * (-1)^k) = 1`
    set e := SignType.sign Q.leadingCoeff *
      (-1 : SignType) ^ Multiset.card (P.roots.filter (r < ·))
    have h_e_ne : e ≠ 0 := by
      simp only [e, ne_eq, mul_eq_zero, not_or]
      refine ⟨h_lc_ne, ?_⟩
      exact pow_ne_zero _ (by decide : (-1 : SignType) ≠ 0)
    -- For any nonzero `e : SignType`, `e * e = 1`.
    rcases SignType.trichotomy e with h_e | h_e | h_e
    · rw [h_e]; decide
    · exact absurd h_e h_e_ne
    · rw [h_e]; decide
  -- (4) Apply Proposition 2.21 to translate sign of derivative into HasSignRight.
  have h_QP_rm : (Q * P).rootMultiplicity r = 1 := by
    rw [Polynomial.rootMultiplicity_mul hQP_ne, h_mQ_zero, h_mP_one]
  have h_right := Proposition2_21.proposition_2_21_right hIVP hQP_ne r
  -- `h_right : HasSignRight (Q * P) r (sign((D^k)(Q*P).eval r))`, k = 1.
  -- Convert `(D^1)` to `derivative`.
  have h_iter1 : (((⇑Polynomial.derivative)^[(Q * P).rootMultiplicity r])
      (Q * P)).eval r = (Q * P).derivative.eval r := by
    rw [h_QP_rm]; simp
  rw [h_iter1, h_sign_QP_deriv] at h_right
  exact ⟨h_gt, h_odd, h_right⟩

/-- **Key forward-direction lemma.** Between any two distinct `P`-roots
    `r₁ < r₂` with no other `P`-root strictly between, if both produce
    `−∞ → +∞` jumps and neither is a `Q`-root, then `Q` has a root in
    `(r₁, r₂)`.

    Proof: from the jump condition at `r₂`, Proposition 2.21 (right) and
    uniqueness of `HasSignRight` give `sign((Q · P)' r₂) = 1`. Then
    Proposition 2.21 (left) at `r₂` gives `HasSignLeft (Q · P) r₂ (-1)`,
    since the multiplicity is 1. Combined with `HasSignRight (Q · P) r₁ 1`,
    we have `(Q · P)(t)` positive just to the right of `r₁` and negative
    just to the left of `r₂`. The IVP applied to `Q · P` gives a zero,
    which must be a `Q`-root since `P` has no roots between `r₁` and `r₂`. -/
private lemma exists_Q_root_in_gap
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hP_ne : P ≠ 0) (hQ_ne : Q ≠ 0)
    (h_simple : ∀ r ∈ P.roots, P.rootMultiplicity r = 1)
    (h_jump : ∀ r ∈ P.roots, JumpsFromNegInfToPosInf Q P r)
    (h_not_Q : ∀ r ∈ P.roots, r ∉ Q.roots)
    {r₁ r₂ : R} (hr₁ : r₁ ∈ P.roots) (hr₂ : r₂ ∈ P.roots) (h_lt : r₁ < r₂)
    (h_no_between : ∀ r₃ ∈ P.roots, ¬ (r₁ < r₃ ∧ r₃ < r₂)) :
    ∃ q ∈ Q.roots, r₁ < q ∧ q < r₂ := by
  classical
  -- Sign on the right of `r₁` is `+1`.
  obtain ⟨_, _, hsign_r₁⟩ := h_jump r₁ hr₁
  -- Multiplicity of `Q · P` at each P-root is `1`.
  have hQP_ne : Q * P ≠ 0 := mul_ne_zero hQ_ne hP_ne
  have h_mQP_one : ∀ r ∈ P.roots, (Q * P).rootMultiplicity r = 1 := by
    intro r hr
    rw [Polynomial.rootMultiplicity_mul hQP_ne]
    have : Q.rootMultiplicity r = 0 := by
      by_contra h
      apply h_not_Q r hr
      rw [Polynomial.mem_roots hQ_ne]
      exact (Polynomial.rootMultiplicity_pos hQ_ne).mp (Nat.pos_of_ne_zero h)
    rw [this, h_simple r hr]
  -- Apply Prop 2.21 right at `r₂`: HasSignRight (Q*P) r₂ (sign((D^k)(Q*P) r₂)).
  have h_right_r₂ := Proposition2_21.proposition_2_21_right hIVP hQP_ne r₂
  -- From jump at `r₂`: HasSignRight (Q*P) r₂ 1.
  obtain ⟨_, _, hsign_r₂⟩ := h_jump r₂ hr₂
  -- Uniqueness: sign of derivative = 1.
  have h_sign_at_r₂ : SignType.sign
      ((((⇑Polynomial.derivative)^[(Q * P).rootMultiplicity r₂]) (Q * P)).eval r₂) =
        1 := h_right_r₂.unique hsign_r₂
  -- Apply Prop 2.21 left at `r₂` to get HasSignLeft (Q*P) r₂ (-1).
  have h_left_r₂ := Proposition2_21.proposition_2_21_left hIVP hQP_ne r₂
  rw [h_sign_at_r₂, mul_one] at h_left_r₂
  have h_mQP_r₂ : (Q * P).rootMultiplicity r₂ = 1 := h_mQP_one r₂ hr₂
  rw [h_mQP_r₂, pow_one] at h_left_r₂
  -- Now: HasSignRight (Q*P) r₁ 1, HasSignLeft (Q*P) r₂ (-1). Find t₀, t₁.
  obtain ⟨b₁, hb₁_gt, hb₁_sign⟩ := hsign_r₁
  obtain ⟨a₂, ha₂_lt, ha₂_sign⟩ := h_left_r₂
  -- Choose `t₀` strictly between `r₁` and `min b₁ r₂`.
  have h_min_gt_r₁ : r₁ < min b₁ r₂ := lt_min hb₁_gt h_lt
  obtain ⟨t₀, ht₀_lo, ht₀_hi⟩ := exists_between h_min_gt_r₁
  have ht₀_lt_r₂ : t₀ < r₂ := lt_of_lt_of_le ht₀_hi (min_le_right _ _)
  have ht₀_lt_b₁ : t₀ < b₁ := lt_of_lt_of_le ht₀_hi (min_le_left _ _)
  have h_QP_t₀_pos : 0 < (Q * P).eval t₀ := by
    have h_sign := hb₁_sign t₀ ⟨ht₀_lo, ht₀_lt_b₁⟩
    exact sign_eq_one_iff.mp h_sign
  -- Choose `t₁` strictly between `max a₂ t₀` and `r₂`.
  have h_max_lt_r₂ : max a₂ t₀ < r₂ := max_lt ha₂_lt ht₀_lt_r₂
  obtain ⟨t₁, ht₁_lo, ht₁_hi⟩ := exists_between h_max_lt_r₂
  have ht₁_gt_a₂ : a₂ < t₁ := lt_of_le_of_lt (le_max_left _ _) ht₁_lo
  have ht₁_gt_t₀ : t₀ < t₁ := lt_of_le_of_lt (le_max_right _ _) ht₁_lo
  have h_QP_t₁_neg : (Q * P).eval t₁ < 0 := by
    have h_sign := ha₂_sign t₁ ⟨ht₁_gt_a₂, ht₁_hi⟩
    exact sign_eq_neg_one_iff.mp h_sign
  -- Apply IVP to `Q * P` on `(t₀, t₁)`.
  have h_prod_neg : (Q * P).eval t₀ * (Q * P).eval t₁ < 0 :=
    mul_neg_of_pos_of_neg h_QP_t₀_pos h_QP_t₁_neg
  obtain ⟨c, hc_lo, hc_hi, hc_zero⟩ := hIVP (Q * P) t₀ t₁ ht₁_gt_t₀ h_prod_neg
  -- `c ∈ (r₁, r₂)`: from `r₁ < t₀ < c < t₁ < r₂`.
  have hc_gt_r₁ : r₁ < c := lt_trans ht₀_lo hc_lo
  have hc_lt_r₂ : c < r₂ := lt_trans hc_hi ht₁_hi
  -- `(Q · P)(c) = 0` and `P(c) ≠ 0` (no `P`-root between `r₁` and `r₂`),
  -- so `Q(c) = 0`.
  have hP_c_ne : P.eval c ≠ 0 := by
    intro hP_c
    have hc_root : c ∈ P.roots := (Polynomial.mem_roots hP_ne).mpr hP_c
    exact h_no_between c hc_root ⟨hc_gt_r₁, hc_lt_r₂⟩
  have hQ_c : Q.eval c = 0 := by
    rw [Polynomial.eval_mul] at hc_zero
    rcases mul_eq_zero.mp hc_zero with h | h
    · exact h
    · exact absurd h hP_c_ne
  exact ⟨c, (Polynomial.mem_roots hQ_ne).mpr hQ_c, hc_gt_r₁, hc_lt_r₂⟩

/-- **BPR Remark 2.55(a).** With `p = deg(P)`, `q = deg(Q)`, and `q < p`:
    `Ind(Q/P; a, b) = p` if and only if
    1. `q = p − 1`,
    2. the signs of the leading coefficients of `P` and `Q` agree,
    3. all roots of `P` and `Q` are simple and lie in `(a, b)`, and
    4. between any two consecutive roots of `P` there is exactly one root
       of `Q`.

    The maximum possible value of the Cauchy index on any interval is
    `P.natDegree` (`cauchyIndexOn_le_natDegree`); attaining this maximum
    forces the structural conditions above. -/
theorem remark_2_55_a
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (Q P : R[X]) (a b : ExtendedPoint R)
    (hP_pos : 0 < P.natDegree)
    (hQ_lt : Q.degree < P.degree) :
    cauchyIndexOn Q P a b = (P.natDegree : ℤ) ↔
      Q.natDegree + 1 = P.natDegree ∧
      SignType.sign P.leadingCoeff = SignType.sign Q.leadingCoeff ∧
      Multiset.card P.roots = P.natDegree ∧
      P.roots.Nodup ∧
      Multiset.card Q.roots = Q.natDegree ∧
      Q.roots.Nodup ∧
      (∀ r ∈ P.roots, r ∈ ExtendedPoint.openInterval a b) ∧
      (∀ s ∈ Q.roots, s ∈ ExtendedPoint.openInterval a b) ∧
      Interlacing P Q := by
  classical
  refine ⟨?_, ?_⟩
  · -- Forward direction.
    intro h_cauchy
    obtain ⟨h_card_F, h_card_roots, h_nodup, h_jumps, _⟩ :=
      cauchyIndexOn_eq_natDegree_extract Q P a b h_cauchy
    have hP_ne : P ≠ 0 := by
      intro hP
      rw [hP] at hQ_lt
      simp [Polynomial.degree_zero] at hQ_lt
    -- Each P-root is simple.
    have h_P_root_simple : ∀ r ∈ P.roots, P.rootMultiplicity r = 1 := by
      intro r hr
      have h_count : Multiset.count r P.roots = 1 := by
        have h_le : Multiset.count r P.roots ≤ 1 :=
          Multiset.nodup_iff_count_le_one.mp h_nodup r
        have h_ge : 1 ≤ Multiset.count r P.roots :=
          Multiset.one_le_count_iff_mem.mpr hr
        omega
      rw [← Polynomial.count_roots]; exact h_count
    -- Each P-root is in `(a, b)` and gives a `−∞ → +∞` jump.
    have h_in_and_jump : ∀ r ∈ P.roots,
        r ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf Q P r := by
      intro r hr
      exact h_jumps r (Multiset.mem_toFinset.mpr hr)
    -- Each P-root is not a Q-root (from the jump conditions).
    have h_P_root_not_Q : ∀ r ∈ P.roots, r ∉ Q.roots := by
      intro r hr h_inQ
      obtain ⟨_, ⟨h_gt, _, _⟩⟩ := h_in_and_jump r hr
      have hQ_ne : Q ≠ 0 := by
        intro hQ; rw [hQ] at h_inQ; simp at h_inQ
      have h_mQ_ge_1 : 1 ≤ Q.rootMultiplicity r := by
        rw [← Polynomial.count_roots]
        exact Multiset.one_le_count_iff_mem.mpr h_inQ
      have h_mP : P.rootMultiplicity r = 1 := h_P_root_simple r hr
      omega
    -- Use the given `hP_pos` to enter the main case.
    · -- Main case: `P.natDegree ≥ 1` (from hypothesis).
      have h_roots_nonempty : P.roots.toFinset.Nonempty := by
        rw [← Finset.card_pos, h_card_F]; exact hP_pos
      have h_roots_nonempty' := h_roots_nonempty
      obtain ⟨r₀, hr₀⟩ := h_roots_nonempty'
      have hr₀_root : r₀ ∈ P.roots := Multiset.mem_toFinset.mp hr₀
      have hQ_ne : Q ≠ 0 := by
        intro hQ
        obtain ⟨_, ⟨_, _, hsign⟩⟩ := h_in_and_jump r₀ hr₀_root
        obtain ⟨b, hb_gt, hb_sign⟩ := hsign
        obtain ⟨t, ht_lo, ht_hi⟩ := exists_between hb_gt
        have h_sign_eq : SignType.sign ((Q * P).eval t) = 1 :=
          hb_sign t ⟨ht_lo, ht_hi⟩
        rw [hQ, zero_mul, Polynomial.eval_zero, sign_zero] at h_sign_eq
        exact absurd h_sign_eq (by decide)
      -- Build injection: for each non-max P-root r', produce Q-root in
      -- the gap (r', next_P r').
      set max_P := P.roots.toFinset.max' h_roots_nonempty
      have hmax_mem : max_P ∈ P.roots :=
        Multiset.mem_toFinset.mp (P.roots.toFinset.max'_mem _)
      set NonMax := P.roots.toFinset.filter (· < max_P)
      have hNonMax_card : NonMax.card = P.natDegree - 1 := by
        have h1 : NonMax = P.roots.toFinset.erase max_P := by
          ext x
          simp only [NonMax, Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨hx, hlt⟩
            exact ⟨ne_of_lt hlt, hx⟩
          · rintro ⟨hne, hx⟩
            refine ⟨hx, lt_of_le_of_ne (P.roots.toFinset.le_max' x hx) hne⟩
        rw [h1, Finset.card_erase_of_mem (P.roots.toFinset.max'_mem _), h_card_F]
      have hNonMax_lt : ∀ {r'}, r' ∈ NonMax → r' < max_P := by
        intro r' hr'; exact (Finset.mem_filter.mp hr').2
      have hNonMax_in_P : ∀ {r'}, r' ∈ NonMax → r' ∈ P.roots := by
        intro r' hr'
        exact Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr').1
      -- next_P r': min P-root > r'.
      have h_gt_nonempty : ∀ {r'}, r' ∈ NonMax →
          (P.roots.toFinset.filter (r' < ·)).Nonempty := by
        intro r' hr'
        refine ⟨max_P, Finset.mem_filter.mpr
          ⟨P.roots.toFinset.max'_mem _, hNonMax_lt hr'⟩⟩
      let next_P : ∀ r' ∈ NonMax, R := fun r' hr' =>
        (P.roots.toFinset.filter (r' < ·)).min' (h_gt_nonempty hr')
      have hnext_gt : ∀ r' (hr' : r' ∈ NonMax), r' < next_P r' hr' := fun r' hr' =>
        (Finset.mem_filter.mp ((P.roots.toFinset.filter
          (r' < ·)).min'_mem (h_gt_nonempty hr'))).2
      have hnext_mem : ∀ r' (hr' : r' ∈ NonMax), next_P r' hr' ∈ P.roots := fun r' hr' =>
        Multiset.mem_toFinset.mp (Finset.mem_filter.mp
          ((P.roots.toFinset.filter (r' < ·)).min'_mem (h_gt_nonempty hr'))).1
      have hnext_no_between : ∀ r' (hr' : r' ∈ NonMax) (r₃ : R), r₃ ∈ P.roots →
          ¬ (r' < r₃ ∧ r₃ < next_P r' hr') := by
        intro r' hr' r₃ hr₃ ⟨h_left, h_right⟩
        have hr₃_finset : r₃ ∈ P.roots.toFinset.filter (r' < ·) :=
          Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr₃, h_left⟩
        have h_ge := (P.roots.toFinset.filter (r' < ·)).min'_le r₃ hr₃_finset
        exact absurd h_right (not_lt.mpr h_ge)
      -- For each non-max P-root r', use exists_Q_root_in_gap.
      let φ : ∀ r' ∈ NonMax, R := fun r' hr' =>
        (exists_Q_root_in_gap hIVP P Q hP_ne hQ_ne h_P_root_simple
          (fun r hr => (h_in_and_jump r hr).2) h_P_root_not_Q
          (hNonMax_in_P hr') (hnext_mem r' hr') (hnext_gt r' hr')
          (fun r₃ hr₃ => hnext_no_between r' hr' r₃ hr₃)).choose
      have hφ_spec : ∀ r' (hr' : r' ∈ NonMax),
          φ r' hr' ∈ Q.roots ∧ r' < φ r' hr' ∧ φ r' hr' < next_P r' hr' := fun r' hr' =>
        (exists_Q_root_in_gap hIVP P Q hP_ne hQ_ne h_P_root_simple
          (fun r hr => (h_in_and_jump r hr).2) h_P_root_not_Q
          (hNonMax_in_P hr') (hnext_mem r' hr') (hnext_gt r' hr')
          (fun r₃ hr₃ => hnext_no_between r' hr' r₃ hr₃)).choose_spec
      -- φ maps to Q.roots.toFinset.
      have hφ_mem : ∀ r' (hr' : r' ∈ NonMax), φ r' hr' ∈ Q.roots.toFinset := by
        intro r' hr'
        exact Multiset.mem_toFinset.mpr (hφ_spec r' hr').1
      -- φ injective: different r' give different gaps.
      have hφ_inj : ∀ r₁ (h₁ : r₁ ∈ NonMax) r₂ (h₂ : r₂ ∈ NonMax),
          φ r₁ h₁ = φ r₂ h₂ → r₁ = r₂ := by
        intro r₁ h₁ r₂ h₂ hφ_eq
        by_contra h_ne
        rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
        · -- r₁ < r₂. Then next_P r₁ ≤ r₂.
          have hr₂_in_filter : r₂ ∈ P.roots.toFinset.filter (r₁ < ·) :=
            Finset.mem_filter.mpr
              ⟨Multiset.mem_toFinset.mpr (hNonMax_in_P h₂), h_lt⟩
          have h_next_le : next_P r₁ h₁ ≤ r₂ :=
            (P.roots.toFinset.filter (r₁ < ·)).min'_le _ hr₂_in_filter
          have h_φ₁_lt : φ r₁ h₁ < next_P r₁ h₁ := (hφ_spec r₁ h₁).2.2
          have h_φ₂_gt : r₂ < φ r₂ h₂ := (hφ_spec r₂ h₂).2.1
          exact absurd hφ_eq (ne_of_lt
            (lt_of_lt_of_le (lt_of_lt_of_le h_φ₁_lt h_next_le)
              (le_of_lt h_φ₂_gt)))
        · -- Symmetric.
          have hr₁_in_filter : r₁ ∈ P.roots.toFinset.filter (r₂ < ·) :=
            Finset.mem_filter.mpr
              ⟨Multiset.mem_toFinset.mpr (hNonMax_in_P h₁), h_lt⟩
          have h_next_le : next_P r₂ h₂ ≤ r₁ :=
            (P.roots.toFinset.filter (r₂ < ·)).min'_le _ hr₁_in_filter
          have h_φ₂_lt : φ r₂ h₂ < next_P r₂ h₂ := (hφ_spec r₂ h₂).2.2
          have h_φ₁_gt : r₁ < φ r₁ h₁ := (hφ_spec r₁ h₁).2.1
          exact absurd hφ_eq.symm (ne_of_lt
            (lt_of_lt_of_le (lt_of_lt_of_le h_φ₂_lt h_next_le)
              (le_of_lt h_φ₁_gt)))
      -- Cardinality bound: |NonMax| ≤ |Q.roots.toFinset|.
      let φ' : R → R := fun r' => if h : r' ∈ NonMax then φ r' h else r'
      have h_NonMax_le : NonMax.card ≤ Q.roots.toFinset.card := by
        apply Finset.card_le_card_of_injOn φ'
        · intro r' hr'
          show φ' r' ∈ Q.roots.toFinset
          have : φ' r' = φ r' hr' := dite_eq_left hr'
          rw [this]; exact hφ_mem r' hr'
        · intro r₁ h₁ r₂ h₂ h_eq
          simp only [Finset.mem_coe] at h₁ h₂
          rw [show φ' r₁ = φ r₁ h₁ from dite_eq_left h₁,
            show φ' r₂ = φ r₂ h₂ from dite_eq_left h₂] at h_eq
          exact hφ_inj r₁ h₁ r₂ h₂ h_eq
      -- |Q.roots.toFinset| ≤ Q.natDegree.
      have hQ_card_le_natDeg : Q.roots.toFinset.card ≤ Q.natDegree :=
        (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' Q)
      -- Q.natDegree < P.natDegree from hQ_lt.
      have hQ_natDeg_lt : Q.natDegree < P.natDegree := by
        have h_natdeg : Q.natDegree ≤ P.natDegree := by
          rcases eq_or_lt_of_le (Polynomial.natDegree_le_natDegree
            (le_of_lt hQ_lt)) with h | h
          · -- Equal natDegrees but Q.degree < P.degree: contradiction unless P = 0
            exfalso
            have : P.degree = Q.degree := by
              rw [Polynomial.degree_eq_natDegree hP_ne,
                Polynomial.degree_eq_natDegree hQ_ne, h]
            exact absurd hQ_lt (not_lt.mpr (le_of_eq this))
          · exact le_of_lt h
        rcases lt_or_eq_of_le h_natdeg with h | h
        · exact h
        · -- Equal natDegree but Q.degree < P.degree: same contradiction
          exfalso
          have : P.degree = Q.degree := by
            rw [Polynomial.degree_eq_natDegree hP_ne,
              Polynomial.degree_eq_natDegree hQ_ne, h]
          exact absurd hQ_lt (not_lt.mpr (le_of_eq this))
      -- From the chain `P.natDegree − 1 ≤ Q.natDegree < P.natDegree`,
      -- derive `Q.natDegree = P.natDegree − 1`.
      have hQ_natDeg_eq : Q.natDegree + 1 = P.natDegree := by
        have h1 : P.natDegree - 1 ≤ Q.roots.toFinset.card := hNonMax_card ▸ h_NonMax_le
        have h2 : Q.roots.toFinset.card ≤ Q.natDegree := hQ_card_le_natDeg
        omega
      -- Cardinality of Q.roots equals Q.natDegree.
      have hQ_toFinset_eq : Q.roots.toFinset.card = Q.natDegree := by
        have h1 : P.natDegree - 1 ≤ Q.roots.toFinset.card := hNonMax_card ▸ h_NonMax_le
        omega
      have hQ_card_roots : Multiset.card Q.roots = Q.natDegree := by
        have h1 : Q.roots.toFinset.card ≤ Multiset.card Q.roots :=
          Multiset.toFinset_card_le _
        have h2 : Multiset.card Q.roots ≤ Q.natDegree := Polynomial.card_roots' Q
        omega
      have hQ_nodup : Q.roots.Nodup := by
        rw [← Multiset.toFinset_card_eq_card_iff_nodup]
        rw [hQ_toFinset_eq, hQ_card_roots]
      -- The remaining sub-claims (Q-roots in (a,b), Interlacing, sign of lc)
      -- follow from the fact that the injection `φ : NonMax → Q.roots.toFinset`
      -- is now a bijection (cardinalities match: |NonMax| = P.natDegree − 1 =
      -- Q.natDegree = |Q.roots.toFinset|), so every Q-root lies in some gap
      -- between consecutive P-roots, hence in (a, b). The leading-coef sign
      -- claim uses the constancy of `(Q · P)` past `max_P` plus
      -- `hasSignAtPosInfty_leadingCoeff`.
      -- The injection `φ' : NonMax → Q.roots.toFinset` is in fact a
      -- bijection because both sides have the same cardinality.
      have h_φ'_image_subset :
          NonMax.image φ' ⊆ Q.roots.toFinset := by
        intro q hq
        obtain ⟨r', hr', heq⟩ := Finset.mem_image.mp hq
        rw [show φ' r' = φ r' hr' from dite_eq_left hr'] at heq
        rw [← heq]; exact hφ_mem r' hr'
      have h_image_card : (NonMax.image φ').card = NonMax.card := by
        apply Finset.card_image_of_injOn
        intro r₁ h₁ r₂ h₂ heq
        simp only [Finset.mem_coe] at h₁ h₂
        rw [show φ' r₁ = φ r₁ h₁ from dite_eq_left h₁,
          show φ' r₂ = φ r₂ h₂ from dite_eq_left h₂] at heq
        exact hφ_inj r₁ h₁ r₂ h₂ heq
      have h_φ'_image_eq : NonMax.image φ' = Q.roots.toFinset := by
        apply Finset.eq_of_subset_of_card_le h_φ'_image_subset
        rw [h_image_card, hNonMax_card, hQ_toFinset_eq]; omega
      refine ⟨hQ_natDeg_eq, ?_, h_card_roots, h_nodup, hQ_card_roots, hQ_nodup,
              fun r hr => (h_in_and_jump r hr).1, ?_, ?_⟩
      · -- sign(lc_P) = sign(lc_Q): use `hasSignAtPosInfty_leadingCoeff` and
        -- the constancy of `(Q · P)` past `max_P`.
        have hQP_ne : Q * P ≠ 0 := mul_ne_zero hQ_ne hP_ne
        -- All Q-roots are < max_P (each q ∈ Q.roots has q < next_P r' ≤ max_P).
        have h_Q_roots_lt_max : ∀ q ∈ Q.roots, q < max_P := by
          intro q hq
          have hq_F : q ∈ Q.roots.toFinset := Multiset.mem_toFinset.mpr hq
          rw [← h_φ'_image_eq] at hq_F
          obtain ⟨r', hr', heq⟩ := Finset.mem_image.mp hq_F
          have heq' : φ r' hr' = q := by
            rw [show φ' r' = φ r' hr' from dite_eq_left hr'] at heq
            exact heq
          have hq_lt_next : q < next_P r' hr' := heq' ▸ (hφ_spec r' hr').2.2
          have hnext_le_max : next_P r' hr' ≤ max_P :=
            P.roots.toFinset.le_max' _ (Multiset.mem_toFinset.mpr (hnext_mem r' hr'))
          exact lt_of_lt_of_le hq_lt_next hnext_le_max
        -- For t > max_P, (Q · P)(t) ≠ 0.
        have h_QP_ne_above : ∀ t > max_P, (Q * P).eval t ≠ 0 := by
          intro t ht_gt h_QP_t
          rw [Polynomial.eval_mul, mul_eq_zero] at h_QP_t
          rcases h_QP_t with h | h
          · -- Q(t) = 0 ⇒ t ∈ Q.roots ⇒ t < max_P, contradicting t > max_P.
            have : t ∈ Q.roots := (Polynomial.mem_roots hQ_ne).mpr h
            exact absurd (h_Q_roots_lt_max t this) (not_lt.mpr (le_of_lt ht_gt))
          · -- P(t) = 0 ⇒ t ∈ P.roots ⇒ t ≤ max_P, contradicting t > max_P.
            have : t ∈ P.roots := (Polynomial.mem_roots hP_ne).mpr h
            have : t ≤ max_P := P.roots.toFinset.le_max' t (Multiset.mem_toFinset.mpr this)
            exact absurd this (not_le.mpr ht_gt)
        -- Get b₁ > max_P with sign((Q*P)(t)) = 1 on (max_P, b₁).
        obtain ⟨_, ⟨_, _, hsign_max⟩⟩ := h_in_and_jump max_P hmax_mem
        obtain ⟨b₁, hb₁_gt, hb₁_sign⟩ := hsign_max
        -- Show: sign((Q·P)(t)) = 1 for all t > max_P.
        have h_sign_above_max : ∀ t > max_P, SignType.sign ((Q * P).eval t) = 1 := by
          intro t ht_gt
          rcases lt_or_ge t b₁ with h_lt_b | h_ge_b
          · exact hb₁_sign t ⟨ht_gt, h_lt_b⟩
          · -- t ≥ b₁: use IVP between a point in (max_P, b₁) and t.
            obtain ⟨t₀, ht₀_lo, ht₀_hi⟩ := exists_between hb₁_gt
            have h_QP_t₀_pos : 0 < (Q * P).eval t₀ :=
              sign_eq_one_iff.mp (hb₁_sign t₀ ⟨ht₀_lo, ht₀_hi⟩)
            -- (Q · P)(t) ≠ 0.
            have h_QP_t_ne : (Q * P).eval t ≠ 0 := h_QP_ne_above t ht_gt
            -- If (Q · P)(t) < 0, IVP gives a zero in (t₀, t), contradicting `h_QP_ne_above`.
            by_contra h_sign_t_ne
            have h_QP_t_neg : (Q * P).eval t < 0 := by
              rcases SignType.trichotomy (SignType.sign ((Q * P).eval t)) with h | h | h
              · exact sign_eq_neg_one_iff.mp h
              · exact absurd ((sign_eq_zero_iff).mp h) h_QP_t_ne
              · exact absurd h h_sign_t_ne
            have ht₀_lt_t : t₀ < t :=
              lt_of_lt_of_le ht₀_hi h_ge_b
            have h_prod_neg : (Q * P).eval t₀ * (Q * P).eval t < 0 :=
              mul_neg_of_pos_of_neg h_QP_t₀_pos h_QP_t_neg
            obtain ⟨c, hc_lo, hc_hi, hc_zero⟩ :=
              hIVP (Q * P) t₀ t ht₀_lt_t h_prod_neg
            have hc_gt_max : max_P < c := lt_trans ht₀_lo hc_lo
            exact h_QP_ne_above c hc_gt_max hc_zero
        -- HasSignAtPosInfty (Q*P) 1.
        have h_QP_pos_inf : HasSignAtPosInfty (Q * P) 1 :=
          ⟨max_P, h_sign_above_max⟩
        -- HasSignAtPosInfty (Q*P) (sign((Q*P).lc)).
        have h_QP_pos_inf_lc :
            HasSignAtPosInfty (Q * P) (SignType.sign (Q * P).leadingCoeff) :=
          hasSignAtPosInfty_leadingCoeff (Q * P)
        -- By uniqueness, sign((Q*P).lc) = 1.
        have h_sign_lc_QP : SignType.sign (Q * P).leadingCoeff = 1 :=
          HasSignAtPosInfty.unique h_QP_pos_inf_lc h_QP_pos_inf
        -- sign(lc_Q · lc_P) = 1.
        rw [Polynomial.leadingCoeff_mul, sign_mul] at h_sign_lc_QP
        -- Both signs nonzero, product = 1 ⇒ same sign.
        have h_lc_P_ne : SignType.sign P.leadingCoeff ≠ 0 := by
          rw [Ne, sign_eq_zero_iff, Polynomial.leadingCoeff_eq_zero]
          exact hP_ne
        have h_lc_Q_ne : SignType.sign Q.leadingCoeff ≠ 0 := by
          rw [Ne, sign_eq_zero_iff, Polynomial.leadingCoeff_eq_zero]
          exact hQ_ne
        rcases SignType.trichotomy (SignType.sign P.leadingCoeff) with hP | hP | hP
        · rcases SignType.trichotomy (SignType.sign Q.leadingCoeff) with hQ | hQ | hQ
          · rw [hP, hQ]
          · exact absurd hQ h_lc_Q_ne
          · rw [hP, hQ] at h_sign_lc_QP; exact absurd h_sign_lc_QP (by decide)
        · exact absurd hP h_lc_P_ne
        · rcases SignType.trichotomy (SignType.sign Q.leadingCoeff) with hQ | hQ | hQ
          · rw [hP, hQ] at h_sign_lc_QP; exact absurd h_sign_lc_QP (by decide)
          · exact absurd hQ h_lc_Q_ne
          · rw [hP, hQ]
      · -- All Q-roots in (a, b).
        intro s hs
        have hs_F : s ∈ Q.roots.toFinset := Multiset.mem_toFinset.mpr hs
        rw [← h_φ'_image_eq] at hs_F
        obtain ⟨r', hr', heq⟩ := Finset.mem_image.mp hs_F
        have heq' : φ r' hr' = s := by
          rw [show φ' r' = φ r' hr' from dite_eq_left hr'] at heq
          exact heq
        have hr'_lt_s : r' < s := heq' ▸ (hφ_spec r' hr').2.1
        have hs_lt_next : s < next_P r' hr' := heq' ▸ (hφ_spec r' hr').2.2
        have hr'_in : r' ∈ ExtendedPoint.openInterval a b :=
          (h_in_and_jump r' (hNonMax_in_P hr')).1
        have hnext_in : next_P r' hr' ∈ ExtendedPoint.openInterval a b :=
          (h_in_and_jump (next_P r' hr') (hnext_mem r' hr')).1
        cases a with
        | finite a' =>
          cases b with
          | finite b' =>
            simp only [ExtendedPoint.openInterval, Set.mem_Ioo] at hr'_in hnext_in ⊢
            exact ⟨lt_trans hr'_in.1 hr'_lt_s, lt_trans hs_lt_next hnext_in.2⟩
          | posInf =>
            simp only [ExtendedPoint.openInterval, Set.mem_Ioi] at hr'_in hnext_in ⊢
            exact lt_trans hr'_in hr'_lt_s
          | negInf =>
            simp only [ExtendedPoint.openInterval] at hr'_in
            exact hr'_in.elim
        | posInf =>
          simp only [ExtendedPoint.openInterval] at hr'_in
          exact hr'_in.elim
        | negInf =>
          cases b with
          | finite b' =>
            simp only [ExtendedPoint.openInterval, Set.mem_Iio] at hr'_in hnext_in ⊢
            exact lt_trans hs_lt_next hnext_in
          | posInf =>
            simp only [ExtendedPoint.openInterval, Set.mem_univ]
          | negInf =>
            simp only [ExtendedPoint.openInterval] at hr'_in
            exact hr'_in.elim
      · -- Interlacing P Q: bijection φ gives existence and uniqueness.
        intro r₁ r₂ h_lt hr₁_root hr₂_root h_no_between
        have hr₁_mem : r₁ ∈ P.roots := (Polynomial.mem_roots hP_ne).mpr hr₁_root
        have hr₂_mem : r₂ ∈ P.roots := (Polynomial.mem_roots hP_ne).mpr hr₂_root
        have hr₂_le_max : r₂ ≤ max_P :=
          P.roots.toFinset.le_max' r₂ (Multiset.mem_toFinset.mpr hr₂_mem)
        have hr₁_lt_max : r₁ < max_P := lt_of_lt_of_le h_lt hr₂_le_max
        have hr₁_NonMax : r₁ ∈ NonMax :=
          Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr₁_mem, hr₁_lt_max⟩
        have hnext_eq : next_P r₁ hr₁_NonMax = r₂ := by
          apply le_antisymm
          · apply (P.roots.toFinset.filter (r₁ < ·)).min'_le
            exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr₂_mem, h_lt⟩
          · by_contra h
            push Not at h
            have hnext_root := hnext_mem r₁ hr₁_NonMax
            have hnext_gt' := hnext_gt r₁ hr₁_NonMax
            exact h_no_between (next_P r₁ hr₁_NonMax)
              ((Polynomial.mem_roots hP_ne).mp hnext_root) ⟨hnext_gt', h⟩
        refine ⟨φ r₁ hr₁_NonMax, ⟨?_, ?_, ?_⟩, ?_⟩
        · exact (Polynomial.mem_roots hQ_ne).mp (hφ_spec r₁ hr₁_NonMax).1
        · exact (hφ_spec r₁ hr₁_NonMax).2.1
        · rw [← hnext_eq]; exact (hφ_spec r₁ hr₁_NonMax).2.2
        · -- Uniqueness via bijection.
          rintro q ⟨hq_root, hq_lt₁, hq_lt₂⟩
          have hq_mem : q ∈ Q.roots := (Polynomial.mem_roots hQ_ne).mpr hq_root
          have hq_F : q ∈ Q.roots.toFinset := Multiset.mem_toFinset.mpr hq_mem
          rw [← h_φ'_image_eq] at hq_F
          obtain ⟨r', hr'_NonMax, heq⟩ := Finset.mem_image.mp hq_F
          have heq' : φ r' hr'_NonMax = q := by
            rw [show φ' r' = φ r' hr'_NonMax from dite_eq_left hr'_NonMax] at heq
            exact heq
          have hr'_lt_q : r' < q := heq' ▸ (hφ_spec r' hr'_NonMax).2.1
          have hq_lt_next_r' : q < next_P r' hr'_NonMax :=
            heq' ▸ (hφ_spec r' hr'_NonMax).2.2
          have hr'_eq : r' = r₁ := by
            by_contra h_ne
            rcases lt_or_gt_of_ne h_ne with h_r'_lt | h_r₁_lt
            · -- r' < r₁: then next_P r' ≤ r₁ < q, contradicting q < next_P r'.
              have hr₁_in : r₁ ∈ P.roots.toFinset.filter (r' < ·) :=
                Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr₁_mem, h_r'_lt⟩
              have hr₁_ge : next_P r' hr'_NonMax ≤ r₁ :=
                (P.roots.toFinset.filter (r' < ·)).min'_le _ hr₁_in
              exact absurd hq_lt_next_r'
                (not_lt.mpr (le_trans hr₁_ge (le_of_lt hq_lt₁)))
            · -- r₁ < r' < q < r₂: r' is a P-root strictly between r₁ and r₂.
              exact h_no_between r'
                ((Polynomial.mem_roots hP_ne).mp (hNonMax_in_P hr'_NonMax))
                ⟨h_r₁_lt, lt_trans hr'_lt_q hq_lt₂⟩
          subst hr'_eq
          rw [← heq']
  · -- Backward direction (fully proven).
    rintro ⟨hq, hsign, hP_card, hP_nodup, hQ_card, hQ_nodup,
            hP_in, _hQ_in, hint⟩
    -- Derive `P ≠ 0` and `Q ≠ 0` from the structural hypotheses.
    have hP_ne : P ≠ 0 := by
      intro hP
      rw [hP, Polynomial.natDegree_zero] at hq
      omega
    have hQ_ne : Q ≠ 0 := by
      intro hQ
      rw [hQ, Polynomial.leadingCoeff_zero, sign_zero] at hsign
      have : P.leadingCoeff = 0 := by
        rw [← sign_eq_zero_iff]; exact hsign
      exact hP_ne (Polynomial.leadingCoeff_eq_zero.mp this)
    -- Every distinct P-root produces a `−∞ → +∞` jump, lies in `(a, b)`.
    have h_jumps : ∀ r ∈ P.roots, JumpsFromNegInfToPosInf Q P r := by
      intro r hr
      exact jumps_at_P_root hIVP P Q hP_ne hQ_ne hP_card hP_nodup hQ_card
        hQ_nodup hq hsign hint hr
    -- The positive-jump filter equals `P.roots.toFinset`.
    have h_pos_eq : P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf Q P x) =
        P.roots.toFinset := by
      apply Finset.filter_eq_self.mpr
      intro r hr
      have hr_mem : r ∈ P.roots := Multiset.mem_toFinset.mp hr
      exact ⟨hP_in r hr_mem, h_jumps r hr_mem⟩
    -- The negative-jump filter is empty: a single root cannot satisfy both
    -- `JumpsFromNegInfToPosInf` (sign +1) and `JumpsFromPosInfToNegInf`
    -- (sign −1) by uniqueness of `HasSignRight`.
    have h_neg_eq : P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromPosInfToNegInf Q P x) =
        ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro r hr h_neg
      have hr_mem : r ∈ P.roots := Multiset.mem_toFinset.mp hr
      have h_pos := h_jumps r hr_mem
      obtain ⟨_, _, h_sign_pos⟩ := h_pos
      obtain ⟨_, _, h_sign_neg⟩ := h_neg.2
      have : (1 : SignType) = -1 := h_sign_pos.unique h_sign_neg
      exact absurd this (by decide)
    -- Compute `cauchyIndexOn`.
    show ((P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
        ((P.roots.toFinset.filter (fun x =>
          x ∈ ExtendedPoint.openInterval a b ∧
          JumpsFromPosInfToNegInf Q P x)).card : ℤ) =
        P.natDegree
    rw [h_pos_eq, h_neg_eq, Finset.card_empty, Nat.cast_zero, sub_zero]
    have h_toFinset : P.roots.toFinset.card = Multiset.card P.roots :=
      Multiset.toFinset_card_of_nodup hP_nodup
    rw [h_toFinset, hP_card]

/-! #### Helper lemmas for Remark 2.55(b)

The key combinatorial fact is that `Q` and `Q % P` agree modulo the
"high-order" perturbation `K · P` (where `K = Q / P`), which leaves all
relevant lower-order behavior at `P`-roots untouched. -/

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `rootMultiplicity` is preserved under negation. -/
private lemma rootMultiplicity_neg'
    (p : R[X]) (a : R) :
    (-p).rootMultiplicity a = p.rootMultiplicity a := by
  classical
  rcases eq_or_ne p 0 with hp | hp
  · simp [hp]
  have hnp : -p ≠ 0 := neg_ne_zero.mpr hp
  have h_iff_le : ∀ n, n ≤ (-p).rootMultiplicity a ↔ n ≤ p.rootMultiplicity a := by
    intro n
    rw [Polynomial.le_rootMultiplicity_iff hnp, Polynomial.le_rootMultiplicity_iff hp,
      dvd_neg]
  apply Nat.le_antisymm
  · exact (h_iff_le _).mp (le_refl _)
  · exact (h_iff_le _).mpr (le_refl _)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- If `g` has strictly smaller `rootMultiplicity` at `x` than `f`, then
    `(f + g).rootMultiplicity x = g.rootMultiplicity x`. -/
private lemma rootMultiplicity_add_of_lt'
    {x : R} {f g : R[X]} (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (h_lt : g.rootMultiplicity x < f.rootMultiplicity x) :
    (f + g).rootMultiplicity x = g.rootMultiplicity x := by
  classical
  set m := g.rootMultiplicity x with hm_def
  -- `f + g ≠ 0`: else `f = -g` and so `f.rootMul = g.rootMul`, contradicting `h_lt`.
  have hfg_ne : f + g ≠ 0 := by
    intro h
    have hf_eq : f = -g := by linear_combination h
    have h_eq : f.rootMultiplicity x = g.rootMultiplicity x := by
      rw [hf_eq]; exact rootMultiplicity_neg' g x
    omega
  -- `(X − C x)^m ∣ g` and `(X − C x)^m ∣ f`, so `(X − C x)^m ∣ (f + g)`.
  have h_dvd_g : (Polynomial.X - Polynomial.C x)^m ∣ g :=
    (Polynomial.le_rootMultiplicity_iff hg_ne).mp (le_refl m)
  have h_dvd_f : (Polynomial.X - Polynomial.C x)^m ∣ f :=
    (Polynomial.le_rootMultiplicity_iff hf_ne).mp (le_of_lt h_lt)
  have h_dvd_fg : (Polynomial.X - Polynomial.C x)^m ∣ (f + g) :=
    dvd_add h_dvd_f h_dvd_g
  have h_le : m ≤ (f + g).rootMultiplicity x :=
    (Polynomial.le_rootMultiplicity_iff hfg_ne).mpr h_dvd_fg
  -- `(X − C x)^(m+1) ∤ (f + g)`: else it would divide `((f + g) − f) = g`,
  -- contradicting `m = g.rootMultiplicity x`.
  have h_nodvd : ¬ (Polynomial.X - Polynomial.C x)^(m+1) ∣ (f + g) := by
    intro h_dvd
    have h_dvd_f' : (Polynomial.X - Polynomial.C x)^(m+1) ∣ f :=
      (Polynomial.le_rootMultiplicity_iff hf_ne).mp h_lt
    have h_dvd_g' : (Polynomial.X - Polynomial.C x)^(m+1) ∣ g := by
      have h_sub : (f + g) - f = g := by ring
      rw [← h_sub]
      exact dvd_sub h_dvd h_dvd_f'
    have : m + 1 ≤ g.rootMultiplicity x :=
      (Polynomial.le_rootMultiplicity_iff hg_ne).mpr h_dvd_g'
    omega
  have h_lt_succ : (f + g).rootMultiplicity x < m + 1 := by
    by_contra h
    push Not at h
    exact h_nodvd ((Polynomial.le_rootMultiplicity_iff hfg_ne).mp h)
  omega

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `Q ≠ 0` whenever `P ≠ 0`, `Q / P ≠ 0`, and `Q % P ≠ 0`.

    Reason: if `Q = 0`, then `K · P + R = 0` so `R = −K · P`, but
    `R.degree < P.degree` (Euclidean) while `(K · P).degree ≥ P.degree`
    when `K ≠ 0` and `P ≠ 0`. -/
private lemma Q_ne_zero_of_div_mod_ne
    {Q P : R[X]} (hP_ne : P ≠ 0) (hK : Q / P ≠ 0) :
    Q ≠ 0 := by
  classical
  intro hQ
  have hKP_ne : Q / P * P ≠ 0 := mul_ne_zero hK hP_ne
  have h_div_add_mod : P * (Q / P) + Q % P = Q := EuclideanDomain.div_add_mod Q P
  have h_mod_eq : Q % P = -((Q / P) * P) := by
    linear_combination h_div_add_mod + hQ
  have h_mod_deg : (Q % P).degree < P.degree :=
    Polynomial.degree_mod_lt Q hP_ne
  rw [h_mod_eq, Polynomial.degree_neg] at h_mod_deg
  have h_KP_deg : P.degree ≤ ((Q / P) * P).degree := by
    rw [Polynomial.degree_mul, add_comm]
    have : (0 : WithBot ℕ) ≤ (Q / P).degree := by
      rw [Polynomial.zero_le_degree_iff]; exact hK
    exact le_add_of_nonneg_right this
  exact absurd h_mod_deg (not_lt.mpr h_KP_deg)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Helper: multiplicity equivalence `Q.rootMultiplicity x < µ_P ↔
    (Q%P).rootMultiplicity x < µ_P` for the `Q % P ≠ 0` case, with
    equality of multiplicities under either side.

    Write `Q = K · P + R` (with `K = Q / P`, `R = Q % P`). If `K = 0`,
    `Q = R` and the iff is trivial. Otherwise `(K · P).rootMultiplicity x ≥
    µ_P`, so by `rootMultiplicity_add_of_lt` the lower-multiplicity `R`
    dominates `Q`'s behavior at `x`. -/
private lemma rootMultiplicity_mod_lt_iff_of_mod_ne
    (Q P : R[X]) (hP_ne : P ≠ 0) (hR_ne : Q % P ≠ 0) (x : R) :
    (Q.rootMultiplicity x < P.rootMultiplicity x ↔
      (Q % P).rootMultiplicity x < P.rootMultiplicity x) ∧
    (Q.rootMultiplicity x < P.rootMultiplicity x →
      Q.rootMultiplicity x = (Q % P).rootMultiplicity x) := by
  classical
  set K := Q / P with hK_def
  set R := Q % P with hR_def
  have hQ_eq : Q = K * P + R := by
    have h := EuclideanDomain.div_add_mod Q P
    show Q = K * P + R
    rw [mul_comm] at h
    linear_combination -h
  rcases eq_or_ne K 0 with hK | hK
  · have hQ_R : Q = R := by rw [hQ_eq, hK, zero_mul, zero_add]
    refine ⟨?_, ?_⟩
    · rw [hQ_R]
    · intro _; rw [hQ_R]
  have hKP_ne : K * P ≠ 0 := mul_ne_zero hK hP_ne
  have hKP_rootMul : (K * P).rootMultiplicity x =
      K.rootMultiplicity x + P.rootMultiplicity x :=
    Polynomial.rootMultiplicity_mul hKP_ne
  have hKP_ge : P.rootMultiplicity x ≤ (K * P).rootMultiplicity x := by
    rw [hKP_rootMul]; omega
  have hQ_ne : Q ≠ 0 := Q_ne_zero_of_div_mod_ne hP_ne hK
  -- Bidirectional analysis.
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- Q.rootMul < µ_P → R.rootMul < µ_P.
    intro hQ_lt
    by_contra h_ge
    push Not at h_ge
    have h_min_ge : P.rootMultiplicity x ≤
        min ((K * P).rootMultiplicity x) (R.rootMultiplicity x) :=
      le_min hKP_ge h_ge
    have h_min_le : min ((K * P).rootMultiplicity x) (R.rootMultiplicity x) ≤
        Q.rootMultiplicity x := by
      rw [hQ_eq]
      exact Polynomial.rootMultiplicity_add (p := K * P) (q := R) x
        (hQ_eq ▸ hQ_ne)
    have : P.rootMultiplicity x ≤ Q.rootMultiplicity x := le_trans h_min_ge h_min_le
    have : Q.rootMultiplicity x = (K * P + R).rootMultiplicity x := by
      rw [← hQ_eq]
    omega
  · -- R.rootMul < µ_P → Q.rootMul < µ_P.
    intro hR_lt
    have h_lt_KP : R.rootMultiplicity x < (K * P).rootMultiplicity x :=
      lt_of_lt_of_le hR_lt hKP_ge
    have h_eq : (K * P + R).rootMultiplicity x = R.rootMultiplicity x :=
      rootMultiplicity_add_of_lt' hKP_ne hR_ne h_lt_KP
    rw [hQ_eq, h_eq]; exact hR_lt
  · -- Q.rootMul < µ_P → Q.rootMul = R.rootMul.
    intro hQ_lt
    by_contra h_ne
    -- We will show R.rootMul < µ_P via the iff direction we just proved,
    -- and then derive Q.rootMul = R.rootMul via rootMultiplicity_add_of_lt.
    have hR_lt : R.rootMultiplicity x < P.rootMultiplicity x := by
      by_contra h_ge
      push Not at h_ge
      have h_min_ge : P.rootMultiplicity x ≤
          min ((K * P).rootMultiplicity x) (R.rootMultiplicity x) :=
        le_min hKP_ge h_ge
      have h_min_le : min ((K * P).rootMultiplicity x) (R.rootMultiplicity x) ≤
          Q.rootMultiplicity x := by
        rw [hQ_eq]
        exact Polynomial.rootMultiplicity_add (p := K * P) (q := R) x
          (hQ_eq ▸ hQ_ne)
      omega
    have h_lt_KP : R.rootMultiplicity x < (K * P).rootMultiplicity x :=
      lt_of_lt_of_le hR_lt hKP_ge
    have h_eq : (K * P + R).rootMultiplicity x = R.rootMultiplicity x :=
      rootMultiplicity_add_of_lt' hKP_ne hR_ne h_lt_KP
    have : Q.rootMultiplicity x = R.rootMultiplicity x := by rw [hQ_eq]; exact h_eq
    exact h_ne this

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- If `k < p.rootMultiplicity x`, then the `k`-th iterated derivative of
    `p` evaluates to zero at `x`. Proof: factor `p = (X − Cx)^µ · q` and
    expand the iterated derivative via Leibniz; every term contains a
    positive power of `X − Cx`, which vanishes at `x`. -/
private lemma eval_iterate_derivative_eq_zero_of_lt_rootMultiplicity
    (p : R[X]) (x : R) {k : ℕ} (hk : k < p.rootMultiplicity x) :
    (((⇑Polynomial.derivative)^[k]) p).eval x = 0 := by
  set μ := p.rootMultiplicity x with hμ
  set q := p /ₘ (X - C x)^μ with hq
  have hp_eq : p = (X - C x)^μ * q :=
    (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p x).symm
  conv_lhs => rw [hp_eq]
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.eval_smul, Polynomial.eval_mul,
    Polynomial.iterate_derivative_X_sub_pow,
    Polynomial.eval_smul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_pow]
  · simp
  · exact Nat.sub_ne_zero_of_lt (lt_of_le_of_lt (Nat.sub_le k i) hk)

/-- Helper: `HasSignRight ((Q % P) * P) x s ↔ HasSignRight (Q * P) x s`
    when `Q.rootMultiplicity x < µ_P` (where `µ_P = P.rootMultiplicity x`).
    The two products differ by `K · P²` (where `K = Q / P`), which has
    multiplicity at least `2 · µ_P` at `x` — strictly greater than
    `(Q · P)`'s multiplicity `µ_P + ν`. Hence the `(µ_P + ν)`-th derivative
    of the difference vanishes at `x`, so by Proposition 2.21 (which uses
    IVP) and uniqueness of `HasSignRight`, the two `HasSignRight` predicates
    coincide. -/
private lemma hasSignRight_mod_iff_of_mod_ne
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (Q P : R[X]) (hP_ne : P ≠ 0) (hR_ne : Q % P ≠ 0) (x : R)
    (hQ_lt : Q.rootMultiplicity x < P.rootMultiplicity x)
    (s : SignType) :
    HasSignRight ((Q % P) * P) x s ↔ HasSignRight (Q * P) x s := by
  classical
  set Rmod := Q % P with hRmod_def
  set K := Q / P with hK_def
  have hQ_eq : Q = K * P + Rmod := by
    have h := EuclideanDomain.div_add_mod Q P
    rw [mul_comm] at h
    linear_combination -h
  -- `Q ≠ 0` since `Rmod ≠ 0`.
  have hQ_ne : Q ≠ 0 := by
    intro h
    apply hR_ne
    rw [hRmod_def, h, EuclideanDomain.zero_mod]
  -- `Q.rootMul = Rmod.rootMul`.
  obtain ⟨_, h_eq_mult⟩ := rootMultiplicity_mod_lt_iff_of_mod_ne Q P hP_ne hR_ne x
  have h_q_eq_r : Q.rootMultiplicity x = Rmod.rootMultiplicity x := h_eq_mult hQ_lt
  -- Set `µ` and abbreviate.
  set μ := P.rootMultiplicity x with hμ_def
  -- `Q*P` and `Rmod*P` are nonzero with the same rootMul at `x`.
  have hQP_ne : Q * P ≠ 0 := mul_ne_zero hQ_ne hP_ne
  have hRP_ne : Rmod * P ≠ 0 := mul_ne_zero hR_ne hP_ne
  have h_QP_rootMul : (Q * P).rootMultiplicity x = Q.rootMultiplicity x + μ :=
    Polynomial.rootMultiplicity_mul hQP_ne
  have h_RP_rootMul : (Rmod * P).rootMultiplicity x = Rmod.rootMultiplicity x + μ :=
    Polynomial.rootMultiplicity_mul hRP_ne
  have h_rootMul_eq : (Q * P).rootMultiplicity x = (Rmod * P).rootMultiplicity x := by
    rw [h_QP_rootMul, h_RP_rootMul, h_q_eq_r]
  -- Apply Prop 2.21 to both.
  have h_QP_right := Proposition2_21.proposition_2_21_right hIVP hQP_ne x
  have h_RP_right := Proposition2_21.proposition_2_21_right hIVP hRP_ne x
  -- Show the canonical signs agree.
  -- Set `k := (Q*P).rootMul x = (Rmod*P).rootMul x = Q.rootMul + µ`.
  set k := (Q * P).rootMultiplicity x with hk_def
  -- `Q*P = K*P*P + Rmod*P`.
  have h_QP_eq_sum : Q * P = K * P * P + Rmod * P := by rw [hQ_eq]; ring
  -- Show `(D^k(K*P*P)).eval x = 0`.
  have h_KPP_zero : (((⇑Polynomial.derivative)^[k]) (K * P * P)).eval x = 0 := by
    by_cases hK : K = 0
    · rw [hK]; simp
    have hKP_ne : K * P ≠ 0 := mul_ne_zero hK hP_ne
    have hKPP_ne : K * P * P ≠ 0 := mul_ne_zero hKP_ne hP_ne
    have h_KPP_rootMul : (K * P * P).rootMultiplicity x =
        K.rootMultiplicity x + μ + μ := by
      rw [Polynomial.rootMultiplicity_mul hKPP_ne,
        Polynomial.rootMultiplicity_mul hKP_ne]
    have h_k_lt : k < (K * P * P).rootMultiplicity x := by
      rw [h_KPP_rootMul]
      have : k = Q.rootMultiplicity x + μ := h_QP_rootMul
      omega
    exact eval_iterate_derivative_eq_zero_of_lt_rootMultiplicity _ _ h_k_lt
  -- Therefore `(D^k(Q*P)).eval x = (D^k(Rmod*P)).eval x`.
  have h_eval_eq : (((⇑Polynomial.derivative)^[k]) (Q * P)).eval x =
      (((⇑Polynomial.derivative)^[(Rmod * P).rootMultiplicity x]) (Rmod * P)).eval x := by
    have h_iter_add : ((⇑Polynomial.derivative)^[k]) (Q * P) =
        ((⇑Polynomial.derivative)^[k]) (K * P * P) +
        ((⇑Polynomial.derivative)^[k]) (Rmod * P) := by
      rw [h_QP_eq_sum]
      exact iterate_map_add Polynomial.derivative k (K * P * P) (Rmod * P)
    rw [h_iter_add, Polynomial.eval_add, h_KPP_zero, zero_add, h_rootMul_eq]
  -- Hence the canonical signs coincide.
  have h_signs_eq :
      SignType.sign ((((⇑Polynomial.derivative)^[(Q * P).rootMultiplicity x])
        (Q * P)).eval x) =
      SignType.sign ((((⇑Polynomial.derivative)^[(Rmod * P).rootMultiplicity x])
        (Rmod * P)).eval x) := by
    rw [show (Q * P).rootMultiplicity x = k from rfl, h_eval_eq]
  -- Combine via uniqueness.
  constructor
  · intro h
    have hs : s = SignType.sign ((((⇑Polynomial.derivative)^[(Rmod * P).rootMultiplicity x])
        (Rmod * P)).eval x) := HasSignRight.unique h h_RP_right
    rw [hs, ← h_signs_eq]
    exact h_QP_right
  · intro h
    have hs : s = SignType.sign ((((⇑Polynomial.derivative)^[(Q * P).rootMultiplicity x])
        (Q * P)).eval x) := HasSignRight.unique h h_QP_right
    rw [hs, h_signs_eq]
    exact h_RP_right

/-- Helper: jump predicate equivalence under taking `Q` to `Q % P`. -/
private lemma jumpsFromNegInfToPosInf_mod_iff
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (Q P : R[X]) (hP_ne : P ≠ 0) (x : R) :
    JumpsFromNegInfToPosInf (Q % P) P x ↔ JumpsFromNegInfToPosInf Q P x := by
  -- Case split on `Q % P = 0`.
  rcases eq_or_ne (Q % P) 0 with hR | hR_ne
  · -- `Q % P = 0`: both jump predicates are False.
    -- `(Q%P)` side: `HasSignRight (0 * P) x 1` requires sign 0 = 1, impossible.
    -- `Q` side: if `Q = 0`, multiplicity condition fails. If `Q = K · P` with
    -- `K ≠ 0`, then `Q.rootMul x ≥ µ_P`, so the multiplicity condition
    -- `µ_P > Q.rootMul x` fails too.
    constructor
    · -- (Q%P) side false: deconstruct and derive False.
      rintro ⟨_, _, h_sign⟩
      rw [hR, zero_mul] at h_sign
      obtain ⟨b, hb_gt, hb_sign⟩ := h_sign
      obtain ⟨t, ht_lo, ht_hi⟩ := exists_between hb_gt
      have h_eval : SignType.sign ((0 : R[X]).eval t) = 1 :=
        hb_sign t ⟨ht_lo, ht_hi⟩
      simp at h_eval
    · -- Q side: derive `R = 0` situation, show predicate false.
      rintro ⟨h_gt, h_odd, h_sign⟩
      -- Q = K · P (since R = 0), so Q.rootMul ≥ µ_P; contradicts h_gt.
      have hQ_eq : Q = (Q / P) * P := by
        have h := EuclideanDomain.div_add_mod Q P
        rw [hR, add_zero] at h
        rw [mul_comm]; exact h.symm
      rcases eq_or_ne (Q / P) 0 with hK | hK
      · -- Q = 0 · P = 0: rootMul = 0, but x ∈ P.roots gives µ_P > 0, so h_gt
        -- says `µ_P > 0`. We need a sign condition contradiction.
        rw [hK, zero_mul] at hQ_eq
        rw [hQ_eq, zero_mul] at h_sign
        obtain ⟨b, hb_gt, hb_sign⟩ := h_sign
        obtain ⟨t, ht_lo, ht_hi⟩ := exists_between hb_gt
        have h_eval : SignType.sign ((0 : R[X]).eval t) = 1 :=
          hb_sign t ⟨ht_lo, ht_hi⟩
        simp at h_eval
      · -- Q = K · P with K ≠ 0. Q.rootMul = K.rootMul + µ_P ≥ µ_P.
        have hKP_ne : (Q / P) * P ≠ 0 := mul_ne_zero hK hP_ne
        have hQ_ne : Q ≠ 0 := hQ_eq ▸ hKP_ne
        have hQ_rootMul : Q.rootMultiplicity x =
            (Q / P).rootMultiplicity x + P.rootMultiplicity x := by
          conv_lhs => rw [hQ_eq]
          exact Polynomial.rootMultiplicity_mul hKP_ne
        rw [hQ_rootMul] at h_gt
        omega
  · -- `Q % P ≠ 0`: use the helpers.
    unfold JumpsFromNegInfToPosInf
    obtain ⟨h_iff_mult, h_eq_mult⟩ :=
      rootMultiplicity_mod_lt_iff_of_mod_ne Q P hP_ne hR_ne x
    constructor
    · rintro ⟨h_gt, h_odd, h_sign⟩
      have h_gt' := h_iff_mult.mpr h_gt
      refine ⟨h_gt', ?_,
        (hasSignRight_mod_iff_of_mod_ne hIVP Q P hP_ne hR_ne x h_gt' 1).mp
          h_sign⟩
      rw [(h_eq_mult h_gt').symm] at h_odd
      exact h_odd
    · rintro ⟨h_gt, h_odd, h_sign⟩
      have h_gt' := h_iff_mult.mp h_gt
      refine ⟨h_gt', ?_,
        (hasSignRight_mod_iff_of_mod_ne hIVP Q P hP_ne hR_ne x h_gt 1).mpr
          h_sign⟩
      rw [h_eq_mult h_gt] at h_odd
      exact h_odd

/-- Helper: jump predicate equivalence (other direction). -/
private lemma jumpsFromPosInfToNegInf_mod_iff
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (Q P : R[X]) (hP_ne : P ≠ 0) (x : R) :
    JumpsFromPosInfToNegInf (Q % P) P x ↔ JumpsFromPosInfToNegInf Q P x := by
  rcases eq_or_ne (Q % P) 0 with hR | hR_ne
  · constructor
    · rintro ⟨_, _, h_sign⟩
      rw [hR, zero_mul] at h_sign
      obtain ⟨b, hb_gt, hb_sign⟩ := h_sign
      obtain ⟨t, ht_lo, ht_hi⟩ := exists_between hb_gt
      have h_eval : SignType.sign ((0 : R[X]).eval t) = -1 :=
        hb_sign t ⟨ht_lo, ht_hi⟩
      simp at h_eval
    · rintro ⟨h_gt, h_odd, h_sign⟩
      have hQ_eq : Q = (Q / P) * P := by
        have h := EuclideanDomain.div_add_mod Q P
        rw [hR, add_zero] at h
        rw [mul_comm]; exact h.symm
      rcases eq_or_ne (Q / P) 0 with hK | hK
      · rw [hK, zero_mul] at hQ_eq
        rw [hQ_eq, zero_mul] at h_sign
        obtain ⟨b, hb_gt, hb_sign⟩ := h_sign
        obtain ⟨t, ht_lo, ht_hi⟩ := exists_between hb_gt
        have h_eval : SignType.sign ((0 : R[X]).eval t) = -1 :=
          hb_sign t ⟨ht_lo, ht_hi⟩
        simp at h_eval
      · have hKP_ne : (Q / P) * P ≠ 0 := mul_ne_zero hK hP_ne
        have hQ_rootMul : Q.rootMultiplicity x =
            (Q / P).rootMultiplicity x + P.rootMultiplicity x := by
          conv_lhs => rw [hQ_eq]
          exact Polynomial.rootMultiplicity_mul hKP_ne
        rw [hQ_rootMul] at h_gt
        omega
  · unfold JumpsFromPosInfToNegInf
    obtain ⟨h_iff_mult, h_eq_mult⟩ :=
      rootMultiplicity_mod_lt_iff_of_mod_ne Q P hP_ne hR_ne x
    constructor
    · rintro ⟨h_gt, h_odd, h_sign⟩
      have h_gt' := h_iff_mult.mpr h_gt
      refine ⟨h_gt', ?_,
        (hasSignRight_mod_iff_of_mod_ne hIVP Q P hP_ne hR_ne x h_gt' (-1)).mp
          h_sign⟩
      rw [(h_eq_mult h_gt').symm] at h_odd
      exact h_odd
    · rintro ⟨h_gt, h_odd, h_sign⟩
      have h_gt' := h_iff_mult.mp h_gt
      refine ⟨h_gt', ?_,
        (hasSignRight_mod_iff_of_mod_ne hIVP Q P hP_ne hR_ne x h_gt (-1)).mpr
          h_sign⟩
      rw [h_eq_mult h_gt] at h_odd
      exact h_odd

/-- **BPR Remark 2.55(b).** If `R = Rem(Q, P)` is the Euclidean remainder
    of `Q` by `P`, then `Ind(Q/P; a, b) = Ind(R/P; a, b)`.

    Intuition: writing `Q = K · P + R` with `K = Q / P` and `R = Q % P`,
    we have `Q/P = K + R/P` where `K` is a polynomial (everywhere finite),
    so `Q/P` and `R/P` differ only by a continuous polynomial term, and
    therefore have the same `±∞`-jumps at any `P`-root. -/
theorem remark_2_55_b
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (Q P : R[X]) (a b : ExtendedPoint R) (hP_ne : P ≠ 0) :
    cauchyIndexOn (Q % P) P a b = cauchyIndexOn Q P a b := by
  classical
  -- The two filtered Finsets agree pointwise (per `x ∈ P.roots.toFinset`).
  have h_pos_eq : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf (Q % P) P x) =
      P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf Q P x) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨h_in, h_jump⟩
      exact ⟨h_in,
        (jumpsFromNegInfToPosInf_mod_iff hIVP Q P hP_ne x).mp h_jump⟩
    · rintro ⟨h_in, h_jump⟩
      exact ⟨h_in,
        (jumpsFromNegInfToPosInf_mod_iff hIVP Q P hP_ne x).mpr h_jump⟩
  have h_neg_eq : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromPosInfToNegInf (Q % P) P x) =
      P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromPosInfToNegInf Q P x) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨h_in, h_jump⟩
      exact ⟨h_in,
        (jumpsFromPosInfToNegInf_mod_iff hIVP Q P hP_ne x).mp h_jump⟩
    · rintro ⟨h_in, h_jump⟩
      exact ⟨h_in,
        (jumpsFromPosInfToNegInf_mod_iff hIVP Q P hP_ne x).mpr h_jump⟩
  show ((P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧
      JumpsFromNegInfToPosInf (Q % P) P x)).card : ℤ) -
      ((P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromPosInfToNegInf (Q % P) P x)).card : ℤ) =
      ((P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
      ((P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromPosInfToNegInf Q P x)).card : ℤ)
  rw [h_pos_eq, h_neg_eq]

end Azurite.BPR

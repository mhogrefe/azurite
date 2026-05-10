import Azurite.BasuPollackRoy.Chapter2.Section2_2
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_25
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Notation_2_26
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_20
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_21
import Azurite.BasuPollackRoy.Chapter2.SignAtPoint

/-!
# BPR Theorem 2.35: Budan-Fourier Theorem

For `P ∈ R[X]` of degree `p` over a real closed field `R`, and `a, b ∈ R ∪ {−∞, +∞}`:

  1. `Var(Der(P); a, b) ≥ num(P; (a, b])`
  2. `Var(Der(P); a, b) − num(P; (a, b])` is even.

Theorem 2.33 (Descartes' rule of signs) is a particular case, obtained at
`(0, +∞)` via the identity `Var(P) = Var(Der(P); 0, +∞)`.

The key technical input is Lemma 2.36 below.

## Lemma 2.36 (BPR)

Let `c` be a root of `P` of multiplicity `mu ≥ 0`. If no `P^{(k)}` for
`0 ≤ k ≤ p` has a root in `[d, c) ∪ (c, d']`, then
  (a) `Var(Der(P); d, c) − mu` is non-negative and even,
  (b) `Var(Der(P); c, d') = 0`.

The proof is by induction on the degree of `P`, splitting on whether
`P(c) = 0` (mu > 0) or `P(c) ≠ 0` (mu = 0), with a four-way case analysis
(parity of `ν := mult_c(P')`, sign of `P^{(ν+1)}(c) · P(c)`) in the latter.
-/

namespace Azurite.BPR.Theorem2_35

open Polynomial Azurite.BPR Azurite.BPR.Proposition2_20 Azurite.BPR.Proposition2_21

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ### Auxiliary: natDegree of derivative in char 0 -/

/-- In a characteristic-zero ring, `natDegree (derivative P) = natDegree P - 1`
    when `natDegree P ≥ 1`. Used to show `der P = P :: der (derivative P)`. -/
lemma natDegree_derivative_of_pos {P : R[X]} (hP : 1 ≤ P.natDegree) :
    (derivative P).natDegree = P.natDegree - 1 :=
  Polynomial.natDegree_eq_of_degree_eq_some
    (Polynomial.degree_derivative_eq P (Nat.lt_of_lt_of_le Nat.zero_lt_one hP))

/-! ### Auxiliary: der P = P :: der (derivative P) -/

/-- When `P.natDegree ≥ 1`, the derivative list unfolds as a cons:
    `der P = P :: der (derivative P)`. Immediate from the range definition
    and `natDegree_derivative_of_pos`. -/
lemma der_eq_cons {P : R[X]} (hP : 1 ≤ P.natDegree) :
    der P = P :: der (derivative P) := by
  unfold der
  rw [natDegree_derivative_of_pos hP, Nat.sub_add_cancel hP,
    List.range_succ_eq_map]
  simp only [List.map_cons, Function.iterate_zero_apply, List.map_map]
  congr 1

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The derivative list is always nonempty with head `P`: `der P = P :: rest`
    for some `rest`. Unlike `der_eq_cons`, this does not require `P.natDegree ≥ 1`
    (when `P.natDegree = 0`, `rest = []`). -/
private lemma der_cons_exists (P : R[X]) : ∃ rest, der P = P :: rest := by
  unfold der
  rw [List.range_succ_eq_map, List.map_cons]
  exact ⟨_, rfl⟩

/-! ### Auxiliary: Var unfolding lemmas -/

omit [IsStrictOrderedRing R] in
/-- If both head elements are nonzero, `Var` splits as the sign-change
    indicator of the pair plus `Var` of the tail. This is the workhorse for
    comparing `varAt (der P) x` to `varAt (der Q) x` where `Q = derivative P`. -/
private lemma Var_cons_cons_of_ne_zero {a b : R} {rest : List R}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Var (a :: b :: rest) = (if a * b < 0 then 1 else 0) + Var (b :: rest) := by
  unfold Var
  rw [List.filter_cons, List.filter_cons]
  simp only [decide_not, ne_eq, ha, not_false_eq_true, decide_true,
    ↓reduceIte, hb]
  rfl

omit [IsStrictOrderedRing R] in
/-- Filtering zeros out of the tail of `a :: l` does not change `Var`. Useful
    when `l` has leading zeros that should be dropped before comparing. -/
private lemma Var_cons_eq_cons_filter (a : R) (l : List R) :
    Var (a :: l) = Var (a :: l.filter (· ≠ 0)) := by
  unfold Var
  rw [List.filter_cons, List.filter_cons]
  simp only [List.filter_filter, decide_not, Bool.and_self, Bool.not_eq_true',
    decide_eq_false_iff_not]

omit [IsStrictOrderedRing R] in
/-- Inserting a zero after the head does not change `Var`: zeros are absorbed
    by the filter regardless of whether the head itself is zero. -/
private lemma Var_cons_zero_cons (a : R) (l : List R) :
    Var (a :: (0 : R) :: l) = Var (a :: l) := by
  unfold Var
  by_cases ha : a = 0
  · subst ha; simp
  · simp [ha]

/-! ### Auxiliary: varAt identity when the tail has leading zeros -/

/-- When `P.eval c ≠ 0` and `Q ≠ 0`, we can compute `varAt (P :: der Q) c` in
    terms of `varAt (der Q) c` plus a jump indicator: the first nonzero
    evaluation in `der Q` at `c` is `(derivative^[ν] Q)(c)` where
    `ν = Q.rootMultiplicity c`, so `Var` sees the pair `(P(c), (d^ν Q)(c))`
    across the intervening zeros. Proved by strong induction on `Q.natDegree`:
    when `Q(c) ≠ 0` the cons-cons unfolding applies directly; when `Q(c) = 0`
    we strip the leading zero and recurse on `derivative Q`. -/
lemma varAt_cons_der_eq (P Q : R[X]) {c : R}
    (hPc : P.eval c ≠ 0) (hQ_ne : Q ≠ 0) :
    varAt (P :: der Q) (.finite c) =
      (if P.eval c * ((⇑derivative)^[Q.rootMultiplicity c] Q).eval c < 0
        then 1 else 0) + varAt (der Q) (.finite c) := by
  suffices H : ∀ (n : ℕ) (Q : R[X]), Q.natDegree = n → Q ≠ 0 →
      varAt (P :: der Q) (.finite c) =
        (if P.eval c * ((⇑derivative)^[Q.rootMultiplicity c] Q).eval c < 0
          then 1 else 0) + varAt (der Q) (.finite c) from
    H Q.natDegree Q rfl hQ_ne
  intro n
  induction n with
  | zero =>
    intro Q hQnat hQ_ne
    -- Q is a nonzero constant; Q(c) ≠ 0, rootMult = 0, der Q = [Q].
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hQnat
    have ha_ne : a ≠ 0 := fun h => hQ_ne (ha ▸ h ▸ by simp)
    have hQc_ne : Q.eval c ≠ 0 := by rw [← ha]; simpa
    have hmult : Q.rootMultiplicity c = 0 :=
      Polynomial.rootMultiplicity_eq_zero hQc_ne
    have hder : der Q = [Q] := by unfold der; rw [hQnat]; rfl
    rw [hmult]
    simp only [Function.iterate_zero_apply]
    rw [hder, varAt_finite, varAt_finite]
    simp only [List.map_cons, List.map_nil]
    rw [Var_cons_cons_of_ne_zero hPc hQc_ne,
      Var_of_forall_ne_zero (by simp [hQc_ne])]
    rfl
  | succ n ih =>
    intro Q hQnat hQ_ne
    have hQpos : 1 ≤ Q.natDegree := by rw [hQnat]; omega
    have hderQ_cons : der Q = Q :: der (derivative Q) := der_eq_cons hQpos
    have hderQnat : (derivative Q).natDegree = n := by
      have h := natDegree_derivative_of_pos hQpos
      omega
    have hderQ_ne : derivative Q ≠ 0 := fun h => by
      have hh := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
      rw [hQnat] at hh; omega
    by_cases hQc : Q.eval c = 0
    · -- Q(c) = 0: strip the leading zero and recurse on derivative Q.
      have hmult_pos : 1 ≤ Q.rootMultiplicity c :=
        (Polynomial.rootMultiplicity_pos hQ_ne).mpr hQc
      have hmult : Q.rootMultiplicity c =
          (derivative Q).rootMultiplicity c + 1 := by
        have h := Polynomial.derivative_rootMultiplicity_of_root hQc
        omega
      rw [hmult]
      rw [show (⇑derivative)^[(derivative Q).rootMultiplicity c + 1] Q =
            (⇑derivative)^[(derivative Q).rootMultiplicity c] (derivative Q)
        from Function.iterate_succ_apply _ _ _]
      rw [hderQ_cons, varAt_finite, varAt_finite]
      simp only [List.map_cons]
      rw [hQc, Var_cons_zero_cons, Var_zero_cons]
      have ih_applied := ih (derivative Q) hderQnat hderQ_ne
      rw [varAt_finite, varAt_finite] at ih_applied
      simp only [List.map_cons] at ih_applied
      exact ih_applied
    · -- Q(c) ≠ 0: direct cons-cons unfolding.
      have hmult : Q.rootMultiplicity c = 0 :=
        Polynomial.rootMultiplicity_eq_zero hQc
      rw [hmult]
      simp only [Function.iterate_zero_apply]
      rw [hderQ_cons, varAt_finite, varAt_finite]
      simp only [List.map_cons]
      exact Var_cons_cons_of_ne_zero hPc hQc

/-! ### Auxiliary: sign constancy on a root-free interval -/

/-- If `Q` does not vanish anywhere in the closed interval `[x, y]` and `x ≤ y`,
    then `Q` has the same sign at `x` and `y`. This is the key input that lets
    us compare `varAt (der P)` at different evaluation points inside a
    root-free interval. -/
lemma sign_eq_of_no_root_Icc (hIVP : HasIntermediateValueProperty R)
    (Q : R[X]) {x y : R} (hxy : x ≤ y)
    (hne : ∀ z ∈ Set.Icc x y, Q.eval z ≠ 0) :
    SignType.sign (Q.eval x) = SignType.sign (Q.eval y) := by
  rcases eq_or_lt_of_le hxy with heq | hxy
  · rw [heq]
  have hne_Ioo : ∀ z ∈ Set.Ioo x y, Q.eval z ≠ 0 :=
    fun z hz => hne z ⟨hz.1.le, hz.2.le⟩
  obtain ⟨bx, hxbx, hsigR⟩ :=
    hasSignRight_of_eval_ne_zero hIVP (hne x ⟨le_refl x, hxy.le⟩)
  obtain ⟨ay, hay_y, hsigL⟩ :=
    hasSignLeft_of_eval_ne_zero hIVP (hne y ⟨hxy.le, le_refl y⟩)
  rcases proposition_2_20 hIVP Q x y hne_Ioo with hpos | hneg
  · obtain ⟨z, hxz, hzm⟩ := exists_between (lt_min hxbx hxy)
    have hzbx : z < bx := lt_of_lt_of_le hzm (min_le_left _ _)
    have hzy : z < y := lt_of_lt_of_le hzm (min_le_right _ _)
    have hsx : SignType.sign (Q.eval x) = 1 := by
      rw [← hsigR z ⟨hxz, hzbx⟩]; exact sign_pos (hpos z ⟨hxz, hzy⟩)
    obtain ⟨w, hwm, hwy⟩ := exists_between (max_lt hxy hay_y)
    have haw : ay < w := lt_of_le_of_lt (le_max_right _ _) hwm
    have hxw : x < w := lt_of_le_of_lt (le_max_left _ _) hwm
    have hsy : SignType.sign (Q.eval y) = 1 := by
      rw [← hsigL w ⟨haw, hwy⟩]; exact sign_pos (hpos w ⟨hxw, hwy⟩)
    rw [hsx, hsy]
  · obtain ⟨z, hxz, hzm⟩ := exists_between (lt_min hxbx hxy)
    have hzbx : z < bx := lt_of_lt_of_le hzm (min_le_left _ _)
    have hzy : z < y := lt_of_lt_of_le hzm (min_le_right _ _)
    have hsx : SignType.sign (Q.eval x) = -1 := by
      rw [← hsigR z ⟨hxz, hzbx⟩]; exact sign_neg (hneg z ⟨hxz, hzy⟩)
    obtain ⟨w, hwm, hwy⟩ := exists_between (max_lt hxy hay_y)
    have haw : ay < w := lt_of_le_of_lt (le_max_right _ _) hwm
    have hxw : x < w := lt_of_le_of_lt (le_max_left _ _) hwm
    have hsy : SignType.sign (Q.eval y) = -1 := by
      rw [← hsigL w ⟨haw, hwy⟩]; exact sign_neg (hneg w ⟨hxw, hwy⟩)
    rw [hsx, hsy]

/-! ### BPR Lemma 2.36 -/

/-- **BPR Lemma 2.36.** Let `c` be a root of `P` of multiplicity `mu ≥ 0`.
    Assume no iterated derivative `P^{(k)}` (`0 ≤ k ≤ deg P`) has a root
    in `[d, c) ∪ (c, d']`. Then
      (a) `Var(Der(P); d, c) − mu` is non-negative and even,
      (b) `Var(Der(P); c, d') = 0`.
    Proved by induction on `P.natDegree`, applying the IH to `derivative P`. -/
theorem lemma_2_36 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {c d d' : R} (hdc : d < c) (hcd' : c < d')
    (hno_root : ∀ k ≤ P.natDegree, ∀ x,
      x ∈ Set.Ico d c ∪ Set.Ioc c d' →
      ((⇑derivative)^[k] P).eval x ≠ 0) :
    ((P.rootMultiplicity c : ℤ) ≤
        varBetween (der P) (.finite d) (.finite c) ∧
      Even (varBetween (der P) (.finite d) (.finite c) -
        P.rootMultiplicity c)) ∧
    varBetween (der P) (.finite c) (.finite d') = 0 := by
  suffices H : ∀ (n : ℕ) (P : R[X]), P.natDegree = n → ∀ {c d d' : R},
      d < c → c < d' →
      (∀ k ≤ P.natDegree, ∀ x, x ∈ Set.Ico d c ∪ Set.Ioc c d' →
        ((⇑derivative)^[k] P).eval x ≠ 0) →
      ((P.rootMultiplicity c : ℤ) ≤
          varBetween (der P) (.finite d) (.finite c) ∧
        Even (varBetween (der P) (.finite d) (.finite c) -
          P.rootMultiplicity c)) ∧
      varBetween (der P) (.finite c) (.finite d') = 0 from
    H P.natDegree P rfl hdc hcd' hno_root
  clear hno_root hdc hcd'
  intro n
  induction n with
  | zero =>
    intro P hP c d d' hdc _hcd' hno_root
    -- Base case: P is a nonzero constant. der P = [P], so both varBetween = 0.
    -- P ≠ 0 from the no-root hypothesis at x = d, k = 0.
    have hP_ne : P ≠ 0 := fun hzero => by
      have := hno_root 0 (Nat.zero_le _) d (Or.inl ⟨le_refl d, hdc⟩)
      simp [hzero] at this
    -- Extract the constant value.
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hP
    -- a ≠ 0 since P = C a ≠ 0.
    have ha_ne : a ≠ 0 := fun h => hP_ne (ha ▸ h ▸ by simp)
    -- der P = [P].
    have hder : der P = [P] := by
      unfold der; rw [hP]; rfl
    -- c is not a root of P (nonzero constant never vanishes).
    have hPc_ne : P.eval c ≠ 0 := by rw [← ha]; simpa
    have hmult : P.rootMultiplicity c = 0 := by
      apply Polynomial.rootMultiplicity_eq_zero
      intro hroot
      exact hPc_ne hroot
    have hvar_eq : ∀ x, varAt (der P) (.finite x) = 0 := fun x => by
      rw [hder, varAt_finite]
      simp only [List.map_cons, List.map_nil]
      by_cases hx : P.eval x = 0
      · rw [hx, Var_zero_cons]; rfl
      · rw [Var_of_forall_ne_zero (by simp [hx])]; rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hmult]
      unfold varBetween
      simp [hvar_eq]
    · rw [hmult]
      unfold varBetween
      simp [hvar_eq]
    · unfold varBetween
      simp [hvar_eq]
  | succ n ih =>
    intro P hP c d d' hdc hcd' hno_root
    -- Inductive case: P.natDegree = n + 1.
    -- Let Q = derivative P; Q.natDegree = n, so IH applies.
    set Q := derivative P with hQ
    have hPpos : 1 ≤ P.natDegree := by rw [hP]; omega
    have hQnat : Q.natDegree = n := by
      rw [hQ, natDegree_derivative_of_pos hPpos, hP]; rfl
    have hder_cons : der P = P :: der Q := der_eq_cons hPpos
    -- Derive the no-root hypothesis for Q from the one for P.
    have hno_root_Q : ∀ k ≤ Q.natDegree, ∀ x,
        x ∈ Set.Ico d c ∪ Set.Ioc c d' →
        ((⇑derivative)^[k] Q).eval x ≠ 0 := by
      intro k hk x hx
      have hk' : k + 1 ≤ P.natDegree := by
        rw [hQnat] at hk; rw [hP]; omega
      have h := hno_root (k + 1) hk' x hx
      rwa [Function.iterate_succ_apply] at h
    obtain ⟨⟨hQmult_le, hQeven⟩, hQright⟩ := ih Q hQnat hdc hcd' hno_root_Q
    -- P ≠ 0 from the no-root hypothesis at x = d, k = 0.
    have hP_ne : P ≠ 0 := fun hzero => by
      have := hno_root 0 (Nat.zero_le _) d (Or.inl ⟨le_refl d, hdc⟩)
      simp [hzero] at this
    -- Split on whether c is a root of P.
    by_cases hPc : P.eval c = 0
    · -- Case mu ≥ 1: P(c) = 0.
      -- IH bound on Q lifts to P: prepending P.eval c = 0 at c does not
      -- change Var, while at d the signs of P and Q are opposite (so varAt
      -- jumps by 1) and at d' the signs agree (so varAt is unchanged).
      set mu := P.rootMultiplicity c with hmu_def
      have hQ_ne : Q ≠ 0 := fun h => by
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
        rw [hP] at this; omega
      have hmu_pos : 1 ≤ mu :=
        (Polynomial.rootMultiplicity_pos hP_ne).mpr hPc
      have hmuQ : Q.rootMultiplicity c = mu - 1 := by
        rw [hQ]
        exact Polynomial.derivative_rootMultiplicity_of_root hPc
      -- `derivative^[mu] P = derivative^[mu - 1] Q` (same iterated derivative).
      have hPmu_eq_Qν : ((⇑derivative)^[mu] P) = ((⇑derivative)^[mu - 1] Q) := by
        rw [hQ, ← Function.iterate_succ_apply]
        congr 1
        omega
      -- `σ = sign(P^(mu)(c)) = sign(Q^(mu-1)(c))`.
      set σ : SignType := SignType.sign (((⇑derivative)^[mu] P).eval c) with hσ_def
      have hP_sr : HasSignRight P c σ := proposition_2_21_right hIVP hP_ne c
      have hP_sl : HasSignLeft P c ((-1)^mu * σ) := proposition_2_21_left hIVP hP_ne c
      have hQ_sr : HasSignRight Q c σ := by
        have h := proposition_2_21_right hIVP hQ_ne c
        rw [hmuQ, ← hPmu_eq_Qν] at h
        exact h
      have hQ_sl : HasSignLeft Q c ((-1)^(mu - 1) * σ) := by
        have h := proposition_2_21_left hIVP hQ_ne c
        rw [hmuQ, ← hPmu_eq_Qν] at h
        exact h
      have hPd_ne : P.eval d ≠ 0 :=
        hno_root 0 (Nat.zero_le _) d (Or.inl ⟨le_refl d, hdc⟩)
      have hPd'_ne : P.eval d' ≠ 0 :=
        hno_root 0 (Nat.zero_le _) d' (Or.inr ⟨hcd', le_refl d'⟩)
      have hQd_ne : Q.eval d ≠ 0 := by
        have h := hno_root 1 hPpos d (Or.inl ⟨le_refl d, hdc⟩)
        rwa [Function.iterate_one] at h
      have hQd'_ne : Q.eval d' ≠ 0 := by
        have h := hno_root 1 hPpos d' (Or.inr ⟨hcd', le_refl d'⟩)
        rwa [Function.iterate_one] at h
      -- Signs at d, d' via HasSignRight/Left + sign constancy on root-free intervals.
      have hP_sign_d' : SignType.sign (P.eval d') = σ := by
        obtain ⟨b, hcb, hsb⟩ := hP_sr
        obtain ⟨ε, hcε, hεm⟩ := exists_between (lt_min hcb hcd')
        have hεb : ε < b := lt_of_lt_of_le hεm (min_le_left _ _)
        have hεd' : ε ≤ d' := le_of_lt (lt_of_lt_of_le hεm (min_le_right _ _))
        have hsε := hsb ε ⟨hcε, hεb⟩
        have hne : ∀ z ∈ Set.Icc ε d', P.eval z ≠ 0 := fun z hz =>
          hno_root 0 (Nat.zero_le _) z
            (Or.inr ⟨lt_of_lt_of_le hcε hz.1, hz.2⟩)
        rw [← hsε, sign_eq_of_no_root_Icc hIVP P hεd' hne]
      have hQ_sign_d' : SignType.sign (Q.eval d') = σ := by
        obtain ⟨b, hcb, hsb⟩ := hQ_sr
        obtain ⟨ε, hcε, hεm⟩ := exists_between (lt_min hcb hcd')
        have hεb : ε < b := lt_of_lt_of_le hεm (min_le_left _ _)
        have hεd' : ε ≤ d' := le_of_lt (lt_of_lt_of_le hεm (min_le_right _ _))
        have hsε := hsb ε ⟨hcε, hεb⟩
        have hne : ∀ z ∈ Set.Icc ε d', Q.eval z ≠ 0 := fun z hz => by
          have h := hno_root 1 hPpos z
            (Or.inr ⟨lt_of_lt_of_le hcε hz.1, hz.2⟩)
          rwa [Function.iterate_one] at h
        rw [← hsε, sign_eq_of_no_root_Icc hIVP Q hεd' hne]
      have hP_sign_d : SignType.sign (P.eval d) = (-1)^mu * σ := by
        obtain ⟨a, had, hsa⟩ := hP_sl
        obtain ⟨ε, hεm, hεc⟩ := exists_between (max_lt had hdc)
        have hεa : a < ε := lt_of_le_of_lt (le_max_left _ _) hεm
        have hdε : d ≤ ε := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hεm)
        have hsε := hsa ε ⟨hεa, hεc⟩
        have hne : ∀ z ∈ Set.Icc d ε, P.eval z ≠ 0 := fun z hz =>
          hno_root 0 (Nat.zero_le _) z
            (Or.inl ⟨hz.1, lt_of_le_of_lt hz.2 hεc⟩)
        rw [sign_eq_of_no_root_Icc hIVP P hdε hne, hsε]
      have hQ_sign_d : SignType.sign (Q.eval d) = (-1)^(mu - 1) * σ := by
        obtain ⟨a, had, hsa⟩ := hQ_sl
        obtain ⟨ε, hεm, hεc⟩ := exists_between (max_lt had hdc)
        have hεa : a < ε := lt_of_le_of_lt (le_max_left _ _) hεm
        have hdε : d ≤ ε := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hεm)
        have hsε := hsa ε ⟨hεa, hεc⟩
        have hne : ∀ z ∈ Set.Icc d ε, Q.eval z ≠ 0 := fun z hz => by
          have h := hno_root 1 hPpos z
            (Or.inl ⟨hz.1, lt_of_le_of_lt hz.2 hεc⟩)
          rwa [Function.iterate_one] at h
        rw [sign_eq_of_no_root_Icc hIVP Q hdε hne, hsε]
      -- `σ ≠ 0` since sign(P(d')) = σ and P(d') ≠ 0.
      have hσ_ne : σ ≠ 0 := fun h =>
        hPd'_ne (sign_eq_zero_iff.mp (hP_sign_d'.trans h))
      -- P(d') and Q(d') same sign ⇒ product positive.
      have hPQd'_pos : 0 < P.eval d' * Q.eval d' := by
        have hs : SignType.sign (P.eval d' * Q.eval d') = 1 := by
          rw [sign_mul, hP_sign_d', hQ_sign_d']
          rcases σ with _ | _ | _
          · exact absurd rfl hσ_ne
          all_goals decide
        exact sign_eq_one_iff.mp hs
      -- `(-1 : SignType)^n` is never zero.
      have hpow_ne_zero : ∀ n : ℕ, (-1 : SignType)^n ≠ 0 := by
        intro n
        induction n with
        | zero => decide
        | succ k ih =>
          rw [pow_succ]; intro h
          rcases mul_eq_zero.mp h with h | h
          · exact ih h
          · exact absurd h (by decide)
      -- P(d) and Q(d) opposite signs ⇒ product negative.
      have hPQd_neg : P.eval d * Q.eval d < 0 := by
        have hs : SignType.sign (P.eval d * Q.eval d) = -1 := by
          rw [sign_mul, hP_sign_d, hQ_sign_d]
          have hmueq : mu = (mu - 1) + 1 := (Nat.sub_add_cancel hmu_pos).symm
          nth_rewrite 1 [hmueq]
          rw [pow_succ]
          rcases σ with _ | _ | _
          · exact absurd rfl hσ_ne
          all_goals (
            rcases h : (-1 : SignType)^(mu - 1) with _ | _ | _
            · exact absurd h (hpow_ne_zero _)
            all_goals decide)
        exact sign_eq_neg_one_iff.mp hs
      -- der Q = Q :: rest, to enable the cons-cons Var unfolding.
      obtain ⟨rest, hderQ⟩ := der_cons_exists Q
      -- At c: prepending zero leaves varAt unchanged.
      have hvarc : varAt (der P) (.finite c) = varAt (der Q) (.finite c) := by
        rw [varAt_finite, varAt_finite, hder_cons]
        simp only [List.map_cons]
        rw [hPc, Var_zero_cons]
      -- At d': same-sign heads ⇒ no jump.
      have hvard' : varAt (der P) (.finite d') = varAt (der Q) (.finite d') := by
        rw [varAt_finite, varAt_finite, hder_cons, hderQ]
        simp only [List.map_cons]
        rw [Var_cons_cons_of_ne_zero hPd'_ne hQd'_ne,
          if_neg (not_lt.mpr (le_of_lt hPQd'_pos)), zero_add]
      -- At d: opposite-sign heads ⇒ jump of exactly 1.
      have hvard : varAt (der P) (.finite d) = 1 + varAt (der Q) (.finite d) := by
        rw [varAt_finite, varAt_finite, hder_cons, hderQ]
        simp only [List.map_cons]
        rw [Var_cons_cons_of_ne_zero hPd_ne hQd_ne, if_pos hPQd_neg]
      -- `((mu - 1 : ℕ) : ℤ) = (mu : ℤ) - 1` since mu ≥ 1.
      have hcast_sub : ((mu - 1 : ℕ) : ℤ) = (mu : ℤ) - 1 := by
        rw [Nat.cast_sub hmu_pos]; push_cast; ring
      -- Conclude using the IH on Q.
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- mu ≤ varBetween (der P) d c.
        unfold varBetween at hQmult_le ⊢
        rw [hvard, hvarc]
        rw [hmuQ] at hQmult_le
        rw [hcast_sub] at hQmult_le
        push_cast at hQmult_le ⊢
        omega
      · -- Even (varBetween (der P) d c - mu).
        unfold varBetween at hQeven ⊢
        rw [hvard, hvarc]
        rw [hmuQ] at hQeven
        rw [hcast_sub] at hQeven
        push_cast at hQeven ⊢
        convert hQeven using 1
        ring
      · -- varBetween (der P) c d' = 0.
        unfold varBetween at hQright ⊢
        rw [hvarc, hvard']
        exact hQright
    · -- Case mu = 0: P(c) ≠ 0.
      -- `ν := Q.rootMultiplicity c`. Prop 2.21 for Q gives sign τ on the
      -- right of `c` and sign `(-1)^ν · τ` on the left; for P (rootMult = 0)
      -- both sides carry the sign σP = sign(P(c)). At `c`, the helper
      -- `varAt_cons_der_eq` handles leading zeros in the der Q list. Signs
      -- at `d` and `d'` are constant (no roots), so the jump indicators
      -- between der P and der Q have the structure: jd' = jc always, and
      -- `jd = jc` when ν is even, `jd + jc = 1` when ν is odd. Combined
      -- with the IH on Q (bound ν, parity ν), the required bound and
      -- evenness for mu = 0 drop out.
      have hmult_P : P.rootMultiplicity c = 0 :=
        Polynomial.rootMultiplicity_eq_zero hPc
      set ν := Q.rootMultiplicity c with hν_def
      have hQ_ne : Q ≠ 0 := fun h => by
        have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
        rw [hP] at this; omega
      set σP : SignType := SignType.sign (P.eval c) with hσP_def
      set τ : SignType := SignType.sign (((⇑derivative)^[ν] Q).eval c) with hτ_def
      have hσP_ne : σP ≠ 0 := fun h => hPc (sign_eq_zero_iff.mp h)
      -- Prop 2.21 for P (rootMult = 0): sign σP both sides.
      have hP_sr : HasSignRight P c σP := by
        have h := proposition_2_21_right hIVP hP_ne c
        rw [hmult_P] at h
        simp only [Function.iterate_zero_apply] at h
        exact h
      have hP_sl : HasSignLeft P c σP := by
        have h := proposition_2_21_left hIVP hP_ne c
        rw [hmult_P] at h
        simp only [Function.iterate_zero_apply, pow_zero, one_mul] at h
        exact h
      have hQ_sr : HasSignRight Q c τ := proposition_2_21_right hIVP hQ_ne c
      have hQ_sl : HasSignLeft Q c ((-1)^ν * τ) :=
        proposition_2_21_left hIVP hQ_ne c
      have hPd_ne : P.eval d ≠ 0 :=
        hno_root 0 (Nat.zero_le _) d (Or.inl ⟨le_refl d, hdc⟩)
      have hPd'_ne : P.eval d' ≠ 0 :=
        hno_root 0 (Nat.zero_le _) d' (Or.inr ⟨hcd', le_refl d'⟩)
      have hQd_ne : Q.eval d ≠ 0 := by
        have h := hno_root 1 hPpos d (Or.inl ⟨le_refl d, hdc⟩)
        rwa [Function.iterate_one] at h
      have hQd'_ne : Q.eval d' ≠ 0 := by
        have h := hno_root 1 hPpos d' (Or.inr ⟨hcd', le_refl d'⟩)
        rwa [Function.iterate_one] at h
      -- Sign extensions to d, d'.
      have hP_sign_d' : SignType.sign (P.eval d') = σP := by
        obtain ⟨b, hcb, hsb⟩ := hP_sr
        obtain ⟨ε, hcε, hεm⟩ := exists_between (lt_min hcb hcd')
        have hεb : ε < b := lt_of_lt_of_le hεm (min_le_left _ _)
        have hεd' : ε ≤ d' := le_of_lt (lt_of_lt_of_le hεm (min_le_right _ _))
        have hsε := hsb ε ⟨hcε, hεb⟩
        have hne : ∀ z ∈ Set.Icc ε d', P.eval z ≠ 0 := fun z hz =>
          hno_root 0 (Nat.zero_le _) z
            (Or.inr ⟨lt_of_lt_of_le hcε hz.1, hz.2⟩)
        rw [← hsε, sign_eq_of_no_root_Icc hIVP P hεd' hne]
      have hQ_sign_d' : SignType.sign (Q.eval d') = τ := by
        obtain ⟨b, hcb, hsb⟩ := hQ_sr
        obtain ⟨ε, hcε, hεm⟩ := exists_between (lt_min hcb hcd')
        have hεb : ε < b := lt_of_lt_of_le hεm (min_le_left _ _)
        have hεd' : ε ≤ d' := le_of_lt (lt_of_lt_of_le hεm (min_le_right _ _))
        have hsε := hsb ε ⟨hcε, hεb⟩
        have hne : ∀ z ∈ Set.Icc ε d', Q.eval z ≠ 0 := fun z hz => by
          have h := hno_root 1 hPpos z
            (Or.inr ⟨lt_of_lt_of_le hcε hz.1, hz.2⟩)
          rwa [Function.iterate_one] at h
        rw [← hsε, sign_eq_of_no_root_Icc hIVP Q hεd' hne]
      have hP_sign_d : SignType.sign (P.eval d) = σP := by
        obtain ⟨a, had, hsa⟩ := hP_sl
        obtain ⟨ε, hεm, hεc⟩ := exists_between (max_lt had hdc)
        have hεa : a < ε := lt_of_le_of_lt (le_max_left _ _) hεm
        have hdε : d ≤ ε := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hεm)
        have hsε := hsa ε ⟨hεa, hεc⟩
        have hne : ∀ z ∈ Set.Icc d ε, P.eval z ≠ 0 := fun z hz =>
          hno_root 0 (Nat.zero_le _) z
            (Or.inl ⟨hz.1, lt_of_le_of_lt hz.2 hεc⟩)
        rw [sign_eq_of_no_root_Icc hIVP P hdε hne, hsε]
      have hQ_sign_d : SignType.sign (Q.eval d) = (-1)^ν * τ := by
        obtain ⟨a, had, hsa⟩ := hQ_sl
        obtain ⟨ε, hεm, hεc⟩ := exists_between (max_lt had hdc)
        have hεa : a < ε := lt_of_le_of_lt (le_max_left _ _) hεm
        have hdε : d ≤ ε := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hεm)
        have hsε := hsa ε ⟨hεa, hεc⟩
        have hne : ∀ z ∈ Set.Icc d ε, Q.eval z ≠ 0 := fun z hz => by
          have h := hno_root 1 hPpos z
            (Or.inl ⟨hz.1, lt_of_le_of_lt hz.2 hεc⟩)
          rwa [Function.iterate_one] at h
        rw [sign_eq_of_no_root_Icc hIVP Q hdε hne, hsε]
      -- `τ ≠ 0` from sign(Q(d')) = τ and Q(d') ≠ 0.
      have hτ_ne : τ ≠ 0 := fun h =>
        hQd'_ne (sign_eq_zero_iff.mp (hQ_sign_d'.trans h))
      -- Sign products at d, c, d'.
      have hsign_d : SignType.sign (P.eval d * Q.eval d) = σP * ((-1)^ν * τ) := by
        rw [sign_mul, hP_sign_d, hQ_sign_d]
      have hsign_d' : SignType.sign (P.eval d' * Q.eval d') = σP * τ := by
        rw [sign_mul, hP_sign_d', hQ_sign_d']
      have hsign_c : SignType.sign (P.eval c * ((⇑derivative)^[ν] Q).eval c)
          = σP * τ := sign_mul _ _
      -- The `(ν+1)`th indicator expressed via rootMult_c Q = ν.
      obtain ⟨rest, hderQ⟩ := der_cons_exists Q
      have hvard : varAt (der P) (.finite d) =
          (if P.eval d * Q.eval d < 0 then 1 else 0) +
            varAt (der Q) (.finite d) := by
        rw [varAt_finite, varAt_finite, hder_cons, hderQ]
        simp only [List.map_cons]
        exact Var_cons_cons_of_ne_zero hPd_ne hQd_ne
      have hvard' : varAt (der P) (.finite d') =
          (if P.eval d' * Q.eval d' < 0 then 1 else 0) +
            varAt (der Q) (.finite d') := by
        rw [varAt_finite, varAt_finite, hder_cons, hderQ]
        simp only [List.map_cons]
        exact Var_cons_cons_of_ne_zero hPd'_ne hQd'_ne
      have hvarc : varAt (der P) (.finite c) =
          (if P.eval c * ((⇑derivative)^[ν] Q).eval c < 0 then 1 else 0) +
            varAt (der Q) (.finite c) := by
        rw [hder_cons]; exact varAt_cons_der_eq P Q hPc hQ_ne
      -- The key relationship: jd' = jc always, and jd relates to jc via ν parity.
      have hjc_eq_jd' :
          (if P.eval c * ((⇑derivative)^[ν] Q).eval c < 0 then (1 : ℕ) else 0)
            = (if P.eval d' * Q.eval d' < 0 then 1 else 0) :=
        if_congr (by rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff,
          hsign_c, hsign_d']) rfl rfl
      rcases Nat.even_or_odd ν with hν_even | hν_odd
      · -- ν even ⇒ jd = jc.
        have hpow_even : ((-1 : SignType))^ν = 1 := Even.neg_one_pow hν_even
        have hjd_eq_jc :
            (if P.eval d * Q.eval d < 0 then (1 : ℕ) else 0)
              = (if P.eval c * ((⇑derivative)^[ν] Q).eval c < 0 then 1 else 0) :=
          if_congr (by rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff,
            hsign_d, hsign_c, hpow_even, one_mul]) rfl rfl
        obtain ⟨k, hk⟩ := hν_even
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · unfold varBetween at hQmult_le ⊢
          rw [hvard, hvarc, hjd_eq_jc]
          push_cast [hmult_P]
          omega
        · unfold varBetween at hQeven ⊢
          rw [hvard, hvarc, hjd_eq_jc]
          push_cast [hmult_P]
          -- Even (varAt Q d - varAt Q c). Given hQeven: Even(varAt Q d - varAt Q c - ν).
          -- With ν even, both are equivalent.
          rcases hQeven with ⟨m, hm⟩
          refine ⟨m + k, ?_⟩
          push_cast [hk] at hm ⊢
          linarith
        · unfold varBetween at hQright ⊢
          rw [hvarc, hvard', hjc_eq_jd']
          push_cast at hQright ⊢
          omega
      · -- ν odd ⇒ jd + jc = 1.
        have hpow_odd : ((-1 : SignType))^ν = -1 := Odd.neg_one_pow hν_odd
        -- sign(P(d) Q(d)) = σP * (-1)^ν * τ = -(σP * τ) = -sign(P(c) * ...).
        have hd_opposite_c :
            SignType.sign (P.eval d * Q.eval d)
              = - SignType.sign (P.eval c * ((⇑derivative)^[ν] Q).eval c) := by
          rw [hsign_d, hsign_c, hpow_odd, neg_one_mul, mul_neg]
        -- (deriv^[ν] Q)(c) ≠ 0 (else τ = 0).
        have hderνQc_ne : ((⇑derivative)^[ν] Q).eval c ≠ 0 := fun h =>
          hτ_ne (by rw [hτ_def, h, sign_zero])
        have hpcQνc_ne : P.eval c * ((⇑derivative)^[ν] Q).eval c ≠ 0 :=
          mul_ne_zero hPc hderνQc_ne
        -- Split on which product is negative. This directly determines jd and jc.
        obtain ⟨k, hk⟩ := hν_odd
        rcases lt_or_gt_of_ne hpcQνc_ne with hc_neg | hc_pos
        · -- P(c) * deriv^[ν]Q(c) < 0, so jc = 1. And P(d)*Q(d) > 0, so jd = 0.
          have hd_pos : 0 < P.eval d * Q.eval d := by
            apply sign_eq_one_iff.mp
            rw [hd_opposite_c, sign_eq_neg_one_iff.mpr hc_neg]; decide
          have hjd_false : ¬ (P.eval d * Q.eval d < 0) := not_lt.mpr hd_pos.le
          have hjc_true : P.eval c * ((⇑derivative)^[ν] Q).eval c < 0 := hc_neg
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · unfold varBetween at hQmult_le ⊢
            rw [hvard, hvarc, if_neg hjd_false, if_pos hjc_true]
            push_cast [hmult_P]
            push_cast [hk] at hQmult_le
            omega
          · unfold varBetween at hQeven ⊢
            rw [hvard, hvarc, if_neg hjd_false, if_pos hjc_true]
            push_cast [hmult_P]
            rcases hQeven with ⟨m, hm⟩
            refine ⟨m + k, ?_⟩
            push_cast [hk] at hm ⊢
            linarith
          · unfold varBetween at hQright ⊢
            rw [hvarc, hvard', hjc_eq_jd']
            push_cast at hQright ⊢
            omega
        · -- P(c) * deriv^[ν]Q(c) > 0, so jc = 0. And P(d)*Q(d) < 0, so jd = 1.
          have hd_neg : P.eval d * Q.eval d < 0 := by
            apply sign_eq_neg_one_iff.mp
            rw [hd_opposite_c, sign_eq_one_iff.mpr hc_pos]
          have hjd_true : P.eval d * Q.eval d < 0 := hd_neg
          have hjc_false : ¬ (P.eval c * ((⇑derivative)^[ν] Q).eval c < 0) :=
            not_lt.mpr hc_pos.le
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · unfold varBetween at hQmult_le ⊢
            rw [hvard, hvarc, if_pos hjd_true, if_neg hjc_false]
            push_cast [hmult_P]
            push_cast [hk] at hQmult_le
            omega
          · unfold varBetween at hQeven ⊢
            rw [hvard, hvarc, if_pos hjd_true, if_neg hjc_false]
            push_cast [hmult_P]
            rcases hQeven with ⟨m, hm⟩
            refine ⟨m + k + 1, ?_⟩
            push_cast [hk] at hm ⊢
            linarith
          · unfold varBetween at hQright ⊢
            rw [hvarc, hvard', hjc_eq_jd']
            push_cast at hQright ⊢
            omega

/-! ### Auxiliary: iterated derivatives are nonzero for `k ≤ natDegree P` -/

/-- In any field of characteristic zero (here ensured by `Field R` together
    with `IsStrictOrderedRing R`), for `P ≠ 0` and `k ≤ P.natDegree`, the
    `k`-th iterated derivative is nonzero: its leading-position coefficient
    `P.natDegree.descFactorial k · P.leadingCoeff` is a product of a positive
    natural cast and a nonzero leading coefficient. -/
private lemma iterate_derivative_ne_zero_of_le_natDegree
    {P : R[X]} (hP : P ≠ 0) {k : ℕ} (hk : k ≤ P.natDegree) :
    (⇑derivative)^[k] P ≠ 0 := by
  intro h
  have hcoeff : ((⇑derivative)^[k] P).coeff (P.natDegree - k) =
      (P.natDegree.descFactorial k : R) * P.leadingCoeff := by
    have := Polynomial.coeff_iterate_derivative (p := P) (k := k) (P.natDegree - k)
    rw [Nat.sub_add_cancel hk] at this
    rw [this, nsmul_eq_mul]; rfl
  have h0 : ((⇑derivative)^[k] P).coeff (P.natDegree - k) = 0 := by rw [h]; simp
  rw [h0] at hcoeff
  have hfact_ne : (P.natDegree.descFactorial k : R) ≠ 0 := by
    have hpos : 0 < P.natDegree.descFactorial k := Nat.descFactorial_pos.mpr hk
    have : (0 : R) < (P.natDegree.descFactorial k : R) := by exact_mod_cast hpos
    exact ne_of_gt this
  exact absurd hcoeff.symm (mul_ne_zero hfact_ne
    (Polynomial.leadingCoeff_ne_zero.mpr hP))

/-! ### Auxiliary: buffers avoiding all iterated-derivative roots -/

/-- There is an interval `(r, b)` to the right of `r` avoiding all roots of
    every iterated derivative `P^{(k)}` for `k ≤ P.natDegree`. Induction on
    `k ≤ P.natDegree`: intersect the single-polynomial buffer from
    `exists_no_root_Ioo_right` for each `P^{(k)}`. -/
private lemma exists_no_root_Ioo_right_forall_der
    {P : R[X]} (hP : P ≠ 0) (r : R) :
    ∃ b, r < b ∧ ∀ x ∈ Set.Ioo r b, ∀ k ≤ P.natDegree,
      ((⇑derivative)^[k] P).eval x ≠ 0 := by
  -- Induction on the iteration bound m from P.natDegree down to 0.
  suffices H : ∀ m ≤ P.natDegree, ∃ b, r < b ∧ ∀ x ∈ Set.Ioo r b,
      ∀ k ≤ m, ((⇑derivative)^[k] P).eval x ≠ 0 from H _ le_rfl
  intro m hm
  induction m with
  | zero =>
    obtain ⟨b, hrb, hb⟩ := exists_no_root_Ioo_right hP r
    refine ⟨b, hrb, fun x hx k hk => ?_⟩
    interval_cases k
    simpa using hb x hx
  | succ m ih =>
    obtain ⟨b₁, hrb₁, hb₁⟩ := ih (Nat.le_of_succ_le hm)
    have hne : (⇑derivative)^[m + 1] P ≠ 0 :=
      iterate_derivative_ne_zero_of_le_natDegree hP hm
    obtain ⟨b₂, hrb₂, hb₂⟩ := exists_no_root_Ioo_right hne r
    refine ⟨min b₁ b₂, lt_min hrb₁ hrb₂, fun x hx k hk => ?_⟩
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact hb₁ x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩ k
        (Nat.le_of_lt_succ hlt)
    · have : k = m + 1 := le_antisymm hk hge
      rw [this]
      exact hb₂ x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩

/-- There is an interval `(a, r)` to the left of `r` avoiding all roots of
    every iterated derivative `P^{(k)}` for `k ≤ P.natDegree`. -/
lemma exists_no_root_Ioo_left_forall_der
    {P : R[X]} (hP : P ≠ 0) (r : R) :
    ∃ a, a < r ∧ ∀ x ∈ Set.Ioo a r, ∀ k ≤ P.natDegree,
      ((⇑derivative)^[k] P).eval x ≠ 0 := by
  suffices H : ∀ m ≤ P.natDegree, ∃ a, a < r ∧ ∀ x ∈ Set.Ioo a r,
      ∀ k ≤ m, ((⇑derivative)^[k] P).eval x ≠ 0 from H _ le_rfl
  intro m hm
  induction m with
  | zero =>
    obtain ⟨a, har, ha⟩ := exists_no_root_Ioo_left hP r
    refine ⟨a, har, fun x hx k hk => ?_⟩
    interval_cases k
    simpa using ha x hx
  | succ m ih =>
    obtain ⟨a₁, ha₁r, ha₁⟩ := ih (Nat.le_of_succ_le hm)
    have hne : (⇑derivative)^[m + 1] P ≠ 0 :=
      iterate_derivative_ne_zero_of_le_natDegree hP hm
    obtain ⟨a₂, ha₂r, ha₂⟩ := exists_no_root_Ioo_left hne r
    refine ⟨max a₁ a₂, max_lt ha₁r ha₂r, fun x hx k hk => ?_⟩
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact ha₁ x ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩ k
        (Nat.le_of_lt_succ hlt)
    · have : k = m + 1 := le_antisymm hk hge
      rw [this]
      exact ha₂ x ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, hx.2⟩

/-! ### One-sided variants of Lemma 2.36

Lemma 2.36 needs a root-free zone on **both** sides of `c`. For Theorem 2.35
we apply it to the endpoints `a` and `b` of the overall interval, where the
"outside" side is outside `(a, b]` — we handle that with a buffer from
`exists_no_root_Ioo_{left,right}_forall_der`. -/

/-- Left-sided Lemma 2.36: if no `P^{(k)}` has a root in `[d, c)`, then
    `Var(Der P; d, c) ≥ rootMult_c(P)` and has matching parity. Proven by
    adjoining a right buffer from `exists_no_root_Ioo_right_forall_der` to
    satisfy Lemma 2.36's combined hypothesis. -/
theorem lemma_2_36_left (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (hP : P ≠ 0) {c d : R} (hdc : d < c)
    (hno_root : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ico d c,
      ((⇑derivative)^[k] P).eval x ≠ 0) :
    ((P.rootMultiplicity c : ℤ) ≤
        varBetween (der P) (.finite d) (.finite c)) ∧
    Even (varBetween (der P) (.finite d) (.finite c) - P.rootMultiplicity c) := by
  obtain ⟨d', hcd', hd'⟩ := exists_no_root_Ioo_right_forall_der hP c
  obtain ⟨d'', hcd'', hd''d'⟩ := exists_between hcd'
  have hno_root' : ∀ k ≤ P.natDegree, ∀ x,
      x ∈ Set.Ico d c ∪ Set.Ioc c d'' →
      ((⇑derivative)^[k] P).eval x ≠ 0 := by
    intro k hk x hx
    rcases hx with hxl | hxr
    · exact hno_root k hk x hxl
    · exact hd' x ⟨hxr.1, lt_of_le_of_lt hxr.2 hd''d'⟩ k hk
  exact (lemma_2_36 hIVP P hdc hcd'' hno_root').1

/-- Right-sided Lemma 2.36: if no `P^{(k)}` has a root in `(c, d']`, then
    `Var(Der P; c, d') = 0`. Proven by adjoining a left buffer from
    `exists_no_root_Ioo_left_forall_der`. -/
theorem lemma_2_36_right (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) (hP : P ≠ 0) {c d' : R} (hcd' : c < d')
    (hno_root : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc c d',
      ((⇑derivative)^[k] P).eval x ≠ 0) :
    varBetween (der P) (.finite c) (.finite d') = 0 := by
  obtain ⟨d, hdc, hd⟩ := exists_no_root_Ioo_left_forall_der hP c
  obtain ⟨d_, hdd_, hd_c⟩ := exists_between hdc
  have hno_root' : ∀ k ≤ P.natDegree, ∀ x,
      x ∈ Set.Ico d_ c ∪ Set.Ioc c d' →
      ((⇑derivative)^[k] P).eval x ≠ 0 := by
    intro k hk x hx
    rcases hx with hxl | hxr
    · exact hd x ⟨lt_of_lt_of_le hdd_ hxl.1, hxl.2⟩ k hk
    · exact hno_root k hk x hxr
  exact (lemma_2_36 hIVP P hd_c hcd' hno_root').2

/-! ### Critical points of `P` in a half-open interval -/

open Classical in
/-- The finite set of critical points of `P` in `(a, b]`: points `r ∈ (a, b]`
    at which some iterated derivative `P^{(k)}` (`k ≤ P.natDegree`) vanishes.
    For `P ≠ 0`, this captures the essential structure BPR uses to subdivide
    `(a, b]` in the proof of Theorem 2.35. -/
noncomputable def critPointsIoc (P : R[X]) (a b : R) : Finset R :=
  (Finset.range (P.natDegree + 1)).biUnion fun k =>
    (((⇑derivative)^[k] P).roots.toFinset).filter (fun r => a < r ∧ r ≤ b)

/-- Membership characterization: `r ∈ critPointsIoc P a b` iff `r ∈ (a, b]`
    and some `P^{(k)}` vanishes at `r`. -/
lemma mem_critPointsIoc_iff {P : R[X]} (hP : P ≠ 0) {r a b : R} :
    r ∈ critPointsIoc P a b ↔
    (a < r ∧ r ≤ b) ∧
      ∃ k ≤ P.natDegree, ((⇑derivative)^[k] P).eval r = 0 := by
  classical
  simp only [critPointsIoc, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_range, Multiset.mem_toFinset]
  constructor
  · rintro ⟨k, hk, hr_roots, hab⟩
    have hne := iterate_derivative_ne_zero_of_le_natDegree hP
      (Nat.lt_succ_iff.mp hk)
    rw [Polynomial.mem_roots hne] at hr_roots
    exact ⟨hab, k, Nat.lt_succ_iff.mp hk, hr_roots⟩
  · rintro ⟨hab, k, hk, hr⟩
    have hne := iterate_derivative_ne_zero_of_le_natDegree hP hk
    refine ⟨k, Nat.lt_succ_iff.mpr hk, ?_, hab⟩
    rw [Polynomial.mem_roots hne]
    exact hr

/-! ### Splitting `numRoots` and `varBetween` at an intermediate point -/

omit [IsStrictOrderedRing R] in
/-- Reduced form of `numRoots` at two finite endpoints: direct filter card. -/
lemma numRoots_finite_finite (P : R[X]) (a b : R) :
    numRoots P (.finite a) (.finite b) =
      (P.roots.filter (fun r => a < r ∧ r ≤ b)).card := rfl

omit [IsStrictOrderedRing R] in
/-- Additivity of `varBetween` over a middle point: the trivial consequence of
    `varBetween = varAt a - varAt b`. -/
lemma varBetween_split (P : List R[X]) (a c b : ExtendedPoint R) :
    varBetween P a c + varBetween P c b = varBetween P a b := by
  unfold varBetween; ring

omit [IsStrictOrderedRing R] in
/-- Additivity of `numRoots` over a middle point `c ∈ [a, b]`. Uses the
    partition of the half-open interval `(a, b]` into `(a, c] ⊔ (c, b]`. -/
lemma numRoots_split (P : R[X]) {a c b : R} (hac : a ≤ c) (hcb : c ≤ b) :
    numRoots P (.finite a) (.finite b) =
      numRoots P (.finite a) (.finite c) +
      numRoots P (.finite c) (.finite b) := by
  classical
  simp only [numRoots_finite_finite]
  rw [← Multiset.card_add]
  congr 1
  conv_lhs => rw [← Multiset.filter_add_not (fun r : R => r ≤ c)
    (P.roots.filter (fun r => a < r ∧ r ≤ b))]
  congr 1
  · rw [Multiset.filter_filter]
    congr 1
    funext r
    exact propext
      ⟨fun ⟨h0, h1, _⟩ => ⟨h1, h0⟩,
       fun ⟨h1, h2⟩ => ⟨h2, h1, le_trans h2 hcb⟩⟩
  · rw [Multiset.filter_filter]
    congr 1
    funext r
    simp only [not_le]
    exact propext
      ⟨fun ⟨h0, _, h2⟩ => ⟨h0, h2⟩,
       fun ⟨h0, h2⟩ => ⟨h0, lt_of_le_of_lt hac h0, h2⟩⟩

omit [IsStrictOrderedRing R] in
/-- When `(d, c)` has no root of `P` and `d < c`, `numRoots P (d, c]` is just
    the multiplicity of `c` as a root (0 if `c` is not a root). -/
lemma numRoots_Ioc_of_no_root {P : R[X]} (hP : P ≠ 0) {d c : R} (hdc : d < c)
    (hno : ∀ x ∈ Set.Ioo d c, P.eval x ≠ 0) :
    numRoots P (.finite d) (.finite c) = P.rootMultiplicity c := by
  classical
  simp only [numRoots_finite_finite]
  have hmult : P.rootMultiplicity c = P.roots.count c :=
    (Polynomial.count_roots P).symm
  rw [hmult]
  have hfilter : P.roots.filter (fun r => d < r ∧ r ≤ c) =
      P.roots.filter (fun r => r = c) := by
    apply Multiset.filter_congr
    intro r hr
    constructor
    · rintro ⟨hd_lt, hr_le⟩
      rcases lt_or_eq_of_le hr_le with hlt | heq
      · exfalso
        have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
        exact hno r ⟨hd_lt, hlt⟩ hPr
      · exact heq
    · rintro rfl
      exact ⟨hdc, le_refl r⟩
  rw [hfilter, Multiset.filter_eq', Multiset.card_replicate]

/-- Absent all `P^{(k)}` roots in `(c, b]`, the right-side half `varBetween
    (der P); c, b` vanishes and `numRoots P (c, b] = 0`. Used for the
    rightmost piece in Budan-Fourier. -/
lemma varBetween_and_numRoots_eq_zero_of_no_root_Ioc
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0)
    {c b : R} (hcb : c < b)
    (hno : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc c b,
      ((⇑derivative)^[k] P).eval x ≠ 0) :
    varBetween (der P) (.finite c) (.finite b) = 0 ∧
    numRoots P (.finite c) (.finite b) = 0 := by
  refine ⟨lemma_2_36_right hIVP P hP hcb hno, ?_⟩
  classical
  simp only [numRoots_finite_finite]
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro r hr ⟨hcr, hrb⟩
  have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
  have hne := hno 0 (Nat.zero_le _) r ⟨hcr, hrb⟩
  simp at hne
  exact hne hPr

/-! ### Membership structure: `critPointsIoc` restricted to sub-intervals -/

omit [IsStrictOrderedRing R] in
/-- If the larger interval has empty `critPointsIoc`, so does the smaller. -/
lemma critPointsIoc_subset_of_Ioc_subset
    {P : R[X]} {a b a' b' : R} (ha : a ≤ a') (hb : b' ≤ b) :
    critPointsIoc P a' b' ⊆ critPointsIoc P a b := by
  classical
  intro r hr
  simp only [critPointsIoc, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_range] at hr ⊢
  obtain ⟨k, hk, hrk, hab'⟩ := hr
  exact ⟨k, hk, hrk, ⟨lt_of_le_of_lt ha hab'.1, le_trans hab'.2 hb⟩⟩

/-- If `critPointsIoc P a b = ∅` then no iterated derivative has a root in
    `(a, b]`. Used for the base case of Budan-Fourier. -/
lemma no_iter_deriv_root_of_critPointsIoc_empty
    {P : R[X]} (hP : P ≠ 0) {a b : R}
    (h : critPointsIoc P a b = ∅) :
    ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc a b, ((⇑derivative)^[k] P).eval x ≠ 0 := by
  intro k hk x hx hzero
  have hmem : x ∈ critPointsIoc P a b := (mem_critPointsIoc_iff hP).mpr
    ⟨⟨hx.1, hx.2⟩, k, hk, hzero⟩
  rw [h] at hmem
  exact Finset.notMem_empty _ hmem

/-- If `c = max (critPointsIoc P a b)`, then `(c, b]` contains no iterated
    derivative root. -/
lemma no_iter_deriv_root_Ioc_of_max_critPointsIoc
    {P : R[X]} (hP : P ≠ 0) {a b c : R}
    (hc : c ∈ critPointsIoc P a b)
    (hmax : ∀ r ∈ critPointsIoc P a b, r ≤ c) :
    ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc c b, ((⇑derivative)^[k] P).eval x ≠ 0 := by
  have hac : a < c ∧ c ≤ b := ((mem_critPointsIoc_iff hP).mp hc).1
  intro k hk x hx hzero
  have hmem : x ∈ critPointsIoc P a b := (mem_critPointsIoc_iff hP).mpr
    ⟨⟨lt_trans hac.1 hx.1, hx.2⟩, k, hk, hzero⟩
  exact absurd hx.1 (not_lt.mpr (hmax x hmem))

/-- Strict card decrease: if `c ∈ critPointsIoc P a b` and `d < c`, then
    `critPointsIoc P a d` has strictly fewer elements. -/
lemma critPointsIoc_card_lt_of_lt_max
    {P : R[X]} (hP : P ≠ 0) {a b d c : R} (hcb : c ≤ b) (hdc : d < c)
    (hc : c ∈ critPointsIoc P a b) :
    (critPointsIoc P a d).card < (critPointsIoc P a b).card := by
  apply Finset.card_lt_card
  refine ⟨critPointsIoc_subset_of_Ioc_subset (le_refl a) (le_trans (le_of_lt hdc) hcb), ?_⟩
  intro hsub
  have hcd : c ∈ critPointsIoc P a d := hsub hc
  have : c ≤ d := ((mem_critPointsIoc_iff hP).mp hcd).1.2
  exact absurd hdc (not_lt.mpr this)

/-! ### Main Budan-Fourier theorem (finite-endpoint case) -/

private theorem budan_fourier_finite_aux
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) :
    ∀ (N : ℕ) {a b : R}, a < b → (critPointsIoc P a b).card ≤ N →
      ((numRoots P (.finite a) (.finite b) : ℤ) ≤
        varBetween (der P) (.finite a) (.finite b)) ∧
      Even (varBetween (der P) (.finite a) (.finite b) -
        (numRoots P (.finite a) (.finite b) : ℤ)) := by
  intro N
  induction N with
  | zero =>
    intro a b hab hle
    rw [Nat.le_zero, Finset.card_eq_zero] at hle
    obtain ⟨hvar, hnum⟩ := varBetween_and_numRoots_eq_zero_of_no_root_Ioc
      hIVP hP hab (no_iter_deriv_root_of_critPointsIoc_empty hP hle)
    refine ⟨?_, ?_⟩
    · rw [hvar, hnum]; simp
    · rw [hvar, hnum]; simp
  | succ N ih =>
    intro a b hab hle
    by_cases hcard_zero : (critPointsIoc P a b).card = 0
    · rw [Finset.card_eq_zero] at hcard_zero
      obtain ⟨hvar, hnum⟩ := varBetween_and_numRoots_eq_zero_of_no_root_Ioc
        hIVP hP hab (no_iter_deriv_root_of_critPointsIoc_empty hP hcard_zero)
      refine ⟨?_, ?_⟩
      · rw [hvar, hnum]; simp
      · rw [hvar, hnum]; simp
    -- Nonempty case: pick c = max of critPointsIoc
    have hne : (critPointsIoc P a b).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_zero)
    set c := (critPointsIoc P a b).max' hne with hc_def
    have hc_mem : c ∈ critPointsIoc P a b := Finset.max'_mem _ _
    have hc_max : ∀ r ∈ critPointsIoc P a b, r ≤ c :=
      fun r hr => Finset.le_max' _ r hr
    have hac : a < c ∧ c ≤ b := ((mem_critPointsIoc_iff hP).mp hc_mem).1
    -- (c, b] has no iter. deriv. root
    have hnoCb : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ioc c b,
        ((⇑derivative)^[k] P).eval x ≠ 0 :=
      no_iter_deriv_root_Ioc_of_max_critPointsIoc hP hc_mem hc_max
    -- Find e: upper bound for non-c critical points
    set S' := (critPointsIoc P a b).erase c with hS'_def
    have ⟨e, hae, hec, heS⟩ : ∃ e : R, a ≤ e ∧ e < c ∧
        ∀ r ∈ critPointsIoc P a b, r ≠ c → r ≤ e := by
      by_cases hS'ne : S'.Nonempty
      · refine ⟨S'.max' hS'ne, ?_, ?_, ?_⟩
        · have hmem_S' : S'.max' hS'ne ∈ S' := Finset.max'_mem _ _
          have : S'.max' hS'ne ∈ critPointsIoc P a b :=
            Finset.mem_of_mem_erase hmem_S'
          exact le_of_lt ((mem_critPointsIoc_iff hP).mp this).1.1
        · have hmem_S' : S'.max' hS'ne ∈ S' := Finset.max'_mem _ _
          have hne_c : S'.max' hS'ne ≠ c := (Finset.mem_erase.mp hmem_S').1
          have hmem : S'.max' hS'ne ∈ critPointsIoc P a b :=
            Finset.mem_of_mem_erase hmem_S'
          exact lt_of_le_of_ne (hc_max _ hmem) hne_c
        · intro r hr hrc
          exact Finset.le_max' _ _ (Finset.mem_erase.mpr ⟨hrc, hr⟩)
      · refine ⟨a, le_refl _, hac.1, ?_⟩
        intro r hr hrc
        exfalso
        exact hS'ne ⟨r, Finset.mem_erase.mpr ⟨hrc, hr⟩⟩
    -- Get buffer from exists_no_root_Ioo_left_forall_der
    obtain ⟨d₀, hd₀c, hd₀⟩ := exists_no_root_Ioo_left_forall_der hP c
    -- Pick d ∈ (max e d₀, c)
    obtain ⟨d, hed, hdc⟩ : ∃ d, max e d₀ < d ∧ d < c :=
      exists_between (max_lt hec hd₀c)
    have hed' : e < d := lt_of_le_of_lt (le_max_left _ _) hed
    have hd₀d : d₀ < d := lt_of_le_of_lt (le_max_right _ _) hed
    have had : a < d := lt_of_le_of_lt hae hed'
    have hdb : d ≤ b := le_trans (le_of_lt hdc) hac.2
    -- [d, c) root-free for all iter. derivs
    have hnoDc : ∀ k ≤ P.natDegree, ∀ x ∈ Set.Ico d c,
        ((⇑derivative)^[k] P).eval x ≠ 0 := by
      intro k hk x hx
      exact hd₀ x ⟨lt_of_lt_of_le hd₀d hx.1, hx.2⟩ k hk
    -- (d, c) root-free for P (special case k = 0)
    have hnoDc_P : ∀ x ∈ Set.Ioo d c, P.eval x ≠ 0 := by
      intro x hx hzero
      have := hnoDc 0 (Nat.zero_le _) x ⟨le_of_lt hx.1, hx.2⟩
      simp at this
      exact this hzero
    -- critPointsIoc P a d has smaller card
    have hcard_ad : (critPointsIoc P a d).card < (critPointsIoc P a b).card :=
      critPointsIoc_card_lt_of_lt_max hP hac.2 hdc hc_mem
    have hcard_ad_le : (critPointsIoc P a d).card ≤ N :=
      Nat.le_of_lt_succ (lt_of_lt_of_le hcard_ad hle)
    -- Apply IH to (a, d]
    obtain ⟨h_ad_ineq, h_ad_even⟩ := ih had hcard_ad_le
    -- Apply lemma_2_36_left at c
    obtain ⟨h_dc_ineq, h_dc_even⟩ := lemma_2_36_left hIVP P hP hdc hnoDc
    -- numRoots P (d, c] = rootMultiplicity c P
    have h_numDc : numRoots P (.finite d) (.finite c) = P.rootMultiplicity c :=
      numRoots_Ioc_of_no_root hP hdc hnoDc_P
    -- Split (a, b] at c and then at d
    have hsplit_num : numRoots P (.finite a) (.finite b) =
        numRoots P (.finite a) (.finite d) +
        numRoots P (.finite d) (.finite c) +
        numRoots P (.finite c) (.finite b) := by
      rw [numRoots_split P (le_of_lt had) hdb,
          numRoots_split P (le_of_lt hdc) hac.2, ← add_assoc]
    have hsplit_var : varBetween (der P) (.finite a) (.finite b) =
        varBetween (der P) (.finite a) (.finite d) +
        varBetween (der P) (.finite d) (.finite c) +
        varBetween (der P) (.finite c) (.finite b) := by
      rw [← varBetween_split (der P) (.finite a) (.finite c) (.finite b),
          ← varBetween_split (der P) (.finite a) (.finite d) (.finite c)]
    -- Case on c = b vs c < b to handle (c, b]
    rcases lt_or_eq_of_le hac.2 with hcb | hcb
    · -- c < b: use varBetween_and_numRoots_eq_zero_of_no_root_Ioc
      obtain ⟨h_cb_var, h_cb_num⟩ :=
        varBetween_and_numRoots_eq_zero_of_no_root_Ioc hIVP hP hcb hnoCb
      rw [hsplit_num, hsplit_var, h_cb_var, h_cb_num, h_numDc]
      push_cast
      refine ⟨?_, ?_⟩
      · linarith
      · have heven : Even ((varBetween (der P) (.finite a) (.finite d) -
              (numRoots P (.finite a) (.finite d) : ℤ)) +
            (varBetween (der P) (.finite d) (.finite c) -
              (P.rootMultiplicity c : ℤ))) := h_ad_even.add h_dc_even
        convert heven using 1
        ring
    · -- c = b: (c, b] is empty
      have h_cb_var : varBetween (der P) (.finite c) (.finite b) = 0 := by
        rw [hcb]; unfold varBetween; ring
      have h_cb_num : numRoots P (.finite c) (.finite b) = 0 := by
        rw [hcb]
        simp only [numRoots_finite_finite]
        rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
        rintro r _ ⟨h1, h2⟩
        exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
      rw [hsplit_num, hsplit_var, h_cb_var, h_cb_num, h_numDc]
      push_cast
      refine ⟨?_, ?_⟩
      · linarith
      · have heven : Even ((varBetween (der P) (.finite a) (.finite d) -
              (numRoots P (.finite a) (.finite d) : ℤ)) +
            (varBetween (der P) (.finite d) (.finite c) -
              (P.rootMultiplicity c : ℤ))) := h_ad_even.add h_dc_even
        convert heven using 1
        ring

/-- **BPR Theorem 2.35 (Budan-Fourier, finite-endpoint case).** For any nonzero
    `P ∈ R[X]` and `a < b`, the number of sign variations of `Der(P)` on `(a, b]`
    bounds the number of roots of `P` on `(a, b]` (counted with multiplicity),
    and the difference `Var(Der(P); a, b) − num(P; (a, b])` is even. -/
theorem budan_fourier_finite (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {a b : R} (hab : a < b) :
    ((numRoots P (.finite a) (.finite b) : ℤ) ≤
      varBetween (der P) (.finite a) (.finite b)) ∧
    Even (varBetween (der P) (.finite a) (.finite b) -
      (numRoots P (.finite a) (.finite b) : ℤ)) :=
  budan_fourier_finite_aux hIVP hP _ hab (le_refl _)

/-! ### Reduction to the finite case for `±∞` endpoints

For `|x|` large, Proposition 2.4 (via `hasSignAtPosInfty_leadingCoeff`) says
`sign((⇑derivative)^[k] P .eval x) = sign((⇑derivative)^[k] P).leadingCoeff`.
Taking the max over `k ≤ natDegree P` of the bounds gives a single `B` at which
all iterated derivatives' signs stabilize. For such `B`:
  * `varAt (der P) (finite B) = varAt (der P) posInf` (by `Var_congr_sign`).
  * No root of `P` lies beyond `B` (since `P(x) ≠ 0` for `x > B`), so
    `numRoots P (finite a) (finite B) = numRoots P (finite a) posInf`.

The `±∞` cases then follow from `budan_fourier_finite`. -/

/-- There exists a bound `B` such that for every `x > B` and every `k ≤ natDegree P`,
    the sign of `(derivative)^[k] P` at `x` matches the sign of its leading
    coefficient. -/
private lemma exists_bound_pos_iterate_signs (P : R[X]) :
    ∃ B, ∀ k ≤ P.natDegree, ∀ x, B < x →
      SignType.sign (((⇑derivative)^[k] P).eval x) =
        SignType.sign ((⇑derivative)^[k] P).leadingCoeff := by
  classical
  choose M hM using (fun k : Fin (P.natDegree + 1) =>
    hasSignAtPosInfty_leadingCoeff ((⇑derivative)^[k.val] P))
  set S : Finset R := Finset.image M Finset.univ
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨S.max' hS, fun k hk x hx => ?_⟩
  have hM_mem : M ⟨k, Nat.lt_succ_of_le hk⟩ ∈ S :=
    Finset.mem_image.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, Finset.mem_univ _, rfl⟩
  have hM_le : M ⟨k, Nat.lt_succ_of_le hk⟩ ≤ S.max' hS :=
    Finset.le_max' _ _ hM_mem
  exact hM ⟨k, Nat.lt_succ_of_le hk⟩ x (lt_of_le_of_lt hM_le hx)

/-- Symmetric bound at `−∞`: for every `x < B` and every `k ≤ natDegree P`,
    `sign((derivative)^[k] P .eval x) = (-1)^natDegree · sign(leadingCoeff)`. -/
private lemma exists_bound_neg_iterate_signs (P : R[X]) :
    ∃ B, ∀ k ≤ P.natDegree, ∀ x, x < B →
      SignType.sign (((⇑derivative)^[k] P).eval x) =
        (-1) ^ ((⇑derivative)^[k] P).natDegree *
          SignType.sign ((⇑derivative)^[k] P).leadingCoeff := by
  classical
  choose M hM using (fun k : Fin (P.natDegree + 1) =>
    hasSignAtNegInfty_leadingCoeff ((⇑derivative)^[k.val] P))
  set S : Finset R := Finset.image M Finset.univ
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨S.min' hS, fun k hk x hx => ?_⟩
  have hM_mem : M ⟨k, Nat.lt_succ_of_le hk⟩ ∈ S :=
    Finset.mem_image.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, Finset.mem_univ _, rfl⟩
  have hM_ge : S.min' hS ≤ M ⟨k, Nat.lt_succ_of_le hk⟩ :=
    Finset.min'_le _ _ hM_mem
  exact hM ⟨k, Nat.lt_succ_of_le hk⟩ x (lt_of_lt_of_le hx hM_ge)

/-- If `B` stabilizes the signs of all iterated derivatives, then
    `varAt (der P) (finite B) = varAt (der P) posInf`. -/
private lemma varAt_finite_eq_posInf_of_signs_stable
    {P : R[X]} {B : R}
    (h : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B) =
        SignType.sign ((⇑derivative)^[k] P).leadingCoeff) :
    varAt (der P) (.finite B) = varAt (der P) ExtendedPoint.posInf := by
  rw [varAt_finite, varAt_posInf]
  apply Var_congr_sign
  unfold der
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp_apply]
  exact h i (Nat.lt_succ_iff.mp hi)

/-- Symmetric: if `B` stabilizes signs at `−∞`, then
    `varAt (der P) (finite B) = varAt (der P) negInf`. -/
private lemma varAt_finite_eq_negInf_of_signs_stable
    {P : R[X]} {B : R}
    (h : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B) =
        (-1) ^ ((⇑derivative)^[k] P).natDegree *
          SignType.sign ((⇑derivative)^[k] P).leadingCoeff) :
    varAt (der P) (.finite B) = varAt (der P) ExtendedPoint.negInf := by
  rw [varAt_finite, varAt_negInf]
  apply Var_congr_sign
  unfold der
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp hi
  have hsign_mul :
      SignType.sign ((-1 : R) ^ ((⇑derivative)^[i] P).natDegree *
        ((⇑derivative)^[i] P).leadingCoeff) =
      (-1) ^ ((⇑derivative)^[i] P).natDegree *
        SignType.sign ((⇑derivative)^[i] P).leadingCoeff := by
    rw [sign_mul]
    congr 1
    rcases Nat.even_or_odd ((⇑derivative)^[i] P).natDegree with hev | hod
    · rw [hev.neg_one_pow, hev.neg_one_pow, sign_one]
    · rw [hod.neg_one_pow, hod.neg_one_pow]
      exact _root_.sign_neg neg_one_lt_zero
  simp only [Function.comp_apply]
  rw [h i hi', hsign_mul]

omit [IsStrictOrderedRing R] in
/-- If every root of `P` is `≤ B`, then
    `numRoots P (finite a) (finite B) = numRoots P (finite a) posInf`. -/
private lemma numRoots_finite_eq_posInf_of_roots_bdd [IsDomain R]
    {P : R[X]} {a B : R} (hB : ∀ r ∈ P.roots, r ≤ B) :
    numRoots P (.finite a) (.finite B) = numRoots P (.finite a) .posInf := by
  classical
  show (P.roots.filter (fun r => a < r ∧ r ≤ B)).card =
    (P.roots.filter (a < ·)).card
  congr 1
  apply Multiset.filter_congr
  intro r hr
  exact ⟨fun h => h.1, fun h => ⟨h, hB r hr⟩⟩

omit [IsStrictOrderedRing R] in
/-- If every root of `P` is strictly `> B`, then
    `numRoots P (finite B) (finite b) = numRoots P negInf (finite b)`. -/
private lemma numRoots_finite_eq_negInf_of_roots_bdd [IsDomain R]
    {P : R[X]} {B b : R} (hB : ∀ r ∈ P.roots, B < r) :
    numRoots P (.finite B) (.finite b) = numRoots P .negInf (.finite b) := by
  classical
  show (P.roots.filter (fun r => B < r ∧ r ≤ b)).card =
    (P.roots.filter (· ≤ b)).card
  congr 1
  apply Multiset.filter_congr
  intro r hr
  exact ⟨fun h => h.2, fun h => ⟨hB r hr, h⟩⟩

omit [IsStrictOrderedRing R] in
/-- Symmetric versions for the `negInf, posInf` case. -/
private lemma numRoots_finite_finite_eq_negInf_posInf [IsDomain R]
    {P : R[X]} {B₁ B₂ : R} (hB₁ : ∀ r ∈ P.roots, B₁ < r)
    (hB₂ : ∀ r ∈ P.roots, r ≤ B₂) :
    numRoots P (.finite B₁) (.finite B₂) = numRoots P .negInf .posInf := by
  classical
  show (P.roots.filter (fun r => B₁ < r ∧ r ≤ B₂)).card = P.roots.card
  congr 1
  rw [Multiset.filter_eq_self]
  exact fun r hr => ⟨hB₁ r hr, hB₂ r hr⟩

/-- A witness `B > a` giving a finite endpoint that matches `posInf` for both
    `varBetween` and `numRoots`. -/
private lemma exists_finite_eq_posInf
    {P : R[X]} (hP : P ≠ 0) (a : R) :
    ∃ B, a < B ∧
      varAt (der P) (.finite B) = varAt (der P) .posInf ∧
      numRoots P (.finite a) (.finite B) = numRoots P (.finite a) .posInf := by
  obtain ⟨M, hM⟩ := exists_bound_pos_iterate_signs P
  -- Pick B strictly larger than both `a` and `M`.
  set B := max a M + 1 with hB_def
  have hMB : M < B := by rw [hB_def]; linarith [le_max_right a M]
  have haB : a < B := by rw [hB_def]; linarith [le_max_left a M]
  have hsign_at_B : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B) =
        SignType.sign ((⇑derivative)^[k] P).leadingCoeff :=
    fun k hk => hM k hk B hMB
  have hP_lc : P.leadingCoeff ≠ 0 := fun h => hP (Polynomial.leadingCoeff_eq_zero.mp h)
  have hroots_bd : ∀ r ∈ P.roots, r ≤ B := by
    intro r hr
    by_contra hrB
    push Not at hrB
    have hMr : M < r := lt_trans hMB hrB
    have hsign := hM 0 (Nat.zero_le _) r hMr
    simp only [Function.iterate_zero_apply] at hsign
    have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
    rw [hPr, _root_.sign_zero] at hsign
    have : SignType.sign P.leadingCoeff = 0 := hsign.symm
    rw [sign_eq_zero_iff] at this
    exact hP_lc this
  exact ⟨B, haB,
    varAt_finite_eq_posInf_of_signs_stable hsign_at_B,
    numRoots_finite_eq_posInf_of_roots_bdd hroots_bd⟩

/-- A witness `B < b` giving a finite endpoint that matches `negInf`. -/
private lemma exists_finite_eq_negInf
    {P : R[X]} (hP : P ≠ 0) (b : R) :
    ∃ B, B < b ∧
      varAt (der P) (.finite B) = varAt (der P) .negInf ∧
      numRoots P (.finite B) (.finite b) = numRoots P .negInf (.finite b) := by
  obtain ⟨M, hM⟩ := exists_bound_neg_iterate_signs P
  set B := min b M - 1 with hB_def
  have hBM : B < M := by rw [hB_def]; linarith [min_le_right b M]
  have hBb : B < b := by rw [hB_def]; linarith [min_le_left b M]
  have hsign_at_B : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B) =
        (-1) ^ ((⇑derivative)^[k] P).natDegree *
          SignType.sign ((⇑derivative)^[k] P).leadingCoeff :=
    fun k hk => hM k hk B hBM
  have hP_lc : P.leadingCoeff ≠ 0 := fun h => hP (Polynomial.leadingCoeff_eq_zero.mp h)
  have hroots_bd : ∀ r ∈ P.roots, B < r := by
    intro r hr
    by_contra hrB
    push Not at hrB
    have hrM : r < M := lt_of_le_of_lt hrB hBM
    have hsign := hM 0 (Nat.zero_le _) r hrM
    simp only [Function.iterate_zero_apply] at hsign
    have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
    rw [hPr, _root_.sign_zero] at hsign
    have hsign_lc_ne : SignType.sign P.leadingCoeff ≠ 0 := by
      rwa [ne_eq, sign_eq_zero_iff]
    have hpow_ne : ((-1 : SignType)) ^ P.natDegree ≠ 0 := by
      rcases Nat.even_or_odd P.natDegree with hev | hod
      · rw [hev.neg_one_pow]; decide
      · rw [hod.neg_one_pow]; decide
    exact mul_ne_zero hpow_ne hsign_lc_ne hsign.symm
  exact ⟨B, hBb,
    varAt_finite_eq_negInf_of_signs_stable hsign_at_B,
    numRoots_finite_eq_negInf_of_roots_bdd hroots_bd⟩

/-- **BPR Theorem 2.35 (Budan-Fourier), `(a, +∞)` case.** -/
theorem budan_fourier_posInf (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (a : R) :
    ((numRoots P (.finite a) .posInf : ℤ) ≤
      varBetween (der P) (.finite a) .posInf) ∧
    Even (varBetween (der P) (.finite a) .posInf -
      (numRoots P (.finite a) .posInf : ℤ)) := by
  obtain ⟨B, haB, hvar, hnum⟩ := exists_finite_eq_posInf hP a
  have hfin := budan_fourier_finite hIVP hP haB
  have hvar_eq : varBetween (der P) (.finite a) .posInf =
      varBetween (der P) (.finite a) (.finite B) := by
    unfold varBetween; rw [hvar]
  rw [hvar_eq, ← hnum]
  exact hfin

/-- **BPR Theorem 2.35 (Budan-Fourier), `(−∞, b]` case.** -/
theorem budan_fourier_negInf (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (b : R) :
    ((numRoots P .negInf (.finite b) : ℤ) ≤
      varBetween (der P) .negInf (.finite b)) ∧
    Even (varBetween (der P) .negInf (.finite b) -
      (numRoots P .negInf (.finite b) : ℤ)) := by
  obtain ⟨B, hBb, hvar, hnum⟩ := exists_finite_eq_negInf hP b
  have hfin := budan_fourier_finite hIVP hP hBb
  have hvar_eq : varBetween (der P) .negInf (.finite b) =
      varBetween (der P) (.finite B) (.finite b) := by
    unfold varBetween; rw [hvar]
  rw [hvar_eq, ← hnum]
  exact hfin

/-- **BPR Theorem 2.35 (Budan-Fourier), `(−∞, +∞)` case.** -/
theorem budan_fourier_negInf_posInf (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) :
    ((numRoots P .negInf .posInf : ℤ) ≤ varBetween (der P) .negInf .posInf) ∧
    Even (varBetween (der P) .negInf .posInf -
      (numRoots P .negInf .posInf : ℤ)) := by
  obtain ⟨Mp, hMp⟩ := exists_bound_pos_iterate_signs P
  obtain ⟨Mn, hMn⟩ := exists_bound_neg_iterate_signs P
  set B₂ := max Mp (Mn + 1) + 1 with hB₂_def
  set B₁ := min Mn (Mp - 1) - 1 with hB₁_def
  have hMpB₂ : Mp < B₂ := by rw [hB₂_def]; linarith [le_max_left Mp (Mn + 1)]
  have hB₁Mn : B₁ < Mn := by rw [hB₁_def]; linarith [min_le_left Mn (Mp - 1)]
  have hB₁_lt_B₂ : B₁ < B₂ := by
    have h1 : B₁ < Mp := by
      rw [hB₁_def]; linarith [min_le_right Mn (Mp - 1)]
    have h2 : Mn < B₂ := by
      rw [hB₂_def]; linarith [le_max_right Mp (Mn + 1)]
    -- Either pathway works; we just need B₁ < B₂. Use B₁ < Mp ≤ B₂.
    linarith
  -- Sign stabilization at B₂ (posInf side).
  have hsign_at_B₂ : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B₂) =
        SignType.sign ((⇑derivative)^[k] P).leadingCoeff :=
    fun k hk => hMp k hk B₂ hMpB₂
  -- Sign stabilization at B₁ (negInf side).
  have hsign_at_B₁ : ∀ k ≤ P.natDegree,
      SignType.sign (((⇑derivative)^[k] P).eval B₁) =
        (-1) ^ ((⇑derivative)^[k] P).natDegree *
          SignType.sign ((⇑derivative)^[k] P).leadingCoeff :=
    fun k hk => hMn k hk B₁ hB₁Mn
  have hP_lc : P.leadingCoeff ≠ 0 := fun h => hP (Polynomial.leadingCoeff_eq_zero.mp h)
  -- All roots ≤ B₂.
  have hroots_bd₂ : ∀ r ∈ P.roots, r ≤ B₂ := by
    intro r hr
    by_contra hrB
    push Not at hrB
    have hMr : Mp < r := lt_trans hMpB₂ hrB
    have hsign := hMp 0 (Nat.zero_le _) r hMr
    simp only [Function.iterate_zero_apply] at hsign
    have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
    rw [hPr, _root_.sign_zero] at hsign
    have : SignType.sign P.leadingCoeff = 0 := hsign.symm
    rw [sign_eq_zero_iff] at this
    exact hP_lc this
  -- All roots > B₁.
  have hroots_bd₁ : ∀ r ∈ P.roots, B₁ < r := by
    intro r hr
    by_contra hrB
    push Not at hrB
    have hrM : r < Mn := lt_of_le_of_lt hrB hB₁Mn
    have hsign := hMn 0 (Nat.zero_le _) r hrM
    simp only [Function.iterate_zero_apply] at hsign
    have hPr : P.eval r = 0 := (Polynomial.mem_roots hP).mp hr
    rw [hPr, _root_.sign_zero] at hsign
    have hsign_lc_ne : SignType.sign P.leadingCoeff ≠ 0 := by
      rwa [ne_eq, sign_eq_zero_iff]
    have hpow_ne : ((-1 : SignType)) ^ P.natDegree ≠ 0 := by
      rcases Nat.even_or_odd P.natDegree with hev | hod
      · rw [hev.neg_one_pow]; decide
      · rw [hod.neg_one_pow]; decide
    exact mul_ne_zero hpow_ne hsign_lc_ne hsign.symm
  have hvar_B₂ : varAt (der P) (.finite B₂) = varAt (der P) .posInf :=
    varAt_finite_eq_posInf_of_signs_stable hsign_at_B₂
  have hvar_B₁ : varAt (der P) (.finite B₁) = varAt (der P) .negInf :=
    varAt_finite_eq_negInf_of_signs_stable hsign_at_B₁
  have hnum_eq : numRoots P (.finite B₁) (.finite B₂) = numRoots P .negInf .posInf :=
    numRoots_finite_finite_eq_negInf_posInf hroots_bd₁ hroots_bd₂
  have hfin := budan_fourier_finite hIVP hP hB₁_lt_B₂
  have hvar_eq : varBetween (der P) .negInf .posInf =
      varBetween (der P) (.finite B₁) (.finite B₂) := by
    unfold varBetween; rw [hvar_B₁, hvar_B₂]
  rw [hvar_eq, ← hnum_eq]
  exact hfin

/-! ### BPR Example 2.37

The polynomial `P = X² − X + 1` has no real root (its discriminant `−3` is
negative), but `Var(Der(P); 0, 1) = 2`:
  * `Der(P) = [X² − X + 1, 2X − 1, 2]`.
  * Evaluating at `0` gives `[1, −1, 2]` with two sign changes.
  * Evaluating at `1` gives `[1, 1, 2]` with no sign change.
  * Hence `Var(Der(P); 0, 1) = 2 − 0 = 2`.

It is impossible to refine `(0, 1]` into `(0, a]` and `(a, 1]` with each
piece contributing one sign variation, since otherwise Budan–Fourier would
force `P` to have two real roots in `(0, 1]`. Any sub-interval containing
`1/2` (where `P` attains its minimum) necessarily contributes `2` sign
variations. This shows that the bound in Budan–Fourier is tight in the
sense of parity — here both sides have the same parity `2 ≡ 0 (mod 2)` —
but is not tight as an equality.

We record `Der(P)` as the explicit list `[X² − X + 1, 2X − 1, 2]` (bypassing
the `der` computation that would require unfolding iterated derivatives). -/

example :
    varAt ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X]) (.finite 0) = 2 := by
  simp [varAt_finite, Var]; norm_num [varNonzero]

example :
    varAt ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X]) (.finite 1) = 0 := by
  simp [varAt_finite, Var]; norm_num [varNonzero]

example :
    varBetween ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X])
      (.finite 0) (.finite 1) = 2 := by
  have h0 : varAt ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X]) (.finite 0) = 2 := by
    simp [varAt_finite, Var]; norm_num [varNonzero]
  have h1 : varAt ([X ^ 2 - X + 1, 2 * X - 1, C 2] : List ℚ[X]) (.finite 1) = 0 := by
    simp [varAt_finite, Var]; norm_num [varNonzero]
  unfold varBetween
  rw [h0, h1]
  rfl

/-! ### Refinement impossibility

BPR Example 2.37 continues: "It is impossible to find `a ∈ (0, 1]` such
that `Var(Der(P); 0, a] = 1` and `Var(Der(P); a, 1] = 1`, since otherwise
`P` would have two real roots." We formalise this as a theorem over any
real-closed-style field `R` with the intermediate-value property.

The argument is: if both sub-intervals contributed exactly one variation,
Budan-Fourier would force `numRoots ≥ 1` on each (since `Var − numRoots`
is even and nonneg). Summed, `numRoots` on `(0, 1]` would be `≥ 2`. But
`X² − X + 1` has no real root at all: `4 (X² − X + 1) = (2X − 1)² + 3 ≥ 3`. -/

/-- `P := X² − X + 1` is strictly positive on `R` for any
    `IsStrictOrderedRing R`: `4·P(x) = (2x − 1)² + 3 ≥ 3 > 0`. -/
private lemma example_2_37_positive (x : R) :
    0 < ((X : R[X]) ^ 2 - X + 1).eval x := by
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  nlinarith [sq_nonneg (2 * x - 1)]

/-- `P := X² − X + 1` is nonzero in `R[X]` (evaluation at `0` is `1`). -/
private lemma example_2_37_ne_zero : ((X : R[X]) ^ 2 - X + 1) ≠ 0 := fun h => by
  have h0 := example_2_37_positive (0 : R)
  rw [h] at h0; simp at h0

/-- `P := X² − X + 1` has no real root: `P.roots = 0` as a multiset. -/
private lemma example_2_37_roots_empty :
    ((X : R[X]) ^ 2 - X + 1).roots = 0 := by
  classical
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  exact ne_of_gt (example_2_37_positive r)
    ((Polynomial.mem_roots example_2_37_ne_zero).mp hr)

/-- **BPR Example 2.37 (refinement impossibility).** For `P = X² − X + 1`,
    there is no `a ∈ (0, 1]` such that each of the sub-intervals `(0, a]`
    and `(a, 1]` contributes exactly one sign variation to
    `Var(Der(P); ·, ·)`.

    If both `Var(Der(P); 0, a] = 1` and `Var(Der(P); a, 1] = 1`, then by
    Budan-Fourier each sub-interval would contain at least one real root of
    `P`, giving at least two roots in `(0, 1]`.  But `X² − X + 1` has no
    real root, since `4 (X² − X + 1) = (2X − 1)² + 3 ≥ 3 > 0`. -/
theorem example_2_37_no_refinement
    (hIVP : HasIntermediateValueProperty R) {a : R} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ¬ (varBetween (der ((X : R[X]) ^ 2 - X + 1)) (.finite 0) (.finite a) = 1 ∧
       varBetween (der ((X : R[X]) ^ 2 - X + 1)) (.finite a) (.finite 1) = 1) := by
  rintro ⟨hV0a, hVa1⟩
  set P : R[X] := X ^ 2 - X + 1
  have hP_ne : P ≠ 0 := example_2_37_ne_zero
  have hroots : P.roots = 0 := example_2_37_roots_empty
  have h_num_zero : ∀ c d : R, numRoots P (.finite c) (.finite d) = 0 := by
    intro c d
    rw [numRoots_finite_finite, hroots]
    simp
  rcases lt_or_eq_of_le ha1 with ha_lt1 | ha_eq1
  · -- Case `a < 1`: apply Budan-Fourier on `(0, a]`.
    have hBF0a := budan_fourier_finite hIVP hP_ne ha0
    rw [hV0a, h_num_zero 0 a] at hBF0a
    exact (by decide : ¬ Even (1 - (0 : ℤ))) hBF0a.2
  · -- Case `a = 1`: `varBetween (.finite 1) (.finite 1) = 0 ≠ 1`.
    subst ha_eq1
    unfold varBetween at hVa1
    simp at hVa1

/-! ## BPR Exercise 2.12

Immediate corollaries of the Budan-Fourier theorem:

- If `Var(Der(P); a, b] = 0`, then `P` has no root in `(a, b]`.
- If `Var(Der(P); a, b] = 1`, then `P` has exactly one root in `(a, b]`,
  and that root is simple (multiplicity `1`).

Both follow from the fact that `num(P; (a, b]) ≤ Var(Der(P); a, b]` with
the difference even and non-negative. -/

/-- **BPR Exercise 2.12 (first part, root-count form).** If
    `Var(Der(P); a, b] = 0`, then `num(P; (a, b]) = 0`. -/
theorem numRoots_eq_zero_of_var_eq_zero
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) {a b : R}
    (hab : a < b) (hV : varBetween (der P) (.finite a) (.finite b) = 0) :
    numRoots P (.finite a) (.finite b) = 0 := by
  have hBF := budan_fourier_finite hIVP hP hab
  rw [hV] at hBF
  have hle : (numRoots P (.finite a) (.finite b) : ℤ) ≤ 0 := hBF.1
  exact_mod_cast le_antisymm hle (Int.natCast_nonneg _)

/-- **BPR Exercise 2.12 (second part, root-count form).** If
    `Var(Der(P); a, b] = 1`, then `num(P; (a, b]) = 1`. -/
theorem numRoots_eq_one_of_var_eq_one
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) {a b : R}
    (hab : a < b) (hV : varBetween (der P) (.finite a) (.finite b) = 1) :
    numRoots P (.finite a) (.finite b) = 1 := by
  have hBF := budan_fourier_finite hIVP hP hab
  rw [hV] at hBF
  obtain ⟨hle, heven⟩ := hBF
  set n : ℕ := numRoots P (.finite a) (.finite b)
  have hle_n : n ≤ 1 := by exact_mod_cast hle
  interval_cases n
  · exact absurd heven (by decide)
  · rfl

/-- **BPR Exercise 2.12 (first part).** If `Var(Der(P); a, b] = 0`, then
    `P` has no root in `(a, b]`. -/
theorem no_root_of_var_eq_zero
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) {a b : R}
    (hab : a < b) (hV : varBetween (der P) (.finite a) (.finite b) = 0) :
    ∀ r ∈ Set.Ioc a b, ¬ P.IsRoot r := by
  classical
  intro r hr hr_root
  have hn := numRoots_eq_zero_of_var_eq_zero hIVP hP hab hV
  rw [numRoots_finite_finite] at hn
  have hfilter_zero : P.roots.filter (fun r => a < r ∧ r ≤ b) = 0 :=
    Multiset.card_eq_zero.mp hn
  have hmem : r ∈ P.roots.filter (fun r => a < r ∧ r ≤ b) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP).mpr hr_root, hr⟩
  rw [hfilter_zero] at hmem
  exact Multiset.notMem_zero r hmem

/-- **BPR Exercise 2.12 (second part).** If `Var(Der(P); a, b] = 1`, then
    `P` has exactly one root in `(a, b]`, and that root is simple
    (i.e. has multiplicity `1`). -/
theorem unique_simple_root_of_var_eq_one
    (hIVP : HasIntermediateValueProperty R) {P : R[X]} (hP : P ≠ 0) {a b : R}
    (hab : a < b) (hV : varBetween (der P) (.finite a) (.finite b) = 1) :
    ∃ r ∈ Set.Ioc a b, P.IsRoot r ∧ P.rootMultiplicity r = 1 ∧
      ∀ r' ∈ Set.Ioc a b, P.IsRoot r' → r' = r := by
  classical
  have hn := numRoots_eq_one_of_var_eq_one hIVP hP hab hV
  rw [numRoots_finite_finite] at hn
  obtain ⟨r, hr_eq⟩ := Multiset.card_eq_one.mp hn
  have hr_mem : r ∈ P.roots.filter (fun r => a < r ∧ r ≤ b) := by
    rw [hr_eq]; exact Multiset.mem_singleton_self r
  rw [Multiset.mem_filter] at hr_mem
  obtain ⟨hr_roots, hr_ioc⟩ := hr_mem
  refine ⟨r, hr_ioc, (Polynomial.mem_roots hP).mp hr_roots, ?_, ?_⟩
  · -- rootMultiplicity r = 1
    have hcnt : Multiset.count r (P.roots.filter (fun r => a < r ∧ r ≤ b)) = 1 := by
      rw [hr_eq]; exact Multiset.count_singleton_self r
    rw [Multiset.count_filter, if_pos hr_ioc] at hcnt
    rw [← Polynomial.count_roots]; exact hcnt
  · intro r' hr' hr'_root
    have hr'_mem : r' ∈ P.roots.filter (fun r => a < r ∧ r ≤ b) :=
      Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP).mpr hr'_root, hr'⟩
    rw [hr_eq, Multiset.mem_singleton] at hr'_mem
    exact hr'_mem

/-! ## BPR Remark 2.38: equality when all roots are real

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
   componentwise — in particular on the middle interval. -/

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

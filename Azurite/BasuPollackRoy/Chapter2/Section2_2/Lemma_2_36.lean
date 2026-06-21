import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_25
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Notation_2_26
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_20
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_21
import Azurite.BasuPollackRoy.Chapter2.Section2_1.SignAtPoint

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
    (Polynomial.degree_derivative (Nat.lt_of_lt_of_le Nat.zero_lt_one hP).ne')

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
      have hh := Polynomial.derivative_eq_zero.mp h
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
        have := Polynomial.derivative_eq_zero.mp h
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
        have := Polynomial.derivative_eq_zero.mp h
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
lemma iterate_derivative_ne_zero_of_le_natDegree
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


end Azurite.BPR.Theorem2_35

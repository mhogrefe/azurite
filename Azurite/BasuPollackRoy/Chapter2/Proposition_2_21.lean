import Azurite.BasuPollackRoy.Chapter2.SignAtPoint

/-!
# BPR Proposition 2.21: Sign of a Polynomial to the Right / Left of a Root

**Proposition 2.21 (BPR).** If `r` is a root of `P ∈ R[X]` of multiplicity `µ`
in a real closed field `R`, then the sign of `P` to the right of `r` is the
sign of `P^{(µ)}(r)`, and the sign of `P` to the left of `r` is the sign of
`(−1)^µ · P^{(µ)}(r)`.

*Proof.* Write `P = (X − r)^µ · Q` with `Q(r) ≠ 0`. Since
`P^{(µ)}(r) = µ! · Q(r)` (Taylor) and `µ! > 0`, we have
`sign(Q(r)) = sign(P^{(µ)}(r))`. It thus suffices to show
  - `sign(P)` to the right of `r` equals `sign(Q(r))`,
  - `sign(P)` to the left  of `r` equals `(−1)^µ · sign(Q(r))`.

On a sufficiently small interval `(a, b)` around `r` avoiding all other roots
of `Q`, Proposition 2.20 gives `Q` constant sign there (equal to `sign(Q(r))`).
For `x > r`, `(x − r)^µ > 0` so `sign(P(x)) = sign(Q(x)) = sign(Q(r))`;
for `x < r`, `sign((x − r)^µ) = (−1)^µ`.
-/

namespace Azurite.BPR.Proposition2_21

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_11 Azurite.BPR.Proposition2_20

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Nonzero polynomials have non-vanishing intervals -/

/-- A nonzero polynomial has no root in some open interval `(r, b)` to the
    right of any `r`. -/
lemma exists_no_root_Ioo_right {Q : R[X]} (hQ : Q ≠ 0) (r : R) :
    ∃ b, r < b ∧ ∀ x ∈ Set.Ioo r b, Q.eval x ≠ 0 := by
  classical
  set F : Finset R := Q.roots.toFinset.filter (r < ·)
  by_cases hF : F.Nonempty
  · refine ⟨F.min' hF, (Finset.mem_filter.mp (F.min'_mem hF)).2, ?_⟩
    intro x hx hQx
    have hxF : x ∈ F := by
      refine Finset.mem_filter.mpr ⟨?_, hx.1⟩
      rw [Multiset.mem_toFinset, mem_roots hQ]
      exact hQx
    exact absurd hx.2 (not_lt.mpr (F.min'_le x hxF))
  · refine ⟨r + 1, by linarith, ?_⟩
    intro x hx hQx
    apply hF
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, hx.1⟩⟩
    rw [Multiset.mem_toFinset, mem_roots hQ]
    exact hQx

/-- A nonzero polynomial has no root in some open interval `(a, r)` to the
    left of any `r`. -/
lemma exists_no_root_Ioo_left {Q : R[X]} (hQ : Q ≠ 0) (r : R) :
    ∃ a, a < r ∧ ∀ x ∈ Set.Ioo a r, Q.eval x ≠ 0 := by
  classical
  set F : Finset R := Q.roots.toFinset.filter (· < r)
  by_cases hF : F.Nonempty
  · refine ⟨F.max' hF, (Finset.mem_filter.mp (F.max'_mem hF)).2, ?_⟩
    intro x hx hQx
    have hxF : x ∈ F := by
      refine Finset.mem_filter.mpr ⟨?_, hx.2⟩
      rw [Multiset.mem_toFinset, mem_roots hQ]
      exact hQx
    exact absurd hx.1 (not_lt.mpr (F.le_max' x hxF))
  · refine ⟨r - 1, by linarith, ?_⟩
    intro x hx hQx
    apply hF
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, hx.2⟩⟩
    rw [Multiset.mem_toFinset, mem_roots hQ]
    exact hQx

/-! ## Sign of a polynomial near a non-vanishing point -/

/-- If `Q.eval r ≠ 0` and `R` has the intermediate value property, then
    `HasSignRight Q r (sign Q.eval r)`: `Q` takes the sign of `Q(r)` on some
    interval `(r, b)`. -/
theorem hasSignRight_of_eval_ne_zero (hIVP : HasIntermediateValueProperty R)
    {Q : R[X]} {r : R} (hQr : Q.eval r ≠ 0) :
    HasSignRight Q r (SignType.sign (Q.eval r)) := by
  have hQne : Q ≠ 0 := fun h => by simp [h] at hQr
  obtain ⟨b, hrb, hne_right⟩ := exists_no_root_Ioo_right hQne r
  obtain ⟨a, har, hne_left⟩ := exists_no_root_Ioo_left hQne r
  have hQ_ne_on : ∀ x ∈ Set.Ioo a b, Q.eval x ≠ 0 := by
    intro x hx
    rcases lt_trichotomy x r with hxr | hxr | hxr
    · exact hne_left x ⟨hx.1, hxr⟩
    · exact hxr ▸ hQr
    · exact hne_right x ⟨hxr, hx.2⟩
  have hrin : r ∈ Set.Ioo a b := ⟨har, hrb⟩
  rcases proposition_2_20 hIVP Q a b hQ_ne_on with hpos | hneg
  · rw [sign_pos (hpos r hrin)]
    exact ⟨b, hrb, fun x hx => sign_pos (hpos x ⟨lt_trans har hx.1, hx.2⟩)⟩
  · rw [sign_neg (hneg r hrin)]
    exact ⟨b, hrb, fun x hx => sign_neg (hneg x ⟨lt_trans har hx.1, hx.2⟩)⟩

/-- Left analogue. -/
theorem hasSignLeft_of_eval_ne_zero (hIVP : HasIntermediateValueProperty R)
    {Q : R[X]} {r : R} (hQr : Q.eval r ≠ 0) :
    HasSignLeft Q r (SignType.sign (Q.eval r)) := by
  have hQne : Q ≠ 0 := fun h => by simp [h] at hQr
  obtain ⟨b, hrb, hne_right⟩ := exists_no_root_Ioo_right hQne r
  obtain ⟨a, har, hne_left⟩ := exists_no_root_Ioo_left hQne r
  have hQ_ne_on : ∀ x ∈ Set.Ioo a b, Q.eval x ≠ 0 := by
    intro x hx
    rcases lt_trichotomy x r with hxr | hxr | hxr
    · exact hne_left x ⟨hx.1, hxr⟩
    · exact hxr ▸ hQr
    · exact hne_right x ⟨hxr, hx.2⟩
  have hrin : r ∈ Set.Ioo a b := ⟨har, hrb⟩
  rcases proposition_2_20 hIVP Q a b hQ_ne_on with hpos | hneg
  · rw [sign_pos (hpos r hrin)]
    exact ⟨a, har, fun x hx => sign_pos (hpos x ⟨hx.1, lt_trans hx.2 hrb⟩)⟩
  · rw [sign_neg (hneg r hrin)]
    exact ⟨a, har, fun x hx => sign_neg (hneg x ⟨hx.1, lt_trans hx.2 hrb⟩)⟩

/-! ## Proposition 2.21 -/

/-- Sign of the `µ`-th derivative equals the sign of `Q(r)` in the factorization
    `P = (X − C r)^µ · Q`. Intermediate fact used in Proposition 2.21. -/
lemma sign_iterate_derivative_eq_sign_Q {P : R[X]} {r : R} (_hP : P ≠ 0) :
    SignType.sign (((⇑derivative)^[P.rootMultiplicity r] P).eval r) =
    SignType.sign ((P /ₘ (X - C r) ^ P.rootMultiplicity r).eval r) := by
  rw [eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul, sign_mul]
  have hfac_pos : (0 : R) < (P.rootMultiplicity r).factorial := by
    exact_mod_cast Nat.factorial_pos _
  rw [sign_pos hfac_pos, one_mul]

/-- **BPR Proposition 2.21 (right side).** If `P ≠ 0` and `R` has the
    intermediate value property, then the sign of `P` to the right of `r`
    equals the sign of `P^{(µ)}(r)` where `µ = P.rootMultiplicity r`. -/
theorem proposition_2_21_right (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (r : R) :
    HasSignRight P r
      (SignType.sign (((⇑derivative)^[P.rootMultiplicity r] P).eval r)) := by
  set mu := P.rootMultiplicity r
  set Q := P /ₘ (X - C r) ^ mu
  have hPfac : (X - C r) ^ mu * Q = P := pow_mul_divByMonic_rootMultiplicity_eq P r
  have hQr : Q.eval r ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero r hP
  rw [sign_iterate_derivative_eq_sign_Q hP]
  obtain ⟨b, hrb, hQ_sign⟩ := hasSignRight_of_eval_ne_zero hIVP hQr
  refine ⟨b, hrb, ?_⟩
  intro x hx
  have hPx : P.eval x = (x - r) ^ mu * Q.eval x := by
    rw [← hPfac]; simp
  rw [hPx, sign_mul]
  have hxr_pos : 0 < x - r := sub_pos.mpr hx.1
  have hxr_pow_pos : 0 < (x - r) ^ mu := pow_pos hxr_pos mu
  rw [sign_pos hxr_pow_pos, one_mul]
  exact hQ_sign x hx

/-- **BPR Proposition 2.21 (left side).** The sign of `P` to the left of `r`
    equals `(−1)^µ · sign(P^{(µ)}(r))` where `µ = P.rootMultiplicity r`. -/
theorem proposition_2_21_left (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (r : R) :
    HasSignLeft P r
      ((-1) ^ P.rootMultiplicity r *
        SignType.sign (((⇑derivative)^[P.rootMultiplicity r] P).eval r)) := by
  set mu := P.rootMultiplicity r
  set Q := P /ₘ (X - C r) ^ mu
  have hPfac : (X - C r) ^ mu * Q = P := pow_mul_divByMonic_rootMultiplicity_eq P r
  have hQr : Q.eval r ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero r hP
  rw [sign_iterate_derivative_eq_sign_Q hP]
  obtain ⟨a, har, hQ_sign⟩ := hasSignLeft_of_eval_ne_zero hIVP hQr
  refine ⟨a, har, ?_⟩
  intro x hx
  have hPx : P.eval x = (x - r) ^ mu * Q.eval x := by
    rw [← hPfac]; simp
  rw [hPx, sign_mul]
  have hxr_neg : x - r < 0 := sub_neg.mpr hx.2
  rw [sign_pow, sign_neg hxr_neg]
  exact congrArg _ (hQ_sign x hx)

/-! ## Real-closed corollaries -/

/-- **Proposition 2.21 (right side), real closed form.** -/
theorem proposition_2_21_right_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) (hP : P ≠ 0) (r : R) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    HasSignRight P r
      (SignType.sign (((⇑derivative)^[P.rootMultiplicity r] P).eval r)) := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact proposition_2_21_right theorem_2_11_b_c hP r

/-- **Proposition 2.21 (left side), real closed form.** -/
theorem proposition_2_21_left_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) (hP : P ≠ 0) (r : R) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    HasSignLeft P r
      ((-1) ^ P.rootMultiplicity r *
        SignType.sign (((⇑derivative)^[P.rootMultiplicity r] P).eval r)) := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact proposition_2_21_left theorem_2_11_b_c hP r

/-! ## Proposition 2.22: Rolle's Theorem -/

/-- If `Q ≠ 0` does not vanish on `[a, b]` (with `a < b`) and `R` has the IVP,
    then `sign(Q(a)) = sign(Q(b))` (constant sign on `[a, b]`). -/
private lemma sign_eq_of_no_root_Icc (hIVP : HasIntermediateValueProperty R)
    {Q : R[X]} (hQ : Q ≠ 0) {a b : R} (hab : a < b)
    (hne : ∀ x ∈ Set.Icc a b, Q.eval x ≠ 0) :
    SignType.sign (Q.eval a) = SignType.sign (Q.eval b) := by
  obtain ⟨a', ha', hne_l⟩ := exists_no_root_Ioo_left hQ a
  obtain ⟨b', hb', hne_r⟩ := exists_no_root_Ioo_right hQ b
  have hne_all : ∀ x ∈ Set.Ioo a' b', Q.eval x ≠ 0 := by
    intro x ⟨hxa', hxb'⟩
    by_cases hax : a ≤ x
    · by_cases hxb : x ≤ b
      · exact hne x ⟨hax, hxb⟩
      · exact hne_r x ⟨not_le.mp hxb, hxb'⟩
    · exact hne_l x ⟨hxa', not_le.mp hax⟩
  have ha_mem : a ∈ Set.Ioo a' b' := ⟨ha', lt_trans hab hb'⟩
  have hb_mem : b ∈ Set.Ioo a' b' := ⟨lt_trans ha' hab, hb'⟩
  rcases proposition_2_20 hIVP Q a' b' hne_all with hpos | hneg
  · rw [sign_pos (hpos a ha_mem), sign_pos (hpos b hb_mem)]
  · rw [sign_neg (hneg a ha_mem), sign_neg (hneg b hb_mem)]

/-- **Rolle's theorem, base case.** If `P(a) = P(b) = 0`, `a < b`, `P ≠ 0`, and
    `P` does not vanish on `(a, b)`, then `P'` has a root in `(a, b)`. -/
private lemma rolle_base (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {a b : R} (hab : a < b)
    (hPa : P.eval a = 0) (hPb : P.eval b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, P.eval x ≠ 0) :
    ∃ c ∈ Set.Ioo a b, (derivative P).eval c = 0 := by
  -- Factor P = (X - C a)^m * Q₀, Q₀(a) ≠ 0
  set m := P.rootMultiplicity a with hm_def
  set Q₀ := P /ₘ (X - C a) ^ m with hQ₀_def
  have hP₀ : (X - C a) ^ m * Q₀ = P := pow_mul_divByMonic_rootMultiplicity_eq P a
  have hQ₀a : Q₀.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hP
  have hQ₀_ne : Q₀ ≠ 0 := fun h => hQ₀a (by simp [h])
  -- Evaluation lemma for P
  have hP_eval : ∀ x, P.eval x = (x - a) ^ m * Q₀.eval x := fun x => by
    have := congr_arg (Polynomial.eval x) hP₀; simp at this; linarith
  -- m ≥ 1 since P(a) = 0
  have hm_pos : 0 < m := (rootMultiplicity_pos hP).mpr hPa
  -- Q₀(b) = 0 (from P(b) = 0 and a ≠ b)
  have hQ₀b : Q₀.eval b = 0 := by
    have := hP_eval b; rw [hPb] at this
    exact (mul_eq_zero.mp this.symm).resolve_left
      (pow_ne_zero _ (sub_ne_zero.mpr (ne_of_gt hab)))
  -- Factor Q₀ = (X - C b)^n * Q, Q(b) ≠ 0
  set n := Q₀.rootMultiplicity b with hn_def
  set Q := Q₀ /ₘ (X - C b) ^ n with hQ_def
  have hQ₀_fac : (X - C b) ^ n * Q = Q₀ := pow_mul_divByMonic_rootMultiplicity_eq Q₀ b
  have hQb : Q.eval b ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero b hQ₀_ne
  have hQ_ne : Q ≠ 0 := fun h => hQb (by simp [h])
  -- n ≥ 1
  have hn_pos : 0 < n := (rootMultiplicity_pos hQ₀_ne).mpr hQ₀b
  -- Evaluation lemma for Q₀
  have hQ₀_eval : ∀ x, Q₀.eval x = (x - b) ^ n * Q.eval x := fun x => by
    have := congr_arg (Polynomial.eval x) hQ₀_fac; simp at this; exact this.symm
  -- Q(a) ≠ 0
  have hQa : Q.eval a ≠ 0 := by
    intro h; have := hQ₀_eval a; rw [h, mul_zero] at this; exact hQ₀a this
  -- P = (X - C a)^m * (X - C b)^n * Q
  have hP_eq : P = (X - C a) ^ m * ((X - C b) ^ n * Q) := by
    calc P = (X - C a) ^ m * Q₀ := hP₀.symm
      _ = (X - C a) ^ m * ((X - C b) ^ n * Q) := by rw [← hQ₀_fac]
  -- Combined evaluation
  have hP_eval' : ∀ x, P.eval x = (x - a) ^ m * ((x - b) ^ n * Q.eval x) := fun x => by
    rw [hP_eval, hQ₀_eval]
  -- Q doesn't vanish on [a, b]
  have hQ_ne_Icc : ∀ x ∈ Set.Icc a b, Q.eval x ≠ 0 := by
    intro x ⟨hax, hxb⟩ hQx
    rcases hax.eq_or_lt with rfl | hax
    · exact hQa hQx
    · rcases hxb.eq_or_lt with rfl | hxb
      · exact hQb hQx
      · exact hne x ⟨hax, hxb⟩ (by rw [hP_eval' x, hQx, mul_zero, mul_zero])
  -- sign(Q(a)) = sign(Q(b))
  have hQ_sign : SignType.sign (Q.eval a) = SignType.sign (Q.eval b) :=
    sign_eq_of_no_root_Icc hIVP hQ_ne hab hQ_ne_Icc
  -- Q(a) * Q(b) > 0
  have hQab_pos : 0 < Q.eval a * Q.eval b := by
    rcases lt_or_gt_of_ne hQa with hQa_neg | hQa_pos
    · exact mul_pos_of_neg_of_neg hQa_neg
        (sign_eq_neg_one_iff.mp (hQ_sign ▸ sign_neg hQa_neg))
    · exact mul_pos hQa_pos
        (sign_eq_one_iff.mp (hQ_sign ▸ sign_pos hQa_pos))
  -- Write m = m' + 1, n = n' + 1
  obtain ⟨m', hm⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n', hn⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  -- Define Q₁
  set Q₁ : R[X] :=
    C (↑m : R) * (X - C b) * Q +
    C (↑n : R) * (X - C a) * Q +
    (X - C a) * (X - C b) * derivative Q with hQ₁_def
  -- Q₁(a) * Q₁(b) < 0
  have hQ₁a : Q₁.eval a = ↑m * (a - b) * Q.eval a := by
    simp [hQ₁_def]
  have hQ₁b : Q₁.eval b = ↑n * (b - a) * Q.eval b := by
    simp [hQ₁_def]
  have hQ₁_opp : Q₁.eval a * Q₁.eval b < 0 := by
    rw [hQ₁a, hQ₁b]
    have : ↑m * (a - b) * Q.eval a * (↑n * (b - a) * Q.eval b) =
        -(↑m * ↑n * (b - a) ^ 2 * (Q.eval a * Q.eval b)) := by ring
    rw [this]
    have h_pos : (0 : R) < ↑m * ↑n * (b - a) ^ 2 * (Q.eval a * Q.eval b) :=
      mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hm_pos)
        (Nat.cast_pos.mpr hn_pos)) (sq_pos_of_pos (sub_pos.mpr hab))) hQab_pos
    linarith
  -- IVP gives c ∈ (a, b) with Q₁(c) = 0
  obtain ⟨c, hac, hcb, hQ₁c⟩ := hIVP Q₁ a b hab hQ₁_opp
  refine ⟨c, ⟨hac, hcb⟩, ?_⟩
  -- It suffices to factor out (c-a)^m'*(c-b)^n' and use Q₁(c) = 0
  suffices hsuff : (derivative P).eval c =
      (c - a) ^ m' * ((c - b) ^ n' * Q₁.eval c) by
    rw [hsuff, hQ₁c, mul_zero, mul_zero]
  rw [hP_eq, hm, hn]
  simp only [derivative_mul, derivative_pow_succ, derivative_X_sub_C, mul_one,
    eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, hQ₁_def]
  push_cast [hm, hn]
  ring

/-- **BPR Proposition 2.22 (Rolle's theorem).** Let `R` be an ordered field with
    the intermediate value property, `P ∈ R[X]`, `a < b`, `P(a) = P(b) = 0`.
    Then `P'` has a root in `(a, b)`. -/
theorem proposition_2_22 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {a b : R} (hab : a < b)
    (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Set.Ioo a b, (derivative P).eval c = 0 := by
  by_cases hP : P = 0
  · obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ⟨c, ⟨hac, hcb⟩, by simp [hP]⟩
  classical
  set F := P.roots.toFinset.filter (fun x => a < x ∧ x ≤ b) with hF_def
  have hb_in : b ∈ F := by
    rw [hF_def, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP]
    exact ⟨hPb, hab, le_refl b⟩
  set c := F.min' ⟨b, hb_in⟩
  have hc_mem := Finset.mem_filter.mp (F.min'_mem ⟨b, hb_in⟩)
  have hac : a < c := hc_mem.2.1
  have hcb : c ≤ b := hc_mem.2.2
  have hPc : P.eval c = 0 := by
    rw [Multiset.mem_toFinset, mem_roots hP] at hc_mem; exact hc_mem.1
  have hno_root : ∀ x ∈ Set.Ioo a c, P.eval x ≠ 0 := by
    intro x hx hPx
    have hxF : x ∈ F := by
      rw [hF_def, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP]
      exact ⟨hPx, hx.1, le_of_lt (lt_of_lt_of_le hx.2 hcb)⟩
    exact absurd hx.2 (not_lt.mpr (F.min'_le x hxF))
  obtain ⟨d, hd, hPd⟩ := rolle_base hIVP hP hac hPa hPc hno_root
  exact ⟨d, ⟨hd.1, lt_of_lt_of_le hd.2 hcb⟩, hPd⟩

/-- **Proposition 2.22 (Rolle's theorem), real closed form.** -/
theorem proposition_2_22_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) {a b : R} :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    a < b → P.eval a = 0 → P.eval b = 0 →
    ∃ c ∈ Set.Ioo a b, (derivative P).eval c = 0 := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact proposition_2_22 theorem_2_11_b_c P

/-! ## Corollary 2.23: Mean Value Theorem -/

/-- **BPR Corollary 2.23 (Mean Value Theorem).** Let `R` be an ordered field with
    the intermediate value property, `P ∈ R[X]`, `a < b`. Then there exists
    `c ∈ (a, b)` such that `P(b) - P(a) = (b - a) * P'(c)`. -/
theorem corollary_2_23 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {a b : R} (hab : a < b) :
    ∃ c ∈ Set.Ioo a b, P.eval b - P.eval a = (b - a) * (derivative P).eval c := by
  -- Q(X) = (P(b) - P(a)) * (X - a) - (b - a) * (P(X) - P(a))
  set Q := C (P.eval b - P.eval a) * (X - C a) - C (b - a) * (P - C (P.eval a))
  have hQa : Q.eval a = 0 := by simp [Q]
  have hQb : Q.eval b = 0 := by simp [Q]; ring
  obtain ⟨c, hc, hQ'c⟩ := proposition_2_22 hIVP Q hab hQa hQb
  refine ⟨c, hc, ?_⟩
  -- Q'(X) = (P(b) - P(a)) - (b - a) * P'(X), so Q'(c) = 0 gives the result
  have hQ' : derivative Q = C (P.eval b - P.eval a) - C (b - a) * derivative P := by
    simp [Q, derivative_sub, derivative_mul, derivative_C]
  have hQ'c_eq : (derivative Q).eval c =
      (P.eval b - P.eval a) - (b - a) * (derivative P).eval c := by
    simp [hQ']
  linarith

/-- **Corollary 2.23 (Mean Value Theorem), real closed form.** -/
theorem corollary_2_23_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) {a b : R} :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    a < b →
    ∃ c ∈ Set.Ioo a b, P.eval b - P.eval a = (b - a) * (derivative P).eval c := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact corollary_2_23 theorem_2_11_b_c P

/-! ## Corollary 2.24: Monotonicity from derivative sign -/

/-- **BPR Corollary 2.24 (increasing case).** If `P' > 0` on `(a, b)`, then
    `P` is strictly increasing on `[a, b]`. -/
theorem corollary_2_24_increasing (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {a b : R} (_hab : a < b)
    (hP' : ∀ x ∈ Set.Ioo a b, 0 < (derivative P).eval x) :
    StrictMonoOn (fun x => P.eval x) (Set.Icc a b) := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hMVT⟩ := corollary_2_23 hIVP P hxy
  have hc_ab : c ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_lt hx.1 hc.1, lt_of_lt_of_le hc.2 hy.2⟩
  linarith [mul_pos (sub_pos.mpr hxy) (hP' c hc_ab)]

/-- **BPR Corollary 2.24 (decreasing case).** If `P' < 0` on `(a, b)`, then
    `P` is strictly decreasing on `[a, b]`. -/
theorem corollary_2_24_decreasing (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {a b : R} (_hab : a < b)
    (hP' : ∀ x ∈ Set.Ioo a b, (derivative P).eval x < 0) :
    StrictAntiOn (fun x => P.eval x) (Set.Icc a b) := by
  intro x hx y hy hxy
  obtain ⟨c, hc, hMVT⟩ := corollary_2_23 hIVP P hxy
  have hc_ab : c ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_lt hx.1 hc.1, lt_of_lt_of_le hc.2 hy.2⟩
  linarith [mul_neg_of_pos_of_neg (sub_pos.mpr hxy) (hP' c hc_ab)]

/-- **Corollary 2.24 (increasing), real closed form.** -/
theorem corollary_2_24_increasing_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) {a b : R} :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    a < b →
    (∀ x ∈ Set.Ioo a b, 0 < (derivative P).eval x) →
    StrictMonoOn (fun x => P.eval x) (Set.Icc a b) := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact corollary_2_24_increasing theorem_2_11_b_c P

/-- **Corollary 2.24 (decreasing), real closed form.** -/
theorem corollary_2_24_decreasing_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) {a b : R} :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    a < b →
    (∀ x ∈ Set.Ioo a b, (derivative P).eval x < 0) →
    StrictAntiOn (fun x => P.eval x) (Set.Icc a b) := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact corollary_2_24_decreasing theorem_2_11_b_c P

end Azurite.BPR.Proposition2_21

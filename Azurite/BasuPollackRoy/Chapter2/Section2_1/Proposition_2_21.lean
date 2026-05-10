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

end Azurite.BPR.Proposition2_21

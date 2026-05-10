import Azurite.BasuPollackRoy.Chapter2.Section2_1

/-!
# BPR Theorem 2.11 c) => a): Intermediate Value Property => Real Closed

**Theorem 2.11 (c => a) (BPR).** If R is an ordered field with the intermediate value
property, then R is real closed.

**Proof strategy.** We show (1) every positive element has a square root, and
(2) every odd-degree polynomial has a root. Both use the IVP combined with
Proposition 2.4 to establish sign changes at sufficiently large values.
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Auxiliary: bound for Prop 2.4 -/

/-- The threshold value from Proposition 2.4: `2 * ∑ᵢ |aᵢ/aₚ|`.
    For |x| > this bound, sign(P(x)) = sign(leadingCoeff * x^deg). -/
noncomputable def prop24Bound (P : R[X]) : R :=
  2 * ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i / P.leadingCoeff|

theorem prop24Bound_nonneg (P : R[X]) : 0 ≤ prop24Bound P := by
  unfold prop24Bound
  apply mul_nonneg (by norm_num : (0:R) ≤ 2)
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-- For x > prop24Bound P, sign(P(x)) = sign(leadingCoeff * x^deg). -/
theorem sign_eval_of_large_pos (P : R[X]) (hP : P ≠ 0) (x : R)
    (hx : prop24Bound P < x) :
    SignType.sign (P.eval x) = SignType.sign (P.leadingCoeff * x ^ P.natDegree) := by
  apply prop_2_4 P hP
  rw [abs_of_pos (lt_of_le_of_lt (prop24Bound_nonneg P) hx)]
  exact hx

/-- For x < -(prop24Bound P), sign(P(x)) = sign(leadingCoeff * x^deg). -/
theorem sign_eval_of_large_neg (P : R[X]) (hP : P ≠ 0) (x : R)
    (hx : x < -prop24Bound P) :
    SignType.sign (P.eval x) = SignType.sign (P.leadingCoeff * x ^ P.natDegree) := by
  apply prop_2_4 P hP
  rw [abs_of_neg (lt_of_lt_of_le hx (neg_nonpos.mpr (prop24Bound_nonneg P)))]
  simp only [prop24Bound] at hx ⊢; linarith

/-! ## Part 1: Every positive element has a square root -/

/-- The polynomial X² - C y. -/
private noncomputable def sqMinusConst (y : R) : R[X] := X ^ 2 - C y

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem sqMinusConst_eval (y x : R) :
    (sqMinusConst y).eval x = x ^ 2 - y := by
  simp [sqMinusConst, eval_sub, eval_pow, eval_X, eval_C]

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem sqMinusConst_eval_zero (y : R) :
    (sqMinusConst y).eval 0 = -y := by
  simp [sqMinusConst_eval]

private theorem sqMinusConst_eval_pos_of_large (y : R) (x : R) (hx1 : 1 ≤ x) (hx2 : y < x) :
    0 < (sqMinusConst y).eval x := by
  rw [sqMinusConst_eval]
  nlinarith [sq_nonneg (x - 1)]

theorem isSquare_of_nonneg (hIVP : Azurite.BPR.HasIntermediateValueProperty R) {y : R} (hy : 0 ≤ y) :
    IsSquare y := by
  rcases eq_or_lt_of_le hy with rfl | hy_pos
  · exact ⟨0, by ring⟩
  -- P = X² - y has P(0) = -y < 0
  set P := sqMinusConst y
  have hP0 : P.eval 0 < 0 := by rw [sqMinusConst_eval_zero]; linarith
  -- Pick x large enough that P(x) > 0
  set x := |y| + 1
  have hx1 : 1 ≤ x := by linarith [abs_nonneg y]
  have hx2 : y < x := by linarith [le_abs_self y]
  have hPx : 0 < P.eval x := sqMinusConst_eval_pos_of_large y x hx1 hx2
  -- Sign change: P(0) * P(x) < 0
  have hsign : P.eval 0 * P.eval x < 0 := mul_neg_of_neg_of_pos hP0 hPx
  have h0x : (0 : R) < x := by positivity
  -- IVP gives a root r ∈ (0, x)
  obtain ⟨r, _, _, hPr⟩ := hIVP P 0 x h0x hsign
  rw [sqMinusConst_eval] at hPr
  exact ⟨r, by linarith⟩

/-! ## Part 2: Every odd-degree polynomial has a root -/

/-- A nonzero polynomial of odd degree takes a positive value for some large x
    and a negative value for some small (large negative) x, or vice versa.
    Combined with IVP, this gives a root. -/
theorem exists_isRoot_of_odd_natDegree (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    {P : R[X]} (hodd : Odd P.natDegree) : ∃ x, P.IsRoot x := by
  by_cases hP : P = 0
  · exact ⟨0, by simp [hP]⟩
  -- Pick values beyond the Prop 2.4 bound
  set B := prop24Bound P
  set xp := B + 1
  set xn := -(B + 1)
  have hxp : B < xp := by linarith
  have hxn : xn < -B := by linarith
  -- Sign at xp
  have hsign_p := sign_eval_of_large_pos P hP xp hxp
  -- Sign at xn
  have hsign_n := sign_eval_of_large_neg P hP xn hxn
  -- The leading term at xp is leadingCoeff * xp^deg with xp > 0
  -- The leading term at xn is leadingCoeff * xn^deg with xn < 0
  -- Since deg is odd, xn^deg < 0, so the signs differ
  have hxp_pos : 0 < xp := by linarith [prop24Bound_nonneg P]
  have hxn_neg : xn < 0 := by linarith [prop24Bound_nonneg P]
  have hxn_ne : xn ≠ 0 := ne_of_lt hxn_neg
  have hxp_ne : xp ≠ 0 := ne_of_gt hxp_pos
  -- xp^deg > 0 since xp > 0
  have hxp_pow_pos : 0 < xp ^ P.natDegree := pow_pos hxp_pos _
  -- xn^deg < 0 since xn < 0 and deg is odd
  have hxn_pow_neg : xn ^ P.natDegree < 0 := Odd.pow_neg hodd hxn_neg
  -- Leading coeff is nonzero
  have hlc_ne : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  -- The leading terms at xp and xn have opposite signs
  have hlead_opp : P.leadingCoeff * xp ^ P.natDegree *
      (P.leadingCoeff * xn ^ P.natDegree) < 0 := by
    have : P.leadingCoeff * xp ^ P.natDegree * (P.leadingCoeff * xn ^ P.natDegree) =
        P.leadingCoeff ^ 2 * (xp ^ P.natDegree * xn ^ P.natDegree) := by ring
    rw [this]
    apply mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hlc_ne)
    exact mul_neg_of_pos_of_neg hxp_pow_pos hxn_pow_neg
  -- Transfer to P.eval via Prop 2.4 sign equality
  have hPeval_opp : P.eval xn * P.eval xp < 0 := by
    -- Case split on sign of leading coefficient
    rcases lt_or_gt_of_ne hlc_ne with hlc_neg | hlc_pos
    · -- lc < 0: lead at xp < 0, lead at xn > 0
      have hlp : P.leadingCoeff * xp ^ P.natDegree < 0 :=
        mul_neg_of_neg_of_pos hlc_neg hxp_pow_pos
      have hln : 0 < P.leadingCoeff * xn ^ P.natDegree :=
        mul_pos_of_neg_of_neg hlc_neg hxn_pow_neg
      have hPxp_neg : P.eval xp < 0 :=
        sign_eq_neg_one_iff.mp (hsign_p.trans (sign_eq_neg_one_iff.mpr hlp))
      have hPxn_pos : 0 < P.eval xn :=
        sign_eq_one_iff.mp (hsign_n.trans (sign_eq_one_iff.mpr hln))
      exact mul_neg_of_pos_of_neg hPxn_pos hPxp_neg
    · -- lc > 0: lead at xp > 0, lead at xn < 0
      have hlp : 0 < P.leadingCoeff * xp ^ P.natDegree :=
        mul_pos hlc_pos hxp_pow_pos
      have hln : P.leadingCoeff * xn ^ P.natDegree < 0 :=
        mul_neg_of_pos_of_neg hlc_pos hxn_pow_neg
      have hPxp_pos : 0 < P.eval xp :=
        sign_eq_one_iff.mp (hsign_p.trans (sign_eq_one_iff.mpr hlp))
      have hPxn_neg : P.eval xn < 0 :=
        sign_eq_neg_one_iff.mp (hsign_n.trans (sign_eq_neg_one_iff.mpr hln))
      exact mul_neg_of_neg_of_pos hPxn_neg hPxp_pos
  -- xn < xp
  have hxn_lt_xp : xn < xp := by linarith [prop24Bound_nonneg P]
  -- IVP gives a root
  obtain ⟨r, _, _, hPr⟩ := hIVP P xn xp hxn_lt_xp hPeval_opp
  exact ⟨r, hPr⟩

/-! ## Main theorem -/

/-- **BPR Theorem 2.11 (c => a).** If R has the intermediate value property,
    then R is real closed. -/
theorem theorem_2_11_c_a (hIVP : Azurite.BPR.HasIntermediateValueProperty R) :
    IsRealClosed R :=
  IsRealClosed.of_linearOrderedField
    (isSquare_of_nonneg hIVP)
    (exists_isRoot_of_odd_natDegree hIVP)

end Azurite.BPR.Theorem2_11

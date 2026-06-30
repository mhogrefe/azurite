import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_18

/-!
# Equal-degree resultant reduction (for BPR Exercise 8.2)

When `deg P = deg Q`, the signed subresultant algorithm cannot be applied directly (it needs
`deg Q < deg P`).  Following BPR Exercise 8.2, we replace `Q` by

  `Q₁ := a_p · Q − b_p · P`   (`a_p = lcof P`, `b_p = lcof Q`),

whose leading terms cancel, so `deg Q₁ < deg P`.  The key identity is

  `a_p^r · Res(P, Q) = Res(P, Q₁)`,  where `r = deg Q₁`.

Proof (over an integral domain, no splitting field needed): scaling the second argument by the
constant `a_p` multiplies the resultant by `a_p^{deg P}` (`resultant_C_mul_right`); since
`a_p · Q = Q₁ + b_p · P`, adding the multiple `b_p · P` of `P` is invisible at fixed formal degree
`deg P` (`resultant_add_mul_right`); and dropping the formal degree of the second argument from
`deg P` down to `r` costs a factor `a_p^{deg P − r}` (`resultant_add_right_deg`).  Cancelling
`a_p^{deg P − r}` (using `IsDomain`) leaves `a_p^r · Res(P,Q) = Res(P, Q₁)`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

/-- **BPR Exercise 8.2 (key identity).**  For `P ≠ 0` with `deg P = deg Q`, writing
    `Q₁ = a_p·Q − b_p·P` (`a_p = lcof P`, `b_p = lcof Q`, whose leading terms cancel so
    `deg Q₁ < deg P`), one has `a_p^{deg Q₁} · Res(P,Q) = Res(P, Q₁)`. -/
theorem leadingCoeff_pow_mul_Res_eq {D : Type*} [CommRing D] [IsDomain D] (P Q : D[X])
    (hP : P ≠ 0) (hpq : P.natDegree = Q.natDegree) :
    P.leadingCoeff ^ (C P.leadingCoeff * Q - C Q.leadingCoeff * P).natDegree * Res P Q
      = Res P (C P.leadingCoeff * Q - C Q.leadingCoeff * P) := by
  set a := P.leadingCoeff with ha_def
  set b := Q.leadingCoeff with hb_def
  set Q₁ := C a * Q - C b * P with hQ₁
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hr : Q₁.natDegree ≤ P.natDegree := by
    rw [hQ₁]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le a Q).trans (le_of_eq hpq.symm)
    · exact natDegree_C_mul_le b P
  have hCaQ : C a * Q = Q₁ + P * C b := by rw [hQ₁]; ring
  -- Way 1: scaling the second argument by the constant `a`.
  have h1 : Res P (C a * Q) = a ^ P.natDegree * Res P Q := by
    rw [Res_eq_resultant, Res_eq_resultant, natDegree_C_mul ha, resultant_C_mul_right]
  -- Way 2: `a·Q = Q₁ + b·P`; drop the multiple of `P`, then the formal degree from `p` to `r`.
  have hdeg := resultant_add_right_deg (f := P) (g := Q₁) (m := P.natDegree)
    (n := Q₁.natDegree) (P.natDegree - Q₁.natDegree) (le_refl _)
  rw [Nat.add_sub_cancel' hr, show P.coeff P.natDegree = a from rfl] at hdeg
  have hp_mul : (C b).natDegree + P.natDegree ≤ Q.natDegree := by rw [natDegree_C]; omega
  have h2 : Res P (C a * Q) = a ^ (P.natDegree - Q₁.natDegree) * Res P Q₁ := by
    rw [Res_eq_resultant P (C a * Q), natDegree_C_mul ha, hCaQ,
      resultant_add_mul_right (f := P) (g := Q₁) (p := C b) (m := P.natDegree) (n := Q.natDegree)
        hp_mul (le_refl _), ← hpq, hdeg, ← Res_eq_resultant P Q₁]
  -- Combine and cancel `a^{p-r}`.
  rw [h1] at h2
  have hpow : a ^ P.natDegree = a ^ (P.natDegree - Q₁.natDegree) * a ^ Q₁.natDegree := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, mul_assoc] at h2
  exact mul_left_cancel₀ (pow_ne_zero _ ha) h2

end Azurite.BPR.Chapter4

import Azurite.BasuPollackRoy.Chapter2.Section2_6.Example_2_94
import Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxMonomial

/-! # BPR §2.6 Example 2.96 — the substitution `P₁ = ε^{−1}P(ε^{1/3}(1+X))`

Continuing Example 2.94, we choose the edge `E` (with `ξ = 1/3`, `β = 1`) and the root `x = 1`
of the characteristic polynomial `Q(P,E,X) = 1 − X³` (multiplicity `1`), and substitute
`X = ε^{1/3}(1 + X)`, dividing by `ε^β = ε`:

`P₁(X) = ε^{−1} P(ε^{1/3}(1 + X))`.

We verify the explicit expansion of `P₁` from BPR, and that it exhibits Lemma 2.95(a): every
coefficient `bᵢ` has `o(bᵢ) ≥ 0`, with `o(b₀) > 0` and `o(b₁) = 0` (since `x = 1` has
multiplicity `r = 1`).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [CharZero R]

/-- `ε = ε^1` as a Puiseux monomial. -/
theorem eps_mono : (puiseuxEps : PuiseuxSeries R) = puiseuxMonomial 1 := by
  apply Subtype.ext; rw [puiseuxEps_coe, coe_puiseuxMonomial]

/-- `(ε^ξ)^n = ε^{nξ}`. -/
theorem mono_pow (ξ : ℚ) (n : ℕ) :
    (puiseuxMonomial ξ : PuiseuxSeries R) ^ n = puiseuxMonomial ((n : ℚ) * ξ) := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, puiseuxMonomial_mul]; congr 1; push_cast; ring

/-- `(ε^{1/3}(1+X))^n = ε^{n/3}(1+X)^n`. -/
theorem subpow (n : ℕ) :
    (C (puiseuxMonomial (1 / 3 : ℚ)) * (1 + X) : Polynomial (PuiseuxSeries R)) ^ n
      = C (puiseuxMonomial ((n : ℚ) / 3)) * (1 + X) ^ n := by
  rw [mul_pow, ← C_pow, mono_pow]; congr 3; push_cast; ring

/-- **`P₁(X) = ε^{−1} P(ε^{1/3}(1 + X))`** (Example 2.96). -/
noncomputable def exP1 : Polynomial (PuiseuxSeries R) :=
  C (puiseuxMonomial (-1)) * (exP.comp (C (puiseuxMonomial (1 / 3)) * (1 + X)))

/-! ### The monomial-coefficient reductions -/

theorem cf0 : (puiseuxMonomial (-1) * puiseuxMonomial 1 : PuiseuxSeries R) = 1 := by
  rw [puiseuxMonomial_mul, show (-1 : ℚ) + 1 = 0 by norm_num, puiseuxMonomial_zero]

theorem cf2 :
    (puiseuxMonomial (-1) * -(2 * (puiseuxMonomial 1 : PuiseuxSeries R) ^ 2)
      * puiseuxMonomial (2 / 3)) = -(2 * puiseuxMonomial (5 / 3)) := by
  rw [mono_pow, show ((2 : ℕ) : ℚ) * 1 = 2 by norm_num,
    show puiseuxMonomial (-1) * -(2 * puiseuxMonomial (2 : ℚ)) * puiseuxMonomial (2 / 3)
      = -(2 * (puiseuxMonomial (-1) * puiseuxMonomial 2 * puiseuxMonomial (2 / 3))) by ring,
    puiseuxMonomial_mul, puiseuxMonomial_mul, show (-1 : ℚ) + 2 + 2 / 3 = 5 / 3 by norm_num]

theorem cf3 : (puiseuxMonomial (-1) * -1 * puiseuxMonomial 1 : PuiseuxSeries R) = -1 := by
  rw [show puiseuxMonomial (-1) * -1 * puiseuxMonomial 1
    = -(puiseuxMonomial (-1) * puiseuxMonomial 1) by ring, cf0]

/-- **The explicit expansion of `P₁`** (BPR Example 2.96). -/
theorem exP1_eq :
    (exP1 : Polynomial (PuiseuxSeries R))
      = C (puiseuxMonomial (5 / 3)) * X ^ 5
        + C (puiseuxMonomial (4 / 3) + 5 * puiseuxMonomial (5 / 3)) * X ^ 4
        + C (-1 + 4 * puiseuxMonomial (4 / 3) + 10 * puiseuxMonomial (5 / 3)) * X ^ 3
        + C (-3 + 8 * puiseuxMonomial (5 / 3) + 6 * puiseuxMonomial (4 / 3)) * X ^ 2
        + C (puiseuxMonomial (5 / 3) - 3 + 4 * puiseuxMonomial (4 / 3)) * X
        + C (-puiseuxMonomial (5 / 3) + puiseuxMonomial (4 / 3)) := by
  rw [exP1, exP, eps_mono]
  simp only [add_comp, monomial_comp, pow_zero, mul_one]
  rw [subpow 2, subpow 3, subpow 4, subpow 5]
  simp only [mul_add, ← mul_assoc, ← map_mul]
  rw [show ((2 : ℕ) : ℚ) / 3 = 2 / 3 by norm_num, show ((3 : ℕ) : ℚ) / 3 = 1 by norm_num,
    show ((4 : ℕ) : ℚ) / 3 = 4 / 3 by norm_num, show ((5 : ℕ) : ℚ) / 3 = 5 / 3 by norm_num,
    cf0, cf2, cf3]
  simp only [one_mul, map_one, map_neg, map_mul, map_ofNat, map_add, map_sub]
  ring

/-! ### The coefficients `bᵢ` and Lemma 2.95(a) -/

/-- `b₀ = −ε^{5/3} + ε^{4/3}`. -/
theorem exP1_coeff0 :
    (exP1 : Polynomial (PuiseuxSeries R)).coeff 0 = -puiseuxMonomial (5 / 3) + puiseuxMonomial (4 / 3) := by
  rw [exP1_eq]; simp [coeff_C, coeff_C_mul, coeff_X_pow]

/-- `b₁ = ε^{5/3} − 3 + 4ε^{4/3}`. -/
theorem exP1_coeff1 :
    (exP1 : Polynomial (PuiseuxSeries R)).coeff 1
      = puiseuxMonomial (5 / 3) - 3 + 4 * puiseuxMonomial (4 / 3) := by
  rw [exP1_eq]; simp [add_mul, sub_mul, mul_assoc, coeff_C, coeff_C_mul, coeff_X_pow, coeff_X]

/-- The order of a Puiseux series is unchanged by negation. -/
theorem puiseuxOrder_neg (a : PuiseuxSeries R) : puiseuxOrder R (-a) = puiseuxOrder R a := by
  rw [puiseuxOrder, puiseuxOrder, Subfield.coe_neg, HahnSeries.orderTop_neg]

/-- **Lemma 2.95(a), the `o(b₀) > 0` case** for this example: `o(b₀) = 4/3 > 0`. -/
theorem order_exP1_coeff0 :
    puiseuxOrder R (exP1.coeff 0) = ((4 / 3 : ℚ) : WithTop ℚ) := by
  rw [exP1_coeff0,
    puiseuxOrder_add_of_ne _ _ (by
      rw [puiseuxOrder_neg, puiseuxOrder_puiseuxMonomial, puiseuxOrder_puiseuxMonomial]
      norm_num),
    puiseuxOrder_neg, puiseuxOrder_puiseuxMonomial, puiseuxOrder_puiseuxMonomial,
    min_eq_right (by rw [WithTop.coe_le_coe]; norm_num)]

theorem puiseuxOrder_three : puiseuxOrder R (3 : PuiseuxSeries R) = 0 := by
  have h : ((3 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 3 := by
    rw [show ((3 : PuiseuxSeries R) : HahnSeries ℚ R) = (3 : HahnSeries ℚ R) from by norm_cast,
      ← HahnSeries.C_apply, map_ofNat]
  rw [puiseuxOrder, h, HahnSeries.orderTop_single (by norm_num : (3 : R) ≠ 0)]; rfl

theorem puiseuxOrder_four : puiseuxOrder R (4 : PuiseuxSeries R) = 0 := by
  have h : ((4 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 4 := by
    rw [show ((4 : PuiseuxSeries R) : HahnSeries ℚ R) = (4 : HahnSeries ℚ R) from by norm_cast,
      ← HahnSeries.C_apply, map_ofNat]
  rw [puiseuxOrder, h, HahnSeries.orderTop_single (by norm_num : (4 : R) ≠ 0)]; rfl

/-- **Lemma 2.95(a), the `o(b_r) = 0` case** for this example (`r = 1`): `o(b₁) = 0`, because the
order-`0` constant `−3` (the value `Q'(1)` of the multiplicity-`1` root) survives. -/
theorem order_exP1_coeff1 : puiseuxOrder R (exP1.coeff 1) = 0 := by
  rw [exP1_coeff1]
  have hm3 : puiseuxOrder R (puiseuxMonomial (5 / 3) - 3 : PuiseuxSeries R) = 0 := by
    rw [sub_eq_add_neg,
      puiseuxOrder_add_of_ne _ _ (by
        rw [puiseuxOrder_puiseuxMonomial, puiseuxOrder_neg, puiseuxOrder_three]
        exact_mod_cast (by norm_num : (5 / 3 : ℚ) ≠ 0)),
      puiseuxOrder_puiseuxMonomial, puiseuxOrder_neg, puiseuxOrder_three,
      min_eq_right (by exact_mod_cast (by norm_num : (0 : ℚ) ≤ 5 / 3))]
  have h4m : puiseuxOrder R (4 * puiseuxMonomial (4 / 3) : PuiseuxSeries R)
      = ((4 / 3 : ℚ) : WithTop ℚ) := by
    rw [puiseuxOrder_mul, puiseuxOrder_four, puiseuxOrder_puiseuxMonomial, zero_add]
  rw [puiseuxOrder_add_of_ne _ _ (by
      rw [hm3, h4m]; exact_mod_cast (by norm_num : (0 : ℚ) ≠ 4 / 3)),
    hm3, h4m, min_eq_left (by exact_mod_cast (by norm_num : (0 : ℚ) ≤ 4 / 3))]

/-! ### The Newton diagram of `P₁` -/

theorem exP1_coeff2 : (exP1 : Polynomial (PuiseuxSeries R)).coeff 2
    = -3 + 8 * puiseuxMonomial (5 / 3) + 6 * puiseuxMonomial (4 / 3) := by
  rw [exP1_eq]; simp [add_mul, sub_mul, mul_assoc, coeff_C, coeff_C_mul, coeff_X_pow, coeff_X]

theorem exP1_coeff3 : (exP1 : Polynomial (PuiseuxSeries R)).coeff 3
    = -1 + 4 * puiseuxMonomial (4 / 3) + 10 * puiseuxMonomial (5 / 3) := by
  rw [exP1_eq]; simp [add_mul, sub_mul, mul_assoc, coeff_C, coeff_C_mul, coeff_X_pow, coeff_X]

theorem exP1_coeff4 : (exP1 : Polynomial (PuiseuxSeries R)).coeff 4
    = puiseuxMonomial (4 / 3) + 5 * puiseuxMonomial (5 / 3) := by
  rw [exP1_eq]; simp [add_mul, sub_mul, mul_assoc, coeff_C, coeff_C_mul, coeff_X_pow, coeff_X]

theorem exP1_coeff5 : (exP1 : Polynomial (PuiseuxSeries R)).coeff 5 = puiseuxMonomial (5 / 3) := by
  rw [exP1_eq]; simp [add_mul, sub_mul, mul_assoc, coeff_C, coeff_C_mul, coeff_X_pow, coeff_X]

/-- The Laurent coercion of an `OfNat` constant is the corresponding single term at exponent `0`. -/
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((OfNat.ofNat n : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 (OfNat.ofNat n) := by
  rw [show ((OfNat.ofNat n : PuiseuxSeries R) : HahnSeries ℚ R) = (OfNat.ofNat n : HahnSeries ℚ R)
    from by norm_cast, ← HahnSeries.C_apply, map_ofNat]

theorem coe_ofNat_mul_mono (n : ℕ) [n.AtLeastTwo] (ξ : ℚ) :
    ((OfNat.ofNat n * puiseuxMonomial ξ : PuiseuxSeries R) : HahnSeries ℚ R)
      = HahnSeries.single ξ (OfNat.ofNat n) := by
  rw [Subfield.coe_mul, coe_ofNat, coe_puiseuxMonomial, HahnSeries.single_mul_single, zero_add,
    mul_one]

theorem coe_neg_one : ((-1 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 (-1) := by
  rw [show ((-1 : PuiseuxSeries R) : HahnSeries ℚ R) = (-1 : HahnSeries ℚ R) from by norm_cast,
    ← HahnSeries.C_apply]; norm_num

theorem coe_neg_three : ((-3 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 (-3) := by
  rw [show (-3 : PuiseuxSeries R) = -(3 : PuiseuxSeries R) from rfl, Subfield.coe_neg, coe_ofNat,
    ← HahnSeries.single_neg]

theorem coe_b0 : ((exP1.coeff 0 : PuiseuxSeries R) : HahnSeries ℚ R)
    = -HahnSeries.single (5 / 3) 1 + HahnSeries.single (4 / 3) 1 := by
  rw [exP1_coeff0, Subfield.coe_add, Subfield.coe_neg, coe_puiseuxMonomial, coe_puiseuxMonomial]

theorem coe_b1 : ((exP1.coeff 1 : PuiseuxSeries R) : HahnSeries ℚ R)
    = HahnSeries.single (5 / 3) 1 - HahnSeries.single 0 3 + HahnSeries.single (4 / 3) 4 := by
  rw [exP1_coeff1, Subfield.coe_add, Subfield.coe_sub, coe_puiseuxMonomial, coe_ofNat,
    coe_ofNat_mul_mono]

theorem coe_b2 : ((exP1.coeff 2 : PuiseuxSeries R) : HahnSeries ℚ R)
    = HahnSeries.single 0 (-3) + HahnSeries.single (5 / 3) 8 + HahnSeries.single (4 / 3) 6 := by
  rw [exP1_coeff2, Subfield.coe_add, Subfield.coe_add, coe_neg_three, coe_ofNat_mul_mono,
    coe_ofNat_mul_mono]

theorem coe_b3 : ((exP1.coeff 3 : PuiseuxSeries R) : HahnSeries ℚ R)
    = HahnSeries.single 0 (-1) + HahnSeries.single (4 / 3) 4 + HahnSeries.single (5 / 3) 10 := by
  rw [exP1_coeff3, Subfield.coe_add, Subfield.coe_add, coe_neg_one, coe_ofNat_mul_mono,
    coe_ofNat_mul_mono]

theorem coe_b4 : ((exP1.coeff 4 : PuiseuxSeries R) : HahnSeries ℚ R)
    = HahnSeries.single (4 / 3) 1 + HahnSeries.single (5 / 3) 5 := by
  rw [exP1_coeff4, Subfield.coe_add, coe_puiseuxMonomial, coe_ofNat_mul_mono]

theorem coe_b5 : ((exP1.coeff 5 : PuiseuxSeries R) : HahnSeries ℚ R)
    = HahnSeries.single (5 / 3) 1 := by
  rw [exP1_coeff5, coe_puiseuxMonomial]

/-- **The Newton diagram of `P₁`** (Example 2.96 continued): the 14 points
`{(i, r) : r ∈ supp(b_i)}`, three per middle column and two/one at the ends. -/
theorem exP1_newtonDiagram :
    newtonDiagram (exP1 (R := R)) = {(0, 4/3), (0, 5/3), (1, 0), (1, 4/3), (1, 5/3),
      (2, 0), (2, 4/3), (2, 5/3), (3, 0), (3, 4/3), (3, 5/3), (4, 4/3), (4, 5/3), (5, 5/3)} := by
  ext ⟨i, r⟩
  simp only [mem_newtonDiagram, newtonCoeff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  rcases Nat.lt_or_ge i 6 with hlt | hge
  · interval_cases i
    · rw [coe_b0, HahnSeries.coeff_add, HahnSeries.coeff_neg, HahnSeries.coeff_single,
        HahnSeries.coeff_single]; norm_num
      constructor
      · intro h; by_contra hc; push Not at hc; rw [if_neg (by tauto), if_neg (by tauto)] at h; simp at h
      · rintro (rfl | rfl) <;> norm_num
    · rw [coe_b1, HahnSeries.coeff_add, HahnSeries.coeff_sub, HahnSeries.coeff_single,
        HahnSeries.coeff_single, HahnSeries.coeff_single]; norm_num
      constructor
      · intro h; by_contra hc; push Not at hc
        rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)] at h; simp at h
      · rintro (rfl | rfl | rfl) <;> norm_num
    · rw [coe_b2, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
        HahnSeries.coeff_single, HahnSeries.coeff_single]; norm_num
      constructor
      · intro h; by_contra hc; push Not at hc
        rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)] at h; simp at h
      · rintro (rfl | rfl | rfl) <;> norm_num
    · rw [coe_b3, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
        HahnSeries.coeff_single, HahnSeries.coeff_single]; norm_num
      constructor
      · intro h; by_contra hc; push Not at hc
        rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)] at h; simp at h
      · rintro (rfl | rfl | rfl) <;> norm_num
    · rw [coe_b4, HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single]; norm_num
      constructor
      · intro h; by_contra hc; push Not at hc; rw [if_neg (by tauto), if_neg (by tauto)] at h; simp at h
      · rintro (rfl | rfl) <;> norm_num
    · rw [coe_b5, HahnSeries.coeff_single]; norm_num
  · rw [show (exP1 (R := R)).coeff i = 0 from Polynomial.coeff_eq_zero_of_natDegree_lt (by
      have hd : (exP1 (R := R)).natDegree ≤ 5 := by rw [exP1_eq]; compute_degree!
      omega)]
    simp only [ZeroMemClass.coe_zero, HahnSeries.coeff_zero, ne_eq, not_true_eq_false, false_iff]
    rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> omega

end Azurite.BPR

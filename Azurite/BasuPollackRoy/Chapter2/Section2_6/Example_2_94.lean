import Azurite.BasuPollackRoy.Chapter2.Section2_6.CharacteristicPolynomial
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Infinitesimal

/-! # BPR §2.6 Example 2.94 — a Newton diagram

For `P(X) = ε − 2ε²X² − X³ + εX⁴ + εX⁵ ∈ R⟨⟨ε⟩⟩[X]` we compute the Newton diagram. Each `Xⁱ`
coefficient is a single ε-monomial, so each nonzero column contributes one point, and the Newton
diagram is `{(0,1), (2,2), (3,0), (4,1), (5,1)}`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- The polynomial `P(X) = ε − 2ε²X² − X³ + εX⁴ + εX⁵` of Example 2.94. -/
noncomputable def exP : Polynomial (PuiseuxSeries R) :=
  monomial 0 puiseuxEps + monomial 2 (-(2 * puiseuxEps ^ 2))
    + monomial 3 (-1) + monomial 4 puiseuxEps + monomial 5 puiseuxEps

/-- `ε²` is the Puiseux monomial `ε^{2/1}`. -/
theorem coe_eps_sq :
    ((puiseuxEps ^ 2 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 2 1 := by
  rw [SubmonoidClass.coe_pow, puiseuxEps_coe, sq, HahnSeries.single_mul_single]; norm_num

/-- A single term `single e c` (with `c ≠ 0`) is nonzero at `ε^r` exactly when `r = e`. -/
theorem single_coeff_ne_zero_iff {e r : ℚ} {c : R} (hc : c ≠ 0) :
    (HahnSeries.single e c).coeff r ≠ 0 ↔ r = e := by
  rw [HahnSeries.coeff_single]; split <;> simp_all

theorem coe_coeff0 :
    ((exP.coeff 0 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 1 1 := by
  rw [show (exP (R := R)).coeff 0 = puiseuxEps from by simp [exP, coeff_monomial], puiseuxEps_coe]

theorem coe_coeff4 :
    ((exP.coeff 4 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 1 1 := by
  rw [show (exP (R := R)).coeff 4 = puiseuxEps from by simp [exP, coeff_monomial], puiseuxEps_coe]

theorem coe_coeff5 :
    ((exP.coeff 5 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 1 1 := by
  rw [show (exP (R := R)).coeff 5 = puiseuxEps from by simp [exP, coeff_monomial], puiseuxEps_coe]

theorem coe_coeff2 :
    ((exP.coeff 2 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 2 (-2) := by
  rw [show (exP (R := R)).coeff 2 = -(2 * puiseuxEps ^ 2) from by simp [exP, coeff_monomial],
    Subfield.coe_neg, Subfield.coe_mul, coe_eps_sq,
    show ((2 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 2 from by
      rw [show ((2 : PuiseuxSeries R) : HahnSeries ℚ R) = (2 : HahnSeries ℚ R) from by norm_cast,
        ← HahnSeries.C_apply, map_ofNat],
    HahnSeries.single_mul_single, ← HahnSeries.single_neg]
  norm_num

theorem coe_coeff3 :
    ((exP.coeff 3 : PuiseuxSeries R) : HahnSeries ℚ R) = HahnSeries.single 0 (-1) := by
  rw [show (exP (R := R)).coeff 3 = -1 from by simp [exP, coeff_monomial],
    show ((-1 : PuiseuxSeries R) : HahnSeries ℚ R) = (-1 : HahnSeries ℚ R) from by norm_cast,
    ← HahnSeries.C_apply]
  norm_num

/-- **The Newton diagram of `P` (Example 2.94)** is `{(0,1), (2,2), (3,0), (4,1), (5,1)}`. -/
theorem exP_newtonDiagram [CharZero R] :
    newtonDiagram (exP (R := R)) = {(0, 1), (2, 2), (3, 0), (4, 1), (5, 1)} := by
  ext ⟨i, r⟩
  simp only [mem_newtonDiagram, newtonCoeff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  rcases Nat.lt_or_ge i 6 with hlt | hge
  · interval_cases i
    · rw [coe_coeff0, single_coeff_ne_zero_iff (one_ne_zero)]; simp
    · rw [show (exP (R := R)).coeff 1 = 0 from by simp [exP, coeff_monomial]]; simp
    · rw [coe_coeff2, single_coeff_ne_zero_iff (by norm_num : (-2 : R) ≠ 0)]; simp
    · rw [coe_coeff3, single_coeff_ne_zero_iff (by norm_num : (-1 : R) ≠ 0)]; simp
    · rw [coe_coeff4, single_coeff_ne_zero_iff (one_ne_zero)]; simp
    · rw [coe_coeff5, single_coeff_ne_zero_iff (one_ne_zero)]; simp
  · rw [show (exP (R := R)).coeff i = 0 from by
        simp only [exP, coeff_add, coeff_monomial]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        ring]
    simp only [ZeroMemClass.coe_zero, HahnSeries.coeff_zero, ne_eq, not_true_eq_false, false_iff]
    rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> omega

/-! ## Orders, initial coefficients, and slopes -/

theorem order0 : puiseuxOrder R (exP.coeff 0 : PuiseuxSeries R) = ((1 : ℚ) : WithTop ℚ) := by
  rw [puiseuxOrder, coe_coeff0, HahnSeries.orderTop_single one_ne_zero]

theorem order1 : puiseuxOrder R (exP.coeff 1 : PuiseuxSeries R) = ⊤ := by
  rw [show (exP (R := R)).coeff 1 = 0 from by simp [exP, coeff_monomial], puiseuxOrder]; simp

theorem order2 [CharZero R] :
    puiseuxOrder R (exP.coeff 2 : PuiseuxSeries R) = ((2 : ℚ) : WithTop ℚ) := by
  rw [puiseuxOrder, coe_coeff2, HahnSeries.orderTop_single (by norm_num : (-2 : R) ≠ 0)]

theorem order3 : puiseuxOrder R (exP.coeff 3 : PuiseuxSeries R) = ((0 : ℚ) : WithTop ℚ) := by
  rw [puiseuxOrder, coe_coeff3, HahnSeries.orderTop_single (by norm_num : (-1 : R) ≠ 0)]

theorem order4 : puiseuxOrder R (exP.coeff 4 : PuiseuxSeries R) = ((1 : ℚ) : WithTop ℚ) := by
  rw [puiseuxOrder, coe_coeff4, HahnSeries.orderTop_single one_ne_zero]

theorem order5 : puiseuxOrder R (exP.coeff 5 : PuiseuxSeries R) = ((1 : ℚ) : WithTop ℚ) := by
  rw [puiseuxOrder, coe_coeff5, HahnSeries.orderTop_single one_ne_zero]

theorem initCoeff0 : puiseuxInitCoeff R (exP.coeff 0 : PuiseuxSeries R) = 1 := by
  rw [puiseuxInitCoeff, coe_coeff0, HahnSeries.leadingCoeff_of_single]

theorem initCoeff3 : puiseuxInitCoeff R (exP.coeff 3 : PuiseuxSeries R) = -1 := by
  rw [puiseuxInitCoeff, coe_coeff3, HahnSeries.leadingCoeff_of_single]

theorem initCoeff5 : puiseuxInitCoeff R (exP.coeff 5 : PuiseuxSeries R) = 1 := by
  rw [puiseuxInitCoeff, coe_coeff5, HahnSeries.leadingCoeff_of_single]

/-- The slope of the edge `E = [M₀, M₃] = [(0,1), (3,0)]` is `−1/3` (so `ξ_E = 1/3`). -/
theorem slope_E : newtonSlope ((0 : ℕ), (1 : ℚ)) ((3 : ℕ), (0 : ℚ)) = -1 / 3 := by
  rw [newtonSlope]; norm_num

/-- The slope of the edge `F = [M₃, M₅] = [(3,0), (5,1)]` is `1/2` (so `ξ_F = −1/2`). -/
theorem slope_F : newtonSlope ((3 : ℕ), (0 : ℚ)) ((5 : ℕ), (1 : ℚ)) = 1 / 2 := by
  rw [newtonSlope]; norm_num

/-! ## The two edges and their characteristic polynomials -/

open Classical in
/-- The columns whose points lie on the edge `E = [(0,1), (3,0)]` are `0` and `3`. -/
theorem filter_E [CharZero R] :
    (Finset.Icc (0 : ℕ) 3).filter (colOnLine (exP (R := R)) ((0 : ℕ), (1 : ℚ)) ((3 : ℕ), (0 : ℚ)))
      = {0, 3} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, hn3⟩, hcol⟩
    interval_cases n
    · exact Or.inl rfl
    · rw [colOnLine, order1] at hcol; exact absurd hcol WithTop.top_ne_coe
    · rw [colOnLine, order2, show lineValue ((0 : ℕ), (1 : ℚ)) ((3 : ℕ), (0 : ℚ)) 2 = 1 / 3 from by
        rw [lineValue, slope_E]; norm_num] at hcol
      exact absurd (WithTop.coe_inj.mp hcol) (by norm_num)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨by omega, colOnLine_left order0⟩
    · exact ⟨by omega, colOnLine_right (by norm_num) order3⟩

open Classical in
/-- The columns whose points lie on the edge `F = [(3,0), (5,1)]` are `3` and `5`. -/
theorem filter_F :
    (Finset.Icc (3 : ℕ) 5).filter (colOnLine (exP (R := R)) ((3 : ℕ), (0 : ℚ)) ((5 : ℕ), (1 : ℚ)))
      = {3, 5} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn3, _⟩, hcol⟩
    interval_cases n
    · exact Or.inl rfl
    · rw [colOnLine, order4, show lineValue ((3 : ℕ), (0 : ℚ)) ((5 : ℕ), (1 : ℚ)) 4 = 1 / 2 from by
        rw [lineValue, slope_F]; norm_num] at hcol
      exact absurd (WithTop.coe_inj.mp hcol) (by norm_num)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨by omega, colOnLine_left order3⟩
    · exact ⟨by omega, colOnLine_right (by norm_num) order5⟩

/-- **`Q(P, E, X) = 1 − X³`** for the edge `E = [M₀, M₃]`. -/
theorem charPoly_E [CharZero R] :
    charPoly (exP (R := R)) ((0 : ℕ), (1 : ℚ)) ((3 : ℕ), (0 : ℚ)) = 1 - X ^ 3 := by
  rw [charPoly, filter_E, Finset.sum_insert (by norm_num), Finset.sum_singleton, initCoeff0,
    initCoeff3, Polynomial.monomial_zero_left, map_one,
    show monomial 3 (-1 : R) = -X ^ 3 from by rw [← C_mul_X_pow_eq_monomial]; simp]
  ring

/-- **`Q(P, F, X) = X³(X² − 1) = X⁵ − X³`** for the edge `F = [M₃, M₅]`. -/
theorem charPoly_F :
    charPoly (exP (R := R)) ((3 : ℕ), (0 : ℚ)) ((5 : ℕ), (1 : ℚ)) = X ^ 5 - X ^ 3 := by
  rw [charPoly, filter_F, Finset.sum_insert (by norm_num), Finset.sum_singleton, initCoeff3,
    initCoeff5, show monomial 3 (-1 : R) = -X ^ 3 from by rw [← C_mul_X_pow_eq_monomial]; simp,
    show monomial 5 (1 : R) = X ^ 5 from by rw [← C_mul_X_pow_eq_monomial]; simp]
  ring

/-! ## The full Newton-polygon certificate -/

theorem puiseuxEps_ne_zero : (puiseuxEps : PuiseuxSeries R) ≠ 0 := by
  intro h
  have hz : (HahnSeries.single (1 : ℚ) (1 : R)) = 0 := by rw [← puiseuxEps_coe, h]; simp
  exact HahnSeries.single_ne_zero (one_ne_zero) hz

/-- The degree of `P` is `5` (the leading term is `εX⁵`). -/
theorem natDegree_exP : (exP (R := R)).natDegree = 5 := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    simp only [exP, coeff_add, coeff_monomial]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    ring
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [show (exP (R := R)).coeff 5 = puiseuxEps from by simp [exP, coeff_monomial]]
    exact puiseuxEps_ne_zero

/-- Every point of the Newton diagram lies on or above the edge `E = [(0,1), (3,0)]`. -/
theorem onOrAbove_E [CharZero R] :
    ∀ Q ∈ newtonDiagram (exP (R := R)), OnOrAbove ((0 : ℕ), (1 : ℚ)) ((3 : ℕ), (0 : ℚ)) Q := by
  intro Q hQ
  rw [exP_newtonDiagram] at hQ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl <;> (rw [onOrAbove_iff, slope_E]; norm_num)

/-- Every point of the Newton diagram lies on or above the edge `F = [(3,0), (5,1)]`. -/
theorem onOrAbove_F [CharZero R] :
    ∀ Q ∈ newtonDiagram (exP (R := R)), OnOrAbove ((3 : ℕ), (0 : ℚ)) ((5 : ℕ), (1 : ℚ)) Q := by
  intro Q hQ
  rw [exP_newtonDiagram] at hQ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl <;> (rw [onOrAbove_iff, slope_F]; norm_num)

/-- **The list `[M₀, M₃, M₅] = [(0,1), (3,0), (5,1)]` is a Newton polygon of `P`** (Example
2.94): a full `IsNewtonPolygon` certificate. -/
theorem exP_isNewtonPolygon [CharZero R] :
    IsNewtonPolygon (exP (R := R)) [((0 : ℕ), (1 : ℚ)), (3, 0), (5, 1)] where
  isColumnPoint := by intro V hV; fin_cases hV <;> [exact order0; exact order3; exact order5]
  head_eq := ⟨1, rfl⟩
  getLast_eq := ⟨1, by rw [natDegree_exP]; rfl⟩
  strictMono_fst := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]; omega
  diagram_onOrAbove := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨onOrAbove_E, onOrAbove_F⟩
  convex := by
    simp only [List.tail_cons, List.zip_cons_cons, List.zip_nil_right, List.isChain_cons_cons,
      List.isChain_singleton, and_true]
    rw [onOrAbove_iff, slope_E]; norm_num

end Azurite.BPR

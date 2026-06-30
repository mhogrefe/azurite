import Azurite.AzPolynomial.Resultant
import Azurite.AzPolynomial.Equiv.SignedSubresultant
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_27
import Azurite.BasuPollackRoy.Chapter4.Section4_2.ResReduce
import Azurite.AzPolynomial.MvCoeffParse
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzMvPolynomial.Equiv.ExactDivCR
import Azurite.AzMvPolynomial.ToString

/-!
# Correctness of `AzPolynomial.resultant` (BPR Exercise 8.2)

`resultant P Q = Res (toPoly P) (toPoly Q)` over an integral domain with computable exact division.
The proof assembles:
* `resultantGt_eq` (the `deg Q < deg P` case): the constant subcase via `resultant_C_right`, the
  `deg Q ≥ 1` subcase via `signedSubresultant_toPoly_domain` (`s₀ = sRes₀`) and
  `sRes_zero_eq_eps_mul_Res` (`Res = ε_p · sRes₀`);
* the swap (`resultant_comm`) and the equal-degree `Q₁` reduction (`leadingCoeff_pow_mul_Res_eq`).
-/

namespace Azurite.AzPolynomial

open Azurite.BPR.Chapter4 Polynomial _root_.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R] [IsDomain R]

/-- Correctness of `resultantGt` (when `deg Q < deg P`). -/
theorem resultantGt_eq (P Q : AzPolynomial R) (hpq : Q.natDegree < P.natDegree) :
    resultantGt P Q = Res (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
  have hpd : (toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
  have hqd : (toPoly Q).natDegree = Q.natDegree := AzPolynomial.natDegree_toPoly Q
  have hPm : toPoly P ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hpd; omega
  unfold resultantGt
  split_ifs with hq0
  · -- `deg Q = 0`: constant, `Res = (Q₀)^{deg P}`.
    have hqd0 : (toPoly Q).natDegree = 0 := by rw [hqd, hq0]
    rw [Res_eq_resultant, hqd0, hpd,
      show Q.coeff 0 = (toPoly Q).coeff 0 from (coeff_toPoly_eq Q 0).symm,
      Polynomial.eq_C_of_natDegree_eq_zero hqd0, Polynomial.resultant_C_right]
    simp
  · -- `deg Q ≥ 1`: `Res = ε_p · sRes₀`.
    have hq1 : 1 ≤ Q.natDegree := by omega
    have hQm : toPoly Q ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hqd; omega
    have hPne : P ≠ 0 := fun h => hPm (by rw [h]; exact toPoly_zero)
    have hQne : Q ≠ 0 := fun h => hQm (by rw [h]; exact toPoly_zero)
    rw [(signedSubresultant_toPoly_domain P Q hPne hQne hpq hq1).2,
      show ((List.range (P.natDegree + 1)).map (sRes (toPoly P) (toPoly Q))).headD 0
          = sRes (toPoly P) (toPoly Q) 0 from by rw [List.range_succ_eq_map]; simp,
      sRes_zero_eq_eps_mul_Res, hpd,
      show (epsilonSign P.natDegree : R) = ((ε P.natDegree : ℤ) : R) from by
        rw [epsilonSign_eq, ε]; push_cast; ring,
      ← mul_assoc, ← Int.cast_mul,
      show ε P.natDegree * ε P.natDegree = 1 from by
        rw [ε, ← pow_add]; exact Even.neg_one_pow ⟨_, rfl⟩,
      Int.cast_one, one_mul]

/-- **BPR Exercise 8.2 (correctness).**  The computable `resultant P Q` equals the BPR resultant
    `Res (toPoly P) (toPoly Q)`, for `P ≠ 0`. -/
theorem resultant_eq (P Q : AzPolynomial R) (hP : AzPolynomial.toPoly P ≠ 0) :
    resultant P Q = Res (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
  have hpd : (toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
  have hqd : (toPoly Q).natDegree = Q.natDegree := AzPolynomial.natDegree_toPoly Q
  unfold resultant
  split_ifs with h1 h2 h3
  · -- `deg Q < deg P`
    exact resultantGt_eq P Q h1
  · -- `deg P < deg Q`: swap.
    rw [resultantGt_eq Q P h2, Res_eq_resultant (toPoly P) (toPoly Q),
      Polynomial.resultant_comm, ← Res_eq_resultant (toPoly Q) (toPoly P), hpd, hqd]
  · -- `deg P = deg Q = 0`: two constants, `Res = 1`.
    have hqd0 : (toPoly Q).natDegree = 0 := by rw [hqd]; omega
    have hpd0 : (toPoly P).natDegree = 0 := by rw [hpd]; exact h3
    rw [Res_eq_resultant, hpd0, hqd0, Polynomial.eq_C_of_natDegree_eq_zero hqd0,
      Polynomial.resultant_C_right]
    simp
  · -- `deg P = deg Q ≥ 1`: the `Q₁` reduction.
    have hpq_eq : P.natDegree = Q.natDegree := by omega
    set Q₁ := P.leadingCoeff • Q - Q.leadingCoeff • P with hQ₁def
    have htoPolyQ₁ : toPoly Q₁
        = Polynomial.C (toPoly P).leadingCoeff * toPoly Q - Polynomial.C (toPoly Q).leadingCoeff * toPoly P := by
      rw [hQ₁def, toPoly_sub, toPoly_smul, toPoly_smul, Polynomial.smul_eq_C_mul,
        Polynomial.smul_eq_C_mul, leadingCoeff_toPoly, leadingCoeff_toPoly]
    have hpq' : (toPoly P).natDegree = (toPoly Q).natDegree := by rw [hpd, hqd]; exact hpq_eq
    -- `deg Q₁ < deg P` (leading terms cancel).
    have hr : Q₁.natDegree < P.natDegree := by
      rw [← AzPolynomial.natDegree_toPoly Q₁, htoPolyQ₁, ← hpd]
      have hle : (Polynomial.C (toPoly P).leadingCoeff * toPoly Q
          - Polynomial.C (toPoly Q).leadingCoeff * toPoly P).natDegree ≤ (toPoly P).natDegree :=
        (natDegree_sub_le _ _).trans (max_le
          ((natDegree_C_mul_le _ _).trans (le_of_eq hpq'.symm)) (natDegree_C_mul_le _ _))
      have hcoeff : (Polynomial.C (toPoly P).leadingCoeff * toPoly Q
          - Polynomial.C (toPoly Q).leadingCoeff * toPoly P).coeff (toPoly P).natDegree = 0 := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
          show (toPoly Q).coeff (toPoly P).natDegree = (toPoly Q).leadingCoeff from by
            rw [hpq']; rfl,
          show (toPoly P).coeff (toPoly P).natDegree = (toPoly P).leadingCoeff from rfl]
        ring
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have hz : Polynomial.C (toPoly P).leadingCoeff * toPoly Q - Polynomial.C (toPoly Q).leadingCoeff * toPoly P = 0 :=
          leadingCoeff_eq_zero.mp (by rw [Polynomial.leadingCoeff, h, hcoeff])
        rw [hz, Polynomial.natDegree_zero] at h
        rw [hpd] at h; omega
    rw [resultantGt_eq P Q₁ hr]
    have hid := leadingCoeff_pow_mul_Res_eq (toPoly P) (toPoly Q) hP hpq'
    rw [← htoPolyQ₁, AzPolynomial.natDegree_toPoly, leadingCoeff_toPoly] at hid
    rw [← hid]
    have hane : P.leadingCoeff ^ Q₁.natDegree ≠ 0 :=
      pow_ne_zero _ (by rw [← leadingCoeff_toPoly]; exact Polynomial.leadingCoeff_ne_zero.mpr hP)
    apply mul_right_cancel₀ hane
    rw [Azurite.ExactDiv.exactDiv_mul_self _ _ (dvd_mul_right _ _) hane]; ring

/-! ### Computational example (BPR Exercise 8.2)

The resultant of two general quadratics `a₂x² + a₁x + a₀` and `b₂x² + b₁x + b₀`, computed as
values of `AzPolynomial (AzMvPolynomial 6 AzInt)` (univariate in `x`, with coefficients in the
ring `AzInt[a₂,a₁,a₀,b₂,b₁,b₀]`).  This exercises the equal-degree branch: forming
`Q₁ = a₂·Q − b₂·P` (degree 1) and dividing the degree-`1` signed-subresultant computation by `a₂`.
The output is the classical `(a₀b₂−a₂b₀)² − (a₀b₁−a₁b₀)(a₁b₂−a₂b₁)`. -/
section Example

private abbrev MvR6 := AzMvPolynomial 6 AzInt .Degrevlex

/-- The six coefficient names, parsed/printed via `ListVar`. -/
private def quadVars : List String := ["a₂", "a₁", "a₀", "b₂", "b₁", "b₀"]

private instance : Fact quadVars.Nodup := ⟨by decide⟩
private instance : Fact (ListVar.ListVarParsable quadVars) := ⟨by decide⟩

/-- Parse a string as an `AzPolynomial MvR6` (outer variable `x`, inner variables `quadVars`). -/
private def parseQuad (s : String) : AzPolynomial MvR6 :=
  (parseStrMvCoeffWith (ListVar quadVars) (n := 6) (R := AzInt) (ord := .Degrevlex) s).getD 0

-- `Res(a₂x²+a₁x+a₀, b₂x²+b₁x+b₀) = (a₀b₂−a₂b₀)² − (a₀b₁−a₁b₀)(a₁b₂−a₂b₁)`.
#guard (resultant (parseQuad "(a₂)*x^2+(a₁)*x+(a₀)") (parseQuad "(b₂)*x^2+(b₁)*x+(b₀)")).toStrWith
      (ListVar quadVars)
    == "a₀^2*b₂^2-a₁*a₀*b₂*b₁+a₂*a₀*b₁^2+a₁^2*b₂*b₀-2*a₂*a₀*b₂*b₀-a₂*a₁*b₁*b₀+a₂^2*b₀^2"

end Example

end Azurite.AzPolynomial

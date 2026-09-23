import Azurite.BasuPollackRoy.Chapter10.Section10_1.SeparablePart

/-!
# BPR Lemma 10.13: computing the separable part as `P/gcd(P, P′)`

`lemma_10_13`: for `P ≠ 0`, the polynomial `P/gcd(P, P′)` is a separable part
of `P` (`IsSeparablePart`).

BPR's proof decomposes `P = ∏ (X − zᵢ)^{µᵢ}` over the distinct roots and
observes that each `zᵢ` is a root of `P′` of multiplicity `µᵢ − 1`, so
`gcd(P, P′) = ∏ (X − zᵢ)^{µᵢ−1}` and the quotient is `∏ (X − zᵢ)`.

The formalization runs the same computation through root multiplicities
(`rootMultiplicity_div_gcd_derivative`): from `P = gcd·(P/gcd)` the
multiplicities add; the multiplicity in the gcd is the minimum of the
multiplicities (`rootMultiplicity_gcd`, a reusable fact via the
`(X − z)^n ∣ ·` characterization); and the multiplicity of a root in `P′` is
one less than in `P` (char 0, `derivative_rootMultiplicity_of_root`) — so
every root of `P` survives in the quotient with multiplicity exactly one.
Separability then follows from distinctness of the roots
(`nodup_roots_iff_of_splits`). The constant case (`P′ = 0`) degenerates
correctly since a nonzero constant has no roots.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The root multiplicity of a gcd is the minimum of the multiplicities. -/
theorem rootMultiplicity_gcd {P Q : Polynomial (Ri R)} (hP : P ≠ 0) (hQ : Q ≠ 0) (z : Ri R) :
    rootMultiplicity z (EuclideanDomain.gcd P Q)
      = min (rootMultiplicity z P) (rootMultiplicity z Q) := by
  have hg : EuclideanDomain.gcd P Q ≠ 0 := fun h =>
    hP (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  apply le_antisymm
  · apply le_min
    · rw [Polynomial.le_rootMultiplicity_iff hP]
      exact dvd_trans (Polynomial.pow_rootMultiplicity_dvd _ z)
        (EuclideanDomain.gcd_dvd_left P Q)
    · rw [Polynomial.le_rootMultiplicity_iff hQ]
      exact dvd_trans (Polynomial.pow_rootMultiplicity_dvd _ z)
        (EuclideanDomain.gcd_dvd_right P Q)
  · rw [Polynomial.le_rootMultiplicity_iff hg]
    apply EuclideanDomain.dvd_gcd
    · exact dvd_trans (pow_dvd_pow _ (min_le_left _ _))
        (Polynomial.pow_rootMultiplicity_dvd P z)
    · exact dvd_trans (pow_dvd_pow _ (min_le_right _ _))
        (Polynomial.pow_rootMultiplicity_dvd Q z)

/-- The multiplicity computation of BPR's proof: dividing by `gcd(P, P′)`
leaves each root of `P` with multiplicity exactly one. -/
theorem rootMultiplicity_div_gcd_derivative {P : Polynomial (Ri R)} (hP : P ≠ 0) (z : Ri R) :
    rootMultiplicity z (P / EuclideanDomain.gcd P (derivative P))
      = if P.IsRoot z then 1 else 0 := by
  have : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R (Ri R))
  have hg : EuclideanDomain.gcd P (derivative P) ≠ 0 := fun h =>
    hP (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hfac : EuclideanDomain.gcd P (derivative P)
      * (P / EuclideanDomain.gcd P (derivative P)) = P :=
    EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_left _ _)
  have hdiv0 : P / EuclideanDomain.gcd P (derivative P) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hP hfac.symm
  have hadd : rootMultiplicity z P
      = rootMultiplicity z (EuclideanDomain.gcd P (derivative P))
        + rootMultiplicity z (P / EuclideanDomain.gcd P (derivative P)) := by
    conv_lhs => rw [← hfac]
    exact Polynomial.rootMultiplicity_mul (hfac.symm ▸ hP)
  rcases eq_or_ne P.natDegree 0 with hd | hd
  · -- constant case: no roots, and the quotient has none either
    have hzroot : ¬P.IsRoot z := by
      intro h
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hd
      rw [hC, Polynomial.IsRoot, Polynomial.eval_C] at h
      exact hP (by rw [hC, h, Polynomial.C_0])
    rw [ite_eq_right hzroot]
    have h0 : rootMultiplicity z P = 0 := Polynomial.rootMultiplicity_eq_zero hzroot
    omega
  · -- nonconstant case: `P′ ≠ 0` (char 0) and the min formula applies
    have hP' : derivative P ≠ 0 := by
      intro h
      exact hd (Polynomial.derivative_eq_zero.mp h)
    have hgmin := rootMultiplicity_gcd hP hP' z
    by_cases hz : P.IsRoot z
    · rw [ite_eq_left hz]
      have hm1 : 0 < rootMultiplicity z P := (Polynomial.rootMultiplicity_pos hP).mpr hz
      have hder : rootMultiplicity z (derivative P) = rootMultiplicity z P - 1 :=
        Polynomial.derivative_rootMultiplicity_of_root hz
      rw [hder] at hgmin
      omega
    · rw [ite_eq_right hz]
      have h0 : rootMultiplicity z P = 0 := Polynomial.rootMultiplicity_eq_zero hz
      omega

/-- **BPR Lemma 10.13.** The polynomial `P/gcd(P, P′)` is the separable part
of `P`. -/
theorem lemma_10_13 {P : Polynomial (Ri R)} (hP : P ≠ 0) :
    IsSeparablePart (P / EuclideanDomain.gcd P (derivative P)) P := by
  classical
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  have hg : EuclideanDomain.gcd P (derivative P) ≠ 0 := fun h =>
    hP (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hfac : EuclideanDomain.gcd P (derivative P)
      * (P / EuclideanDomain.gcd P (derivative P)) = P :=
    EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_left _ _)
  have hS0 : P / EuclideanDomain.gcd P (derivative P) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hP hfac.symm
  constructor
  · -- separable: split with pairwise distinct roots
    rw [← Polynomial.nodup_roots_iff_of_splits hS0 (IsAlgClosed.splits _),
      Multiset.nodup_iff_count_le_one]
    intro z
    rw [Polynomial.count_roots, rootMultiplicity_div_gcd_derivative hP]
    split <;> omega
  · -- same root set
    ext z
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots hS0, Polynomial.mem_roots hP]
    constructor
    · intro h
      by_contra hz
      have h1 := (Polynomial.rootMultiplicity_pos hS0).mpr h
      rw [rootMultiplicity_div_gcd_derivative hP, ite_eq_right hz] at h1
      omega
    · intro h
      rw [← Polynomial.rootMultiplicity_pos hS0,
        rootMultiplicity_div_gcd_derivative hP, ite_eq_left h]
      omega

end Azurite.BPR

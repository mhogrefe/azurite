import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_13
import Azurite.BasuPollackRoy.Chapter1.Section1_2.RootCharacterizations

/-!
# Lemma 1.14

A finite system of polynomial equations and inequations
$\{P_i = 0\} \cup \{Q_j \ne 0\}$ has a common solution in $C$ if and
only if a degree test on $\gcd(\lcode{listGcd}\,\mathcal{P},\,
\prod \mathcal{Q}^d)$ fails.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]
variable {C : Type*} [Field C]

lemma dvd_of_gcd_deg_eq [DecidableEq K] {P Q : K[X]} (hP : P ≠ 0)
    (hdeg : (gcd P Q).natDegree = P.natDegree) : P ∣ Q := by
  have h1 : gcd P Q ∣ P := gcd_dvd_left P Q
  have h2 : gcd P Q ≠ 0 := by
    intro contra
    have h : 0 ∣ P := by rw [← contra]; exact h1
    exact hP (zero_dvd_iff.mp h)
  obtain ⟨A, hA⟩ := h1
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hA
    exact hP hA
  have hdeg2 : P.natDegree = (gcd P Q).natDegree + A.natDegree := by
    calc P.natDegree = (gcd P Q * A).natDegree := by nth_rw 1 [hA]
      _ = (gcd P Q).natDegree + A.natDegree := natDegree_mul h2 hA0
  have hA_deg : A.natDegree = 0 := by omega
  have hA_unit : IsUnit A := isUnit_iff_degree_eq_zero.mpr (by
    rw [degree_eq_natDegree hA0, hA_deg, Nat.cast_zero])
  have h3 : P ∣ gcd P Q := by
    obtain ⟨u, hu⟩ := hA_unit
    use ↑(u⁻¹)
    calc gcd P Q = gcd P Q * (1 : K[X]) := (mul_one _).symm
      _ = gcd P Q * ↑(1 : K[X]ˣ) := by rw [Units.val_one]
      _ = gcd P Q * ↑(u * u⁻¹ : K[X]ˣ) := by rw [mul_inv_cancel u]
      _ = gcd P Q * (↑u * ↑(u⁻¹) : K[X]) := by rw [Units.val_mul]
      _ = (gcd P Q * ↑u) * ↑(u⁻¹) := by rw [← mul_assoc]
      _ = P * ↑(u⁻¹) := by rw [hu, ← hA]
  exact h3.trans (gcd_dvd_right P Q)

lemma lemma_1_14_core [IsAlgClosed C] [Algebra K C] [DecidableEq K] [DecidableEq C]
    {P Q : K[X]} (hP : P ≠ 0) {d : ℕ} (hd : P.natDegree < d) :
    (∃ x : C, aeval x P = 0 ∧ aeval x Q ≠ 0) ↔ (gcd P (Q ^ d)).natDegree ≠ P.natDegree := by
  constructor
  · rintro ⟨x, hx1, hx2⟩ contra
    have H_dvd : P ∣ Q ^ d := dvd_of_gcd_deg_eq hP contra
    have H_aeval : aeval x P ∣ aeval x (Q ^ d) := map_dvd (aeval x) H_dvd
    rw [hx1] at H_aeval
    have H_0 : aeval x (Q ^ d) = 0 := zero_dvd_iff.mp H_aeval
    rw [map_pow] at H_0
    have hd_pos : 0 < d := by omega
    have H_0' : aeval x Q = 0 := (pow_eq_zero_iff hd_pos.ne').mp H_0
    exact hx2 H_0'
  · intro h
    by_contra! contra
    have H1 : P ∣ Q ^ P.natDegree := (isRoot_subset_iff_dvd_pow hP).mp contra
    have H2 : Q ^ d = Q ^ P.natDegree * Q ^ (d - P.natDegree) := by
      rw [← pow_add]
      have : P.natDegree + (d - P.natDegree) = d := Nat.add_sub_of_le hd.le
      rw [this]
    have H3 : P ∣ Q ^ d := by
      rw [H2]
      exact dvd_mul_of_dvd_left H1 _
    have H_gcd : P ∣ gcd P (Q ^ d) := dvd_gcd (dvd_refl P) H3
    have H_gcd2 : gcd P (Q ^ d) ∣ P := gcd_dvd_left P (Q ^ d)
    have hP_dvd_norm : P.natDegree ≤ (gcd P (Q ^ d)).natDegree := natDegree_le_of_dvd H_gcd (by
      intro contra0
      have : 0 ∣ P := by rw [← contra0]; exact H_gcd2
      exact hP (zero_dvd_iff.mp this))
    have hnorm_dvd_P : (gcd P (Q ^ d)).natDegree ≤ P.natDegree := natDegree_le_of_dvd H_gcd2 hP
    exact h (le_antisymm hnorm_dvd_P hP_dvd_norm)

/-- BPR Lemma 1.14: Yields the non-root criteria for polynomial families using a shifted polynomial GCD algorithm equivalence bound -/
theorem lemma_1_14 [IsAlgClosed C] [Algebra K C] [DecidableEq K] [DecidableEq C]
    (P_fam Q_fam : List K[X]) (hP : listGcd P_fam ≠ 0) {d : ℕ}
    (hd : (listGcd P_fam).natDegree < d) :
    (∃ x : C, (∀ P ∈ P_fam, aeval x P = 0) ∧ (∀ Q ∈ Q_fam, aeval x Q ≠ 0)) ↔
      (gcd (listGcd P_fam) (Q_fam.prod ^ d)).natDegree ≠ (listGcd P_fam).natDegree := by
  have h_equiv : (∃ x : C, (∀ P ∈ P_fam, aeval x P = 0) ∧ (∀ Q ∈ Q_fam, aeval x Q ≠ 0)) ↔
      (∃ x : C, aeval x (listGcd P_fam) = 0 ∧ aeval x Q_fam.prod ≠ 0) := by
    constructor
    · rintro ⟨x, hP_roots, hQ_nonzero⟩
      use x
      constructor
      · exact isRoot_listGcd_iff_forall_isRoot.mpr hP_roots
      · exact not_isRoot_listProd_iff_forall_not_isRoot.mpr hQ_nonzero
    · rintro ⟨x, hP_root, hQ_prod⟩
      use x
      constructor
      · exact isRoot_listGcd_iff_forall_isRoot.mp hP_root
      · exact not_isRoot_listProd_iff_forall_not_isRoot.mp hQ_prod
  rw [h_equiv]
  exact lemma_1_14_core hP hd

end Azurite.BPR

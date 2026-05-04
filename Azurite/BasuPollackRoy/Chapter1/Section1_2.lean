import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Localization.FractionRing
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Coprime
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Corollary1_6
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_7
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_10
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Divisor
import Azurite.BasuPollackRoy.Chapter1.Section1_2.EuclideanDivision
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_5
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_6
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_7
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lcm
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11
import Azurite.BasuPollackRoy.Chapter1.Section1_2.PolynomialBasics
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_5
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_8
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_9
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Remark1_4
import Azurite.BasuPollackRoy.Chapter1.Section1_2.SRemSTermination

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 1: Algebraically Closed Fields
## Section 1.2: Euclidean Division and Greatest Common Divisor

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

In this section, C is an algebraically closed field, D is a subring of C,
and K is the quotient field of D.
-/

namespace Azurite.BPR

open Polynomial

variable {C : Type*} [Field C] [IsAlgClosed C]
variable {D : Type*} [CommRing D] [IsDomain D] [Algebra D C]
variable {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]


/-- BPR Lemma 1.10 (b): U_i V_{i+1} - V_i U_{i+1} = 1.
    Note: BPR states this is (-1)^i, but this was due to an error in their recursion
    for U and V which omitted the signed remainder negation. -/
lemma lemma_1_10_b {P Q : K[X]} (n : ℕ) (hn : ∀ i ≤ n, SRemS P Q i ≠ 0) :
    SRemU P Q n * SRemV P Q (n + 1) - SRemV P Q n * SRemU P Q (n + 1) = 1 := by
  induction n generalizing P Q with
  | zero =>
    dsimp [SRemU, SRemV]
    ring
  | succ n ih =>
    have hn_ne : SRemS P Q (n + 1) ≠ 0 := hn (n + 1) (by omega)
    have hn_ne' : ∀ i ≤ n, SRemS P Q i ≠ 0 := fun i hi => hn i (by omega)
    have ih_app := ih hn_ne'
    have H_U : SRemU P Q (n + 2) = - SRemU P Q n + (SRemS P Q n / SRemS P Q (n + 1)) * SRemU P Q (n + 1) := by
      rw [SRemU, if_neg hn_ne]
    have H_V : SRemV P Q (n + 2) = - SRemV P Q n + (SRemS P Q n / SRemS P Q (n + 1)) * SRemV P Q (n + 1) := by
      rw [SRemV, if_neg hn_ne]
    rw [H_U, H_V]
    calc SRemU P Q (n + 1) * (-SRemV P Q n + SRemS P Q n / SRemS P Q (n + 1) * SRemV P Q (n + 1)) - SRemV P Q (n + 1) * (-SRemU P Q n + SRemS P Q n / SRemS P Q (n + 1) * SRemU P Q (n + 1))
      _ = SRemU P Q n * SRemV P Q (n + 1) - SRemV P Q n * SRemU P Q (n + 1) := by ring
      _ = 1 := by rw [ih_app]

theorem proposition_1_12 {P Q: K[X]} (hP : P ≠ 0) (_hQ : Q ≠ 0) :
    (SRemU P Q (sremTermIndex P Q + 1) * P = - SRemV P Q (sremTermIndex P Q + 1) * Q) ∧
    IsLCM (SRemU P Q (sremTermIndex P Q + 1) * P) P Q := by
  obtain ⟨k, hk_def⟩ : ∃ x, x = sremTermIndex P Q := ⟨_, rfl⟩
  have hk : SRemS P Q (k + 1) = 0 := hk_def ▸ SRemS_sremTermIndex_succ_eq_zero P Q hP
  have hk_ne : SRemS P Q k ≠ 0 := hk_def ▸ SRemS_sremTermIndex_ne_zero P Q hP
  have h_le : ∀ i ≤ k, SRemS P Q i ≠ 0 := hk_def ▸ SRemS_ne_zero_of_le_sremTermIndex P Q hP
  rw [← hk_def]
  constructor
  · have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
      lemma_1_11_bezout P Q (k + 1)
    rw [hk] at hbez
    calc SRemU P Q (k + 1) * P = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q - SRemV P Q (k + 1) * Q := by ring
      _ = 0 - SRemV P Q (k + 1) * Q := by rw [← hbez]
      _ = - SRemV P Q (k + 1) * Q := by ring
  · constructor
    · exact dvd_mul_left P (SRemU P Q (k + 1))
    · constructor
      · have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
          lemma_1_11_bezout P Q (k + 1)
        rw [hk] at hbez
        have H1 : SRemU P Q (k + 1) * P = - SRemV P Q (k + 1) * Q := by
          calc SRemU P Q (k + 1) * P = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q - SRemV P Q (k + 1) * Q := by ring
            _ = 0 - SRemV P Q (k + 1) * Q := by rw [← hbez]
            _ = - SRemV P Q (k + 1) * Q := by ring
        rw [H1]
        exact dvd_mul_left Q (- SRemV P Q (k + 1))
      · intro D hDP hDQ
        obtain ⟨A, hA⟩ := hDP
        obtain ⟨B, hB⟩ := hDQ
        have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
          lemma_1_11_bezout P Q (k + 1)
        rw [hk] at hbez
        have H1 : SRemV P Q (k + 1) * Q = - SRemU P Q (k + 1) * P := by
          calc SRemV P Q (k + 1) * Q = SRemV P Q (k + 1) * Q + SRemU P Q (k + 1) * P - SRemU P Q (k + 1) * P := by ring
            _ = (SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q) - SRemU P Q (k + 1) * P := by ring
            _ = 0 - SRemU P Q (k + 1) * P := by rw [← hbez]
            _ = - SRemU P Q (k + 1) * P := by ring
        have H_alg : D = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := by
          calc D = D * 1 := by ring
            _ = D * (SRemU P Q k * SRemV P Q (k + 1) - SRemV P Q k * SRemU P Q (k + 1)) := by
                rw [← lemma_1_10_b k h_le]
            _ = D * SRemU P Q k * SRemV P Q (k + 1) - D * SRemV P Q k * SRemU P Q (k + 1) := by ring
            _ = (Q * B) * SRemU P Q k * SRemV P Q (k + 1) - (P * A) * SRemV P Q k * SRemU P Q (k + 1) := by
                have h1 : D * SRemU P Q k * SRemV P Q (k + 1) = (Q * B) * SRemU P Q k * SRemV P Q (k + 1) := by rw [hB]
                have h2 : D * SRemV P Q k * SRemU P Q (k + 1) = (P * A) * SRemV P Q k * SRemU P Q (k + 1) := by rw [hA]
                rw [h1, h2]
            _ = B * SRemU P Q k * (SRemV P Q (k + 1) * Q) - A * SRemV P Q k * (SRemU P Q (k + 1) * P) := by ring
            _ = B * SRemU P Q k * (- SRemU P Q (k + 1) * P) - A * SRemV P Q k * (SRemU P Q (k + 1) * P) := by
                rw [H1]
            _ = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := by ring
        have H_d : D = (SRemU P Q (k + 1) * P) * (- B * SRemU P Q k - A * SRemV P Q k) := by
          calc D = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := H_alg
            _ = (SRemU P Q (k + 1) * P) * (- B * SRemU P Q k - A * SRemV P Q k) := by ring
        exact ⟨_, H_d⟩


omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Definition 1.13: Greatest common divisor of a finite family of polynomials. -/
def IsListGCD (G : K[X]) (Ps : List K[X]) : Prop :=
  (∀ P ∈ Ps, G ∣ P) ∧ (∀ D, (∀ P ∈ Ps, D ∣ P) → D ∣ G)

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Algorithm to obtain the GCD of a family inductively. -/
noncomputable def listGcd (Ps : List K[X]) : K[X] :=
  Ps.foldr gcd 0

omit [IsAlgClosed C] [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- The algorithm `listGcd` satisfies the `IsListGCD` specification. -/
theorem listGcd_isListGCD (Ps : List K[X]) : IsListGCD (listGcd Ps) Ps := by
  induction Ps with
  | nil =>
    simp [IsListGCD, listGcd]
  | cons P Ps ih =>
    simp [IsListGCD, listGcd] at *
    constructor
    · constructor
      · exact (gcd_isGCD P (Ps.foldr gcd 0)).1
      · intro P' hP'
        have hG := (gcd_isGCD P (Ps.foldr gcd 0)).2.1
        exact dvd_trans hG (ih.1 P' hP')
    · intro D h1 h2
      exact (gcd_isGCD P (Ps.foldr gcd 0)).2.2 D h1 (ih.2 D h2)

omit [IsAlgClosed C] in
/-- Helper lemma: x is a root of gcd A B iff x is a root of A and B. -/
lemma aeval_gcd_eq_zero_iff [Algebra K C] (A B : K[X]) (x : C) :
    aeval x (gcd A B) = 0 ↔ (aeval x A = 0 ∧ aeval x B = 0) := by
  constructor
  · intro h
    have ⟨CA, hpA⟩ : gcd A B ∣ A := gcd_dvd_left A B
    have ⟨CB, hpB⟩ : gcd A B ∣ B := gcd_dvd_right A B
    have h1 : aeval x A = 0 := by
      calc
        aeval x A = aeval x (gcd A B * CA) := congrArg _ hpA
        _ = aeval x (gcd A B) * aeval x CA := map_mul _ _ _
        _ = 0 * aeval x CA := by rw [h]
        _ = 0 := zero_mul _
    have h2 : aeval x B = 0 := by
      calc
        aeval x B = aeval x (gcd A B * CB) := congrArg _ hpB
        _ = aeval x (gcd A B) * aeval x CB := map_mul _ _ _
        _ = 0 * aeval x CB := by rw [h]
        _ = 0 := zero_mul _
    exact ⟨h1, h2⟩
  · rintro ⟨hA, hB⟩
    have hspan : gcd A B ∈ Ideal.span {A, B} :=
      span_gcd A B ▸ Ideal.mem_span_singleton.mpr (dvd_refl (gcd A B))
    have ⟨U, V, hUV⟩ := Submodule.mem_span_pair.mp hspan
    have hUV' : aeval x (U * A + V * B) = aeval x (gcd A B) := congrArg _ hUV
    calc
      aeval x (gcd A B) = aeval x (U * A + V * B) := hUV'.symm
      _ = aeval x U * aeval x A + aeval x V * aeval x B := by simp
      _ = aeval x U * 0 + aeval x V * 0 := by rw [hA, hB]
      _ = 0 := by ring

omit [IsAlgClosed C] in
/-- Unnumbered Theorem (post Prop 1.13): x ∈ C is a root of every polynomial in 𝒫 if and only if it is a root of gcd(𝒫). -/
theorem isRoot_listGcd_iff_forall_isRoot [Algebra K C] {Ps : List K[X]} {x : C} :
    aeval x (listGcd Ps) = 0 ↔ ∀ P ∈ Ps, aeval x P = 0 := by
  induction Ps with
  | nil =>
    simp [listGcd]
  | cons P Ps ih =>
    simp [listGcd, aeval_gcd_eq_zero_iff]
    intro _
    rwa [← listGcd]

omit [IsAlgClosed C] in
/-- Unnumbered Theorem (post Prop 1.13): x ∈ C is not a root of any polynomial in 𝒬 if and only if it is not a root of ∏ 𝒬. -/
theorem not_isRoot_listProd_iff_forall_not_isRoot [Algebra K C] {Qs : List K[X]} {x : C} :
    aeval x (Qs.prod) ≠ 0 ↔ (∀ Q ∈ Qs, aeval x Q ≠ 0) := by
  induction Qs with
  | nil =>
    simp
  | cons Q Qs ih =>
    simp [List.prod_cons]
    intro _
    exact ih

omit [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- Unnumbered Theorem (post Prop 1.13): Every root of P in C is a root of Q if and only if P ∣ Q^(deg P). Explicitly requires P ≠ 0. -/
theorem isRoot_subset_iff_dvd_pow [Algebra K C] [DecidableEq K] [DecidableEq C] {P Q : K[X]} (hP : P ≠ 0) :
    (∀ x : C, aeval x P = 0 → aeval x Q = 0) ↔ P ∣ Q ^ P.natDegree := by
  constructor
  · intro h
    by_cases hQ : Q = 0
    · simp [hQ]
      by_cases hP0 : P.natDegree = 0
      · have hDeg : P.degree = 0 := by rw [degree_eq_natDegree hP, hP0, Nat.cast_zero]
        have hUnit : IsUnit P := isUnit_iff_degree_eq_zero.mpr hDeg
        exact IsUnit.dvd hUnit
      · have hPowPos : 0 < P.natDegree := by omega
        have hPow : (0 : K[X]) ^ P.natDegree = 0 := zero_pow hPowPos.ne'
        rw [hPow]
        exact dvd_zero P
    · have Hdvd : P.map (algebraMap K C) ∣ (Q.map (algebraMap K C)) ^ P.natDegree := by
        have hP' : P.map (algebraMap K C) ≠ 0 := by
          intro contra
          have := Polynomial.map_eq_zero_iff (RingHom.injective (algebraMap K C)) |>.mp contra
          exact hP this
        have hQ' : Q.map (algebraMap K C) ≠ 0 := by
          intro contra
          have := Polynomial.map_eq_zero_iff (RingHom.injective (algebraMap K C)) |>.mp contra
          exact hQ this
        have H : ∀ x : C, x ∈ (P.map (algebraMap K C)).roots → x ∈ (Q.map (algebraMap K C)).roots := by
          intro x hx
          have hx' : eval x (P.map (algebraMap K C)) = 0 := (mem_roots hP').mp hx
          have hx_aeval : aeval x P = 0 := by
            change eval₂ (algebraMap K C) x P = 0
            rw [← eval_map]
            exact hx'
          have hQx : aeval x Q = 0 := h x hx_aeval
          have hQx_eval : eval₂ (algebraMap K C) x Q = 0 := hQx
          exact (mem_roots hQ').mpr (by rwa [← eval_map] at hQx_eval)
        rw [IsAlgClosed.dvd_iff_roots_le_roots hP' (pow_ne_zero _ hQ')]
        rw [roots_pow _ P.natDegree]
        apply Multiset.le_iff_count.mpr
        intro x
        rw [Multiset.count_nsmul]
        by_cases hx : x ∈ (P.map (algebraMap K C)).roots
        · have hQx := H x hx
          have h1 : 1 ≤ Multiset.count x (Q.map (algebraMap K C)).roots := Multiset.count_pos.mpr hQx
          have h3 : Multiset.count x (P.map (algebraMap K C)).roots ≤ (P.map (algebraMap K C)).roots.card := Multiset.count_le_card x _
          have h4 : (P.map (algebraMap K C)).roots.card ≤ (P.map (algebraMap K C)).natDegree := card_roots' (P.map (algebraMap K C))
          have h5 : (P.map (algebraMap K C)).natDegree = P.natDegree := natDegree_map_eq_of_injective (RingHom.injective _) P
          have h6 : Multiset.count x (P.map (algebraMap K C)).roots ≤ P.natDegree := by omega
          have h7 : P.natDegree ≤ P.natDegree * Multiset.count x (Q.map (algebraMap K C)).roots := Nat.le_mul_of_pos_right _ h1
          omega
        · have h0 : Multiset.count x (P.map (algebraMap K C)).roots = 0 := Multiset.count_eq_zero.mpr hx
          omega
      have Hpow : (Q.map (algebraMap K C)) ^ P.natDegree = (Q ^ P.natDegree).map (algebraMap K C) := by
        simp only [Polynomial.map_pow]
      rw [Hpow] at Hdvd
      exact (Polynomial.map_dvd_map' (algebraMap K C)).mp Hdvd
  · intro h x hx
    have H_dvd : aeval x P ∣ aeval x (Q ^ P.natDegree) := map_dvd (aeval x) h
    rw [hx] at H_dvd
    have H_0 : aeval x (Q ^ P.natDegree) = 0 := zero_dvd_iff.mp H_dvd
    rw [map_pow] at H_0
    exact eq_zero_of_pow_eq_zero H_0

omit [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
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

omit [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
lemma lemma_1_14_core [Algebra K C] [DecidableEq K] [DecidableEq C]
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

omit [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Lemma 1.14: Yields the non-root criteria for polynomial families using a shifted polynomial GCD algorithm equivalence bound -/
theorem lemma_1_14 [Algebra K C] [DecidableEq K] [DecidableEq C]
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

omit [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Lemma 1.14 Corollary 1: A finite family of polynomials has a common root in an algebraically closed field if and only if its GCD is not a non-zero constant. -/
lemma lemma_1_14_cor1 [Algebra K C] [DecidableEq K] [DecidableEq C]
    (P_fam : List K[X]) :
    (∃ x : C, ∀ P ∈ P_fam, aeval x P = 0) ↔ (listGcd P_fam).degree ≠ 0 := by
  by_cases hP : listGcd P_fam = 0
  · have h_deg : (listGcd P_fam).degree ≠ 0 := by rw [hP, degree_zero]; decide
    have h_exists : ∃ x : C, ∀ P ∈ P_fam, aeval x P = 0 := by
      use (0 : C)
      intro P hP_in
      have H_dvd : listGcd P_fam ∣ P := (listGcd_isListGCD P_fam).1 P hP_in
      rw [hP] at H_dvd
      have H_P : P = 0 := zero_dvd_iff.mp H_dvd
      rw [H_P, map_zero]
    exact iff_of_true h_exists h_deg
  · have h_d : (listGcd P_fam).natDegree < (listGcd P_fam).natDegree + 1 := Nat.lt_succ_self _
    have H := lemma_1_14 (C := C) P_fam ([] : List K[X]) hP (d := (listGcd P_fam).natDegree + 1) h_d
    have h_LHS : (∃ x : C, (∀ P ∈ P_fam, aeval x P = 0) ∧ (∀ Q ∈ ([] : List K[X]), aeval x Q ≠ 0)) ↔
      (∃ x : C, ∀ P ∈ P_fam, aeval x P = 0) := by
      simp
    have h_RHS : (gcd (listGcd P_fam) (([] : List K[X]).prod ^ ((listGcd P_fam).natDegree + 1))).natDegree ≠
      (listGcd P_fam).natDegree ↔ (listGcd P_fam).degree ≠ 0 := by
      have H_Q : ([] : List K[X]).prod = (1 : K[X]) := rfl
      have H_Q_pow : (1 : K[X]) ^ ((listGcd P_fam).natDegree + 1) = 1 := one_pow _
      have H_gcd_deg : (gcd (listGcd P_fam) (1 : K[X])).natDegree = 0 := by
        have H_dvd : gcd (listGcd P_fam) 1 ∣ (1 : K[X]) := gcd_dvd_right _ _
        have H_unit : IsUnit (gcd (listGcd P_fam) 1) := isUnit_of_dvd_one H_dvd
        exact natDegree_eq_of_degree_eq_some (isUnit_iff_degree_eq_zero.mp H_unit)
      rw [H_Q, H_Q_pow, H_gcd_deg, ne_comm]
      constructor
      · intro h_nat h_deg
        have : (listGcd P_fam).natDegree = 0 := by
          have h1 : (listGcd P_fam).degree = (listGcd P_fam).natDegree := degree_eq_natDegree hP
          have h2 : (listGcd P_fam).natDegree = 0 ↔ (listGcd P_fam).degree = 0 := by
            constructor
            · intro h; rw [h1, h, Nat.cast_zero]
            · intro h; rw [h1] at h; exact Nat.cast_eq_zero.mp h
          exact h2.mpr h_deg
        exact h_nat this
      · intro h_deg h_nat
        have : (listGcd P_fam).degree = 0 := by
          have h1 : (listGcd P_fam).degree = (listGcd P_fam).natDegree := degree_eq_natDegree hP
          rw [h1, h_nat, Nat.cast_zero]
        exact h_deg this
    rw [← h_LHS]
    rw [← h_RHS]
    exact H

omit [IsDomain D] [Algebra D C] [Algebra D K] [IsFractionRing D K] in
/-- BPR Lemma 1.14 Corollary 2: There is a common non-root for a finite family of polynomials over an algebraically closed field if and only if no polynomial in the family is zero. -/
lemma lemma_1_14_cor2 [Algebra K C] [DecidableEq K] [DecidableEq C]
    (Q_fam : List K[X]) :
    (∃ x : C, ∀ Q ∈ Q_fam, aeval x Q ≠ 0) ↔ 0 ≤ (Q_fam.prod).degree := by
  have h_equiv : (∃ x : C, ∀ Q ∈ Q_fam, aeval x Q ≠ 0) ↔ (∃ x : C, aeval x (Q_fam.prod) ≠ 0) := by
    constructor
    · intro ⟨x, hx⟩
      exact ⟨x, not_isRoot_listProd_iff_forall_not_isRoot.mpr hx⟩
    · intro ⟨x, hx⟩
      exact ⟨x, not_isRoot_listProd_iff_forall_not_isRoot.mp hx⟩
  rw [h_equiv]
  constructor
  · rintro ⟨x, hx⟩
    have h_prod_ne_zero : Q_fam.prod ≠ 0 := by
      rintro h_prod_eq_zero
      rw [h_prod_eq_zero, map_zero] at hx
      exact hx rfl
    have hbot : (Q_fam.prod).degree = (Q_fam.prod).natDegree := degree_eq_natDegree h_prod_ne_zero
    rw [hbot]
    exact Nat.cast_nonneg _
  · rintro h_deg
    have h_prod_ne_zero : Q_fam.prod ≠ 0 := by
      intro contra
      rw [contra, degree_zero] at h_deg
      exact not_le.mpr (WithBot.bot_lt_coe 0) h_deg
    have h_map_ne_zero : (Q_fam.prod.map (algebraMap K C)) ≠ 0 := by
      intro h_map
      have h1 : Q_fam.prod = 0 := Polynomial.map_eq_zero_iff (algebraMap K C).injective |>.mp h_map
      exact h_prod_ne_zero h1
    obtain ⟨x, hx⟩ : ∃ x : C, x ∉ (Q_fam.prod.map (algebraMap K C)).roots.toFinset := Infinite.exists_notMem_finset _
    use x
    have h_not_root : ¬ IsRoot (Q_fam.prod.map (algebraMap K C)) x := by
      intro h_root
      have h_mem : x ∈ (Q_fam.prod.map (algebraMap K C)).roots := mem_roots h_map_ne_zero |>.mpr h_root
      have h_mem_finset : x ∈ (Q_fam.prod.map (algebraMap K C)).roots.toFinset := Multiset.mem_toFinset.mpr h_mem
      exact hx h_mem_finset
    have h_aeval : aeval x Q_fam.prod = eval x (Q_fam.prod.map (algebraMap K C)) := by
      rw [aeval_def, eval_map]
    rw [h_aeval]
    exact h_not_root

end Azurite.BPR

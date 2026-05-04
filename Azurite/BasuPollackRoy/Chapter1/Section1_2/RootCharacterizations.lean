import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_13
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Root characterizations following Proposition 1.13

Three unnumbered statements (which BPR uses informally between
Proposition~1.13 and Lemma~1.14) connect the roots of finite families
of polynomials to gcd, product, and power-divisibility tests.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]
variable {C : Type*} [Field C]

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

/-- Unnumbered Theorem (post Prop 1.13): Every root of P in C is a root of Q if and only if P ∣ Q^(deg P). Explicitly requires P ≠ 0. -/
theorem isRoot_subset_iff_dvd_pow [IsAlgClosed C] [Algebra K C] [DecidableEq K] [DecidableEq C]
    {P Q : K[X]} (hP : P ≠ 0) :
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

end Azurite.BPR

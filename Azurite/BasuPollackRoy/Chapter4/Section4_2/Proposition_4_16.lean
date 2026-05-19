import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_15
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_5
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# BPR Proposition 4.16: resultant vanishes iff common factor

Over a domain `D` with fraction field `K`, the resultant `Res(P, Q)`
of non-zero `P, Q ∈ D[X]` vanishes if and only if `P` and `Q` admit a
non-trivial common factor in `K[X]` — equivalently, `¬ IsCoprime`.

Proof strategy (BPR §4.2.1, using Lemma 4.15 and Proposition 1.5).

1. Lift `Res P p Q q` from `D` to `K = Frac(D)` via the ring-hom-
   functoriality `(algebraMap D K) (Res P p Q q) = Res (P.map _) p
   (Q.map _) q`; injectivity of `algebraMap` gives
   `Res = 0 ↔ Res_K = 0`.

2. Apply Lemma 4.15 over `K[X]` (which is a Field, hence IsDomain) to
   translate `Res_K = 0` into the existence of non-zero `U, V ∈ K[X]`
   with `deg U < q`, `deg V < p`, and `U · P + V · Q = 0`.

3. Use Proposition 1.5 (`P · Q / G` is an LCM whenever `G` is a GCD)
   to obtain the degree identity
   `deg(lcm(P, Q)) + deg(gcd(P, Q)) = deg(P) + deg(Q)` in `K[X]`. The
   existential step (2) is equivalent to `deg(lcm) < p + q` (forward:
   `U · P` is a common multiple of degree below `p + q`; reverse:
   factor `lcm = U · P = V · Q` and rearrange). The degree identity
   then turns `deg(lcm) < p + q` into `deg(gcd) > 0`, i.e., the GCD is
   non-constant, i.e., `¬ IsCoprime P_K Q_K`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-! ### Sylvester matrix commutes with ring homomorphisms -/

/-- The Sylvester matrix is functorial in the coefficient ring. -/
theorem Syl_map {E : Type*} [CommRing E] (f : D →+* E)
    (P : D[X]) (p : ℕ) (Q : D[X]) (q : ℕ) :
    (Syl P p Q q).map f = Syl (P.map f) p (Q.map f) q := by
  ext i j
  simp only [Matrix.map_apply, Syl]
  rw [Matrix.of_apply, Matrix.of_apply]
  split_ifs <;>
  · rw [← Polynomial.coeff_map, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_X]

/-- The resultant commutes with ring homomorphisms. -/
theorem Res_map {E : Type*} [CommRing E] (f : D →+* E)
    (P : D[X]) (p : ℕ) (Q : D[X]) (q : ℕ) :
    f (Res P p Q q) = Res (P.map f) p (Q.map f) q := by
  unfold Res
  rw [RingHom.map_det, ← Syl_map]
  rfl

/-! ### Auxiliary lemmas in `K[X]` -/

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
/-- ∃ `U, V` with the BPR conditions ↔ `lcm(P, Q)` has degree less than
    `P.natDegree + Q.natDegree`. -/
private theorem exists_UV_iff_lcm_natDegree_lt
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (∃ U V : K[X], U ≠ 0 ∧ V ≠ 0 ∧
      U.natDegree < Q.natDegree ∧ V.natDegree < P.natDegree ∧
      U * P + V * Q = 0) ↔
        (lcm P Q).natDegree < P.natDegree + Q.natDegree := by
  constructor
  · rintro ⟨U, V, hU, hV, hUq, hVp, h_rel⟩
    have h_UP_ne : U * P ≠ 0 := mul_ne_zero hU hP
    have h_UP_dvd_P : P ∣ U * P := ⟨U, by ring⟩
    have h_UP_dvd_Q : Q ∣ U * P := by
      rw [show U * P = -(V * Q) from by linear_combination h_rel]
      exact ⟨-V, by ring⟩
    have h_lcm_dvd : lcm P Q ∣ U * P := lcm_dvd h_UP_dvd_P h_UP_dvd_Q
    have h_deg_le : (lcm P Q).natDegree ≤ (U * P).natDegree :=
      Polynomial.natDegree_le_of_dvd h_lcm_dvd h_UP_ne
    have h_UP_deg : (U * P).natDegree = U.natDegree + P.natDegree :=
      Polynomial.natDegree_mul hU hP
    omega
  · intro h_lcm_lt
    have h_lcm_ne : lcm P Q ≠ 0 :=
      fun h => ((lcm_eq_zero_iff P Q).mp h).elim hP hQ
    obtain ⟨U, hU_eq⟩ := dvd_lcm_left P Q
    obtain ⟨V, hV_eq⟩ := dvd_lcm_right P Q
    have hU_ne : U ≠ 0 := by
      intro h; rw [h, mul_zero] at hU_eq; exact h_lcm_ne hU_eq
    have hV_ne : V ≠ 0 := by
      intro h; rw [h, mul_zero] at hV_eq; exact h_lcm_ne hV_eq
    refine ⟨U, -V, hU_ne, neg_ne_zero.mpr hV_ne, ?_, ?_, ?_⟩
    · have : (P * U).natDegree = (lcm P Q).natDegree := by rw [← hU_eq]
      rw [Polynomial.natDegree_mul hP hU_ne] at this
      omega
    · rw [Polynomial.natDegree_neg]
      have : (Q * V).natDegree = (lcm P Q).natDegree := by rw [← hV_eq]
      rw [Polynomial.natDegree_mul hQ hV_ne] at this
      omega
    · have h1 : U * P = lcm P Q := by rw [mul_comm]; exact hU_eq.symm
      have h2 : V * Q = lcm P Q := by rw [mul_comm]; exact hV_eq.symm
      linear_combination h1 - h2

omit [DecidableEq K] in
/-- The LCM/GCD degree identity in `K[X]`, established via BPR
    Proposition 1.5: `lcm P Q` and `P * Q / gcd P Q` are associated. -/
private theorem lcm_natDegree_eq (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (lcm P Q).natDegree + (gcd P Q).natDegree =
      P.natDegree + Q.natDegree := by
  have h_gcd_ne : gcd P Q ≠ 0 :=
    fun h => hP ((gcd_eq_zero_iff P Q).mp h).1
  have h_isLCM : Azurite.BPR.IsLCM (P * Q / gcd P Q) P Q :=
    Azurite.BPR.prop_1_5_gcd P Q
  have h_assoc : Associated (lcm P Q) (P * Q / gcd P Q) :=
    Azurite.BPR.isLCM_associated (Azurite.BPR.lcm_isLCM P Q) h_isLCM
  have h_deg_eq : (lcm P Q).natDegree = (P * Q / gcd P Q).natDegree :=
    Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated h_assoc)
  -- `(P*Q/gcd) * gcd = P*Q`.
  have h_gcd_dvd_PQ : gcd P Q ∣ P * Q := dvd_mul_of_dvd_left (gcd_dvd_left P Q) Q
  have h_mul : gcd P Q * (P * Q / gcd P Q) = P * Q :=
    EuclideanDomain.mul_div_cancel' h_gcd_ne h_gcd_dvd_PQ
  have h_PQ_ne : P * Q ≠ 0 := mul_ne_zero hP hQ
  have h_quot_ne : P * Q / gcd P Q ≠ 0 := by
    intro h
    rw [h, mul_zero] at h_mul
    exact h_PQ_ne h_mul.symm
  have h_PQ_natDeg : (P * Q).natDegree = P.natDegree + Q.natDegree :=
    Polynomial.natDegree_mul hP hQ
  have h_mul_natDeg : (gcd P Q * (P * Q / gcd P Q)).natDegree =
      (gcd P Q).natDegree + (P * Q / gcd P Q).natDegree :=
    Polynomial.natDegree_mul h_gcd_ne h_quot_ne
  rw [h_mul, h_PQ_natDeg] at h_mul_natDeg
  omega

omit [DecidableEq K] in
/-- ¬ IsCoprime in `K[X]` is equivalent to the GCD having positive
    degree. -/
private theorem not_isCoprime_iff_gcd_natDegree_pos
    (P Q : K[X]) (hP : P ≠ 0) (_hQ : Q ≠ 0) :
    ¬ IsCoprime P Q ↔ 0 < (gcd P Q).natDegree := by
  rw [← gcd_isUnit_iff]
  constructor
  · intro h_not_unit
    have h_gcd_ne : gcd P Q ≠ 0 :=
      fun h => hP ((gcd_eq_zero_iff P Q).mp h).1
    by_contra h_not_pos
    push Not at h_not_pos
    have h_natDeg : (gcd P Q).natDegree = 0 := Nat.le_zero.mp h_not_pos
    apply h_not_unit
    rw [Polynomial.eq_C_of_natDegree_eq_zero h_natDeg]
    refine Polynomial.isUnit_C.mpr ?_
    apply Ne.isUnit
    intro h_coeff_zero
    apply h_gcd_ne
    rw [Polynomial.eq_C_of_natDegree_eq_zero h_natDeg, h_coeff_zero, Polynomial.C_0]
  · intro h_pos h_unit
    have := Polynomial.natDegree_eq_zero_of_isUnit h_unit
    omega

/-! ### Main theorem -/

variable [IsDomain D] [DecidableEq D]
variable [Algebra D K] [IsFractionRing D K]

omit [IsDomain D] [DecidableEq D] in
/-- **BPR Proposition 4.16.** Over a domain `D` with fraction field `K`,
    the resultant of non-zero `P, Q ∈ D[X]` vanishes if and only if `P`
    and `Q` are not coprime in `K[X]`. -/
theorem Res_eq_zero_iff_not_isCoprime (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Res P P.natDegree Q Q.natDegree = 0 ↔
      ¬ IsCoprime (P.map (algebraMap D K)) (Q.map (algebraMap D K)) := by
  set fK : D →+* K := algebraMap D K with hfK
  set Pk := P.map fK
  set Qk := Q.map fK
  have h_inj : Function.Injective fK := IsFractionRing.injective D K
  have hPk : Pk ≠ 0 := (Polynomial.map_ne_zero_iff h_inj).mpr hP
  have hQk : Qk ≠ 0 := (Polynomial.map_ne_zero_iff h_inj).mpr hQ
  have hpk_deg : Pk.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h_inj _
  have hqk_deg : Qk.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h_inj _
  -- Step 1: Lift Res to K-side via algebraMap.
  have h_lift : Res P P.natDegree Q Q.natDegree = 0 ↔
                Res Pk P.natDegree Qk Q.natDegree = 0 := by
    constructor
    · intro h
      have h_eq := Res_map fK P P.natDegree Q Q.natDegree
      rw [h, map_zero] at h_eq
      exact h_eq.symm
    · intro h
      apply h_inj
      rw [map_zero, Res_map]
      exact h
  rw [h_lift]
  -- Step 2: Replace D-side natDegrees by K-side natDegrees.
  rw [show P.natDegree = Pk.natDegree from hpk_deg.symm,
      show Q.natDegree = Qk.natDegree from hqk_deg.symm]
  -- Step 3: Apply Lemma 4.15 over K[X] (K is a Field, hence IsDomain).
  rw [Res_eq_zero_iff Pk Qk hPk hQk]
  -- Step 4: Chain through lcm and gcd via Prop 1.5.
  rw [exists_UV_iff_lcm_natDegree_lt Pk Qk hPk hQk,
      not_isCoprime_iff_gcd_natDegree_pos Pk Qk hPk hQk]
  have h_lcm_gcd := lcm_natDegree_eq Pk Qk hPk hQk
  omega

end Azurite.BPR.Chapter4

import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_48
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_38
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_46

/-!
# BPR §8.3.4 Theorem 8.51: size of signed remainders

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.4.

**Theorem 8.51.** If `P, Q ∈ ℤ[X]` have degrees `p, q < p` and coefficients of bitsize `≤ τ`, then
the numerators and denominators of the coefficients of the polynomials in the signed remainder
sequence of `P, Q` (over `ℚ`) have bitsizes bounded by `(p+q)(q+1)(τ + bit(p+q)) + τ`.

The proof (BPR) writes each signed remainder `Sₗ` as `βₗ · sResP_{d(ℓ-1)-1}` (Cor 8.38), with
`βₗ ∈ ℚ` obeying `βₗ = (s_j t_{i-1})/(s_k t_{j-1}) β_{ℓ-2}` (Theorem 8.34).  The coefficients of
`sResP` are integers bounded by Proposition 8.48, and the rational `βₗ` is tracked as an explicit
integer numerator/denominator through the recurrence.

This file builds the supporting machinery first.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

/-- The base change of an integer polynomial to `ℚ`. -/
noncomputable abbrev mapQ (f : ℤ[X]) : ℚ[X] := f.map (Int.castRingHom ℚ)

/-- Bitsize is subadditive over products: `bit(a·b) ≤ bit(a) + bit(b)`. -/
theorem int_size_mul_le (a b : ℤ) : Int.size (a * b) ≤ Int.size a + Int.size b := by
  unfold Int.size
  rw [Int.natAbs_mul, Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)

/-- The bitsize of a divisor is at most the bitsize of the (nonzero) dividend. -/
theorem int_size_dvd_le {d n : ℤ} (hn : n ≠ 0) (h : d ∣ n) : Int.size d ≤ Int.size n := by
  unfold Int.size
  exact Nat.size_le_size (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natAbs_dvd_natAbs.mpr h))

/-- **`sResP` commutes with an injective ring homomorphism.**  For `φ : D →+* E` injective,
    `sResP (P.map φ) (Q.map φ) j = (sResP P Q j).map φ`. -/
theorem sResP_map {D E : Type*} [CommRing E] [CommRing D] {φ : D →+* E}
    (hφ : Function.Injective φ) (P Q : D[X]) (j : ℕ) :
    sResP (P.map φ) (Q.map φ) j = (sResP P Q j).map φ := by
  have hp : (P.map φ).natDegree = P.natDegree := Polynomial.natDegree_map_eq_of_injective hφ P
  have hq : (Q.map φ).natDegree = Q.natDegree := Polynomial.natDegree_map_eq_of_injective hφ Q
  rw [sResP, sResP, hp, hq]
  by_cases hjq : j ≤ Q.natDegree
  · rw [if_pos hjq, if_pos hjq]
    rw [← pdetRing_map φ]
    congr 1
    funext r
    by_cases hr : (r : ℕ) < Q.natDegree - j
    · simp only [hr, if_true, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    · simp only [hr, if_false, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  · rw [if_neg hjq, if_neg hjq]
    by_cases hjp : j = P.natDegree
    · rw [if_pos hjp, if_pos hjp]
    · rw [if_neg hjp, if_neg hjp]
      by_cases hjp1 : j = P.natDegree - 1
      · rw [if_pos hjp1, if_pos hjp1]
      · rw [if_neg hjp1, if_neg hjp1, Polynomial.map_zero]

/-- **The `β_ℓ` proportionality.**  Each nonzero signed remainder is an explicit scalar multiple
    of a signed subresultant polynomial: `Sₗ = C(βₗ) · sResP_{d(ℓ-1)-1}` with
    `βₗ = lcof(Sₗ) / lcof(sResP_{d(ℓ-1)-1})` (Corollary 8.38 + leading-coefficient ratio). -/
theorem SRemS_eq_C_mul_sResP {K : Type*} [Field K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ)
    (hℓne : SRemS P Q ℓ ≠ 0) :
    SRemS P Q ℓ
      = C ((SRemS P Q ℓ).leadingCoeff
            / (sResP P Q ((SRemS P Q (ℓ - 1)).natDegree - 1)).leadingCoeff)
        * sResP P Q ((SRemS P Q (ℓ - 1)).natDegree - 1) := by
  have hassoc := (corollary_8_38 P Q hP hQ hpq hq1 hℓ1 hℓne).1
  have hsne : sResP P Q ((SRemS P Q (ℓ - 1)).natDegree - 1) ≠ 0 := fun h => hℓne
    ((associated_zero_iff_eq_zero _).mp (h ▸ hassoc).symm)
  exact eq_C_leadingCoeff_ratio_mul_of_associated hsne hassoc.symm

/-- **Theorem 8.34 recurrence in remainder form.**  In the recurrence setting, the remainder of
    `sResP_{i-1}` by `sResP_{j-1}` is the explicit scalar multiple
    `-(s_j t_{i-1})/(s_k t_{j-1}) · sResP_{k-1}`. -/
theorem sResP_mod_eq {K : Type*} [Field K] (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ}
    (hj1 : 1 ≤ j) (hji : j < i) (hip : i ≤ P.natDegree + 1) (hne : sResP P Q (i - 1) ≠ 0)
    (hdeg : (sResP P Q (i - 1)).natDegree = j) {k : ℕ} (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) (hk1 : 1 ≤ k)
    (hstd : sBPR P Q k * tBPR P Q (j - 1) ≠ 0) :
    sResP P Q (i - 1) % sResP P Q (j - 1)
      = -(C ((sBPR P Q j * tBPR P Q (i - 1)) / (sBPR P Q k * tBPR P Q (j - 1)))
          * sResP P Q (k - 1)) := by
  obtain ⟨hrec, _⟩ :=
    (theorem_8_34_monolithic P Q hP hQ hpq hq1 hj1 hji hip hne hdeg).2 k hk0 hkdeg
  rw [if_neg (show ¬ k = 0 by omega)] at hrec
  simp only [← Polynomial.C_mul] at hrec
  rw [rem_C_mul] at hrec
  -- hrec : C(s_j t_{i-1}) sResP_{k-1} = -(C(s_k t_{j-1}) (sResP_{i-1} % sResP_{j-1}))
  have hsc : sBPR P Q k * tBPR P Q (j - 1)
      * (sBPR P Q j * tBPR P Q (i - 1) / (sBPR P Q k * tBPR P Q (j - 1)))
      = sBPR P Q j * tBPR P Q (i - 1) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hstd]
  apply mul_left_cancel₀ (show (C (sBPR P Q k * tBPR P Q (j - 1)) : K[X]) ≠ 0
    from Polynomial.C_ne_zero.mpr hstd)
  rw [mul_neg, ← mul_assoc, ← Polynomial.C_mul, hsc]
  linear_combination hrec

section SRemSdeg

variable {K : Type*} [Field K] (P Q : K[X])

/-- If `S_{n+1} ≠ 0` then `S_n ≠ 0`. -/
theorem SRemS_ne_pred (hP : P ≠ 0) {n : ℕ} (hn : SRemS P Q (n + 1) ≠ 0) : SRemS P Q n ≠ 0 := by
  intro hn0
  rcases n with _ | n'
  · exact hP (by rw [← SRemS_fst (P := P) (Q := Q)]; exact hn0)
  · exact hn (SRemS_zero_ge P Q n' hn0 (n' + 2) (by omega))

/-- A nonzero signed remainder has all predecessors nonzero. -/
theorem SRemS_ne_of_le (hP : P ≠ 0) {ℓ : ℕ} (hℓ : SRemS P Q ℓ ≠ 0) {m : ℕ} (hm : m ≤ ℓ) :
    SRemS P Q m ≠ 0 := by
  induction ℓ with
  | zero => rwa [Nat.le_zero.mp hm]
  | succ ℓ' ih =>
    rcases Nat.lt_or_ge m (ℓ' + 1) with h | h
    · exact ih (SRemS_ne_pred P Q hP hℓ) (by omega)
    · rw [show m = ℓ' + 1 by omega]; exact hℓ

/-- Degrees in the signed remainder sequence strictly decrease at nonzero steps. -/
theorem SRemS_natDegree_lt (hpq : Q.natDegree < P.natDegree) {n : ℕ}
    (hn : SRemS P Q (n + 1) ≠ 0) :
    (SRemS P Q (n + 1)).natDegree < (SRemS P Q n).natDegree := by
  rcases n with _ | n'
  · rw [SRemS_fst, SRemS_snd]; exact hpq
  · have hn0 : SRemS P Q (n' + 1) ≠ 0 := fun h =>
      hn (SRemS_zero_ge P Q n' h (n' + 2) (by omega))
    have hx : SRemS P Q n' % SRemS P Q (n' + 1) ≠ 0 := fun h =>
      hn (by rw [SRemS_ss P Q n' hn0, h, neg_zero])
    rw [SRemS_ss P Q n' hn0, Polynomial.natDegree_neg]
    exact Polynomial.natDegree_lt_natDegree hx (Polynomial.degree_mod_lt (SRemS P Q n') hn0)

/-- For `n ≥ 1`, a nonzero `S_n` has degree `≤ q`. -/
theorem SRemS_natDegree_le_q (hpq : Q.natDegree < P.natDegree) (hP : P ≠ 0) {n : ℕ}
    (hn : SRemS P Q (n + 1) ≠ 0) : (SRemS P Q (n + 1)).natDegree ≤ Q.natDegree := by
  induction n with
  | zero => rw [SRemS_snd]
  | succ n' ih =>
    have h1 := SRemS_natDegree_lt P Q hpq hn
    have h2 := ih (SRemS_ne_pred P Q hP hn)
    omega

/-- A nonzero signed remainder has degree `≤ p`. -/
theorem SRemS_natDegree_le_p (hpq : Q.natDegree < P.natDegree) (hP : P ≠ 0) {n : ℕ}
    (hn : SRemS P Q n ≠ 0) : (SRemS P Q n).natDegree ≤ P.natDegree := by
  rcases n with _ | n'
  · rw [SRemS_fst]
  · have := SRemS_natDegree_le_q P Q hpq hP hn; omega

end SRemSdeg

/-! ### Connecting the rational `s_j`, `t_j` to bounded integers

Over `ℚ` (with `P = P₀.map (ℤ→ℚ)`), the signed-subresultant coefficients `s_j = sBPR` and
`t_j = tBPR` are *integers* (casts of coefficients of the integer `sResP P₀ Q₀`).  We record this
integer and its bitsize bound (from Proposition 8.48). -/

/-- The integer underlying `s_j` over `ℚ`: the `Xʲ`-coefficient of the integer `sResP_j`
    (with the convention `s_p = 1`). -/
noncomputable def Sℤ (P₀ Q₀ : ℤ[X]) (j : ℕ) : ℤ :=
  if j = P₀.natDegree then 1 else (sResP P₀ Q₀ j).coeff j

/-- The integer underlying `t_m` over `ℚ` (with the convention `t_p = 1`). -/
noncomputable def Tℤ (P₀ Q₀ : ℤ[X]) (m : ℕ) : ℤ :=
  if m = P₀.natDegree then 1 else (sResP P₀ Q₀ m).leadingCoeff

section Sizes

variable (P₀ Q₀ : ℤ[X])

/-- Over `ℚ`, `s_j = sBPR` is the integer `Sℤ` (cast), for `j ≤ q` or `j = p`. -/
theorem sBPR_eq_cast {j : ℕ} (hpq : Q₀.natDegree < P₀.natDegree)
    (hjq : j ≤ Q₀.natDegree ∨ j = P₀.natDegree) :
    sBPR (P₀.map (Int.castRingHom ℚ)) (Q₀.map (Int.castRingHom ℚ)) j = (Sℤ P₀ Q₀ j : ℚ) := by
  have hpm : (P₀.map (Int.castRingHom ℚ)).natDegree = P₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P₀
  have hqm : (Q₀.map (Int.castRingHom ℚ)).natDegree = Q₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective Q₀
  rw [sBPR, hpm, Sℤ]
  rcases hjq with hjq | hjp
  · rw [if_neg (by omega), if_neg (by omega),
      ← coeff_sResP _ _ (by rw [hpm, hqm]; exact hpq) (by rw [hpm]; omega),
      sResP_map Int.cast_injective, Polynomial.coeff_map]
    rfl
  · rw [if_pos hjp, if_pos hjp, Int.cast_one]

/-- Over `ℚ`, `t_m = tBPR` is the integer `Tℤ` (cast), for all `m`. -/
theorem tBPR_eq_cast (m : ℕ) :
    tBPR (P₀.map (Int.castRingHom ℚ)) (Q₀.map (Int.castRingHom ℚ)) m = (Tℤ P₀ Q₀ m : ℚ) := by
  have hpm : (P₀.map (Int.castRingHom ℚ)).natDegree = P₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P₀
  rw [tBPR, hpm, Tℤ]
  by_cases hm : m = P₀.natDegree
  · rw [if_pos hm, if_pos hm, Int.cast_one]
  · rw [if_neg hm, if_neg hm, sResP_map Int.cast_injective, Polynomial.leadingCoeff,
      Polynomial.leadingCoeff, Polynomial.coeff_map,
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    rfl

variable {τ : ℕ} (hP : ∀ i, Int.size (P₀.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q₀.coeff i) ≤ τ)
  (hpq : Q₀.natDegree < P₀.natDegree)

/-- Abbreviation for the per-coefficient bound `B = (p+q)(τ + bit(p+q))`. -/
local notation "B" => (P₀.natDegree + Q₀.natDegree) * (τ + Nat.size (P₀.natDegree + Q₀.natDegree))

include hP hQ hpq in
/-- `Sℤ j` has bitsize `≤ B`, for `j ≤ q` or `j = p` (Proposition 8.48 / convention). -/
theorem Sℤ_size_le {j : ℕ} (hjq : j ≤ Q₀.natDegree ∨ j = P₀.natDegree) :
    Int.size (Sℤ P₀ Q₀ j) ≤ B := by
  rw [Sℤ]
  rcases hjq with hjq | hjp
  · rw [if_neg (by omega)]
    refine le_trans (sResP_coeff_size_le P₀ Q₀ hP hQ hpq hjq j) ?_
    exact Nat.mul_le_mul (by omega) (Nat.add_le_add_left (Nat.size_le_size (by omega)) _)
  · rw [if_pos hjp]
    have hpq1 : 1 ≤ P₀.natDegree + Q₀.natDegree := by omega
    have hsz1 : 1 ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := by
      have : Nat.size (P₀.natDegree + Q₀.natDegree) ≠ 0 := by rw [Ne, Nat.size_eq_zero]; omega
      omega
    have hB1 : 1 ≤ B := by have := Nat.mul_le_mul hpq1 hsz1; simpa using this
    simpa [Int.size] using hB1

include hP hQ hpq in
/-- `Tℤ m` has bitsize `≤ B`, for all `m` (Proposition 8.48 / boundary conventions). -/
theorem Tℤ_size_le (m : ℕ) : Int.size (Tℤ P₀ Q₀ m) ≤ B := by
  have hpq1 : 1 ≤ P₀.natDegree + Q₀.natDegree := by omega
  have hsz1 : 1 ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := by
    have : Nat.size (P₀.natDegree + Q₀.natDegree) ≠ 0 := by rw [Ne, Nat.size_eq_zero]; omega
    omega
  have hB1 : 1 ≤ B := by
    have := Nat.mul_le_mul hpq1 hsz1; simpa using this
  have hτB : τ ≤ B := by
    calc τ ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := Nat.le_add_right _ _
    _ = 1 * (τ + Nat.size (P₀.natDegree + Q₀.natDegree)) := (one_mul _).symm
    _ ≤ B := Nat.mul_le_mul hpq1 le_rfl
  rw [Tℤ]
  by_cases hm : m = P₀.natDegree
  · rw [if_pos hm]; simpa [Int.size] using hB1
  · rw [if_neg hm]
    by_cases hmq : m ≤ Q₀.natDegree
    · -- determinant range: leadingCoeff is a coefficient, use Prop 8.48
      rw [Polynomial.leadingCoeff]
      exact le_trans (sResP_coeff_size_le P₀ Q₀ hP hQ hpq hmq _)
        (Nat.mul_le_mul (by omega) (Nat.add_le_add_left (Nat.size_le_size (by omega)) _))
    · by_cases hmp1 : m = P₀.natDegree - 1
      · rcases Nat.lt_or_ge (Q₀.natDegree + 1) P₀.natDegree with hgap | hgap
        · -- proper gap: sResP_{p-1} = Q, leadingCoeff(Q) ≤ τ ≤ B
          subst hmp1
          rw [sResP_eq_self_Q P₀ Q₀ hgap, Polynomial.leadingCoeff]
          exact le_trans (hQ _) hτB
        · omega
      · rw [sResP_eq_zero P₀ Q₀ (by omega) hm hmp1, Polynomial.leadingCoeff_zero]
        simp [Int.size]

end Sizes

/-! ### The main induction

Each nonzero signed remainder over `ℚ` is `C(N/D) · sResP_{m}` with integer `N, D` of bitsize
`≤ 1 + ℓ·B`, where `m = mIdx ℓ`. -/

section MainInduction

variable (P₀ Q₀ : ℤ[X]) {τ : ℕ}
  (hP : ∀ i, Int.size (P₀.coeff i) ≤ τ) (hQ : ∀ i, Int.size (Q₀.coeff i) ≤ τ)
  (hpq0 : Q₀.natDegree < P₀.natDegree) (hq1 : 1 ≤ Q₀.natDegree)

local notation "B" => (P₀.natDegree + Q₀.natDegree) * (τ + Nat.size (P₀.natDegree + Q₀.natDegree))

include hP hQ hpq0 hq1 in
/-- **Main induction for Theorem 8.51.**  Each nonzero signed remainder `S_ℓ` over `ℚ` is
    `C(N/D) · sResP_{mIdx ℓ}` for integers `N, D` (`D ≠ 0`) with `bit(N), bit(D) ≤ 1 + ℓ·B`. -/
theorem SRemS_eq_divInt (ℓ : ℕ) (hℓne : SRemS (mapQ P₀) (mapQ Q₀) ℓ ≠ 0) :
    ∃ N D : ℤ, D ≠ 0 ∧ Int.size N ≤ 1 + ℓ * B ∧ Int.size D ≤ 1 + ℓ * B
      ∧ SRemS (mapQ P₀) (mapQ Q₀) ℓ
        = C ((N : ℚ) / (D : ℚ))
          * sResP (mapQ P₀) (mapQ Q₀)
              (if ℓ = 0 then P₀.natDegree
               else (SRemS (mapQ P₀) (mapQ Q₀) (ℓ - 1)).natDegree - 1) := by
  have hP₀ : P₀ ≠ 0 := by rintro rfl; simp at hpq0
  have hQ₀ : Q₀ ≠ 0 := by rintro rfl; simp at hq1
  have hpdm : (mapQ P₀).natDegree = P₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P₀
  have hqdm : (mapQ Q₀).natDegree = Q₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective Q₀
  have hPm : mapQ P₀ ≠ 0 := by intro h; rw [h] at hpdm; simp at hpdm; omega
  have hQm : mapQ Q₀ ≠ 0 := by intro h; rw [h] at hqdm; simp at hqdm; omega
  have hpqm : (mapQ Q₀).natDegree < (mapQ P₀).natDegree := by rw [hpdm, hqdm]; exact hpq0
  have hq1m : 1 ≤ (mapQ Q₀).natDegree := by rw [hqdm]; exact hq1
  suffices key : ∀ N : ℕ, SRemS (mapQ P₀) (mapQ Q₀) N ≠ 0 →
      ∃ NN DD : ℤ, DD ≠ 0 ∧ Int.size NN ≤ 1 + N * B ∧ Int.size DD ≤ 1 + N * B
        ∧ SRemS (mapQ P₀) (mapQ Q₀) N
          = C ((NN : ℚ) / (DD : ℚ))
            * sResP (mapQ P₀) (mapQ Q₀)
                (if N = 0 then P₀.natDegree
                 else (SRemS (mapQ P₀) (mapQ Q₀) (N - 1)).natDegree - 1) from key ℓ hℓne
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hNne
  have hτB : τ ≤ B := by
    calc τ ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := Nat.le_add_right _ _
    _ = 1 * (τ + Nat.size (P₀.natDegree + Q₀.natDegree)) := (one_mul _).symm
    _ ≤ B := Nat.mul_le_mul (by omega) le_rfl
  rcases N with _ | _ | m
  · -- N = 0 : S₀ = P = sResP_p
    refine ⟨1, 1, one_ne_zero, by simp [Int.size], by simp [Int.size], ?_⟩
    rw [if_pos rfl, SRemS_fst, show P₀.natDegree = (mapQ P₀).natDegree from hpdm.symm,
      sResP_eq_self _ _ hpqm, Int.cast_one, div_one, map_one, one_mul]
  · -- N = 1 : S₁ = Q = C(lcof Q / lcof sResP_{p-1}) · sResP_{p-1}
    have hb_idx : ((SRemS (mapQ P₀) (mapQ Q₀) (1 - 1)).natDegree - 1)
        = (mapQ P₀).natDegree - 1 := by rw [Nat.sub_self, SRemS_fst]
    have heq := SRemS_eq_C_mul_sResP (mapQ P₀) (mapQ Q₀) hPm hQm hpqm hq1m (ℓ := 1) le_rfl hNne
    rw [hb_idx] at heq ⊢
    have hbne : sResP (mapQ P₀) (mapQ Q₀) ((mapQ P₀).natDegree - 1) ≠ 0 := by
      intro h; apply hNne; rw [heq, h, mul_zero]
    refine ⟨Q₀.leadingCoeff, Tℤ P₀ Q₀ (P₀.natDegree - 1), ?_, ?_, ?_, ?_⟩
    · -- D ≠ 0
      rw [Tℤ, if_neg (by omega), Ne, Polynomial.leadingCoeff_eq_zero]
      intro h; apply hbne
      rw [hpdm, sResP_map Int.cast_injective, h, Polynomial.map_zero]
    · have h1 : Int.size Q₀.leadingCoeff ≤ τ := by rw [Polynomial.leadingCoeff]; exact hQ _
      have hb : (0 + 1) * B = B := by ring
      rw [hb]; omega
    · have hb : (0 + 1) * B = B := by ring
      rw [hb]; exact le_trans (Tℤ_size_le P₀ Q₀ hP hQ hpq0 (P₀.natDegree - 1)) (by omega)
    · have e1 : (mapQ Q₀).leadingCoeff = (Q₀.leadingCoeff : ℚ) := by
        simp only [Polynomial.leadingCoeff]; rw [Polynomial.coeff_map, hqdm]; rfl
      have e2 : (sResP (mapQ P₀) (mapQ Q₀) ((mapQ P₀).natDegree - 1)).leadingCoeff
          = (Tℤ P₀ Q₀ (P₀.natDegree - 1) : ℚ) := by
        rw [Tℤ, if_neg (show P₀.natDegree - 1 ≠ P₀.natDegree by omega), hpdm,
          sResP_map Int.cast_injective, Polynomial.leadingCoeff, Polynomial.leadingCoeff,
          Polynomial.coeff_map, Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
        rfl
      rw [if_neg (by omega), heq, SRemS_snd, e1, e2]
  · -- N = m + 2 (inductive step)
    rw [if_neg (by omega)]
    simp only [Nat.add_sub_cancel]
    -- predecessors nonzero
    have hSm1ne : SRemS (mapQ P₀) (mapQ Q₀) (m + 1) ≠ 0 := SRemS_ne_pred _ _ hPm hNne
    have hSmne : SRemS (mapQ P₀) (mapQ Q₀) m ≠ 0 := SRemS_ne_pred _ _ hPm hSm1ne
    -- IH at m
    obtain ⟨N₂, D₂, hD₂ne, hN₂sz, hD₂sz, hSm_eq⟩ := ih m (by omega) hSmne
    -- proportionality of S_{m+1}
    have hSm1_eq := SRemS_eq_C_mul_sResP (mapQ P₀) (mapQ Q₀) hPm hQm hpqm hq1m
      (ℓ := m + 1) (by omega) hSm1ne
    simp only [Nat.add_sub_cancel] at hSm1_eq
    -- name the indices
    set a := (if m = 0 then P₀.natDegree
              else (SRemS (mapQ P₀) (mapQ Q₀) (m - 1)).natDegree - 1) with ha_def
    set J := (SRemS (mapQ P₀) (mapQ Q₀) m).natDegree with hJ_def
    set K := (SRemS (mapQ P₀) (mapQ Q₀) (m + 1)).natDegree with hK_def
    -- facts about sResP a (from hSm_eq)
    have hc₂ne : ((N₂ : ℚ) / (D₂ : ℚ)) ≠ 0 :=
      fun h => hSmne (by rw [hSm_eq, h, map_zero, zero_mul])
    have hsResPa_ne : sResP (mapQ P₀) (mapQ Q₀) a ≠ 0 :=
      fun h => hSmne (by rw [hSm_eq, h, mul_zero])
    have hdeg_a : (sResP (mapQ P₀) (mapQ Q₀) a).natDegree = J := by
      rw [hJ_def, hSm_eq, Polynomial.natDegree_C_mul hc₂ne]
    -- facts about sResP (J-1) (from hSm1_eq)
    have hsResPb_ne : sResP (mapQ P₀) (mapQ Q₀) (J - 1) ≠ 0 :=
      fun h => hSm1ne (by rw [hSm1_eq, h, mul_zero])
    have hc₁ne : ((SRemS (mapQ P₀) (mapQ Q₀) (m + 1)).leadingCoeff
        / (sResP (mapQ P₀) (mapQ Q₀) (J - 1)).leadingCoeff) ≠ 0 :=
      div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hSm1ne)
        (Polynomial.leadingCoeff_ne_zero.mpr hsResPb_ne)
    have hdeg_b : (sResP (mapQ P₀) (mapQ Q₀) (J - 1)).natDegree = K := by
      rw [hK_def, hSm1_eq, Polynomial.natDegree_C_mul hc₁ne]
    -- degree bookkeeping
    have hK_le_qm : K ≤ (mapQ Q₀).natDegree := by
      rw [hK_def]; exact SRemS_natDegree_le_q (mapQ P₀) (mapQ Q₀) hpqm hPm hSm1ne
    have hK_le_q : K ≤ Q₀.natDegree := by rw [← hqdm]; exact hK_le_qm
    have hJ_cases : J ≤ Q₀.natDegree ∨ J = P₀.natDegree := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · right; rw [hJ_def, hm0, SRemS_fst, hpdm]
      · left
        have hSm_1ne : SRemS (mapQ P₀) (mapQ Q₀) (m - 1) ≠ 0 :=
          SRemS_ne_of_le (mapQ P₀) (mapQ Q₀) hPm hSmne (by omega)
        have hlt := SRemS_natDegree_lt (mapQ P₀) (mapQ Q₀) hpqm
          (n := m - 1) (by rwa [Nat.sub_add_cancel hmpos])
        have hle := SRemS_natDegree_le_q (mapQ P₀) (mapQ Q₀) hpqm hPm
          (n := m - 1) (by rwa [Nat.sub_add_cancel hmpos])
        rw [Nat.sub_add_cancel hmpos] at hlt hle
        rw [hJ_def]; omega
    have hJ_le_p : J ≤ P₀.natDegree := by rcases hJ_cases with h | h <;> omega
    have hJ_pos : 1 ≤ J := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hJ_def, hm0, SRemS_fst, hpdm]; omega
      · by_contra hcon
        have hunit : IsUnit (SRemS (mapQ P₀) (mapQ Q₀) m) :=
          Polynomial.isUnit_iff_degree_eq_zero.mpr (by
            rw [Polynomial.degree_eq_natDegree hSmne, ← hJ_def]; norm_cast; omega)
        apply hSm1ne
        have hmm : m + 1 = (m - 1) + 2 := by omega
        rw [hmm, SRemS_ss (mapQ P₀) (mapQ Q₀) (m - 1) (by rwa [Nat.sub_add_cancel hmpos]),
          Nat.sub_add_cancel hmpos, EuclideanDomain.mod_eq_zero.mpr hunit.dvd, neg_zero]
    have hK_pos : 1 ≤ K := by
      by_contra hcon
      have hunit : IsUnit (SRemS (mapQ P₀) (mapQ Q₀) (m + 1)) :=
        Polynomial.isUnit_iff_degree_eq_zero.mpr (by
          rw [Polynomial.degree_eq_natDegree hSm1ne, ← hK_def]; norm_cast; omega)
      apply hNne
      rw [SRemS_ss (mapQ P₀) (mapQ Q₀) m hSm1ne, EuclideanDomain.mod_eq_zero.mpr hunit.dvd, neg_zero]
    have ha_le_J : J ≤ a := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [ha_def, hm0, if_pos rfl, hJ_def, hm0, SRemS_fst, hpdm]
      · rw [ha_def, if_neg (by omega)]
        have hSm_1ne : SRemS (mapQ P₀) (mapQ Q₀) (m - 1) ≠ 0 :=
          SRemS_ne_of_le (mapQ P₀) (mapQ Q₀) hPm hSmne (by omega)
        have hlt := SRemS_natDegree_lt (mapQ P₀) (mapQ Q₀) hpqm
          (n := m - 1) (by rwa [Nat.sub_add_cancel hmpos])
        rw [Nat.sub_add_cancel hmpos] at hlt
        rw [hJ_def]; omega
    have ha_le_p : a ≤ P₀.natDegree := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [ha_def, hm0, if_pos rfl]
      · rw [ha_def, if_neg (by omega)]
        have hSm_1ne : SRemS (mapQ P₀) (mapQ Q₀) (m - 1) ≠ 0 :=
          SRemS_ne_of_le (mapQ P₀) (mapQ Q₀) hPm hSmne (by omega)
        have := SRemS_natDegree_le_p (mapQ P₀) (mapQ Q₀) hpqm hPm hSm_1ne
        rw [hpdm] at this; omega
    -- non-defectiveness at K (Corollary 8.38, part 2) ⟹ s_K ≠ 0
    have hcor := (corollary_8_38 (mapQ P₀) (mapQ Q₀) hPm hQm hpqm hq1m
      (ℓ := m + 1) (by omega) hSm1ne).2
    rw [← hK_def] at hcor
    have hsResPK_ne : sResP (mapQ P₀) (mapQ Q₀) K ≠ 0 :=
      fun h => hSm1ne (hcor.eq_zero_iff.mp h)
    have hdeg_K : (sResP (mapQ P₀) (mapQ Q₀) K).natDegree = K := by
      have := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hcor)
      rw [← hK_def] at this; exact this
    have hsBPRK_ne : sBPR (mapQ P₀) (mapQ Q₀) K ≠ 0 :=
      sBPR_ne_of_nondef (mapQ P₀) (mapQ Q₀) hpqm hK_le_qm hsResPK_ne hdeg_K
    have htBPRb_ne : tBPR (mapQ P₀) (mapQ Q₀) (J - 1) ≠ 0 :=
      tBPR_ne_of_ne (mapQ P₀) (mapQ Q₀) (by rw [hpdm]; omega) hsResPb_ne
    have hstd : sBPR (mapQ P₀) (mapQ Q₀) K * tBPR (mapQ P₀) (mapQ Q₀) (J - 1) ≠ 0 :=
      mul_ne_zero hsBPRK_ne htBPRb_ne
    -- cast bridges
    have es_J : sBPR (mapQ P₀) (mapQ Q₀) J = (Sℤ P₀ Q₀ J : ℚ) := sBPR_eq_cast P₀ Q₀ hpq0 hJ_cases
    have et_a : tBPR (mapQ P₀) (mapQ Q₀) a = (Tℤ P₀ Q₀ a : ℚ) := tBPR_eq_cast P₀ Q₀ a
    have es_K : sBPR (mapQ P₀) (mapQ Q₀) K = (Sℤ P₀ Q₀ K : ℚ) :=
      sBPR_eq_cast P₀ Q₀ hpq0 (Or.inl hK_le_q)
    have et_b : tBPR (mapQ P₀) (mapQ Q₀) (J - 1) = (Tℤ P₀ Q₀ (J - 1) : ℚ) := tBPR_eq_cast P₀ Q₀ _
    -- the remainder identity (Theorem 8.34 recurrence)
    have heq_mod := sResP_mod_eq (mapQ P₀) (mapQ Q₀) hPm hQm hpqm hq1m
      (i := a + 1) (j := J) hJ_pos (by omega) (by rw [hpdm]; omega) hsResPa_ne hdeg_a
      hsResPb_ne hdeg_b hK_pos hstd
    simp only [Nat.add_sub_cancel] at heq_mod
    -- nonzero witnesses for D
    have hSℤKne : Sℤ P₀ Q₀ K ≠ 0 := by
      have : (Sℤ P₀ Q₀ K : ℚ) ≠ 0 := es_K ▸ hsBPRK_ne; exact_mod_cast this
    have hTℤbne : Tℤ P₀ Q₀ (J - 1) ≠ 0 := by
      have : (Tℤ P₀ Q₀ (J - 1) : ℚ) ≠ 0 := et_b ▸ htBPRb_ne; exact_mod_cast this
    refine ⟨N₂ * Sℤ P₀ Q₀ J * Tℤ P₀ Q₀ a, D₂ * Sℤ P₀ Q₀ K * Tℤ P₀ Q₀ (J - 1),
      mul_ne_zero (mul_ne_zero hD₂ne hSℤKne) hTℤbne, ?_, ?_, ?_⟩
    · -- size of N
      have hexp : 1 + (m + 2) * B = (1 + m * B) + B + B := by ring
      have h1 := int_size_mul_le (N₂ * Sℤ P₀ Q₀ J) (Tℤ P₀ Q₀ a)
      have h2 := int_size_mul_le N₂ (Sℤ P₀ Q₀ J)
      have h3 := Sℤ_size_le P₀ Q₀ hP hQ hpq0 hJ_cases
      have h4 := Tℤ_size_le P₀ Q₀ hP hQ hpq0 a
      rw [hexp]; omega
    · -- size of D
      have hexp : 1 + (m + 2) * B = (1 + m * B) + B + B := by ring
      have h1 := int_size_mul_le (D₂ * Sℤ P₀ Q₀ K) (Tℤ P₀ Q₀ (J - 1))
      have h2 := int_size_mul_le D₂ (Sℤ P₀ Q₀ K)
      have h3 := Sℤ_size_le P₀ Q₀ hP hQ hpq0 (Or.inl hK_le_q)
      have h4 := Tℤ_size_le P₀ Q₀ hP hQ hpq0 (J - 1)
      rw [hexp]; omega
    · -- the equation
      have hscalar : ((N₂ : ℚ) / (D₂ : ℚ))
          * (((Sℤ P₀ Q₀ J : ℚ) * (Tℤ P₀ Q₀ a : ℚ))
              / ((Sℤ P₀ Q₀ K : ℚ) * (Tℤ P₀ Q₀ (J - 1) : ℚ)))
          = ((N₂ * Sℤ P₀ Q₀ J * Tℤ P₀ Q₀ a : ℤ) : ℚ)
            / ((D₂ * Sℤ P₀ Q₀ K * Tℤ P₀ Q₀ (J - 1) : ℤ) : ℚ) := by
        push_cast; ring
      rw [SRemS_ss (mapQ P₀) (mapQ Q₀) m hSm1ne, hSm_eq, hSm1_eq, rem_C_mul,
        mod_C_mul_right _ _ hc₁ne, heq_mod, es_J, et_a, es_K, et_b,
        mul_neg, neg_neg, ← mul_assoc, ← Polynomial.C_mul, hscalar]

include hP hQ hpq0 hq1 in
/-- **BPR Theorem 8.51 (size of signed remainders).**  For `P, Q ∈ ℤ[X]` of degrees `p, q < p`
    with coefficients of bitsize `≤ τ`, the numerator and denominator of every coefficient of the
    signed remainder sequence (over `ℚ`) have bitsizes bounded (with `B = (p+q)(τ + bit(p+q))`) by
    `(q+2)B + 1` and `(q+1)B + 1` respectively (an honest tightening of BPR's `(p+q)(q+1)(τ +
    bit(p+q)) + τ`). -/
theorem theorem_8_51 (ℓ : ℕ) (hℓ : ℓ ≤ Q₀.natDegree + 1) (a : ℕ) :
    Int.size ((SRemS (mapQ P₀) (mapQ Q₀) ℓ).coeff a).num ≤ (Q₀.natDegree + 2) * B + 1
      ∧ Nat.size ((SRemS (mapQ P₀) (mapQ Q₀) ℓ).coeff a).den ≤ (Q₀.natDegree + 1) * B + 1 := by
  have hpdm : (mapQ P₀).natDegree = P₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P₀
  have hqdm : (mapQ Q₀).natDegree = Q₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective Q₀
  have hPm : mapQ P₀ ≠ 0 := by intro h; rw [h] at hpdm; simp at hpdm; omega
  have hpqm : (mapQ Q₀).natDegree < (mapQ P₀).natDegree := by rw [hpdm, hqdm]; exact hpq0
  have hB1 : 1 ≤ B := by
    have h2 : 1 ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := by
      have : Nat.size (P₀.natDegree + Q₀.natDegree) ≠ 0 := by rw [Ne, Nat.size_eq_zero]; omega
      omega
    have := Nat.mul_le_mul (show 1 ≤ P₀.natDegree + Q₀.natDegree by omega) h2; simpa using this
  have hτB : τ ≤ B := by
    calc τ ≤ τ + Nat.size (P₀.natDegree + Q₀.natDegree) := Nat.le_add_right _ _
    _ = 1 * (τ + Nat.size (P₀.natDegree + Q₀.natDegree)) := (one_mul _).symm
    _ ≤ B := Nat.mul_le_mul (by omega) le_rfl
  have hmono2 : B ≤ (Q₀.natDegree + 2) * B := Nat.le_mul_of_pos_left B (by omega)
  have hmono1 : B ≤ (Q₀.natDegree + 1) * B := Nat.le_mul_of_pos_left B (by omega)
  have hsize1 : Nat.size 1 ≤ 1 := Nat.size_le.mpr (by norm_num)
  by_cases hℓne : SRemS (mapQ P₀) (mapQ Q₀) ℓ = 0
  · rw [hℓne, Polynomial.coeff_zero]
    refine ⟨by rw [Rat.num_zero]; simp [Int.size], ?_⟩
    rw [Rat.den_zero]; omega
  · rcases ℓ with _ | _ | ℓ'
    · -- ℓ = 0 : coeff of P
      rw [SRemS_fst, Polynomial.coeff_map]
      simp only [eq_intCast, Rat.num_intCast, Rat.den_intCast]
      exact ⟨by have := hP a; omega, by omega⟩
    · -- ℓ = 1 : coeff of Q
      rw [SRemS_snd, Polynomial.coeff_map]
      simp only [eq_intCast, Rat.num_intCast, Rat.den_intCast]
      exact ⟨by have := hQ a; omega, by omega⟩
    · -- ℓ = ℓ' + 2
      obtain ⟨N, D, hDne, hNsz, hDsz, hSeq⟩ :=
        SRemS_eq_divInt P₀ Q₀ hP hQ hpq0 hq1 (ℓ' + 1 + 1) hℓne
      rw [if_neg (by omega)] at hSeq
      simp only [Nat.add_sub_cancel] at hSeq
      have hSm1ne : SRemS (mapQ P₀) (mapQ Q₀) (ℓ' + 1) ≠ 0 :=
        SRemS_ne_of_le (mapQ P₀) (mapQ Q₀) hPm hℓne (by omega)
      set mIdx := (SRemS (mapQ P₀) (mapQ Q₀) (ℓ' + 1)).natDegree - 1 with hmIdx_def
      have hmIdx_le : mIdx ≤ Q₀.natDegree := by
        rw [hmIdx_def, ← hqdm]
        have := SRemS_natDegree_le_q (mapQ P₀) (mapQ Q₀) hpqm hPm hSm1ne; omega
      have hIa : Int.size ((sResP P₀ Q₀ mIdx).coeff a) ≤ B :=
        le_trans (sResP_coeff_size_le P₀ Q₀ hP hQ hpq0 hmIdx_le a)
          (Nat.mul_le_mul (by omega) (Nat.add_le_add_left (Nat.size_le_size (by omega)) _))
      have hcoeff : (SRemS (mapQ P₀) (mapQ Q₀) (ℓ' + 1 + 1)).coeff a
          = Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D := by
        rw [hSeq, Polynomial.coeff_C_mul, sResP_map Int.cast_injective, Polynomial.coeff_map]
        simp only [eq_intCast, Rat.divInt_eq_div]; push_cast; ring
      rw [hcoeff]
      have hNmono : Int.size N ≤ 1 + (Q₀.natDegree + 1) * B := by
        refine le_trans hNsz ?_
        have : (ℓ' + 1 + 1) * B ≤ (Q₀.natDegree + 1) * B := Nat.mul_le_mul (by omega) le_rfl
        omega
      have hDmono : Int.size D ≤ 1 + (Q₀.natDegree + 1) * B := by
        refine le_trans hDsz ?_
        have : (ℓ' + 1 + 1) * B ≤ (Q₀.natDegree + 1) * B := Nat.mul_le_mul (by omega) le_rfl
        omega
      refine ⟨?_, ?_⟩
      · have hnum : Int.size (Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).num
            ≤ Int.size (N * (sResP P₀ Q₀ mIdx).coeff a) := by
          rcases eq_or_ne (N * (sResP P₀ Q₀ mIdx).coeff a) 0 with h0 | h0
          · rw [h0, Rat.zero_divInt]; simp [Int.size]
          · exact int_size_dvd_le h0 (Rat.num_dvd _ hDne)
        have hmul := int_size_mul_le N ((sResP P₀ Q₀ mIdx).coeff a)
        have hexp : (Q₀.natDegree + 2) * B + 1 = (1 + (Q₀.natDegree + 1) * B) + B := by ring
        rw [hexp]; omega
      · have hden : ((Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).den : ℤ) ∣ D :=
          Rat.den_dvd _ _
        have hdd : (Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).den ∣ D.natAbs := by
          have := Int.natAbs_dvd_natAbs.mpr hden; simpa using this
        have hle : (Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).den ≤ D.natAbs :=
          Nat.le_of_dvd (Int.natAbs_pos.mpr hDne) hdd
        have hsz : Nat.size (Rat.divInt (N * (sResP P₀ Q₀ mIdx).coeff a) D).den
            ≤ Int.size D := Nat.size_le_size hle
        omega

end MainInduction

end Azurite.BPR.Chapter8

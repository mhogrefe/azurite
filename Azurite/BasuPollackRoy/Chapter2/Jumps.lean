import Azurite.BasuPollackRoy.Chapter2.Proposition_2_21
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue

/-!
# BPR Chapter 2.2: jumps of `Q/P` at a root of `P`

Let `P` and `Q` be polynomials over a real closed field `R` (more generally,
over any ordered field, since the predicates make sense in that setting).

Let `x` be a root of `P`. The function `Q/P` *jumps from `−∞` to `+∞` at `x`*
when:

1. the multiplicity `m` of `x` as a root of `P` is strictly bigger than the
   multiplicity `n` of `x` as a root of `Q`,
2. `m − n` is odd, and
3. the sign of `Q/P` immediately to the right of `x` is positive.

It *jumps from `+∞` to `−∞` at `x`* under the analogous conditions with the
right-hand sign negative.

## Implied one-sided behavior

* **Sign flip across `x` (any ordered field with the IVP).** Because `m − n`
  (equivalently `m + n`) is odd, the sign of `Q · P` flips across `x`:
  - `JumpsFromNegInfToPosInf.hasSignLeft` — `HasSignLeft (Q · P) x (-1)`
  - `JumpsFromPosInfToNegInf.hasSignLeft` — `HasSignLeft (Q · P) x 1`

* **Genuine one-sided limits to ±∞ (over `ℝ`).** Using `Polynomial.continuous`
  on `ℝ` together with the order-topology infrastructure, the rational
  function `Q/P` actually tends to `±∞`:
  - `JumpsFromNegInfToPosInf.tendsto_atTop_nhdsGT` — `Q/P → +∞` as `t → x⁺`
  - `JumpsFromNegInfToPosInf.tendsto_atBot_nhdsLT` — `Q/P → −∞` as `t → x⁻`
  - `JumpsFromPosInfToNegInf.tendsto_atBot_nhdsGT` — `Q/P → −∞` as `t → x⁺`
  - `JumpsFromPosInfToNegInf.tendsto_atTop_nhdsLT` — `Q/P → +∞` as `t → x⁻`
-/

namespace Azurite.BPR

open Polynomial Filter Topology

/-! ### Predicates (over any ordered field) -/

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The function `Q/P` jumps from `−∞` to `+∞` at `x`: the multiplicity of
    `x` as a root of `P` strictly exceeds its multiplicity as a root of `Q`,
    the difference is odd, and the sign of `Q/P` immediately to the right of
    `x` is positive. -/
def JumpsFromNegInfToPosInf (Q P : R[X]) (x : R) : Prop :=
  P.rootMultiplicity x > Q.rootMultiplicity x ∧
  Odd (P.rootMultiplicity x - Q.rootMultiplicity x) ∧
  HasSignRight (Q * P) x 1

/-- The function `Q/P` jumps from `+∞` to `−∞` at `x`: the multiplicity of
    `x` as a root of `P` strictly exceeds its multiplicity as a root of `Q`,
    the difference is odd, and the sign of `Q/P` immediately to the right of
    `x` is negative. -/
def JumpsFromPosInfToNegInf (Q P : R[X]) (x : R) : Prop :=
  P.rootMultiplicity x > Q.rootMultiplicity x ∧
  Odd (P.rootMultiplicity x - Q.rootMultiplicity x) ∧
  HasSignRight (Q * P) x (-1)

/-! ### Auxiliary lemmas (any ordered field) -/

section Aux

variable {Q P : R[X]} {x : R}

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma jump_aux_P_ne (h : P.rootMultiplicity x > Q.rootMultiplicity x) :
    P ≠ 0 := by
  intro hP
  rw [hP, rootMultiplicity_zero] at h
  omega

private lemma jump_aux_Q_ne_of_signRight_pos
    (hsign : HasSignRight (Q * P) x 1) : Q ≠ 0 := by
  intro hQ
  rw [hQ, zero_mul] at hsign
  obtain ⟨b, hxb, hsign'⟩ := hsign
  obtain ⟨t, hxt, htb⟩ := exists_between hxb
  have h_eval : SignType.sign ((0 : R[X]).eval t) = 1 := hsign' t ⟨hxt, htb⟩
  simp at h_eval

private lemma jump_aux_Q_ne_of_signRight_neg
    (hsign : HasSignRight (Q * P) x (-1)) : Q ≠ 0 := by
  intro hQ
  rw [hQ, zero_mul] at hsign
  obtain ⟨b, hxb, hsign'⟩ := hsign
  obtain ⟨t, hxt, htb⟩ := exists_between hxb
  have h_eval : SignType.sign ((0 : R[X]).eval t) = -1 := hsign' t ⟨hxt, htb⟩
  simp at h_eval

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The total multiplicity of `x` as a root of `Q · P` is odd. -/
private lemma jump_aux_odd_total (hQ_ne : Q ≠ 0) (hP_ne : P ≠ 0)
    (hgt : P.rootMultiplicity x > Q.rootMultiplicity x)
    (hodd : Odd (P.rootMultiplicity x - Q.rootMultiplicity x)) :
    Odd ((Q * P).rootMultiplicity x) := by
  rw [rootMultiplicity_mul (mul_ne_zero hQ_ne hP_ne)]
  set m := P.rootMultiplicity x
  set n := Q.rootMultiplicity x
  have heq : n + m = (m - n) + 2 * n := by omega
  rw [heq]
  exact hodd.add_even (even_two_mul _)

end Aux

/-! ### Implied sign on the left (any ordered field with IVP) -/

section ImpliedSignLeft

variable {Q P : R[X]} {x : R}
  (hIVP : Azurite.BPR.HasIntermediateValueProperty R)

include hIVP in
/-- **Implied one-sided fact.** If `Q/P` jumps from `−∞` to `+∞` at `x`, then
    the sign of `Q · P` immediately to the **left** of `x` is `-1`. -/
theorem JumpsFromNegInfToPosInf.hasSignLeft
    (h : JumpsFromNegInfToPosInf Q P x) : HasSignLeft (Q * P) x (-1) := by
  obtain ⟨hgt, hodd, hsign⟩ := h
  have hP_ne : P ≠ 0 := jump_aux_P_ne hgt
  have hQ_ne : Q ≠ 0 := jump_aux_Q_ne_of_signRight_pos hsign
  have hQP_ne : Q * P ≠ 0 := mul_ne_zero hQ_ne hP_ne
  have h_odd_total : Odd ((Q * P).rootMultiplicity x) :=
    jump_aux_odd_total hQ_ne hP_ne hgt hodd
  have h_right := Proposition2_21.proposition_2_21_right hIVP hQP_ne x
  have h_left := Proposition2_21.proposition_2_21_left hIVP hQP_ne x
  have hs : SignType.sign
      ((((⇑derivative)^[(Q * P).rootMultiplicity x]) (Q * P)).eval x) = 1 :=
    h_right.unique hsign
  rw [hs, mul_one, h_odd_total.neg_one_pow] at h_left
  exact h_left

include hIVP in
/-- **Implied one-sided fact.** If `Q/P` jumps from `+∞` to `−∞` at `x`, then
    the sign of `Q · P` immediately to the **left** of `x` is `1`. -/
theorem JumpsFromPosInfToNegInf.hasSignLeft
    (h : JumpsFromPosInfToNegInf Q P x) : HasSignLeft (Q * P) x 1 := by
  obtain ⟨hgt, hodd, hsign⟩ := h
  have hP_ne : P ≠ 0 := jump_aux_P_ne hgt
  have hQ_ne : Q ≠ 0 := jump_aux_Q_ne_of_signRight_neg hsign
  have hQP_ne : Q * P ≠ 0 := mul_ne_zero hQ_ne hP_ne
  have h_odd_total : Odd ((Q * P).rootMultiplicity x) :=
    jump_aux_odd_total hQ_ne hP_ne hgt hodd
  have h_right := Proposition2_21.proposition_2_21_right hIVP hQP_ne x
  have h_left := Proposition2_21.proposition_2_21_left hIVP hQP_ne x
  have hs : SignType.sign
      ((((⇑derivative)^[(Q * P).rootMultiplicity x]) (Q * P)).eval x) = -1 :=
    h_right.unique hsign
  rw [hs, h_odd_total.neg_one_pow] at h_left
  simpa using h_left

end ImpliedSignLeft

/-! ### One-sided limits over `ℝ` -/

section RealLimits

/-- The IVP for `ℝ`, derived from Mathlib's intermediate value theorem. -/
private lemma real_hasIVP : Azurite.BPR.HasIntermediateValueProperty ℝ := by
  intro F a b hab hsign
  have hcont : ContinuousOn (F.eval) (Set.Icc a b) := F.continuous.continuousOn
  rcases mul_neg_iff.mp hsign with ⟨ha_pos, hb_neg⟩ | ⟨ha_neg, hb_pos⟩
  · have hzero : (0 : ℝ) ∈ Set.Ioo (F.eval b) (F.eval a) := ⟨hb_neg, ha_pos⟩
    obtain ⟨c, hc, hFc⟩ := intermediate_value_Ioo' hab.le hcont hzero
    exact ⟨c, hc.1, hc.2, hFc⟩
  · have hzero : (0 : ℝ) ∈ Set.Ioo (F.eval a) (F.eval b) := ⟨ha_neg, hb_pos⟩
    obtain ⟨c, hc, hFc⟩ := intermediate_value_Ioo hab.le hcont hzero
    exact ⟨c, hc.1, hc.2, hFc⟩

variable {Q P : ℝ[X]} {x : ℝ}

/-- The "leftover" factor `R := (Q · P) /ₘ (X − C x)^(m+n)`. -/
private noncomputable def rPoly (Q P : ℝ[X]) (x : ℝ) : ℝ[X] :=
  (Q * P) /ₘ (X - C x) ^ (Q * P).rootMultiplicity x

/-- The "leftover" factor `P̃ := P /ₘ (X − C x)^m`. -/
private noncomputable def pTilde (P : ℝ[X]) (x : ℝ) : ℝ[X] :=
  P /ₘ (X - C x) ^ P.rootMultiplicity x

private lemma pTilde_eval_at_ne (hP_ne : P ≠ 0) :
    (pTilde P x).eval x ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero x hP_ne

private lemma rPoly_eval_at_ne (hQP_ne : Q * P ≠ 0) :
    (rPoly Q P x).eval x ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero x hQP_ne

/-- Pointwise: `P(t) = (t − x)^m · P̃(t)`. -/
private lemma p_eval_factor (P : ℝ[X]) (x t : ℝ) :
    P.eval t = (t - x) ^ P.rootMultiplicity x * (pTilde P x).eval t := by
  have hfac := pow_mul_divByMonic_rootMultiplicity_eq P x
  have h := congrArg (Polynomial.eval t) hfac.symm
  simpa [pTilde] using h

/-- Polynomial identity: `R = P̃ · Q̃` (where `R = (Q·P) /ₘ (X − C x)^(m+n)`,
    `P̃ = P /ₘ (X − C x)^m`, `Q̃ = Q /ₘ (X − C x)^n`). -/
private lemma rPoly_eq_mul (hQ_ne : Q ≠ 0) (hP_ne : P ≠ 0) :
    rPoly Q P x = pTilde Q x * pTilde P x := by
  set m := P.rootMultiplicity x with hm_def
  set n := Q.rootMultiplicity x with hn_def
  set k := (Q * P).rootMultiplicity x with hk_def
  have hk : k = n + m := by rw [hk_def, rootMultiplicity_mul (mul_ne_zero hQ_ne hP_ne)]
  have hP_factor : (X - C x) ^ m * pTilde P x = P :=
    pow_mul_divByMonic_rootMultiplicity_eq P x
  have hQ_factor : (X - C x) ^ n * pTilde Q x = Q :=
    pow_mul_divByMonic_rootMultiplicity_eq Q x
  have hR_factor : (X - C x) ^ k * rPoly Q P x = Q * P :=
    pow_mul_divByMonic_rootMultiplicity_eq (Q * P) x
  -- (X-Cx)^k * R = Q*P = (X-Cx)^n * Q̃ * (X-Cx)^m * P̃ = (X-Cx)^(n+m) * (Q̃ * P̃)
  -- Combine the two factorizations of `Q * P`:
  --   `(X-Cx)^k · R = Q * P = ((X-Cx)^n * Q̃) * ((X-Cx)^m * P̃)
  --                       = (X-Cx)^(n+m) * (Q̃ * P̃)`
  have h_QP_eq : Q * P = (X - C x) ^ (n + m) * (pTilde Q x * pTilde P x) := by
    have : ((X - C x) ^ n * pTilde Q x) * ((X - C x) ^ m * pTilde P x) =
        (X - C x) ^ (n + m) * (pTilde Q x * pTilde P x) := by ring
    rw [← this, hQ_factor, hP_factor]
  have h_combined : (X - C x) ^ k * rPoly Q P x =
      (X - C x) ^ k * (pTilde Q x * pTilde P x) := by
    rw [hR_factor, h_QP_eq, hk]
  exact mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero x)) h_combined

/-- Algebraic identity on the punctured set where `t ≠ x` and `P̃(t) ≠ 0`:
    `Q(t) / P(t) = R(t) / ((t − x)^(m − n) · P̃(t)²)` (when `m ≥ n`). -/
private lemma quotient_factored
    (hQ_ne : Q ≠ 0) (hP_ne : P ≠ 0)
    (hge : Q.rootMultiplicity x ≤ P.rootMultiplicity x)
    {t : ℝ} (ht_ne : t ≠ x)
    (hPtilde_ne : (pTilde P x).eval t ≠ 0) :
    Q.eval t / P.eval t =
      (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2) := by
  set m := P.rootMultiplicity x
  set n := Q.rootMultiplicity x
  have hP_eval : P.eval t = (t - x) ^ m * (pTilde P x).eval t := p_eval_factor P x t
  have hQ_eval : Q.eval t = (t - x) ^ n * (pTilde Q x).eval t := p_eval_factor Q x t
  have hR_eval : (rPoly Q P x).eval t =
      (pTilde Q x).eval t * (pTilde P x).eval t := by
    rw [rPoly_eq_mul hQ_ne hP_ne, eval_mul]
  rw [hQ_eval, hP_eval, hR_eval]
  have htx_ne : t - x ≠ 0 := sub_ne_zero.mpr ht_ne
  have hpow_m_ne : (t - x) ^ m ≠ 0 := pow_ne_zero _ htx_ne
  have hpow_mn_ne : (t - x) ^ (m - n) ≠ 0 := pow_ne_zero _ htx_ne
  have hPt_sq_ne : (pTilde P x).eval t ^ 2 ≠ 0 := pow_ne_zero _ hPtilde_ne
  have hpow_split : (t - x) ^ m = (t - x) ^ n * (t - x) ^ (m - n) := by
    rw [← pow_add, show n + (m - n) = m from by omega]
  rw [hpow_split]
  field_simp

/-- Sign of `R(x)` from `Q/P` jumping `−∞ → +∞`: `R(x) > 0`. -/
private lemma rPoly_eval_pos
    (h : JumpsFromNegInfToPosInf Q P x) : 0 < (rPoly Q P x).eval x := by
  obtain ⟨hgt, _, hsign⟩ := h
  have hP_ne : P ≠ 0 := jump_aux_P_ne hgt
  have hQ_ne : Q ≠ 0 := jump_aux_Q_ne_of_signRight_pos hsign
  have hQP_ne : Q * P ≠ 0 := mul_ne_zero hQ_ne hP_ne
  have h_right := Proposition2_21.proposition_2_21_right real_hasIVP hQP_ne x
  have hs : SignType.sign
      ((((⇑derivative)^[(Q * P).rootMultiplicity x]) (Q * P)).eval x) = 1 :=
    h_right.unique hsign
  -- (D^k)(Q*P)(x) = k! · R(x).
  have h_eval := eval_iterate_derivative_rootMultiplicity (p := Q * P) (t := x)
  show 0 < ((Q * P) /ₘ (X - C x) ^ (Q * P).rootMultiplicity x).eval x
  rw [h_eval, nsmul_eq_mul, sign_mul,
    sign_pos (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _),
    one_mul, sign_eq_one_iff] at hs
  exact hs

/-- Sign of `R(x)` from `Q/P` jumping `+∞ → −∞`: `R(x) < 0`. -/
private lemma rPoly_eval_neg
    (h : JumpsFromPosInfToNegInf Q P x) : (rPoly Q P x).eval x < 0 := by
  obtain ⟨hgt, _, hsign⟩ := h
  have hP_ne : P ≠ 0 := jump_aux_P_ne hgt
  have hQ_ne : Q ≠ 0 := jump_aux_Q_ne_of_signRight_neg hsign
  have hQP_ne : Q * P ≠ 0 := mul_ne_zero hQ_ne hP_ne
  have h_right := Proposition2_21.proposition_2_21_right real_hasIVP hQP_ne x
  have hs : SignType.sign
      ((((⇑derivative)^[(Q * P).rootMultiplicity x]) (Q * P)).eval x) = -1 :=
    h_right.unique hsign
  have h_eval := eval_iterate_derivative_rootMultiplicity (p := Q * P) (t := x)
  show ((Q * P) /ₘ (X - C x) ^ (Q * P).rootMultiplicity x).eval x < 0
  rw [h_eval, nsmul_eq_mul, sign_mul,
    sign_pos (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _),
    one_mul, sign_eq_neg_one_iff] at hs
  exact hs

/-! #### Limit of the denominator -/

/-- For `t > x`, `(t − x)^k > 0` for any `k`. -/
private lemma sub_pow_pos_of_lt {k : ℕ} {t : ℝ} (ht : x < t) :
    0 < (t - x) ^ k := pow_pos (sub_pos.mpr ht) k

/-- For `t < x` and `k` odd, `(t − x)^k < 0`. -/
private lemma sub_pow_neg_of_gt_odd {k : ℕ} (hk : Odd k) {t : ℝ} (ht : t < x) :
    (t - x) ^ k < 0 := hk.pow_neg (sub_neg.mpr ht)

/-- The denominator `(t − x)^(m − n) · P̃(t)²` tends to `0` from above as
    `t → x⁺`, provided `m > n` and `P ≠ 0`. -/
private lemma denom_tendsto_nhdsGT_zero_right
    (hP_ne : P ≠ 0) (hgt : P.rootMultiplicity x > Q.rootMultiplicity x) :
    Tendsto
      (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2) (𝓝[>] x) (𝓝[>] 0) := by
  have hPtilde_ne : (pTilde P x).eval x ≠ 0 := pTilde_eval_at_ne hP_ne
  have hk_ne : P.rootMultiplicity x - Q.rootMultiplicity x ≠ 0 := by omega
  -- Tendency to 𝓝 0
  have h_sub_cts : Continuous (fun t : ℝ => t - x) := by fun_prop
  have h_pow_cts : Continuous
      (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x)) :=
    h_sub_cts.pow _
  have h1 : Tendsto
      (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x))
      (𝓝 x) (𝓝 0) := by
    have := h_pow_cts.tendsto x
    simpa [zero_pow hk_ne] using this
  have h2 : Tendsto (fun t : ℝ => (pTilde P x).eval t ^ 2) (𝓝 x)
      (𝓝 ((pTilde P x).eval x ^ 2)) :=
    ((pTilde P x).continuous.pow 2).tendsto x
  have h_tendsto_zero : Tendsto
      (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2) (𝓝 x) (𝓝 0) := by
    have := h1.mul h2
    simpa using this
  -- Eventually positive on 𝓝[>] x
  have h_pos : ∀ᶠ t in 𝓝[>] x,
      0 < (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2 := by
    have h_t_gt : ∀ᶠ t in 𝓝[>] x, x < t :=
      eventually_nhdsWithin_of_forall (fun _ ht => ht)
    have h_Pt_ne : ∀ᶠ t in 𝓝[>] x, (pTilde P x).eval t ≠ 0 := by
      have hcts := (pTilde P x).continuous.continuousAt (x := x)
      exact (hcts.eventually_ne hPtilde_ne).filter_mono nhdsWithin_le_nhds
    filter_upwards [h_t_gt, h_Pt_ne] with t ht_gt hPt_ne
    have h_pow_pos : 0 < (t - x) ^
        (P.rootMultiplicity x - Q.rootMultiplicity x) :=
      sub_pow_pos_of_lt ht_gt
    have h_sq_pos : 0 < (pTilde P x).eval t ^ 2 := by
      have := hPt_ne; positivity
    exact mul_pos h_pow_pos h_sq_pos
  rw [tendsto_nhdsWithin_iff]
  exact ⟨h_tendsto_zero.mono_left nhdsWithin_le_nhds, by simpa using h_pos⟩

/-- The denominator `(t − x)^(m − n) · P̃(t)²` tends to `0` from below as
    `t → x⁻`, provided `m > n`, `m − n` is odd, and `P ≠ 0`. -/
private lemma denom_tendsto_nhdsLT_zero_left
    (hP_ne : P ≠ 0)
    (hgt : P.rootMultiplicity x > Q.rootMultiplicity x)
    (hodd : Odd (P.rootMultiplicity x - Q.rootMultiplicity x)) :
    Tendsto
      (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2) (𝓝[<] x) (𝓝[<] 0) := by
  have hPtilde_ne : (pTilde P x).eval x ≠ 0 := pTilde_eval_at_ne hP_ne
  have hk_ne : P.rootMultiplicity x - Q.rootMultiplicity x ≠ 0 := by omega
  have h_sub_cts : Continuous (fun t : ℝ => t - x) := by fun_prop
  have h_pow_cts : Continuous
      (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x)) :=
    h_sub_cts.pow _
  have h1 : Tendsto
      (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x))
      (𝓝 x) (𝓝 0) := by
    have := h_pow_cts.tendsto x
    simpa [zero_pow hk_ne] using this
  have h2 : Tendsto (fun t : ℝ => (pTilde P x).eval t ^ 2) (𝓝 x)
      (𝓝 ((pTilde P x).eval x ^ 2)) :=
    ((pTilde P x).continuous.pow 2).tendsto x
  have h_tendsto_zero : Tendsto
      (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2) (𝓝 x) (𝓝 0) := by
    have := h1.mul h2
    simpa using this
  -- Eventually negative on 𝓝[<] x
  have h_neg : ∀ᶠ t in 𝓝[<] x,
      (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2 < 0 := by
    have h_t_lt : ∀ᶠ t in 𝓝[<] x, t < x :=
      eventually_nhdsWithin_of_forall (fun _ ht => ht)
    have h_Pt_ne : ∀ᶠ t in 𝓝[<] x, (pTilde P x).eval t ≠ 0 := by
      have hcts := (pTilde P x).continuous.continuousAt (x := x)
      exact (hcts.eventually_ne hPtilde_ne).filter_mono nhdsWithin_le_nhds
    filter_upwards [h_t_lt, h_Pt_ne] with t ht_lt hPt_ne
    have h_pow_neg : (t - x) ^
        (P.rootMultiplicity x - Q.rootMultiplicity x) < 0 :=
      sub_pow_neg_of_gt_odd hodd ht_lt
    have h_sq_pos : 0 < (pTilde P x).eval t ^ 2 := by
      have := hPt_ne; positivity
    exact mul_neg_of_neg_of_pos h_pow_neg h_sq_pos
  rw [tendsto_nhdsWithin_iff]
  exact ⟨h_tendsto_zero.mono_left nhdsWithin_le_nhds, by simpa using h_neg⟩

/-! #### The four limit theorems -/

/-- `Q/P → +∞` as `t → x⁺` when `Q/P` jumps from `−∞` to `+∞` at `x`. -/
theorem JumpsFromNegInfToPosInf.tendsto_atTop_nhdsGT
    (h : JumpsFromNegInfToPosInf Q P x) :
    Tendsto (fun t => Q.eval t / P.eval t) (𝓝[>] x) atTop := by
  obtain ⟨hgt, hodd, hsign⟩ := h
  have hP_ne : P ≠ 0 := jump_aux_P_ne hgt
  have hQ_ne : Q ≠ 0 := jump_aux_Q_ne_of_signRight_pos hsign
  have hR_pos : 0 < (rPoly Q P x).eval x := rPoly_eval_pos ⟨hgt, hodd, hsign⟩
  have h_t_ne : ∀ᶠ t in 𝓝[>] x, t ≠ x :=
    eventually_nhdsWithin_of_forall (fun _ ht => ne_of_gt ht)
  have h_Pt_ne : ∀ᶠ t in 𝓝[>] x, (pTilde P x).eval t ≠ 0 := by
    have hcts := (pTilde P x).continuous.continuousAt (x := x)
    exact (hcts.eventually_ne (pTilde_eval_at_ne hP_ne)).filter_mono
      nhdsWithin_le_nhds
  have h_eq : ∀ᶠ t in 𝓝[>] x,
      Q.eval t / P.eval t =
        (rPoly Q P x).eval t /
          ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
            (pTilde P x).eval t ^ 2) := by
    filter_upwards [h_t_ne, h_Pt_ne] with t ht_ne hPt_ne using
      quotient_factored hQ_ne hP_ne hgt.le ht_ne hPt_ne
  have h_denom : Tendsto (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) * (pTilde P x).eval t ^ 2) (𝓝[>] x) (𝓝[>] 0) :=
    denom_tendsto_nhdsGT_zero_right hP_ne hgt
  have h_inv : Tendsto
      (fun t : ℝ => ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2)⁻¹) (𝓝[>] x) atTop :=
    h_denom.inv_tendsto_nhdsGT_zero
  have h_num : Tendsto (fun t => (rPoly Q P x).eval t)
      (𝓝[>] x) (𝓝 ((rPoly Q P x).eval x)) :=
    ((rPoly Q P x).continuous.tendsto x).mono_left nhdsWithin_le_nhds
  have h_main : Tendsto
      (fun t => (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2))
      (𝓝[>] x) atTop := by
    have h_to_mul : (fun t => (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2))
        = (fun t => ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2)⁻¹ * (rPoly Q P x).eval t) := by
      funext t; rw [div_eq_inv_mul]
    rw [h_to_mul]
    exact h_inv.atTop_mul_pos hR_pos h_num
  exact h_main.congr' (Filter.EventuallyEq.symm h_eq)

/-- `Q/P → −∞` as `t → x⁻` when `Q/P` jumps from `−∞` to `+∞` at `x`. -/
theorem JumpsFromNegInfToPosInf.tendsto_atBot_nhdsLT
    (h : JumpsFromNegInfToPosInf Q P x) :
    Tendsto (fun t => Q.eval t / P.eval t) (𝓝[<] x) atBot := by
  obtain ⟨hgt, hodd, hsign⟩ := h
  have hP_ne : P ≠ 0 := jump_aux_P_ne hgt
  have hQ_ne : Q ≠ 0 := jump_aux_Q_ne_of_signRight_pos hsign
  have hR_pos : 0 < (rPoly Q P x).eval x := rPoly_eval_pos ⟨hgt, hodd, hsign⟩
  have h_t_ne : ∀ᶠ t in 𝓝[<] x, t ≠ x :=
    eventually_nhdsWithin_of_forall (fun _ ht => ne_of_lt ht)
  have h_Pt_ne : ∀ᶠ t in 𝓝[<] x, (pTilde P x).eval t ≠ 0 := by
    have hcts := (pTilde P x).continuous.continuousAt (x := x)
    exact (hcts.eventually_ne (pTilde_eval_at_ne hP_ne)).filter_mono
      nhdsWithin_le_nhds
  have h_eq : ∀ᶠ t in 𝓝[<] x,
      Q.eval t / P.eval t =
        (rPoly Q P x).eval t /
          ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
            (pTilde P x).eval t ^ 2) := by
    filter_upwards [h_t_ne, h_Pt_ne] with t ht_ne hPt_ne using
      quotient_factored hQ_ne hP_ne hgt.le ht_ne hPt_ne
  have h_denom : Tendsto (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) * (pTilde P x).eval t ^ 2) (𝓝[<] x) (𝓝[<] 0) :=
    denom_tendsto_nhdsLT_zero_left hP_ne hgt hodd
  have h_inv : Tendsto
      (fun t : ℝ => ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2)⁻¹) (𝓝[<] x) atBot :=
    h_denom.inv_tendsto_nhdsLT_zero
  have h_num : Tendsto (fun t => (rPoly Q P x).eval t)
      (𝓝[<] x) (𝓝 ((rPoly Q P x).eval x)) :=
    ((rPoly Q P x).continuous.tendsto x).mono_left nhdsWithin_le_nhds
  have h_main : Tendsto
      (fun t => (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2))
      (𝓝[<] x) atBot := by
    have h_to_mul : (fun t => (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2))
        = (fun t => ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2)⁻¹ * (rPoly Q P x).eval t) := by
      funext t; rw [div_eq_inv_mul]
    rw [h_to_mul]
    exact h_inv.atBot_mul_pos hR_pos h_num
  exact h_main.congr' (Filter.EventuallyEq.symm h_eq)

/-- `Q/P → −∞` as `t → x⁺` when `Q/P` jumps from `+∞` to `−∞` at `x`. -/
theorem JumpsFromPosInfToNegInf.tendsto_atBot_nhdsGT
    (h : JumpsFromPosInfToNegInf Q P x) :
    Tendsto (fun t => Q.eval t / P.eval t) (𝓝[>] x) atBot := by
  obtain ⟨hgt, hodd, hsign⟩ := h
  have hP_ne : P ≠ 0 := jump_aux_P_ne hgt
  have hQ_ne : Q ≠ 0 := jump_aux_Q_ne_of_signRight_neg hsign
  have hR_neg : (rPoly Q P x).eval x < 0 := rPoly_eval_neg ⟨hgt, hodd, hsign⟩
  have h_t_ne : ∀ᶠ t in 𝓝[>] x, t ≠ x :=
    eventually_nhdsWithin_of_forall (fun _ ht => ne_of_gt ht)
  have h_Pt_ne : ∀ᶠ t in 𝓝[>] x, (pTilde P x).eval t ≠ 0 := by
    have hcts := (pTilde P x).continuous.continuousAt (x := x)
    exact (hcts.eventually_ne (pTilde_eval_at_ne hP_ne)).filter_mono
      nhdsWithin_le_nhds
  have h_eq : ∀ᶠ t in 𝓝[>] x,
      Q.eval t / P.eval t =
        (rPoly Q P x).eval t /
          ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
            (pTilde P x).eval t ^ 2) := by
    filter_upwards [h_t_ne, h_Pt_ne] with t ht_ne hPt_ne using
      quotient_factored hQ_ne hP_ne hgt.le ht_ne hPt_ne
  have h_denom : Tendsto (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) * (pTilde P x).eval t ^ 2) (𝓝[>] x) (𝓝[>] 0) :=
    denom_tendsto_nhdsGT_zero_right hP_ne hgt
  have h_inv : Tendsto
      (fun t : ℝ => ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2)⁻¹) (𝓝[>] x) atTop :=
    h_denom.inv_tendsto_nhdsGT_zero
  have h_num : Tendsto (fun t => (rPoly Q P x).eval t)
      (𝓝[>] x) (𝓝 ((rPoly Q P x).eval x)) :=
    ((rPoly Q P x).continuous.tendsto x).mono_left nhdsWithin_le_nhds
  have h_main : Tendsto
      (fun t => (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2))
      (𝓝[>] x) atBot := by
    have h_to_mul : (fun t => (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2))
        = (fun t => ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2)⁻¹ * (rPoly Q P x).eval t) := by
      funext t; rw [div_eq_inv_mul]
    rw [h_to_mul]
    exact h_inv.atTop_mul_neg hR_neg h_num
  exact h_main.congr' (Filter.EventuallyEq.symm h_eq)

/-- `Q/P → +∞` as `t → x⁻` when `Q/P` jumps from `+∞` to `−∞` at `x`. -/
theorem JumpsFromPosInfToNegInf.tendsto_atTop_nhdsLT
    (h : JumpsFromPosInfToNegInf Q P x) :
    Tendsto (fun t => Q.eval t / P.eval t) (𝓝[<] x) atTop := by
  obtain ⟨hgt, hodd, hsign⟩ := h
  have hP_ne : P ≠ 0 := jump_aux_P_ne hgt
  have hQ_ne : Q ≠ 0 := jump_aux_Q_ne_of_signRight_neg hsign
  have hR_neg : (rPoly Q P x).eval x < 0 := rPoly_eval_neg ⟨hgt, hodd, hsign⟩
  have h_t_ne : ∀ᶠ t in 𝓝[<] x, t ≠ x :=
    eventually_nhdsWithin_of_forall (fun _ ht => ne_of_lt ht)
  have h_Pt_ne : ∀ᶠ t in 𝓝[<] x, (pTilde P x).eval t ≠ 0 := by
    have hcts := (pTilde P x).continuous.continuousAt (x := x)
    exact (hcts.eventually_ne (pTilde_eval_at_ne hP_ne)).filter_mono
      nhdsWithin_le_nhds
  have h_eq : ∀ᶠ t in 𝓝[<] x,
      Q.eval t / P.eval t =
        (rPoly Q P x).eval t /
          ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
            (pTilde P x).eval t ^ 2) := by
    filter_upwards [h_t_ne, h_Pt_ne] with t ht_ne hPt_ne using
      quotient_factored hQ_ne hP_ne hgt.le ht_ne hPt_ne
  have h_denom : Tendsto (fun t : ℝ => (t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) * (pTilde P x).eval t ^ 2) (𝓝[<] x) (𝓝[<] 0) :=
    denom_tendsto_nhdsLT_zero_left hP_ne hgt hodd
  have h_inv : Tendsto
      (fun t : ℝ => ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
        (pTilde P x).eval t ^ 2)⁻¹) (𝓝[<] x) atBot :=
    h_denom.inv_tendsto_nhdsLT_zero
  have h_num : Tendsto (fun t => (rPoly Q P x).eval t)
      (𝓝[<] x) (𝓝 ((rPoly Q P x).eval x)) :=
    ((rPoly Q P x).continuous.tendsto x).mono_left nhdsWithin_le_nhds
  have h_main : Tendsto
      (fun t => (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2))
      (𝓝[<] x) atTop := by
    have h_to_mul : (fun t => (rPoly Q P x).eval t /
        ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2))
        = (fun t => ((t - x) ^ (P.rootMultiplicity x - Q.rootMultiplicity x) *
          (pTilde P x).eval t ^ 2)⁻¹ * (rPoly Q P x).eval t) := by
      funext t; rw [div_eq_inv_mul]
    rw [h_to_mul]
    exact h_inv.atBot_mul_neg hR_neg h_num
  exact h_main.congr' (Filter.EventuallyEq.symm h_eq)

end RealLimits

end Azurite.BPR

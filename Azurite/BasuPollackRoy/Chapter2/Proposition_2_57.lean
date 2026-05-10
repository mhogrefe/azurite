import Azurite.BasuPollackRoy.Chapter2.TarskiQuery
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_21

/-!
# BPR Proposition 2.57

For `P ≠ 0` and `Q` in `R[X]` (over a real closed field `R`, or any ordered
field with the intermediate value property), the Tarski-query of `Q` for `P`
on `(a, b)` equals the Cauchy index of `P' · Q / P`:

`TaQ(Q, P; a, b) = Ind(P' · Q / P; a, b)`.

The proof goes via a per-root identity: at each `P`-root `x ∈ (a, b)`, the
contribution `sign(Q(x))` to the Tarski-query equals the jump contribution
of `P' · Q / P` at `x`. Specifically, with `µ = P.rootMultiplicity x ≥ 1`:

* If `Q(x) > 0`, then `P' · Q / P` jumps from `−∞` to `+∞` at `x`
  (contribution `+1` to the index, matching `sign(Q(x)) = +1`).
* If `Q(x) < 0`, then `P' · Q / P` jumps from `+∞` to `−∞` at `x`
  (contribution `−1` to the index, matching `sign(Q(x)) = −1`).
* If `Q(x) = 0`, then `(P' · Q).rootMultiplicity x ≥ µ`, so the
  multiplicity condition for a jump fails (contribution `0`,
  matching `sign(Q(x)) = 0`).
-/

open scoped Polynomial
open Polynomial

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Helper: a polynomial that is nonzero at `x` has root multiplicity zero
    at `x`. -/
private lemma rootMultiplicity_eq_zero_of_eval_ne {p : R[X]} {x : R}
    (h : p.eval x ≠ 0) : p.rootMultiplicity x = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  exact h hroot

/-- For `P ≠ 0` with `1 ≤ P.rootMultiplicity x`, the derivative has
    multiplicity exactly one less:
    `P.derivative.rootMultiplicity x + 1 = P.rootMultiplicity x`.

    Proof: factor `P = (X − Cx)^µ · P̃` with `P̃(x) ≠ 0`. Then
    `P' = (X − Cx)^{µ−1} · g` where `g = µ · P̃ + (X − Cx) · P̃'` and
    `g(x) = µ · P̃(x) ≠ 0` (using char-0 of any ordered field). -/
private lemma rootMultiplicity_derivative
    {P : R[X]} (hP : P ≠ 0) {x : R} (hmu : 1 ≤ P.rootMultiplicity x) :
    P.derivative.rootMultiplicity x + 1 = P.rootMultiplicity x := by
  set mu := P.rootMultiplicity x with hmu_def
  set Ptilde := P /ₘ (X - C x) ^ mu with hPtilde_def
  have hP_eq : (X - C x) ^ mu * Ptilde = P :=
    pow_mul_divByMonic_rootMultiplicity_eq P x
  have hPtilde_eval_ne : Ptilde.eval x ≠ 0 :=
    eval_divByMonic_pow_rootMultiplicity_ne_zero x hP
  set g := (C (mu : R)) * Ptilde + (X - C x) * Ptilde.derivative with hg_def
  have h_deriv : P.derivative = (X - C x) ^ (mu - 1) * g := by
    rw [← hP_eq, derivative_mul, derivative_X_sub_C_pow, hg_def]
    have h_pow_split : (X - C x) ^ mu = (X - C x) ^ (mu - 1) * (X - C x) := by
      rw [← pow_succ, Nat.sub_add_cancel hmu]
    rw [h_pow_split]
    ring
  have hg_eval : g.eval x = (mu : R) * Ptilde.eval x := by simp [g]
  have hmu_R_ne : (mu : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hmu)
  have hg_eval_ne : g.eval x ≠ 0 := by
    rw [hg_eval]; exact mul_ne_zero hmu_R_ne hPtilde_eval_ne
  have hg_ne : g ≠ 0 := fun h => hg_eval_ne (by rw [h]; simp)
  have hpow_ne : ((X - C x) ^ (mu - 1) : R[X]) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero x)
  have hP'_ne : P.derivative ≠ 0 := by
    rw [h_deriv]; exact mul_ne_zero hpow_ne hg_ne
  rw [h_deriv, Polynomial.rootMultiplicity_mul (by rw [← h_deriv]; exact hP'_ne)]
  rw [Polynomial.rootMultiplicity_X_sub_C_pow]
  rw [rootMultiplicity_eq_zero_of_eval_ne hg_eval_ne]
  omega

/-- For `P ≠ 0` with `x ∈ P.roots`, the derivative `P'` is nonzero.
    (In char 0, `P' = 0` forces `P` to be a constant, which has no roots.) -/
private lemma derivative_ne_zero_of_mem_roots
    {P : R[X]} (hP : P ≠ 0) {x : R} (hx : x ∈ P.roots) :
    P.derivative ≠ 0 := by
  intro hP'
  have hroot : P.IsRoot x := (mem_roots hP).mp hx
  have hnatDeg : P.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hP'
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hnatDeg
  rw [IsRoot, eval_C] at hroot
  rw [hroot] at hP
  simp at hP

/-- **Sign-on-right at a `P`-root for `P' · Q · P`.**

    For `P ≠ 0`, `Q ≠ 0`, `x ∈ P.roots`, and `Q(x) ≠ 0`, we have
    `HasSignRight (P' · Q · P) x (sign Q(x))`.

    Proof: factor `P = (X − Cx)^µ · P̃`, `P' = (X − Cx)^{µ−1} · g` with
    `g(x) = µ · P̃(x) ≠ 0`. Then `P' · Q · P = (X − Cx)^{2µ−1} · h` where
    `h = g · Q · P̃` and `h(x) = µ · P̃(x)² · Q(x)`, which has the same sign
    as `Q(x)` (because `µ > 0` and `P̃(x)² > 0`). The IVP then gives a
    right-neighborhood of `x` on which `h` has constant sign `sign Q(x)`,
    multiplied by the positive factor `(t − x)^{2µ−1}`. -/
private lemma hasSignRight_derivative_mul_self
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    {P Q : R[X]} (hP : P ≠ 0) {x : R} (hx : x ∈ P.roots)
    (hQx : Q.eval x ≠ 0) :
    HasSignRight (P.derivative * Q * P) x (SignType.sign (Q.eval x)) := by
  set mu := P.rootMultiplicity x with hmu_def
  have hmu_pos : 1 ≤ mu := (rootMultiplicity_pos hP).mpr ((mem_roots hP).mp hx)
  set Ptilde := P /ₘ (X - C x) ^ mu with hPtilde_def
  have hP_eq : (X - C x) ^ mu * Ptilde = P :=
    pow_mul_divByMonic_rootMultiplicity_eq P x
  have hPtilde_eval_ne : Ptilde.eval x ≠ 0 :=
    eval_divByMonic_pow_rootMultiplicity_ne_zero x hP
  set g := (C (mu : R)) * Ptilde + (X - C x) * Ptilde.derivative with hg_def
  have h_deriv : P.derivative = (X - C x) ^ (mu - 1) * g := by
    rw [← hP_eq, derivative_mul, derivative_X_sub_C_pow, hg_def]
    have h_pow_split : (X - C x) ^ mu = (X - C x) ^ (mu - 1) * (X - C x) := by
      rw [← pow_succ, Nat.sub_add_cancel hmu_pos]
    rw [h_pow_split]
    ring
  have hg_eval : g.eval x = (mu : R) * Ptilde.eval x := by simp [g]
  have hmu_R_ne : (mu : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hmu_pos)
  have hg_eval_ne : g.eval x ≠ 0 := by
    rw [hg_eval]; exact mul_ne_zero hmu_R_ne hPtilde_eval_ne
  -- Define h := g * Q * P̃ and show P'·Q·P = (X-Cx)^{2µ-1} * h.
  set h := g * Q * Ptilde with hh_def
  have hh_factor : P.derivative * Q * P = (X - C x) ^ (2 * mu - 1) * h := by
    rw [h_deriv, ← hP_eq, hh_def]
    have h_pow_combine : (X - C x) ^ (mu - 1) * (X - C x) ^ mu =
        (X - C x) ^ (2 * mu - 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc (X - C x) ^ (mu - 1) * g * Q * ((X - C x) ^ mu * Ptilde)
        = ((X - C x) ^ (mu - 1) * (X - C x) ^ mu) * (g * Q * Ptilde) := by ring
      _ = (X - C x) ^ (2 * mu - 1) * (g * Q * Ptilde) := by rw [h_pow_combine]
  -- h.eval x = µ · P̃(x)² · Q(x), nonzero with sign(h(x)) = sign(Q(x)).
  have hh_eval : h.eval x = (mu : R) * Ptilde.eval x ^ 2 * Q.eval x := by
    rw [hh_def, eval_mul, eval_mul, hg_eval]; ring
  have hh_eval_sign : SignType.sign (h.eval x) = SignType.sign (Q.eval x) := by
    rw [hh_eval]
    have hmu_R_pos : (0 : R) < (mu : R) := by exact_mod_cast hmu_pos
    have hPtilde_sq_pos : 0 < Ptilde.eval x ^ 2 := pow_two_pos_of_ne_zero hPtilde_eval_ne
    have h1 : 0 < (mu : R) * Ptilde.eval x ^ 2 := mul_pos hmu_R_pos hPtilde_sq_pos
    rw [sign_mul, sign_pos h1, one_mul]
  have hh_eval_ne : h.eval x ≠ 0 := by
    intro he
    rw [he, sign_zero] at hh_eval_sign
    exact hQx (sign_eq_zero_iff.mp hh_eval_sign.symm)
  -- HasSignRight h x (sign(Q(x))).
  have h_right_h : HasSignRight h x (SignType.sign (Q.eval x)) := by
    have := Proposition2_21.hasSignRight_of_eval_ne_zero hIVP hh_eval_ne
    rwa [hh_eval_sign] at this
  -- Transfer to (X-Cx)^{2µ-1} * h.
  obtain ⟨b, hxb, h_sign⟩ := h_right_h
  refine ⟨b, hxb, ?_⟩
  intro t ht
  rw [hh_factor, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sign_mul]
  have h_pos : 0 < t - x := sub_pos.mpr ht.1
  have h_pow_pos : 0 < (t - x) ^ (2 * mu - 1) := pow_pos h_pos _
  rw [sign_pos h_pow_pos, one_mul]
  exact h_sign t ht

/-- **Per-root analysis: `−∞ → +∞` jump iff `Q(x) > 0`.** -/
private lemma jumpsFromNegInfToPosInf_derivative_iff_pos
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (Q : R[X]) {x : R} (hx : x ∈ P.roots) :
    JumpsFromNegInfToPosInf (P.derivative * Q) P x ↔ 0 < Q.eval x := by
  set mu := P.rootMultiplicity x with hmu_def
  have hmu_pos : 1 ≤ mu := (rootMultiplicity_pos hP).mpr ((mem_roots hP).mp hx)
  have hP'_ne : P.derivative ≠ 0 := derivative_ne_zero_of_mem_roots hP hx
  -- Case Q = 0
  by_cases hQ : Q = 0
  · constructor
    · rintro ⟨_, _, h_sign⟩
      rw [hQ] at h_sign
      simp at h_sign
      obtain ⟨b, hxb, hb_sign⟩ := h_sign
      obtain ⟨t, ht_lo, ht_hi⟩ := exists_between hxb
      have h_eval : SignType.sign ((0 : R[X]).eval t) = 1 :=
        hb_sign t ⟨ht_lo, ht_hi⟩
      simp at h_eval
    · intro h
      rw [hQ] at h; simp at h
  -- Case Q ≠ 0
  · have hP'Q_ne : P.derivative * Q ≠ 0 := mul_ne_zero hP'_ne hQ
    have h_P'_rootMul : P.derivative.rootMultiplicity x = mu - 1 := by
      have := rootMultiplicity_derivative hP hmu_pos
      omega
    have h_P'Q_rootMul : (P.derivative * Q).rootMultiplicity x =
        mu - 1 + Q.rootMultiplicity x := by
      rw [Polynomial.rootMultiplicity_mul hP'Q_ne, h_P'_rootMul]
    constructor
    · -- Jump → 0 < Q(x).
      rintro ⟨h_gt, h_odd, h_sign⟩
      rw [h_P'Q_rootMul] at h_gt
      -- mu > mu - 1 + Q.rootMul x ⟹ Q.rootMul x = 0 ⟹ Q(x) ≠ 0.
      have h_Q_root : Q.rootMultiplicity x = 0 := by omega
      have hQx : Q.eval x ≠ 0 := by
        intro he
        have : Q.IsRoot x := he
        have := (Polynomial.rootMultiplicity_pos hQ).mpr this
        omega
      -- HasSignRight (P'·Q · P) x 1 = sign(Q.eval x); so sign Q.eval x = 1.
      have h_right := hasSignRight_derivative_mul_self hIVP hP hx hQx
      have h_eq : SignType.sign (Q.eval x) = 1 := HasSignRight.unique h_right h_sign
      exact sign_eq_one_iff.mp h_eq
    · -- 0 < Q(x) → Jump.
      intro hQx_pos
      have hQx : Q.eval x ≠ 0 := ne_of_gt hQx_pos
      have h_Q_root : Q.rootMultiplicity x = 0 :=
        rootMultiplicity_eq_zero_of_eval_ne hQx
      refine ⟨?_, ?_, ?_⟩
      · rw [h_P'Q_rootMul, h_Q_root]; omega
      · rw [h_P'Q_rootMul, h_Q_root]
        rw [show mu - (mu - 1 + 0) = 1 from by omega]
        exact ⟨0, by simp⟩
      · have h_right := hasSignRight_derivative_mul_self hIVP hP hx hQx
        rwa [sign_pos hQx_pos] at h_right

/-- **Per-root analysis: `+∞ → −∞` jump iff `Q(x) < 0`.** -/
private lemma jumpsFromPosInfToNegInf_derivative_iff_neg
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (Q : R[X]) {x : R} (hx : x ∈ P.roots) :
    JumpsFromPosInfToNegInf (P.derivative * Q) P x ↔ Q.eval x < 0 := by
  set mu := P.rootMultiplicity x with hmu_def
  have hmu_pos : 1 ≤ mu := (rootMultiplicity_pos hP).mpr ((mem_roots hP).mp hx)
  have hP'_ne : P.derivative ≠ 0 := derivative_ne_zero_of_mem_roots hP hx
  by_cases hQ : Q = 0
  · constructor
    · rintro ⟨_, _, h_sign⟩
      rw [hQ] at h_sign
      simp at h_sign
      obtain ⟨b, hxb, hb_sign⟩ := h_sign
      obtain ⟨t, ht_lo, ht_hi⟩ := exists_between hxb
      have h_eval : SignType.sign ((0 : R[X]).eval t) = -1 :=
        hb_sign t ⟨ht_lo, ht_hi⟩
      simp at h_eval
    · intro h
      rw [hQ] at h; simp at h
  · have hP'Q_ne : P.derivative * Q ≠ 0 := mul_ne_zero hP'_ne hQ
    have h_P'_rootMul : P.derivative.rootMultiplicity x = mu - 1 := by
      have := rootMultiplicity_derivative hP hmu_pos
      omega
    have h_P'Q_rootMul : (P.derivative * Q).rootMultiplicity x =
        mu - 1 + Q.rootMultiplicity x := by
      rw [Polynomial.rootMultiplicity_mul hP'Q_ne, h_P'_rootMul]
    constructor
    · rintro ⟨h_gt, h_odd, h_sign⟩
      rw [h_P'Q_rootMul] at h_gt
      have h_Q_root : Q.rootMultiplicity x = 0 := by omega
      have hQx : Q.eval x ≠ 0 := by
        intro he
        have : Q.IsRoot x := he
        have := (Polynomial.rootMultiplicity_pos hQ).mpr this
        omega
      have h_right := hasSignRight_derivative_mul_self hIVP hP hx hQx
      have h_eq : SignType.sign (Q.eval x) = -1 := HasSignRight.unique h_right h_sign
      exact sign_eq_neg_one_iff.mp h_eq
    · intro hQx_neg
      have hQx : Q.eval x ≠ 0 := ne_of_lt hQx_neg
      have h_Q_root : Q.rootMultiplicity x = 0 :=
        rootMultiplicity_eq_zero_of_eval_ne hQx
      refine ⟨?_, ?_, ?_⟩
      · rw [h_P'Q_rootMul, h_Q_root]; omega
      · rw [h_P'Q_rootMul, h_Q_root]
        rw [show mu - (mu - 1 + 0) = 1 from by omega]
        exact ⟨0, by simp⟩
      · have h_right := hasSignRight_derivative_mul_self hIVP hP hx hQx
        rwa [sign_neg hQx_neg] at h_right

/-- **BPR Proposition 2.57.** For `P ≠ 0` over an ordered field with the
    intermediate value property, the Tarski-query of `Q` for `P` on the
    open interval `(a, b)` equals the Cauchy index of `P' · Q / P` on
    the same interval:
    `TaQ(Q, P; a, b) = Ind(P' · Q / P; a, b)`. -/
theorem proposition_2_57
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (Q P : R[X]) (hP : P ≠ 0) (a b : ExtendedPoint R) :
    tarskiQueryOn Q P a b = cauchyIndexOn (P.derivative * Q) P a b := by
  classical
  rw [tarskiQueryOn_eq_card_pos_sub_card_neg]
  -- Identify the two filtered Finsets pointwise.
  have h_pos_eq : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧ 0 < Q.eval x) =
      P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf (P.derivative * Q) P x) := by
    apply Finset.filter_congr
    intro x hx
    have hx_root : x ∈ P.roots := Multiset.mem_toFinset.mp hx
    rw [(jumpsFromNegInfToPosInf_derivative_iff_pos hIVP hP Q hx_root)]
  have h_neg_eq : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧ Q.eval x < 0) =
      P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromPosInfToNegInf (P.derivative * Q) P x) := by
    apply Finset.filter_congr
    intro x hx
    have hx_root : x ∈ P.roots := Multiset.mem_toFinset.mp hx
    rw [(jumpsFromPosInfToNegInf_derivative_iff_neg hIVP hP Q hx_root)]
  rw [h_pos_eq, h_neg_eq]
  rfl

open Classical in
/-- **Corollary of Proposition 2.57.** Specialising `Q = 1`, the Tarski-query
    `TaQ(1, P; a, b)` is just the number of distinct roots of `P` in
    `(a, b)`, so the number of distinct roots of `P` in `(a, b)` equals
    `Ind(P'/P; a, b)`. -/
theorem cauchyIndexOn_derivative_self_eq_card_roots_in_openInterval
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P : R[X]) (hP : P ≠ 0) (a b : ExtendedPoint R) :
    ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b)).card : ℤ) =
      cauchyIndexOn P.derivative P a b := by
  classical
  have h := proposition_2_57 hIVP 1 P hP a b
  rw [mul_one] at h
  rw [← h]
  unfold tarskiQueryOn
  simp only [Polynomial.eval_one, sign_one, SignType.coe_one]
  rw [Finset.sum_const, Nat.smul_one_eq_cast]

end Azurite.BPR

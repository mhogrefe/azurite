import Azurite.BasuPollackRoy.Chapter2.CauchyIndex

/-!
# BPR Lemma 2.60

Let `P ≠ 0` and `Q` be polynomials over a real closed field `R`, with
`R' = Rem(P, Q) = P % Q`. Letting `σ(x) = sign(P(x) · Q(x))`, BPR Lemma 2.60
states: if `a, b` are not roots of any polynomial in the signed remainder
sequence of `P, Q`, then

* `Ind(Q/P; a, b) = Ind(−R'/Q; a, b)` if `σ(a) · σ(b) = 1`;
* `Ind(Q/P; a, b) = Ind(−R'/Q; a, b) + σ(b)` if `σ(a) · σ(b) = −1`.

Equivalently `2 · (Ind(Q/P; a, b) − Ind(−R'/Q; a, b)) = σ(b) − σ(a)`.

The proof reduces (via Remark 2.55(b) applied with `(P, Q)` swapped, plus
`Ind(−X/Y) = −Ind(X/Y)`) to the **swap-sum identity**

`Ind(Q/P; a, b) + Ind(P/Q; a, b) = (σ(b) − σ(a)) / 2`

at points where `σ(a), σ(b) ≠ 0`. Per BPR's proof, each `x ∈ (a, b)` with
`(P · Q).rootMultiplicity x` odd produces a sign flip of `P · Q` and a jump
of either `Q/P` (when `µ_P > µ_Q`) or `P/Q` (when `µ_Q > µ_P`); the
sign-flip direction matches the jump direction, so the running sum of
`±1` contributions equals `(σ(b) − σ(a))/2`.

All theorems require the BPR hypothesis `a < b` (extended order),
encoded as `ExtendedPoint.Lt a b`. This rules out the empty-interval
edge cases (e.g. `a = .posInf, b = .finite x`) where `σ(b) − σ(a)` need
not be 0.
-/

open scoped Polynomial
open Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Strict ordering on `ExtendedPoint R`. `Lt a b` holds exactly when the
    open interval `(a, b)` is "ordered nontrivially" — equivalently, when
    `a` lies strictly to the left of `b`. Used to ensure non-empty
    intervals in BPR Lemma 2.60. -/
def ExtendedPoint.Lt : ExtendedPoint R → ExtendedPoint R → Prop
  | .negInf,   .negInf   => False
  | .negInf,   _         => True
  | .finite _, .negInf   => False
  | .finite a, .finite b => a < b
  | .finite _, .posInf   => True
  | .posInf,   _         => False

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `(-Q).rootMultiplicity x = Q.rootMultiplicity x`. -/
private lemma rootMultiplicity_neg' (Q : R[X]) (x : R) :
    (-Q).rootMultiplicity x = Q.rootMultiplicity x := by
  by_cases hQ : Q = 0
  · simp [hQ]
  · have hnegQ : -Q ≠ 0 := neg_ne_zero.mpr hQ
    apply le_antisymm
    · have hQ_self : Q.rootMultiplicity x ≤ Q.rootMultiplicity x := le_refl _
      rw [Polynomial.rootMultiplicity_le_iff hQ] at hQ_self
      rw [Polynomial.rootMultiplicity_le_iff hnegQ]
      intro h
      exact hQ_self (dvd_neg.mp h)
    · have hnegQ_self : (-Q).rootMultiplicity x ≤ (-Q).rootMultiplicity x := le_refl _
      rw [Polynomial.rootMultiplicity_le_iff hnegQ] at hnegQ_self
      rw [Polynomial.rootMultiplicity_le_iff hQ]
      intro h
      exact hnegQ_self (dvd_neg.mpr h)

/-- `HasSignRight (-Q · P) x s ↔ HasSignRight (Q · P) x (-s)`. -/
private lemma hasSignRight_neg_left_iff (Q P : R[X]) (x : R) (s : SignType) :
    HasSignRight (-Q * P) x s ↔ HasSignRight (Q * P) x (-s) := by
  unfold HasSignRight
  have h_eval : ∀ t : R, (-Q * P).eval t = -((Q * P).eval t) := by
    intro t; rw [neg_mul, eval_neg]
  constructor
  · rintro ⟨b, hxb, h_sign⟩
    refine ⟨b, hxb, ?_⟩
    intro t ht
    have h := h_sign t ht
    rw [h_eval, Left.sign_neg] at h
    rw [← h, neg_neg]
  · rintro ⟨b, hxb, h_sign⟩
    refine ⟨b, hxb, ?_⟩
    intro t ht
    have h := h_sign t ht
    rw [h_eval, Left.sign_neg, h, neg_neg]

/-- Negating the numerator of a rational function flips `−∞ → +∞` jumps
    into `+∞ → −∞` jumps. -/
private lemma jumpsFromNegInfToPosInf_neg_iff (Q P : R[X]) (x : R) :
    JumpsFromNegInfToPosInf (-Q) P x ↔ JumpsFromPosInfToNegInf Q P x := by
  unfold JumpsFromNegInfToPosInf JumpsFromPosInfToNegInf
  rw [rootMultiplicity_neg', hasSignRight_neg_left_iff]

/-- Negating the numerator flips `+∞ → −∞` jumps into `−∞ → +∞` jumps. -/
private lemma jumpsFromPosInfToNegInf_neg_iff (Q P : R[X]) (x : R) :
    JumpsFromPosInfToNegInf (-Q) P x ↔ JumpsFromNegInfToPosInf Q P x := by
  unfold JumpsFromNegInfToPosInf JumpsFromPosInfToNegInf
  rw [rootMultiplicity_neg', hasSignRight_neg_left_iff]
  simp

/-- **Negation flips the Cauchy index.** `Ind(−Q/P; a, b) = −Ind(Q/P; a, b)`. -/
theorem cauchyIndexOn_neg_left (Q P : R[X]) (a b : ExtendedPoint R) :
    cauchyIndexOn (-Q) P a b = -cauchyIndexOn Q P a b := by
  classical
  show ((P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧
      JumpsFromNegInfToPosInf (-Q) P x)).card : ℤ) -
      ((P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromPosInfToNegInf (-Q) P x)).card : ℤ) =
      -(((P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
      ((P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromPosInfToNegInf Q P x)).card : ℤ))
  have h_pos : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf (-Q) P x) =
      P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromPosInfToNegInf Q P x) := by
    apply Finset.filter_congr
    intro x _
    rw [jumpsFromNegInfToPosInf_neg_iff]
  have h_neg : P.roots.toFinset.filter (fun x =>
      x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromPosInfToNegInf (-Q) P x) =
      P.roots.toFinset.filter (fun x =>
        x ∈ ExtendedPoint.openInterval a b ∧ JumpsFromNegInfToPosInf Q P x) := by
    apply Finset.filter_congr
    intro x _
    rw [jumpsFromPosInfToNegInf_neg_iff]
  rw [h_pos, h_neg]
  ring

/-- **Negation of the modular numerator.** `Ind(−(P % Q)/Q; a, b) =
    −Ind(P/Q; a, b)` (using Remark 2.55(b) and `cauchyIndexOn_neg_left`). -/
theorem cauchyIndexOn_neg_mod
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hQ_ne : Q ≠ 0)
    (a b : ExtendedPoint R) :
    cauchyIndexOn (-(P % Q)) Q a b = -cauchyIndexOn P Q a b := by
  rw [cauchyIndexOn_neg_left, remark_2_55_b hIVP P Q a b hQ_ne]

/-- The "sigma" tracker: `σ(t) = sign(P(t) · Q(t))` at extended `t`. -/
private noncomputable def sigmaPQ (P Q : R[X]) (t : ExtendedPoint R) : ℤ :=
  (SignType.sign (ExtendedPoint.evalPoly P t * ExtendedPoint.evalPoly Q t) : ℤ)

/-- The "sign-flip contribution" of a polynomial `F` at a point `x`:
    `sign(F̃(x))` if `F` has odd multiplicity at `x`, else `0`, where
    `F̃ = F /ₘ (X − Cx)^(F.rootMultiplicity x)`. By Proposition 2.21,
    this equals `(sign right of x − sign left of x) / 2`. -/
private noncomputable def signFlipAt (F : R[X]) (x : R) : ℤ :=
  if Odd (F.rootMultiplicity x) then
    (SignType.sign ((F /ₘ (X - C x)^F.rootMultiplicity x).eval x) : ℤ)
  else 0

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The "leading factor" `(P · Q)~` at `x` factors as `P̃(x) · Q̃(x)`. -/
private lemma divByMonic_pow_mul_eq_mul
    (P Q : R[X]) (x : R) :
    (P * Q) /ₘ (X - C x)^(P.rootMultiplicity x + Q.rootMultiplicity x) =
      (P /ₘ (X - C x)^P.rootMultiplicity x) *
      (Q /ₘ (X - C x)^Q.rootMultiplicity x) := by
  have hP_factor : (X - C x)^P.rootMultiplicity x *
      (P /ₘ (X - C x)^P.rootMultiplicity x) = P :=
    pow_mul_divByMonic_rootMultiplicity_eq P x
  have hQ_factor : (X - C x)^Q.rootMultiplicity x *
      (Q /ₘ (X - C x)^Q.rootMultiplicity x) = Q :=
    pow_mul_divByMonic_rootMultiplicity_eq Q x
  have h_PQ_eq : P * Q =
      (X - C x)^(P.rootMultiplicity x + Q.rootMultiplicity x) *
      ((P /ₘ (X - C x)^P.rootMultiplicity x) *
       (Q /ₘ (X - C x)^Q.rootMultiplicity x)) := by
    rw [pow_add]
    calc P * Q
        = ((X - C x)^P.rootMultiplicity x *
              (P /ₘ (X - C x)^P.rootMultiplicity x)) *
            ((X - C x)^Q.rootMultiplicity x *
              (Q /ₘ (X - C x)^Q.rootMultiplicity x)) := by rw [hP_factor, hQ_factor]
      _ = ((X - C x)^P.rootMultiplicity x * (X - C x)^Q.rootMultiplicity x) *
            ((P /ₘ (X - C x)^P.rootMultiplicity x) *
              (Q /ₘ (X - C x)^Q.rootMultiplicity x)) := by ring
  rw [h_PQ_eq, mul_divByMonic_cancel_left]
  exact (Polynomial.monic_X_sub_C x).pow _

open Classical in
/-- Compute the integer-coded contribution of a `cauchyIndexOn` summand at
    a single point `x`. For a pair `(Y, X)` of polynomials (numerator,
    denominator), the contribution of `x ∈ X.roots` to `cauchyIndexOn Y X`
    is `+1` if `Y/X` jumps `−∞ → +∞`, `−1` if `+∞ → −∞`, and `0` otherwise. -/
private noncomputable def jumpContrib (Y X : R[X]) (x : R) : ℤ :=
  (if JumpsFromNegInfToPosInf Y X x then (1 : ℤ) else 0) -
  (if JumpsFromPosInfToNegInf Y X x then (1 : ℤ) else 0)

omit [IsStrictOrderedRing R] in
/-- Helper: when `Y.rootMultiplicity x = 0` (i.e., `x ∉ Y.roots`), the
    `jumpContrib X Y x` is zero (no jump can occur because the multiplicity
    condition fails). -/
private lemma jumpContrib_eq_zero_of_rootMultiplicity_zero
    (X Y : R[X]) (x : R) (h : Y.rootMultiplicity x = 0) :
    jumpContrib X Y x = 0 := by
  unfold jumpContrib
  have h1 : ¬ JumpsFromNegInfToPosInf X Y x := fun ⟨h_gt, _, _⟩ => by
    rw [h] at h_gt; omega
  have h2 : ¬ JumpsFromPosInfToNegInf X Y x := fun ⟨h_gt, _, _⟩ => by
    rw [h] at h_gt; omega
  simp [h1, h2]

omit [IsStrictOrderedRing R] in
/-- Helper: when `X.rootMul x ≤ Y.rootMul x` (denominator's multiplicity
    is `≤` numerator's), `jumpContrib Y X x = 0`. -/
private lemma jumpContrib_eq_zero_of_le
    (Y X : R[X]) (x : R)
    (h : X.rootMultiplicity x ≤ Y.rootMultiplicity x) :
    jumpContrib Y X x = 0 := by
  unfold jumpContrib
  have h1 : ¬ JumpsFromNegInfToPosInf Y X x := fun ⟨h_gt, _, _⟩ => not_lt.mpr h h_gt
  have h2 : ¬ JumpsFromPosInfToNegInf Y X x := fun ⟨h_gt, _, _⟩ => not_lt.mpr h h_gt
  simp [h1, h2]

/-- Helper: when the jump-multiplicity conditions are met, `jumpContrib Q P x`
    equals the sign of the leading factor of `Q · P` at `x`, i.e.,
    `sign(((Q·P) /ₘ (X − Cx)^(µ_{QP}))(x))`. Uses Proposition 2.21 +
    uniqueness of `HasSignRight`. -/
private lemma jumpContrib_eq_sign_leading_factor
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (Q P : R[X]) (hQ : Q ≠ 0) (hP : P ≠ 0) (x : R)
    (h_gt : Q.rootMultiplicity x < P.rootMultiplicity x)
    (h_odd : Odd (P.rootMultiplicity x - Q.rootMultiplicity x)) :
    jumpContrib Q P x =
      (SignType.sign
        (((Q * P) /ₘ (X - C x)^((Q * P).rootMultiplicity x)).eval x) : ℤ) := by
  classical
  have hQP : Q * P ≠ 0 := mul_ne_zero hQ hP
  have h_factor_ne :
      ((Q * P) /ₘ (X - C x)^((Q * P).rootMultiplicity x)).eval x ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero x hQP
  -- Prop 2.21: HasSignRight (Q*P) x (sign((leading factor)(x))).
  have h_right_iter := Proposition2_21.proposition_2_21_right hIVP hQP x
  rw [Proposition2_21.sign_iterate_derivative_eq_sign_Q hQP] at h_right_iter
  -- Set s := sign of leading factor. Then s ∈ {-1, +1}.
  set s := SignType.sign
      (((Q * P) /ₘ (X - C x)^((Q * P).rootMultiplicity x)).eval x) with hs_def
  have h_right : HasSignRight (Q * P) x s := h_right_iter
  -- s ≠ 0 because the leading factor doesn't vanish at x.
  have hs_ne : s ≠ 0 := by
    intro h
    apply h_factor_ne
    rw [hs_def] at h
    exact sign_eq_zero_iff.mp h
  -- Case on the value of s.
  rcases SignType.trichotomy s with hs_neg | hs_zero | hs_pos
  · -- s = -1.
    have h_J_neg : JumpsFromPosInfToNegInf Q P x := ⟨h_gt, h_odd, hs_neg ▸ h_right⟩
    have h_not_J_pos : ¬ JumpsFromNegInfToPosInf Q P x := fun ⟨_, _, h⟩ => by
      have h_uniq : s = 1 := HasSignRight.unique h_right h
      rw [hs_neg] at h_uniq
      exact absurd h_uniq (by decide)
    unfold jumpContrib
    rw [if_neg h_not_J_pos, if_pos h_J_neg, hs_neg]
    decide
  · exact absurd hs_zero hs_ne
  · -- s = 1.
    have h_J_pos : JumpsFromNegInfToPosInf Q P x := ⟨h_gt, h_odd, hs_pos ▸ h_right⟩
    have h_not_J_neg : ¬ JumpsFromPosInfToNegInf Q P x := fun ⟨_, _, h⟩ => by
      have h_uniq : s = -1 := HasSignRight.unique h_right h
      rw [hs_pos] at h_uniq
      exact absurd h_uniq (by decide)
    unfold jumpContrib
    rw [if_pos h_J_pos, if_neg h_not_J_neg, hs_pos]
    decide

/-- **Per-root identity (heart of Lemma 2.60).** At any `x : R` and any
    `P, Q : R[X]` with `P ≠ 0` and `Q ≠ 0`, the summed jump contribution
    of `Q/P` and `P/Q` at `x` equals the sign-flip contribution of `P · Q`
    at `x`:

    `jumpContrib Q P x + jumpContrib P Q x = signFlipAt (P · Q) x`.

    Case analysis on `(µ_P, µ_Q)`:
    * Both zero (handled): both sides are zero by
      `jumpContrib_eq_zero_of_rootMultiplicity_zero` and the parity check
      in `signFlipAt`.
    * Otherwise (currently `sorry`): exactly one positive, or both positive
      with sum-even, or both positive with sum-odd (single jump matching
      sign-flip direction by Prop 2.21 + factorization `(P·Q)~ = P̃ · Q̃`). -/
private theorem per_root_jump_sum_eq_signFlip
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (x : R) :
    jumpContrib Q P x + jumpContrib P Q x = signFlipAt (P * Q) x := by
  classical
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  have h_muPQ : (P * Q).rootMultiplicity x =
      P.rootMultiplicity x + Q.rootMultiplicity x :=
    Polynomial.rootMultiplicity_mul hPQ
  -- Trivial case: x is not a root of either P or Q.
  -- Sub-lemma: jumpContrib Y X x = 0 when X.rootMul x and Y.rootMul x have the
  -- same parity (i.e., X.rootMul - Y.rootMul is even).
  have h_no_jump : ∀ X Y : R[X],
      Even (X.rootMultiplicity x + Y.rootMultiplicity x) →
        jumpContrib Y X x = 0 := by
    intro X Y h_even
    unfold jumpContrib
    have h_diff_even : ∀ k1 k2 : ℕ, Even (k1 + k2) → ¬ Odd (k1 - k2) := by
      intro k1 k2 h_e h_o
      rw [Nat.even_iff] at h_e
      rw [Nat.odd_iff] at h_o
      omega
    have h1 : ¬ JumpsFromNegInfToPosInf Y X x := fun ⟨_, h_o, _⟩ =>
      h_diff_even _ _ h_even h_o
    have h2 : ¬ JumpsFromPosInfToNegInf Y X x := fun ⟨_, h_o, _⟩ =>
      h_diff_even _ _ h_even h_o
    simp [h1, h2]
  by_cases h_odd_PQ : Odd ((P * Q).rootMultiplicity x)
  · -- Sum is odd: parities of µ_P, µ_Q differ. Exactly one of `Q/P`, `P/Q`
    -- jumps; the direction matches the sign-flip.
    have h_odd_sum : Odd (P.rootMultiplicity x + Q.rootMultiplicity x) := by
      rwa [h_muPQ] at h_odd_PQ
    -- µ_P ≠ µ_Q (else the sum would be even).
    have h_ne : P.rootMultiplicity x ≠ Q.rootMultiplicity x := by
      intro h
      rw [h, ← two_mul] at h_odd_sum
      exact (Nat.not_even_iff_odd.mpr h_odd_sum) (even_two_mul _)
    -- signFlipAt unfolds via Prop 2.21's leading factor.
    have h_signFlip : signFlipAt (P * Q) x =
        (SignType.sign
          (((P * Q) /ₘ (X - C x)^((P * Q).rootMultiplicity x)).eval x) : ℤ) := by
      unfold signFlipAt; rw [if_pos h_odd_PQ]
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · -- µ_P < µ_Q: `P/Q` jumps; `Q/P` doesn't.
      have h_diff_odd : Odd (Q.rootMultiplicity x - P.rootMultiplicity x) := by
        rw [Nat.odd_iff] at h_odd_sum ⊢
        omega
      rw [jumpContrib_eq_zero_of_le Q P x (le_of_lt h_lt)]
      rw [jumpContrib_eq_sign_leading_factor hIVP P Q hP hQ x h_lt h_diff_odd]
      rw [h_signFlip]
      ring
    · -- µ_P > µ_Q: `Q/P` jumps; `P/Q` doesn't.
      have h_diff_odd : Odd (P.rootMultiplicity x - Q.rootMultiplicity x) := by
        rw [Nat.odd_iff] at h_odd_sum ⊢
        omega
      rw [jumpContrib_eq_zero_of_le P Q x (le_of_lt h_gt)]
      rw [jumpContrib_eq_sign_leading_factor hIVP Q P hQ hP x h_gt h_diff_odd]
      rw [h_signFlip]
      -- Need: sign(((Q*P) /ₘ ...).eval x) = sign(((P*Q) /ₘ ...).eval x).
      -- Q*P = P*Q (commutative).
      rw [show Q * P = P * Q from mul_comm Q P]
      ring
  · -- Sum is even: both `jumpContrib`s are zero (parity condition fails),
    -- and `signFlipAt` is zero by definition.
    have h_even : Even (P.rootMultiplicity x + Q.rootMultiplicity x) := by
      rw [Nat.not_odd_iff_even] at h_odd_PQ
      rwa [h_muPQ] at h_odd_PQ
    have h_even' : Even (Q.rootMultiplicity x + P.rootMultiplicity x) := by
      rw [add_comm]; exact h_even
    rw [h_no_jump Q P h_even']
    rw [h_no_jump P Q h_even]
    unfold signFlipAt
    rw [if_neg h_odd_PQ]
    ring

omit [IsStrictOrderedRing R] in
/-- **Sign jump at a single root, in terms of `signFlipAt`.** For nonzero
    `F` over an ordered field with IVP, the difference between the canonical
    HasSignRight and HasSignLeft signs at `x` equals `2 · signFlipAt F x`.
    By Proposition 2.21, those canonical signs are `sign(F̃(x))` (right) and
    `(-1)^µ · sign(F̃(x))` (left); their difference simplifies as claimed. -/
private lemma sign_jump_at_root_eq_signFlipAt
    (F : R[X]) (x : R) :
    ((SignType.sign ((F /ₘ (X - C x)^F.rootMultiplicity x).eval x) : ℤ) -
      (((-1) ^ F.rootMultiplicity x : SignType) *
          SignType.sign ((F /ₘ (X - C x)^F.rootMultiplicity x).eval x) : ℤ)) =
      2 * signFlipAt F x := by
  classical
  set s := (SignType.sign ((F /ₘ (X - C x)^F.rootMultiplicity x).eval x) : ℤ)
  by_cases h_odd : Odd (F.rootMultiplicity x)
  · -- µ odd: (-1)^µ = -1.
    rw [h_odd.neg_one_pow]
    unfold signFlipAt
    rw [if_pos h_odd]
    show s - ((-1 : SignType) * _ : ℤ) = 2 * s
    have h_neg_one : ((-1 : SignType) : ℤ) = -1 := by decide
    push_cast [h_neg_one]
    ring
  · -- µ even: (-1)^µ = 1.
    have h_even : Even (F.rootMultiplicity x) := Nat.not_odd_iff_even.mp h_odd
    rw [h_even.neg_one_pow]
    unfold signFlipAt
    rw [if_neg h_odd]
    show s - ((1 : SignType) * _ : ℤ) = 2 * 0
    have h_one : ((1 : SignType) : ℤ) = 1 := by decide
    push_cast [h_one]
    ring

/-- **Constant sign on a no-root interval.** Direct from IVP: if `F(a)` and
    `F(b)` are both nonzero and `F` has no roots in the open interval
    `(a, b)`, then `sign(F(a)) = sign(F(b))`. (Equivalent to "if F changed
    sign, IVP would produce a root in (a, b)".) -/
private lemma sign_eval_eq_of_no_root_Ioo
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (F : R[X]) {a b : R} (hab : a < b)
    (h_ne_a : F.eval a ≠ 0) (h_ne_b : F.eval b ≠ 0)
    (h_no_root : ∀ x, a < x → x < b → F.eval x ≠ 0) :
    SignType.sign (F.eval a) = SignType.sign (F.eval b) := by
  by_contra h_ne
  -- F(a) and F(b) are both nonzero with different signs ⇒ F(a) · F(b) < 0.
  have h_prod_neg : F.eval a * F.eval b < 0 := by
    rcases SignType.trichotomy (SignType.sign (F.eval a)) with ha_neg | ha_zero | ha_pos
    · -- sign(F(a)) = -1.
      have ha_neg' : F.eval a < 0 := sign_eq_neg_one_iff.mp ha_neg
      rcases SignType.trichotomy (SignType.sign (F.eval b)) with hb_neg | hb_zero | hb_pos
      · exact absurd (ha_neg.trans hb_neg.symm) h_ne
      · exact absurd (sign_eq_zero_iff.mp hb_zero) h_ne_b
      · have hb_pos' : 0 < F.eval b := sign_eq_one_iff.mp hb_pos
        exact mul_neg_of_neg_of_pos ha_neg' hb_pos'
    · exact absurd (sign_eq_zero_iff.mp ha_zero) h_ne_a
    · -- sign(F(a)) = 1.
      have ha_pos' : 0 < F.eval a := sign_eq_one_iff.mp ha_pos
      rcases SignType.trichotomy (SignType.sign (F.eval b)) with hb_neg | hb_zero | hb_pos
      · have hb_neg' : F.eval b < 0 := sign_eq_neg_one_iff.mp hb_neg
        exact mul_neg_of_pos_of_neg ha_pos' hb_neg'
      · exact absurd (sign_eq_zero_iff.mp hb_zero) h_ne_b
      · exact absurd (ha_pos.trans hb_pos.symm) h_ne
  obtain ⟨x, hxa, hxb, hFx⟩ := hIVP F a b hab h_prod_neg
  exact h_no_root x hxa hxb hFx

omit [IsStrictOrderedRing R] in
/-- For finite `a < b` with `F(a) ≠ 0`, `F(b) ≠ 0`, and `F` having no
    roots in `(a, b)`, the filter of `F`-roots in `(a, b)` is empty. -/
private lemma roots_filter_eq_empty_of_no_root
    (F : R[X]) {a b : R}
    (h_no_root : ∀ x, a < x → x < b → F.eval x ≠ 0) :
    F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a b) = ∅ := by
  classical
  by_cases hF : F = 0
  · rw [hF]; simp
  · ext x
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro h_root h_in
    apply h_no_root x h_in.1 h_in.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hF] at h_root
    exact h_root

/-- **Sign of `F(a)` equals canonical s_left at any later root.** For `F ≠ 0`,
    IVP, finite `a < r` with `F(a) ≠ 0` and no F-roots in `(a, r)`:
    `sign(F(a)) = (-1)^{µ_r} · sign(F̃(r))`, where `µ_r = F.rootMul r` and
    `F̃ = F /ₘ (X − Cr)^{µ_r}`. -/
private lemma sign_eval_eq_canonical_left
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (F : R[X]) (hF : F ≠ 0) {a r : R} (har : a < r)
    (ha : F.eval a ≠ 0)
    (h_no_root : ∀ x, a < x → x < r → F.eval x ≠ 0) :
    SignType.sign (F.eval a) =
      ((-1) ^ F.rootMultiplicity r : SignType) *
        SignType.sign ((F /ₘ (X - C r)^F.rootMultiplicity r).eval r) := by
  classical
  -- Get HasSignLeft witness from Prop 2.21 left.
  have h_left := Proposition2_21.proposition_2_21_left hIVP hF r
  rw [Proposition2_21.sign_iterate_derivative_eq_sign_Q hF] at h_left
  obtain ⟨a', ha'r, h_left_sign⟩ := h_left
  -- Pick t ∈ (max(a, a'), r), so t > a, t > a', t < r.
  obtain ⟨t, ht_lo, ht_hi⟩ := exists_between (max_lt har ha'r)
  have ht_a : a < t := lt_of_le_of_lt (le_max_left _ _) ht_lo
  have ht_a' : a' < t := lt_of_le_of_lt (le_max_right _ _) ht_lo
  have ht_r : t < r := ht_hi
  -- sign(F(t)) = canonical s_left.
  have h_sign_t : SignType.sign (F.eval t) =
      ((-1) ^ F.rootMultiplicity r : SignType) *
        SignType.sign ((F /ₘ (X - C r)^F.rootMultiplicity r).eval r) :=
    h_left_sign t ⟨ht_a', ht_r⟩
  -- F(t) ≠ 0 since t ∈ (a, r) and no roots there.
  have ht_ne : F.eval t ≠ 0 := h_no_root t ht_a ht_r
  -- sign(F(a)) = sign(F(t)) by IVP applied to (a, t) (no roots there).
  have h_sign_a_t : SignType.sign (F.eval a) = SignType.sign (F.eval t) := by
    apply sign_eval_eq_of_no_root_Ioo hIVP F ht_a ha ht_ne
    intro x hxa hxt h_zero
    apply h_no_root x hxa (lt_trans hxt ht_r) h_zero
  rw [h_sign_a_t, h_sign_t]

/-- **Sign of `F(b)` equals canonical s_right at any earlier root.** For `F ≠ 0`,
    IVP, finite `r < b` with `F(b) ≠ 0` and no F-roots in `(r, b)`:
    `sign(F(b)) = sign(F̃(r))`. -/
private lemma sign_eval_eq_canonical_right
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (F : R[X]) (hF : F ≠ 0) {r b : R} (hrb : r < b)
    (hb : F.eval b ≠ 0)
    (h_no_root : ∀ x, r < x → x < b → F.eval x ≠ 0) :
    SignType.sign (F.eval b) =
      SignType.sign ((F /ₘ (X - C r)^F.rootMultiplicity r).eval r) := by
  classical
  have h_right := Proposition2_21.proposition_2_21_right hIVP hF r
  rw [Proposition2_21.sign_iterate_derivative_eq_sign_Q hF] at h_right
  obtain ⟨b', hrb', h_right_sign⟩ := h_right
  obtain ⟨t, ht_lo, ht_hi⟩ := exists_between (lt_min hrb' hrb)
  have ht_r : r < t := ht_lo
  have ht_b' : t < b' := lt_of_lt_of_le ht_hi (min_le_left _ _)
  have ht_b : t < b := lt_of_lt_of_le ht_hi (min_le_right _ _)
  have h_sign_t : SignType.sign (F.eval t) =
      SignType.sign ((F /ₘ (X - C r)^F.rootMultiplicity r).eval r) :=
    h_right_sign t ⟨ht_r, ht_b'⟩
  have ht_ne : F.eval t ≠ 0 := h_no_root t ht_r ht_b
  have h_sign_t_b : SignType.sign (F.eval t) = SignType.sign (F.eval b) := by
    apply sign_eval_eq_of_no_root_Ioo hIVP F ht_b ht_ne hb
    intro x hxt hxb h_zero
    apply h_no_root x (lt_trans ht_r hxt) hxb h_zero
  rw [← h_sign_t_b, h_sign_t]

/-- **Running sign-flip count, finite-endpoint version.** For nonzero `F`,
    finite `a < b` with `F(a), F(b) ≠ 0`:

    `sign(F(b)) − sign(F(a)) = 2 · ∑_{x ∈ F.roots ∩ (a,b)} signFlipAt F x`.

    Strong induction on the number of `F`-roots in `(a, b)`. -/
private lemma running_sign_flip_count_finite
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (F : R[X]) (hF : F ≠ 0) :
    ∀ (n : ℕ) (a b : R), a < b → F.eval a ≠ 0 → F.eval b ≠ 0 →
      (F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a b)).card = n →
      (SignType.sign (F.eval b) : ℤ) - (SignType.sign (F.eval a) : ℤ) =
        2 * ∑ x ∈ F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a b),
          signFlipAt F x := by
  classical
  intro n
  induction n with
  | zero =>
    -- Base: no F-roots in (a, b). Use `sign_eval_eq_of_no_root_Ioo`.
    intro a b hab ha hb h_card
    have h_empty : F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a b) = ∅ :=
      Finset.card_eq_zero.mp h_card
    have h_no_root : ∀ x, a < x → x < b → F.eval x ≠ 0 := by
      intro x hxa hxb h_zero
      have h_in : x ∈ F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a b) := by
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hF]
        exact ⟨h_zero, hxa, hxb⟩
      rw [h_empty] at h_in
      exact (Finset.notMem_empty x) h_in
    rw [h_empty, Finset.sum_empty, mul_zero,
      sign_eval_eq_of_no_root_Ioo hIVP F hab ha hb h_no_root, sub_self]
  | succ k ih =>
    intro a b hab ha hb h_card
    set S := F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a b) with hS_def
    have hS_ne : S.Nonempty := Finset.card_pos.mp (by rw [h_card]; omega)
    -- Pick the smallest root in (a, b).
    set r := S.min' hS_ne with hr_def
    have hr_in : r ∈ S := S.min'_mem hS_ne
    have hr_in_Ioo : r ∈ Set.Ioo a b := (Finset.mem_filter.mp hr_in).2
    have har : a < r := hr_in_Ioo.1
    have hrb : r < b := hr_in_Ioo.2
    have hr_root : F.eval r = 0 :=
      (Polynomial.mem_roots hF).mp
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr_in).1)
    have hr_min : ∀ x ∈ S, r ≤ x := fun x hx => S.min'_le x hx
    -- F has no roots in (a, r): smaller would contradict r being min.
    have h_no_root_aleft : ∀ x, a < x → x < r → F.eval x ≠ 0 := by
      intro x hxa hxr h_zero
      have h_in : x ∈ S := by
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hF]
        exact ⟨h_zero, hxa, lt_trans hxr hrb⟩
      have hr_le : r ≤ x := hr_min x h_in
      exact absurd hxr (not_lt.mpr hr_le)
    -- sign(F(a)) = canonical s_left at r.
    have h_sign_a := sign_eval_eq_canonical_left hIVP F hF har ha h_no_root_aleft
    -- Pick a test point t' ∈ (r, b) past r with HasSignRight property and
    -- no F-roots in (r, t'].
    have h_right := Proposition2_21.proposition_2_21_right hIVP hF r
    rw [Proposition2_21.sign_iterate_derivative_eq_sign_Q hF] at h_right
    obtain ⟨b', hrb', h_right_sign⟩ := h_right
    -- Find t' between r and min(b', b, smallest root past r).
    -- We avoid roots in (r, t'] by picking t' less than any root past r.
    -- Define the "next root past r" set:
    set T := (S.erase r).filter (fun x => r < x) with hT_def
    have hT_eq : T = S.erase r := by
      apply Finset.filter_true_of_mem
      intro x hx
      have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
      have hx_r : x ≠ r := (Finset.mem_erase.mp hx).1
      have hr_le : r ≤ x := hr_min x hxS
      exact lt_of_le_of_ne hr_le (Ne.symm hx_r)
    -- Pick t' close to r so that no roots are in (r, t'].
    have h_t'_exists : ∃ t', r < t' ∧ t' < b' ∧ t' < b ∧
        (∀ x ∈ T, t' < x) := by
      by_cases hT_empty : T = ∅
      · -- No more roots past r in (a, b). Pick any t' ∈ (r, min(b', b)).
        obtain ⟨t', ht'_lo, ht'_hi⟩ := exists_between (lt_min hrb' hrb)
        refine ⟨t', ht'_lo, lt_of_lt_of_le ht'_hi (min_le_left _ _),
          lt_of_lt_of_le ht'_hi (min_le_right _ _), ?_⟩
        intro x hx
        rw [hT_empty] at hx
        exact absurd hx (Finset.notMem_empty x)
      · -- T nonempty. Pick t' < min of T, t' < b', t' < b.
        have hT_ne : T.Nonempty := Finset.nonempty_of_ne_empty hT_empty
        set r' := T.min' hT_ne
        have hr'_in : r' ∈ T := T.min'_mem hT_ne
        have hr'_min : ∀ x ∈ T, r' ≤ x := fun x hx => T.min'_le x hx
        have hr_lt_r' : r < r' := by
          rw [hT_def] at hr'_in
          exact (Finset.mem_filter.mp hr'_in).2
        obtain ⟨t', ht'_lo, ht'_hi⟩ :=
          exists_between (lt_min hrb' (lt_min hrb hr_lt_r'))
        refine ⟨t', ht'_lo,
          lt_of_lt_of_le ht'_hi (min_le_left _ _),
          lt_of_lt_of_le ht'_hi (le_trans (min_le_right _ _) (min_le_left _ _)), ?_⟩
        intro x hx
        have hr'_le : r' ≤ x := hr'_min x hx
        have ht'_lt_r' : t' < r' :=
          lt_of_lt_of_le ht'_hi (le_trans (min_le_right _ _) (min_le_right _ _))
        exact lt_of_lt_of_le ht'_lt_r' hr'_le
    obtain ⟨t', hrt', ht'_b', ht'_b, h_no_root_rt'⟩ := h_t'_exists
    -- sign(F(t')) = canonical s_right at r.
    have h_sign_t' : SignType.sign (F.eval t') =
        SignType.sign ((F /ₘ (X - C r)^F.rootMultiplicity r).eval r) :=
      h_right_sign t' ⟨hrt', ht'_b'⟩
    have ht'_ne : F.eval t' ≠ 0 := by
      intro h_zero
      have h_in : t' ∈ S := by
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hF]
        exact ⟨h_zero, lt_trans har hrt', ht'_b⟩
      have h_in_T : t' ∈ T := by
        rw [hT_eq, Finset.mem_erase]
        exact ⟨ne_of_gt hrt', h_in⟩
      have := h_no_root_rt' t' h_in_T
      exact absurd this (lt_irrefl t')
    -- Apply IH to (t', b). First, count roots there.
    have h_card_t'_b : (F.roots.toFinset.filter
        (fun x => x ∈ Set.Ioo t' b)).card = k := by
      -- (t', b) ∩ F.roots = (a, b) ∩ F.roots \ ({r} ∪ (a, r] ∩ F.roots).
      -- Since (a, r) has no F-roots and r is the smallest root in (a, b):
      -- (t', b) ∩ F.roots = S \ {r} (when no roots in (r, t']).
      have h_eq : F.roots.toFinset.filter (fun x => x ∈ Set.Ioo t' b) =
          S.erase r := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase, Multiset.mem_toFinset,
          Polynomial.mem_roots hF, hS_def]
        constructor
        · rintro ⟨hx_root, hxt', hxb⟩
          have hxr : r < x := lt_trans hrt' hxt'
          refine ⟨ne_of_gt hxr, hx_root, lt_trans har hxr, hxb⟩
        · rintro ⟨hx_ne_r, hx_root, hxa, hxb⟩
          refine ⟨hx_root, ?_, hxb⟩
          have hr_le : r ≤ x := hr_min x (by
            rw [hS_def, Finset.mem_filter]
            exact ⟨by rw [Multiset.mem_toFinset, Polynomial.mem_roots hF]; exact hx_root,
              hxa, hxb⟩)
          have hr_lt : r < x := lt_of_le_of_ne hr_le (Ne.symm hx_ne_r)
          -- x ∈ T, so t' < x.
          have hx_in_T : x ∈ T := by
            rw [hT_eq, Finset.mem_erase]
            refine ⟨hx_ne_r, ?_⟩
            rw [hS_def, Finset.mem_filter]
            refine ⟨?_, hxa, hxb⟩
            rw [Multiset.mem_toFinset, Polynomial.mem_roots hF]; exact hx_root
          exact h_no_root_rt' x hx_in_T
      rw [h_eq, Finset.card_erase_of_mem hr_in]
      omega
    have h_ih := ih t' b ht'_b ht'_ne hb h_card_t'_b
    -- Decompose the sum.
    have h_S_decomp : ∑ x ∈ S, signFlipAt F x =
        signFlipAt F r + ∑ x ∈ F.roots.toFinset.filter
          (fun x => x ∈ Set.Ioo t' b), signFlipAt F x := by
      rw [show F.roots.toFinset.filter (fun x => x ∈ Set.Ioo t' b) =
          S.erase r from ?_]
      · exact (Finset.add_sum_erase S (signFlipAt F) hr_in).symm
      · -- (Same equality as in h_card_t'_b's h_eq.)
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase, Multiset.mem_toFinset,
          Polynomial.mem_roots hF, hS_def]
        constructor
        · rintro ⟨hx_root, hxt', hxb⟩
          have hxr : r < x := lt_trans hrt' hxt'
          refine ⟨ne_of_gt hxr, hx_root, lt_trans har hxr, hxb⟩
        · rintro ⟨hx_ne_r, hx_root, hxa, hxb⟩
          refine ⟨hx_root, ?_, hxb⟩
          have hr_le : r ≤ x := hr_min x (by
            rw [hS_def, Finset.mem_filter]
            exact ⟨by rw [Multiset.mem_toFinset, Polynomial.mem_roots hF]; exact hx_root,
              hxa, hxb⟩)
          have hr_lt : r < x := lt_of_le_of_ne hr_le (Ne.symm hx_ne_r)
          have hx_in_T : x ∈ T := by
            rw [hT_eq, Finset.mem_erase]
            refine ⟨hx_ne_r, ?_⟩
            rw [hS_def, Finset.mem_filter]
            refine ⟨?_, hxa, hxb⟩
            rw [Multiset.mem_toFinset, Polynomial.mem_roots hF]; exact hx_root
          exact h_no_root_rt' x hx_in_T
    -- Now combine: σ(b) - σ(a) = 2 · (signFlipAt F r + ∑ over (t', b))
    --                          = 2 · ∑ over (a, b).
    rw [h_S_decomp]
    -- σ(b) - σ(a) = (σ(b) - σ(t')) + (σ(t') - σ(a))
    --             = 2 · ∑ (t', b) + (s_right - s_left)
    --             = 2 · ∑ (t', b) + 2 · signFlipAt F r.
    have h_sign_jump :
        ((SignType.sign ((F /ₘ (X - C r)^F.rootMultiplicity r).eval r) : ℤ) -
          (((-1) ^ F.rootMultiplicity r : SignType) *
              SignType.sign ((F /ₘ (X - C r)^F.rootMultiplicity r).eval r) : ℤ)) =
        2 * signFlipAt F r := sign_jump_at_root_eq_signFlipAt F r
    have h_sub_a : (SignType.sign (F.eval t') : ℤ) - (SignType.sign (F.eval a) : ℤ) =
        2 * signFlipAt F r := by
      rw [h_sign_t', h_sign_a]
      exact_mod_cast h_sign_jump
    linarith [h_ih, h_sub_a]

/-- **Helper for endpoint extension.** For nonzero `F`, there exists a finite
    point `a₀` such that `sign(F.eval a₀) = sign(evalPoly F .negInf)` and
    `a₀` is strictly less than every `F`-root. -/
private lemma exists_finite_left_of_negInf
    (F : R[X]) (hF : F ≠ 0) :
    ∃ a₀ : R, SignType.sign (F.eval a₀) =
        SignType.sign (ExtendedPoint.evalPoly F ExtendedPoint.negInf) ∧
      (∀ r ∈ F.roots, a₀ < r) ∧ F.eval a₀ ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := hasSignAtNegInfty_leadingCoeff F
  set roots_lb : R :=
    if h : F.roots.toFinset.Nonempty then F.roots.toFinset.min' h else 0
  set a₀ := min M (roots_lb - 1) - 1 with ha₀_def
  have h_lt_M : a₀ < M := by
    have h₁ : a₀ ≤ M - 1 := by
      rw [ha₀_def]
      have : min M (roots_lb - 1) ≤ M := min_le_left _ _
      linarith
    linarith
  have h_lt_roots : ∀ r ∈ F.roots, a₀ < r := by
    intro r hr
    by_cases h_ne : F.roots.toFinset.Nonempty
    · have h_root_in : r ∈ F.roots.toFinset := Multiset.mem_toFinset.mpr hr
      have h_min : F.roots.toFinset.min' h_ne ≤ r :=
        F.roots.toFinset.min'_le r h_root_in
      have hroots_lb : roots_lb = F.roots.toFinset.min' h_ne := by simp [roots_lb, h_ne]
      have h₂ : a₀ ≤ roots_lb - 1 - 1 := by
        rw [ha₀_def]
        have : min M (roots_lb - 1) ≤ roots_lb - 1 := min_le_right _ _
        linarith
      linarith
    · exact absurd (Multiset.mem_toFinset.mpr hr)
        (fun h_in => h_ne ⟨r, h_in⟩)
  -- sign(F(a₀)) = sign at -∞ via hM applied at a₀ < M.
  have h_sign : SignType.sign (F.eval a₀) =
      SignType.sign (ExtendedPoint.evalPoly F ExtendedPoint.negInf) := by
    have h_a₀_in : a₀ ∈ Set.Iio M := h_lt_M
    have h := hM a₀ h_a₀_in
    show SignType.sign (F.eval a₀) =
      SignType.sign ((-1) ^ F.natDegree * F.leadingCoeff)
    rw [h, sign_mul, sign_pow]
    congr 1
    show ((-1) ^ F.natDegree : SignType) = SignType.sign ((-1 : R)) ^ F.natDegree
    have h_neg_one : SignType.sign ((-1 : R)) = -1 := by
      rw [Left.sign_neg, sign_one]
    rw [h_neg_one]
  -- F.eval a₀ ≠ 0 because if it were, a₀ would be a root, contradicting h_lt_roots.
  have h_eval_ne : F.eval a₀ ≠ 0 := by
    intro h_zero
    have h_a₀_root : a₀ ∈ F.roots := (Polynomial.mem_roots hF).mpr h_zero
    exact absurd (h_lt_roots a₀ h_a₀_root) (lt_irrefl _)
  exact ⟨a₀, h_sign, h_lt_roots, h_eval_ne⟩

/-- **Helper for endpoint extension.** For nonzero `F`, there exists a finite
    point `b₀` such that `sign(F.eval b₀) = sign(evalPoly F .posInf)` and
    `b₀` is strictly greater than every `F`-root. -/
private lemma exists_finite_right_of_posInf
    (F : R[X]) (hF : F ≠ 0) :
    ∃ b₀ : R, SignType.sign (F.eval b₀) =
        SignType.sign (ExtendedPoint.evalPoly F ExtendedPoint.posInf) ∧
      (∀ r ∈ F.roots, r < b₀) ∧ F.eval b₀ ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := hasSignAtPosInfty_leadingCoeff F
  set roots_ub : R :=
    if h : F.roots.toFinset.Nonempty then F.roots.toFinset.max' h else 0
  set b₀ := max M (roots_ub + 1) + 1 with hb₀_def
  have h_gt_M : M < b₀ := by
    have h₁ : M + 1 ≤ b₀ := by
      rw [hb₀_def]
      have : M ≤ max M (roots_ub + 1) := le_max_left _ _
      linarith
    linarith
  have h_gt_roots : ∀ r ∈ F.roots, r < b₀ := by
    intro r hr
    by_cases h_ne : F.roots.toFinset.Nonempty
    · have h_root_in : r ∈ F.roots.toFinset := Multiset.mem_toFinset.mpr hr
      have h_max : r ≤ F.roots.toFinset.max' h_ne :=
        F.roots.toFinset.le_max' r h_root_in
      have hroots_ub : roots_ub = F.roots.toFinset.max' h_ne := by simp [roots_ub, h_ne]
      have h₂ : roots_ub + 1 + 1 ≤ b₀ := by
        rw [hb₀_def]
        have : roots_ub + 1 ≤ max M (roots_ub + 1) := le_max_right _ _
        linarith
      linarith
    · exact absurd (Multiset.mem_toFinset.mpr hr)
        (fun h_in => h_ne ⟨r, h_in⟩)
  have h_sign : SignType.sign (F.eval b₀) =
      SignType.sign (ExtendedPoint.evalPoly F ExtendedPoint.posInf) := by
    have h_b₀_in : b₀ ∈ Set.Ioi M := h_gt_M
    have := hM b₀ h_b₀_in
    rw [show (ExtendedPoint.evalPoly F ExtendedPoint.posInf : R) =
        F.leadingCoeff from rfl]
    exact this
  have h_eval_ne : F.eval b₀ ≠ 0 := by
    intro h_zero
    have h_b₀_root : b₀ ∈ F.roots := (Polynomial.mem_roots hF).mpr h_zero
    exact absurd (h_gt_roots b₀ h_b₀_root) (lt_irrefl _)
  exact ⟨b₀, h_sign, h_gt_roots, h_eval_ne⟩

open Classical in
/-- **Running sign-flip count, ExtendedPoint version.** For a nonzero
    polynomial `F` over an ordered field with IVP, with
    `a, b : ExtendedPoint R` such that `evalPoly F a ≠ 0`, `evalPoly F b ≠ 0`,
    and `a < b` (so the open interval `(a, b)` is non-empty):

    `(sign F(b) − sign F(a)) = 2 · ∑_{x ∈ F.roots ∩ (a,b)} signFlipAt F x`.

    The `Lt a b` hypothesis is needed: for `a = .posInf, b = .finite x`,
    the interval is empty (sum = 0) but `σ_F(b) − σ_F(a)` need not be 0. -/
private theorem running_sign_flip_count
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (F : R[X]) (a b : ExtendedPoint R)
    (hab : ExtendedPoint.Lt a b)
    (ha : ExtendedPoint.evalPoly F a ≠ 0)
    (hb : ExtendedPoint.evalPoly F b ≠ 0) :
    (SignType.sign (ExtendedPoint.evalPoly F b) : ℤ) -
        (SignType.sign (ExtendedPoint.evalPoly F a) : ℤ) =
      2 * ∑ x ∈ F.roots.toFinset.filter
            (fun x => x ∈ ExtendedPoint.openInterval a b),
        signFlipAt F x := by
  classical
  have hF : F ≠ 0 := by
    intro h
    apply ha
    rw [h]
    cases a <;> simp [ExtendedPoint.evalPoly]
  -- Strategy: reduce each `±∞` endpoint to a finite one using
  -- `exists_finite_left_of_negInf` / `exists_finite_right_of_posInf`,
  -- then apply `running_sign_flip_count_finite`. The transformations
  -- preserve the sign at each endpoint and the set of `F`-roots in
  -- the open interval. Empty-interval cases (e.g. `a = .posInf`) are
  -- not handled here and would need a separate `a < b` hypothesis.
  cases a with
  | finite a_val =>
    cases b with
    | finite b_val =>
      -- Both finite. If `a_val < b_val`, apply finite version directly.
      have h_lt : a_val < b_val := hab
      simp only [ExtendedPoint.evalPoly, ExtendedPoint.openInterval]
      simp only [ExtendedPoint.evalPoly] at ha hb
      convert running_sign_flip_count_finite hIVP F hF _ a_val b_val h_lt ha hb rfl
    | posInf =>
      -- a finite, b = +∞. Pick b₀ past all F-roots and past a_val.
      obtain ⟨b₀_raw, h_sign_b₀, h_b₀_gt_roots, h_b₀_ne⟩ :=
        exists_finite_right_of_posInf F hF
      -- Strengthen: replace b₀ with max(b₀_raw, a_val + 1) if needed.
      -- We re-derive: pick b₀ via helper construction with a larger M.
      obtain ⟨M, hM⟩ := hasSignAtPosInfty_leadingCoeff F
      set roots_ub : R :=
        if h : F.roots.toFinset.Nonempty then F.roots.toFinset.max' h else 0
      set b₀ := max (max M (roots_ub + 1)) (a_val + 1) + 1 with hb₀_def
      have h_b₀_gt_M : M < b₀ := by
        rw [hb₀_def]
        have : M ≤ max M (roots_ub + 1) := le_max_left _ _
        have : M ≤ max (max M (roots_ub + 1)) (a_val + 1) := le_trans this (le_max_left _ _)
        linarith
      have h_b₀_gt_a : a_val < b₀ := by
        rw [hb₀_def]
        have : a_val + 1 ≤ max (max M (roots_ub + 1)) (a_val + 1) := le_max_right _ _
        linarith
      have h_b₀_gt_roots' : ∀ r ∈ F.roots, r < b₀ := by
        intro r hr
        by_cases h_ne : F.roots.toFinset.Nonempty
        · have h_root_in : r ∈ F.roots.toFinset := Multiset.mem_toFinset.mpr hr
          have h_max : r ≤ F.roots.toFinset.max' h_ne :=
            F.roots.toFinset.le_max' r h_root_in
          have hroots_ub : roots_ub = F.roots.toFinset.max' h_ne := by
            simp [roots_ub, h_ne]
          have : roots_ub + 1 ≤ max M (roots_ub + 1) := le_max_right _ _
          have : roots_ub + 1 ≤ max (max M (roots_ub + 1)) (a_val + 1) :=
            le_trans this (le_max_left _ _)
          rw [hb₀_def]
          linarith
        · exact absurd (Multiset.mem_toFinset.mpr hr)
            (fun h_in => h_ne ⟨r, h_in⟩)
      have h_sign_b₀' : SignType.sign (F.eval b₀) =
          SignType.sign (ExtendedPoint.evalPoly F ExtendedPoint.posInf) := by
        have h_b₀_in : b₀ ∈ Set.Ioi M := h_b₀_gt_M
        have h := hM b₀ h_b₀_in
        show SignType.sign (F.eval b₀) = SignType.sign F.leadingCoeff
        exact h
      have h_b₀_ne' : F.eval b₀ ≠ 0 := by
        intro h_zero
        have h_b₀_root : b₀ ∈ F.roots := (Polynomial.mem_roots hF).mpr h_zero
        exact absurd (h_b₀_gt_roots' b₀ h_b₀_root) (lt_irrefl _)
      -- Now apply finite version to (a_val, b₀).
      have h_filter_eq :
          F.roots.toFinset.filter (fun x =>
            x ∈ ExtendedPoint.openInterval (ExtendedPoint.finite a_val)
              ExtendedPoint.posInf) =
          F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a_val b₀) := by
        apply Finset.filter_congr
        intro x hx
        have hx_root : x ∈ F.roots := Multiset.mem_toFinset.mp hx
        constructor
        · intro h_in_Ioi
          have h_lt_b₀ : x < b₀ := h_b₀_gt_roots' x hx_root
          exact ⟨h_in_Ioi, h_lt_b₀⟩
        · intro h_in_Ioo
          exact h_in_Ioo.1
      simp only [ExtendedPoint.evalPoly] at *
      rw [h_filter_eq]
      have h_finite := running_sign_flip_count_finite hIVP F hF _ a_val b₀ h_b₀_gt_a
        ha h_b₀_ne' rfl
      have h_sign_b' :
          (SignType.sign (F.eval b₀) : ℤ) =
          (SignType.sign F.leadingCoeff : ℤ) := by
        rw [h_sign_b₀']
      rw [h_sign_b'] at h_finite
      convert h_finite
    | negInf =>
      exact (hab : False).elim
  | posInf =>
    cases b with
    | finite b_val =>
      exact (hab : False).elim
    | posInf =>
      exact (hab : False).elim
    | negInf =>
      exact (hab : False).elim
  | negInf =>
    cases b with
    | finite b_val =>
      -- a = -∞, b finite. Pick a₀ less than all F-roots and less than b_val.
      obtain ⟨M, hM⟩ := hasSignAtNegInfty_leadingCoeff F
      set roots_lb : R :=
        if h : F.roots.toFinset.Nonempty then F.roots.toFinset.min' h else 0
      set a₀ := min (min M (roots_lb - 1)) (b_val - 1) - 1 with ha₀_def
      have h_a₀_lt_M : a₀ < M := by
        rw [ha₀_def]
        have : min M (roots_lb - 1) ≤ M := min_le_left _ _
        have : min (min M (roots_lb - 1)) (b_val - 1) ≤ M :=
          le_trans (min_le_left _ _) this
        linarith
      have h_a₀_lt_b : a₀ < b_val := by
        rw [ha₀_def]
        have : min (min M (roots_lb - 1)) (b_val - 1) ≤ b_val - 1 := min_le_right _ _
        linarith
      have h_a₀_lt_roots' : ∀ r ∈ F.roots, a₀ < r := by
        intro r hr
        by_cases h_ne : F.roots.toFinset.Nonempty
        · have h_root_in : r ∈ F.roots.toFinset := Multiset.mem_toFinset.mpr hr
          have h_min : F.roots.toFinset.min' h_ne ≤ r :=
            F.roots.toFinset.min'_le r h_root_in
          have hroots_lb : roots_lb = F.roots.toFinset.min' h_ne := by
            simp [roots_lb, h_ne]
          rw [ha₀_def]
          have : min M (roots_lb - 1) ≤ roots_lb - 1 := min_le_right _ _
          have : min (min M (roots_lb - 1)) (b_val - 1) ≤ roots_lb - 1 :=
            le_trans (min_le_left _ _) this
          linarith
        · exact absurd (Multiset.mem_toFinset.mpr hr)
            (fun h_in => h_ne ⟨r, h_in⟩)
      have h_sign_a₀' : SignType.sign (F.eval a₀) =
          SignType.sign (ExtendedPoint.evalPoly F ExtendedPoint.negInf) := by
        have h_a₀_in : a₀ ∈ Set.Iio M := h_a₀_lt_M
        have h := hM a₀ h_a₀_in
        show SignType.sign (F.eval a₀) =
          SignType.sign ((-1) ^ F.natDegree * F.leadingCoeff)
        rw [h, sign_mul, sign_pow]
        congr 1
        show ((-1) ^ F.natDegree : SignType) =
          SignType.sign ((-1 : R)) ^ F.natDegree
        rw [Left.sign_neg, sign_one]
      have h_a₀_ne' : F.eval a₀ ≠ 0 := by
        intro h_zero
        have h_a₀_root : a₀ ∈ F.roots := (Polynomial.mem_roots hF).mpr h_zero
        exact absurd (h_a₀_lt_roots' a₀ h_a₀_root) (lt_irrefl _)
      have h_filter_eq :
          F.roots.toFinset.filter (fun x =>
            x ∈ ExtendedPoint.openInterval ExtendedPoint.negInf
              (ExtendedPoint.finite b_val)) =
          F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a₀ b_val) := by
        apply Finset.filter_congr
        intro x hx
        have hx_root : x ∈ F.roots := Multiset.mem_toFinset.mp hx
        constructor
        · intro h_in_Iio
          exact ⟨h_a₀_lt_roots' x hx_root, h_in_Iio⟩
        · intro h_in_Ioo
          exact h_in_Ioo.2
      simp only [ExtendedPoint.evalPoly] at *
      rw [h_filter_eq]
      have h_finite := running_sign_flip_count_finite hIVP F hF _ a₀ b_val h_a₀_lt_b
        h_a₀_ne' hb rfl
      have h_sign_a' :
          (SignType.sign (F.eval a₀) : ℤ) =
          (SignType.sign ((-1) ^ F.natDegree * F.leadingCoeff) : ℤ) := by
        rw [h_sign_a₀']
      rw [h_sign_a'] at h_finite
      convert h_finite
    | posInf =>
      -- a = -∞, b = +∞. Construct a₀ < 0 < b₀ with the right sign properties.
      obtain ⟨M_neg, hM_neg⟩ := hasSignAtNegInfty_leadingCoeff F
      obtain ⟨M_pos, hM_pos⟩ := hasSignAtPosInfty_leadingCoeff F
      set roots_lb : R :=
        if h : F.roots.toFinset.Nonempty then F.roots.toFinset.min' h else 0
      set roots_ub : R :=
        if h : F.roots.toFinset.Nonempty then F.roots.toFinset.max' h else 0
      set a₀ := min (min M_neg (roots_lb - 1)) (-1 : R) - 1 with ha₀_def
      set b₀ := max (max M_pos (roots_ub + 1)) (1 : R) + 1 with hb₀_def
      have h_a₀_lt_M_neg : a₀ < M_neg := by
        rw [ha₀_def]
        have : min M_neg (roots_lb - 1) ≤ M_neg := min_le_left _ _
        have : min (min M_neg (roots_lb - 1)) (-1 : R) ≤ M_neg :=
          le_trans (min_le_left _ _) this
        linarith
      have h_a₀_le_neg_one : a₀ ≤ (-1 : R) - 1 := by
        rw [ha₀_def]
        have : min (min M_neg (roots_lb - 1)) (-1 : R) ≤ -1 := min_le_right _ _
        linarith
      have h_b₀_gt_M_pos : M_pos < b₀ := by
        rw [hb₀_def]
        have : M_pos ≤ max M_pos (roots_ub + 1) := le_max_left _ _
        have : M_pos ≤ max (max M_pos (roots_ub + 1)) (1 : R) :=
          le_trans this (le_max_left _ _)
        linarith
      have h_b₀_ge_one : (1 : R) + 1 ≤ b₀ := by
        rw [hb₀_def]
        have : (1 : R) ≤ max (max M_pos (roots_ub + 1)) (1 : R) := le_max_right _ _
        linarith
      have h_lt : a₀ < b₀ := by linarith
      have h_a₀_lt_roots : ∀ r ∈ F.roots, a₀ < r := by
        intro r hr
        by_cases h_ne : F.roots.toFinset.Nonempty
        · have h_root_in : r ∈ F.roots.toFinset := Multiset.mem_toFinset.mpr hr
          have h_min : F.roots.toFinset.min' h_ne ≤ r :=
            F.roots.toFinset.min'_le r h_root_in
          have hroots_lb : roots_lb = F.roots.toFinset.min' h_ne := by
            simp [roots_lb, h_ne]
          rw [ha₀_def]
          have h₁ : min M_neg (roots_lb - 1) ≤ roots_lb - 1 := min_le_right _ _
          have h₂ : min (min M_neg (roots_lb - 1)) (-1 : R) ≤ roots_lb - 1 :=
            le_trans (min_le_left _ _) h₁
          linarith
        · exact absurd (Multiset.mem_toFinset.mpr hr)
            (fun h_in => h_ne ⟨r, h_in⟩)
      have h_b₀_gt_roots : ∀ r ∈ F.roots, r < b₀ := by
        intro r hr
        by_cases h_ne : F.roots.toFinset.Nonempty
        · have h_root_in : r ∈ F.roots.toFinset := Multiset.mem_toFinset.mpr hr
          have h_max : r ≤ F.roots.toFinset.max' h_ne :=
            F.roots.toFinset.le_max' r h_root_in
          have hroots_ub : roots_ub = F.roots.toFinset.max' h_ne := by
            simp [roots_ub, h_ne]
          rw [hb₀_def]
          have h₁ : roots_ub + 1 ≤ max M_pos (roots_ub + 1) := le_max_right _ _
          have h₂ : roots_ub + 1 ≤ max (max M_pos (roots_ub + 1)) (1 : R) :=
            le_trans h₁ (le_max_left _ _)
          linarith
        · exact absurd (Multiset.mem_toFinset.mpr hr)
            (fun h_in => h_ne ⟨r, h_in⟩)
      have h_sign_a₀ : SignType.sign (F.eval a₀) =
          SignType.sign (ExtendedPoint.evalPoly F ExtendedPoint.negInf) := by
        have h_a₀_in : a₀ ∈ Set.Iio M_neg := h_a₀_lt_M_neg
        have h := hM_neg a₀ h_a₀_in
        show SignType.sign (F.eval a₀) =
          SignType.sign ((-1) ^ F.natDegree * F.leadingCoeff)
        rw [h, sign_mul, sign_pow]
        congr 1
        show ((-1) ^ F.natDegree : SignType) =
          SignType.sign ((-1 : R)) ^ F.natDegree
        rw [Left.sign_neg, sign_one]
      have h_sign_b₀ : SignType.sign (F.eval b₀) =
          SignType.sign (ExtendedPoint.evalPoly F ExtendedPoint.posInf) := by
        have h_b₀_in : b₀ ∈ Set.Ioi M_pos := h_b₀_gt_M_pos
        have h := hM_pos b₀ h_b₀_in
        show SignType.sign (F.eval b₀) = SignType.sign F.leadingCoeff
        exact h
      have h_a₀_ne : F.eval a₀ ≠ 0 := by
        intro h_zero
        have h_a₀_root : a₀ ∈ F.roots := (Polynomial.mem_roots hF).mpr h_zero
        exact absurd (h_a₀_lt_roots a₀ h_a₀_root) (lt_irrefl _)
      have h_b₀_ne : F.eval b₀ ≠ 0 := by
        intro h_zero
        have h_b₀_root : b₀ ∈ F.roots := (Polynomial.mem_roots hF).mpr h_zero
        exact absurd (h_b₀_gt_roots b₀ h_b₀_root) (lt_irrefl _)
      have h_roots_in : ∀ r ∈ F.roots, r ∈ Set.Ioo a₀ b₀ := fun r hr =>
        ⟨h_a₀_lt_roots r hr, h_b₀_gt_roots r hr⟩
      have h_filter_eq :
          F.roots.toFinset.filter (fun x =>
            x ∈ ExtendedPoint.openInterval ExtendedPoint.negInf
              ExtendedPoint.posInf) =
          F.roots.toFinset.filter (fun x => x ∈ Set.Ioo a₀ b₀) := by
        apply Finset.filter_congr
        intro x hx
        simp only [ExtendedPoint.openInterval, Set.mem_univ, true_iff]
        exact h_roots_in x (Multiset.mem_toFinset.mp hx)
      simp only [ExtendedPoint.evalPoly, ExtendedPoint.openInterval] at *
      rw [h_filter_eq]
      have h_finite := running_sign_flip_count_finite hIVP F hF _ a₀ b₀ h_lt
        h_a₀_ne h_b₀_ne rfl
      have h_sign_a' :
          (SignType.sign (F.eval a₀) : ℤ) =
          (SignType.sign ((-1) ^ F.natDegree * F.leadingCoeff) : ℤ) := by
        rw [h_sign_a₀]
      have h_sign_b' :
          (SignType.sign (F.eval b₀) : ℤ) =
          (SignType.sign F.leadingCoeff : ℤ) := by
        rw [h_sign_b₀]
      rw [h_sign_a', h_sign_b'] at h_finite
      convert h_finite
    | negInf =>
      exact (hab : False).elim

omit [IsStrictOrderedRing R] in
open Classical in
/-- Helper: `cauchyIndexOn Q P a b` rewritten as a sum of `jumpContrib`s
    over `P.roots.toFinset ∩ (a, b)`. -/
private lemma cauchyIndexOn_eq_sum_jumpContrib
    (Q P : R[X]) (a b : ExtendedPoint R) :
    (cauchyIndexOn Q P a b : ℤ) =
      ∑ x ∈ P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b),
        jumpContrib Q P x := by
  show ((P.roots.toFinset.filter
      (fun x => x ∈ ExtendedPoint.openInterval a b ∧
        JumpsFromNegInfToPosInf Q P x)).card : ℤ) -
      ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧
          JumpsFromPosInfToNegInf Q P x)).card : ℤ) = _
  unfold jumpContrib
  rw [Finset.sum_sub_distrib]
  have h_card_eq : ∀ (Pred : R → Prop) [DecidablePred Pred],
      ((P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧ Pred x)).card : ℤ) =
      ∑ x ∈ P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b),
        (if Pred x then (1 : ℤ) else 0) := by
    intro Pred _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      Nat.smul_one_eq_cast]
    congr 1
    rw [show (P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b ∧ Pred x)) =
        ((P.roots.toFinset.filter
          (fun x => x ∈ ExtendedPoint.openInterval a b)).filter Pred) from ?_]
    ext x
    simp only [Finset.mem_filter, and_assoc]
  rw [h_card_eq, h_card_eq]

/-- **Heart of Lemma 2.60 (swap-sum identity).** When `σ(a), σ(b) ≠ 0`,
    the sum of the Cauchy indices of `Q/P` and `P/Q` on `(a, b)` equals
    `(σ(b) − σ(a))/2`. Concretely, `2 · (Ind(Q/P) + Ind(P/Q)) = σ(b) − σ(a)`.

    Combines `per_root_jump_sum_eq_signFlip` and `running_sign_flip_count`:
    each `(P·Q)`-root contributes `signFlipAt (P·Q) x = jumpContrib Q P x +
    jumpContrib P Q x`; summing over `(a, b)` gives `(σ(b) − σ(a))/2` by the
    running count, and equals `Ind(Q/P; a,b) + Ind(P/Q; a,b)` by
    `cauchyIndexOn_eq_sum_jumpContrib` and zero-extension of `jumpContrib`. -/
theorem cauchyIndexOn_swap_sum
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (a b : ExtendedPoint R)
    (hab : ExtendedPoint.Lt a b)
    (ha : ExtendedPoint.evalPoly P a * ExtendedPoint.evalPoly Q a ≠ 0)
    (hb : ExtendedPoint.evalPoly P b * ExtendedPoint.evalPoly Q b ≠ 0) :
    2 * (cauchyIndexOn Q P a b + cauchyIndexOn P Q a b) =
      sigmaPQ P Q b - sigmaPQ P Q a := by
  classical
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  -- σ_{PQ}(t) = sign((P*Q)(t)).
  have h_evalPQ : ∀ t : ExtendedPoint R,
      ExtendedPoint.evalPoly P t * ExtendedPoint.evalPoly Q t =
        ExtendedPoint.evalPoly (P * Q) t := by
    intro t
    cases t with
    | finite x => simp [ExtendedPoint.evalPoly]
    | posInf => simp [ExtendedPoint.evalPoly, Polynomial.leadingCoeff_mul]
    | negInf =>
      simp [ExtendedPoint.evalPoly, Polynomial.leadingCoeff_mul,
        Polynomial.natDegree_mul hP hQ, pow_add]
      ring
  have ha' : ExtendedPoint.evalPoly (P * Q) a ≠ 0 := by rw [← h_evalPQ]; exact ha
  have hb' : ExtendedPoint.evalPoly (P * Q) b ≠ 0 := by rw [← h_evalPQ]; exact hb
  -- Apply running_sign_flip_count to F = P · Q.
  have h_run := running_sign_flip_count hIVP (P * Q) a b hab ha' hb'
  -- Per-root identity: signFlipAt (P*Q) x = jumpContrib Q P x + jumpContrib P Q x.
  have h_perRoot : ∀ x ∈ (P * Q).roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b),
      signFlipAt (P * Q) x = jumpContrib Q P x + jumpContrib P Q x := fun x _ =>
    (per_root_jump_sum_eq_signFlip hIVP P Q hP hQ x).symm
  rw [Finset.sum_congr rfl h_perRoot, Finset.sum_add_distrib] at h_run
  -- Express each cauchyIndexOn as a sum of jumpContribs.
  have h_cQP_sum : (cauchyIndexOn Q P a b : ℤ) =
      ∑ x ∈ P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b),
        jumpContrib Q P x := cauchyIndexOn_eq_sum_jumpContrib Q P a b
  have h_cPQ_sum : (cauchyIndexOn P Q a b : ℤ) =
      ∑ x ∈ Q.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b),
        jumpContrib P Q x := cauchyIndexOn_eq_sum_jumpContrib P Q a b
  -- (P*Q).roots.toFinset = P.roots.toFinset ∪ Q.roots.toFinset.
  have h_roots : (P * Q).roots.toFinset =
      P.roots.toFinset ∪ Q.roots.toFinset := by
    ext x
    simp [Polynomial.roots_mul hPQ, Multiset.toFinset_add]
  -- Filter distributes over union.
  have h_filter_union :
      ((P * Q).roots.toFinset).filter
        (fun x => x ∈ ExtendedPoint.openInterval a b) =
      (P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b)) ∪
      (Q.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b)) := by
    rw [h_roots, Finset.filter_union]
  -- jumpContrib zero on points in B but not A (i.e., Q-only roots in (a,b)).
  have h_QP_zero : ∀ x ∈ Q.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b),
      x ∉ P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b) → jumpContrib Q P x = 0 := by
    intro x hxB h_notA
    apply jumpContrib_eq_zero_of_rootMultiplicity_zero
    by_contra h_mu
    have h_in_P : x ∈ P.roots := by
      rw [Polynomial.mem_roots hP]
      exact (Polynomial.rootMultiplicity_pos hP).mp (Nat.pos_of_ne_zero h_mu)
    apply h_notA
    rw [Finset.mem_filter, Multiset.mem_toFinset]
    rw [Finset.mem_filter] at hxB
    exact ⟨h_in_P, hxB.2⟩
  have h_PQ_zero : ∀ x ∈ P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b),
      x ∉ Q.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval a b) → jumpContrib P Q x = 0 := by
    intro x hxA h_notB
    apply jumpContrib_eq_zero_of_rootMultiplicity_zero
    by_contra h_mu
    have h_in_Q : x ∈ Q.roots := by
      rw [Polynomial.mem_roots hQ]
      exact (Polynomial.rootMultiplicity_pos hQ).mp (Nat.pos_of_ne_zero h_mu)
    apply h_notB
    rw [Finset.mem_filter, Multiset.mem_toFinset]
    rw [Finset.mem_filter] at hxA
    exact ⟨h_in_Q, hxA.2⟩
  -- Extend the two jumpContrib sums from union back to the individual filters.
  rw [h_filter_union] at h_run
  rw [Finset.sum_union_eq_left h_QP_zero,
      Finset.sum_union_eq_right h_PQ_zero] at h_run
  rw [← h_cQP_sum, ← h_cPQ_sum] at h_run
  -- σ_{PQ} interpretation of h_run.
  have h_sigma_eq : ∀ t : ExtendedPoint R,
      (SignType.sign (ExtendedPoint.evalPoly (P * Q) t) : ℤ) = sigmaPQ P Q t := by
    intro t; unfold sigmaPQ; rw [h_evalPQ]
  rw [h_sigma_eq, h_sigma_eq] at h_run
  linarith

/-- **BPR Lemma 2.60.** With `R' = P % Q`, `σ(t) = sign(P(t) · Q(t))`,
    and `a, b` such that `σ(a), σ(b) ≠ 0`,

    `2 · (Ind(Q/P; a, b) − Ind(−R'/Q; a, b)) = σ(b) − σ(a)`.

    In particular:
    * if `σ(a) = σ(b)`: `Ind(Q/P; a, b) = Ind(−R'/Q; a, b)`;
    * if `σ(a) ≠ σ(b)` (so `σ(a) · σ(b) = −1`):
      `Ind(Q/P; a, b) = Ind(−R'/Q; a, b) + σ(b)`. -/
theorem lemma_2_60
    (hIVP : Azurite.BPR.HasIntermediateValueProperty R)
    (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (a b : ExtendedPoint R)
    (hab : ExtendedPoint.Lt a b)
    (ha : ExtendedPoint.evalPoly P a * ExtendedPoint.evalPoly Q a ≠ 0)
    (hb : ExtendedPoint.evalPoly P b * ExtendedPoint.evalPoly Q b ≠ 0) :
    2 * (cauchyIndexOn Q P a b - cauchyIndexOn (-(P % Q)) Q a b) =
      sigmaPQ P Q b - sigmaPQ P Q a := by
  rw [cauchyIndexOn_neg_mod hIVP P Q hQ a b, sub_neg_eq_add]
  exact cauchyIndexOn_swap_sum hIVP P Q hP hQ a b hab ha hb

end Azurite.BPR

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_20
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_4
import Mathlib.Basic.Sign.Basic

/-!
# Sign of a Polynomial to the Right / Left of a Point and at ±∞

Following BPR Proposition 2.20, it makes sense to talk about the sign of a
polynomial `P ∈ R[X]` immediately to the right (resp. left) of any `a ∈ R`:
the sign of `P` to the right (resp. left) of `a` is the sign of `P` in any
interval `(a, b)` (resp. `(b, a)`) in which `P` does not vanish. One can
likewise speak of the sign of `P` at `+∞` (resp. `−∞`) as the sign of `P(M)`
for `M` sufficiently large (resp. small) — i.e. greater (resp. smaller) than
any root of `P`.

This file defines the four corresponding "has sign" predicates
(`HasSignRight`, `HasSignLeft`, `HasSignAtPosInfty`, `HasSignAtNegInfty`)
and proves that the witnessed sign is unique.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Definitions -/

/-- `P` takes sign `s` immediately to the right of `a`: there exists `b > a`
    such that `sign (P x) = s` for every `x ∈ (a, b)`. When `s ≠ 0` this forces
    `P` to not vanish on `(a, b)`. -/
def HasSignRight (P : R[X]) (a : R) (s : SignType) : Prop :=
  ∃ b, a < b ∧ ∀ x ∈ Set.Ioo a b, SignType.sign (P.eval x) = s

/-- `P` takes sign `s` immediately to the left of `a`: there exists `b < a`
    such that `sign (P x) = s` for every `x ∈ (b, a)`. -/
def HasSignLeft (P : R[X]) (a : R) (s : SignType) : Prop :=
  ∃ b, b < a ∧ ∀ x ∈ Set.Ioo b a, SignType.sign (P.eval x) = s

/-- `P` takes sign `s` at `+∞`: there exists `M` such that `sign (P x) = s`
    for every `x > M` (i.e. on the right ray `Set.Ioi M`). -/
def HasSignAtPosInfty (P : R[X]) (s : SignType) : Prop :=
  ∃ M, ∀ x ∈ Set.Ioi M, SignType.sign (P.eval x) = s

/-- `P` takes sign `s` at `−∞`: there exists `M` such that `sign (P x) = s`
    for every `x < M` (i.e. on the left ray `Set.Iio M`). -/
def HasSignAtNegInfty (P : R[X]) (s : SignType) : Prop :=
  ∃ M, ∀ x ∈ Set.Iio M, SignType.sign (P.eval x) = s

/-! ## Well-definedness (uniqueness of the witnessed sign) -/

/-- The sign to the right of `a` is unique when it exists. -/
theorem HasSignRight.unique {P : R[X]} {a : R} {s₁ s₂ : SignType}
    (h₁ : HasSignRight P a s₁) (h₂ : HasSignRight P a s₂) : s₁ = s₂ := by
  obtain ⟨b₁, hab₁, hs₁⟩ := h₁
  obtain ⟨b₂, hab₂, hs₂⟩ := h₂
  -- Pick a common witness in `(a, min b₁ b₂)`, which is nonempty by density.
  obtain ⟨x, hax, hxm⟩ := exists_between (lt_min hab₁ hab₂)
  have hx₁ : x ∈ Set.Ioo a b₁ := ⟨hax, lt_of_lt_of_le hxm (min_le_left _ _)⟩
  have hx₂ : x ∈ Set.Ioo a b₂ := ⟨hax, lt_of_lt_of_le hxm (min_le_right _ _)⟩
  exact (hs₁ x hx₁).symm.trans (hs₂ x hx₂)

/-- The sign to the left of `a` is unique when it exists. -/
theorem HasSignLeft.unique {P : R[X]} {a : R} {s₁ s₂ : SignType}
    (h₁ : HasSignLeft P a s₁) (h₂ : HasSignLeft P a s₂) : s₁ = s₂ := by
  obtain ⟨b₁, hb₁a, hs₁⟩ := h₁
  obtain ⟨b₂, hb₂a, hs₂⟩ := h₂
  -- Common witness in `(max b₁ b₂, a)`.
  obtain ⟨x, hxm, hxa⟩ := exists_between (max_lt hb₁a hb₂a)
  have hx₁ : x ∈ Set.Ioo b₁ a := ⟨lt_of_le_of_lt (le_max_left _ _) hxm, hxa⟩
  have hx₂ : x ∈ Set.Ioo b₂ a := ⟨lt_of_le_of_lt (le_max_right _ _) hxm, hxa⟩
  exact (hs₁ x hx₁).symm.trans (hs₂ x hx₂)

/-- The sign at `+∞` is unique when it exists. -/
theorem HasSignAtPosInfty.unique {P : R[X]} {s₁ s₂ : SignType}
    (h₁ : HasSignAtPosInfty P s₁) (h₂ : HasSignAtPosInfty P s₂) : s₁ = s₂ := by
  obtain ⟨M₁, hM₁⟩ := h₁
  obtain ⟨M₂, hM₂⟩ := h₂
  -- Any `x` greater than `max M₁ M₂` satisfies both hypotheses.
  set M := max M₁ M₂
  obtain ⟨x, hxM⟩ := exists_gt M
  have hx₁ : x ∈ Set.Ioi M₁ := lt_of_le_of_lt (le_max_left _ _) hxM
  have hx₂ : x ∈ Set.Ioi M₂ := lt_of_le_of_lt (le_max_right _ _) hxM
  exact (hM₁ x hx₁).symm.trans (hM₂ x hx₂)

/-- The sign at `−∞` is unique when it exists. -/
theorem HasSignAtNegInfty.unique {P : R[X]} {s₁ s₂ : SignType}
    (h₁ : HasSignAtNegInfty P s₁) (h₂ : HasSignAtNegInfty P s₂) : s₁ = s₂ := by
  obtain ⟨M₁, hM₁⟩ := h₁
  obtain ⟨M₂, hM₂⟩ := h₂
  set M := min M₁ M₂
  obtain ⟨x, hxM⟩ := exists_lt M
  have hx₁ : x ∈ Set.Iio M₁ := lt_of_lt_of_le hxM (min_le_left _ _)
  have hx₂ : x ∈ Set.Iio M₂ := lt_of_lt_of_le hxM (min_le_right _ _)
  exact (hM₁ x hx₁).symm.trans (hM₂ x hx₂)

/-! ## Functional forms

Given uniqueness, we can extract a canonical `SignType` value when the
"has sign" predicate is realized by some sign. When no sign witnesses the
property (e.g. `P = 0` with no sign but `0` witnessing it, or pathological
cases) we fall back to `0`.
-/

open Classical in
/-- The sign of `P` to the right of `a`: the unique `s` with `HasSignRight P a s`
    if one exists, else `0`. -/
noncomputable def signRight (P : R[X]) (a : R) : SignType :=
  if h : ∃ s, HasSignRight P a s then h.choose else 0

open Classical in
/-- The sign of `P` to the left of `a`. -/
noncomputable def signLeft (P : R[X]) (a : R) : SignType :=
  if h : ∃ s, HasSignLeft P a s then h.choose else 0

open Classical in
/-- The sign of `P` at `+∞`. -/
noncomputable def signAtPosInfty (P : R[X]) : SignType :=
  if h : ∃ s, HasSignAtPosInfty P s then h.choose else 0

open Classical in
/-- The sign of `P` at `−∞`. -/
noncomputable def signAtNegInfty (P : R[X]) : SignType :=
  if h : ∃ s, HasSignAtNegInfty P s then h.choose else 0

/-- Characterization of `signRight`: if any sign witnesses `HasSignRight P a`,
    then `signRight P a` equals that sign. -/
theorem signRight_eq {P : R[X]} {a : R} {s : SignType}
    (h : HasSignRight P a s) : signRight P a = s := by
  unfold signRight
  rw [dite_eq_left ⟨s, h⟩]
  exact HasSignRight.unique (Exists.choose_spec ⟨s, h⟩) h

/-- Characterization of `signLeft`. -/
theorem signLeft_eq {P : R[X]} {a : R} {s : SignType}
    (h : HasSignLeft P a s) : signLeft P a = s := by
  unfold signLeft
  rw [dite_eq_left ⟨s, h⟩]
  exact HasSignLeft.unique (Exists.choose_spec ⟨s, h⟩) h

/-- Characterization of `signAtPosInfty`. -/
theorem signAtPosInfty_eq {P : R[X]} {s : SignType}
    (h : HasSignAtPosInfty P s) : signAtPosInfty P = s := by
  unfold signAtPosInfty
  rw [dite_eq_left ⟨s, h⟩]
  exact HasSignAtPosInfty.unique (Exists.choose_spec ⟨s, h⟩) h

/-- Characterization of `signAtNegInfty`. -/
theorem signAtNegInfty_eq {P : R[X]} {s : SignType}
    (h : HasSignAtNegInfty P s) : signAtNegInfty P = s := by
  unfold signAtNegInfty
  rw [dite_eq_left ⟨s, h⟩]
  exact HasSignAtNegInfty.unique (Exists.choose_spec ⟨s, h⟩) h

/-! ## Sign at `±∞` via the leading coefficient

By BPR Proposition 2.4, for `|x|` large enough the sign of `P(x)` is the sign
of the leading term `aₚ · x^p`. At `+∞` this is just `sign(aₚ)`; at `−∞` it
is `(−1)^p · sign(aₚ)`. These identities also hold vacuously when `P = 0`
(both sides collapse to `0`).
-/

/-- **Sign at `+∞` is the sign of the leading coefficient.** Immediate from
    BPR Proposition 2.4 (applied with `x > 0` large enough, `sign(x^p) = 1`). -/
theorem hasSignAtPosInfty_leadingCoeff (P : R[X]) :
    HasSignAtPosInfty P (SignType.sign P.leadingCoeff) := by
  by_cases hP : P = 0
  · subst hP
    refine ⟨0, ?_⟩
    intro x _
    simp
  · set K : R :=
      2 * ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i / P.leadingCoeff|
    refine ⟨K, ?_⟩
    intro x hx
    have hK_nn : (0 : R) ≤ K := by positivity
    have hx_pos : 0 < x := lt_of_le_of_lt hK_nn hx
    have hx_abs : K < |x| := by rwa [abs_of_pos hx_pos]
    rw [prop_2_4 P hP x hx_abs, sign_mul, sign_pow, sign_pos hx_pos,
        one_pow, mul_one]

/-- **Sign at `−∞` is `(−1)^{deg P}` times the sign of the leading coefficient.**
    Immediate from BPR Proposition 2.4 (applied with `x < 0` large negative,
    `sign(x^p) = (−1)^p`). -/
theorem hasSignAtNegInfty_leadingCoeff (P : R[X]) :
    HasSignAtNegInfty P ((-1) ^ P.natDegree * SignType.sign P.leadingCoeff) := by
  by_cases hP : P = 0
  · subst hP
    refine ⟨0, ?_⟩
    intro x _
    simp
  · set K : R :=
      2 * ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i / P.leadingCoeff|
    refine ⟨-K, ?_⟩
    intro x hx
    have hx_lt : x < -K := hx
    have hK_nn : (0 : R) ≤ K := by positivity
    have hx_neg : x < 0 := lt_of_lt_of_le hx_lt (neg_nonpos_of_nonneg hK_nn)
    have hx_abs : K < |x| := by rw [abs_of_neg hx_neg]; linarith
    rw [prop_2_4 P hP x hx_abs, sign_mul, sign_pow, sign_neg hx_neg, mul_comm]

/-- `signAtPosInfty P = sign P.leadingCoeff`. -/
theorem signAtPosInfty_eq_sign_leadingCoeff (P : R[X]) :
    signAtPosInfty P = SignType.sign P.leadingCoeff :=
  signAtPosInfty_eq (hasSignAtPosInfty_leadingCoeff P)

/-- `signAtNegInfty P = (−1)^{deg P} · sign P.leadingCoeff`. -/
theorem signAtNegInfty_eq_sign_leadingCoeff (P : R[X]) :
    signAtNegInfty P = (-1) ^ P.natDegree * SignType.sign P.leadingCoeff :=
  signAtNegInfty_eq (hasSignAtNegInfty_leadingCoeff P)

end Azurite.BPR

import Azurite.UInt64.Equiv.Basic
import Azurite.UInt64.SqrtRem
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.UInt
import Mathlib.Tactic.Ring

namespace Azurite.UInt64

/-!
Correctness of `sqrt` and `sqrtRem`.

The hardware `Float.sqrt` is treated as an arbitrary `UInt64`-valued
oracle: after the clamp in `floatGuess`, the proof of correctness
follows entirely from properties of the integer correction loops.
The main theorem is `sqrt_toNat : (sqrt n).toNat = Nat.sqrt n.toNat`;
`sqrtRem` then satisfies the usual `s² + r = n`, `r ≤ 2s` invariants.
-/

private theorem cap_toNat : sqrtRem.cap.toNat = 2 ^ 32 - 1 := by decide

/-- Squaring stays in range whenever `s ≤ cap`. -/
private theorem toNat_mul_self_of_le_cap {s : UInt64}
    (h : s.toNat ≤ sqrtRem.cap.toNat) :
    (s * s).toNat = s.toNat * s.toNat := by
  rw [cap_toNat] at h
  rw [_root_.UInt64.toNat_mul]
  apply Nat.mod_eq_of_lt
  calc s.toNat * s.toNat
      ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul h h
    _ < 2 ^ 64 := by decide

/-- `2 * s + 1` stays in range whenever `s ≤ cap`. -/
private theorem toNat_two_mul_succ_of_le_cap {s : UInt64}
    (h : s.toNat ≤ sqrtRem.cap.toNat) :
    (2 * s + 1).toNat = 2 * s.toNat + 1 := by
  rw [cap_toNat] at h
  rw [_root_.UInt64.toNat_add, _root_.UInt64.toNat_mul]
  show ((2 % 2 ^ 64) * s.toNat % 2 ^ 64 + 1 % 2 ^ 64) % 2 ^ 64 = 2 * s.toNat + 1
  have h_two : (2 : Nat) % 2 ^ 64 = 2 := by decide
  have h_one : (1 : Nat) % 2 ^ 64 = 1 := by decide
  rw [h_two, h_one]
  have h_2s : 2 * s.toNat < 2 ^ 64 := by
    calc 2 * s.toNat ≤ 2 * (2 ^ 32 - 1) := Nat.mul_le_mul_left 2 h
      _ < 2 ^ 64 := by decide
  rw [Nat.mod_eq_of_lt h_2s]
  apply Nat.mod_eq_of_lt
  omega

/-- Decrementing a nonzero `UInt64`. -/
private theorem toNat_sub_one_of_ne_zero {s : UInt64} (h : s ≠ 0) :
    (s - 1).toNat = s.toNat - 1 := by
  rw [_root_.UInt64.toNat_sub]
  show (2 ^ 64 - (1 : UInt64).toNat + s.toNat) % 2 ^ 64 = s.toNat - 1
  have h1 : (1 : UInt64).toNat = 1 := by decide
  rw [h1]
  have hs : s.toNat ≠ 0 := fun he => h (_root_.UInt64.eq_of_toNat_eq (by rw [he]; rfl))
  have hs_lt : s.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt s
  have hs_pos : 1 ≤ s.toNat := Nat.one_le_iff_ne_zero.mpr hs
  have : 2 ^ 64 - 1 + s.toNat = (s.toNat - 1) + 2 ^ 64 := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Incrementing a `UInt64` strictly below `cap`. -/
private theorem toNat_add_one_of_lt_cap {s : UInt64}
    (h : s.toNat < sqrtRem.cap.toNat) :
    (s + 1).toNat = s.toNat + 1 := by
  rw [cap_toNat] at h
  rw [_root_.UInt64.toNat_add]
  show (s.toNat + (1 : UInt64).toNat) % 2 ^ 64 = s.toNat + 1
  have h1 : (1 : UInt64).toNat = 1 := by decide
  rw [h1]
  exact Nat.mod_eq_of_lt (by omega)

/-- `n - s * s` doesn't underflow whenever `s * s ≤ n` (as `Nat`s) and
    `s ≤ cap`. -/
private theorem toNat_sub_mul_self {s n : UInt64}
    (h_cap : s.toNat ≤ sqrtRem.cap.toNat)
    (h_le : s.toNat * s.toNat ≤ n.toNat) :
    (n - s * s).toNat = n.toNat - s.toNat * s.toNat := by
  rw [_root_.UInt64.toNat_sub, toNat_mul_self_of_le_cap h_cap]
  have hn_lt : n.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt n
  have : 2 ^ 64 - s.toNat * s.toNat + n.toNat
       = (n.toNat - s.toNat * s.toNat) + 2 ^ 64 := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- After `correctDown` with enough fuel, the result is `≤` the input
    and its square is `≤ n`.  The clamp guarantees `s ≤ cap`. -/
theorem correctDown_spec (s n : UInt64) (fuel : Nat)
    (h_cap : s.toNat ≤ sqrtRem.cap.toNat)
    (h_fuel : s.toNat ≤ fuel) :
    (sqrtRem.correctDown s n fuel).toNat ≤ s.toNat ∧
    (sqrtRem.correctDown s n fuel).toNat * (sqrtRem.correctDown s n fuel).toNat ≤ n.toNat := by
  induction fuel generalizing s with
  | zero =>
    -- s.toNat ≤ 0 ⇒ s = 0
    have hs0 : s.toNat = 0 := Nat.le_zero.mp h_fuel
    rw [sqrtRem.correctDown]
    refine ⟨Nat.le_refl _, ?_⟩
    rw [hs0]; exact Nat.zero_le _
  | succ fuel' ih =>
    rw [sqrtRem.correctDown]
    by_cases hs0 : s = 0
    · -- s = 0: terminate, 0² = 0 ≤ n
      simp only [hs0, ↓reduceIte]
      refine ⟨Nat.le_refl _, ?_⟩
      have : (0 : UInt64).toNat = 0 := by decide
      rw [this]; exact Nat.zero_le _
    · simp only [hs0, ↓reduceIte]
      by_cases h_too_big : s * s > n
      · -- Recurse with s - 1.
        simp only [h_too_big, ↓reduceIte]
        have hs_ne : s.toNat ≠ 0 :=
          fun he => hs0 (_root_.UInt64.eq_of_toNat_eq (by rw [he]; rfl))
        have hs_pos : 1 ≤ s.toNat := Nat.one_le_iff_ne_zero.mpr hs_ne
        have h_sub_toNat : (s - 1).toNat = s.toNat - 1 := toNat_sub_one_of_ne_zero hs0
        have h_sub_cap : (s - 1).toNat ≤ sqrtRem.cap.toNat := by
          rw [h_sub_toNat]; omega
        have h_sub_fuel : (s - 1).toNat ≤ fuel' := by
          rw [h_sub_toNat]; omega
        have ih_applied := ih (s - 1) h_sub_cap h_sub_fuel
        refine ⟨?_, ih_applied.2⟩
        calc (sqrtRem.correctDown (s - 1) n fuel').toNat
            ≤ (s - 1).toNat := ih_applied.1
          _ = s.toNat - 1   := h_sub_toNat
          _ ≤ s.toNat       := Nat.sub_le _ _
      · -- s * s ≤ n: terminate, s² ≤ n.
        simp only [h_too_big, ↓reduceIte]
        refine ⟨Nat.le_refl _, ?_⟩
        rw [← toNat_mul_self_of_le_cap h_cap]
        exact (_root_.UInt64.le_iff_toNat_le).mp (Nat.not_lt.mp h_too_big)

/-- After `correctUp` with enough fuel and the precondition `s² ≤ n`,
    the result `s'` satisfies `s'² ≤ n < (s' + 1)²`.  The result is
    also `≤ cap`. -/
theorem correctUp_spec (s n : UInt64) (fuel : Nat)
    (h_cap : s.toNat ≤ sqrtRem.cap.toNat)
    (h_le : s.toNat * s.toNat ≤ n.toNat)
    (h_fuel : sqrtRem.cap.toNat - s.toNat ≤ fuel) :
    (sqrtRem.correctUp s n fuel).toNat ≤ sqrtRem.cap.toNat ∧
    (sqrtRem.correctUp s n fuel).toNat * (sqrtRem.correctUp s n fuel).toNat ≤ n.toNat ∧
    n.toNat < ((sqrtRem.correctUp s n fuel).toNat + 1) *
              ((sqrtRem.correctUp s n fuel).toNat + 1) := by
  induction fuel generalizing s with
  | zero =>
    -- cap.toNat ≤ s.toNat, combined with s.toNat ≤ cap.toNat ⇒ s = cap.
    have h_eq : s.toNat = sqrtRem.cap.toNat := by omega
    rw [sqrtRem.correctUp]
    refine ⟨by omega, h_le, ?_⟩
    -- n < 2^64 and (cap + 1)² = 2^64, so n < (s + 1)².
    have hn_lt : n.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt n
    rw [h_eq, cap_toNat]
    calc n.toNat < 2 ^ 64                       := hn_lt
      _ = (2 ^ 32 - 1 + 1) * (2 ^ 32 - 1 + 1)   := by decide
  | succ fuel' ih =>
    rw [sqrtRem.correctUp]
    by_cases h_at_cap : s ≥ sqrtRem.cap
    · -- s ≥ cap; combined with s.toNat ≤ cap.toNat ⇒ s.toNat = cap.toNat.
      simp only [h_at_cap, ↓reduceIte]
      have h_ge : sqrtRem.cap.toNat ≤ s.toNat :=
        (_root_.UInt64.le_iff_toNat_le).mp h_at_cap
      have h_eq : s.toNat = sqrtRem.cap.toNat := by omega
      refine ⟨h_cap, h_le, ?_⟩
      have hn_lt : n.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt n
      rw [h_eq, cap_toNat]
      calc n.toNat < 2 ^ 64                     := hn_lt
        _ = (2 ^ 32 - 1 + 1) * (2 ^ 32 - 1 + 1) := by decide
    · simp only [h_at_cap, ↓reduceIte]
      -- s < cap (strict), so s + 1 ≤ cap.
      have h_lt : s.toNat < sqrtRem.cap.toNat := by
        have h_not_ge : ¬ sqrtRem.cap.toNat ≤ s.toNat :=
          fun h => h_at_cap ((_root_.UInt64.le_iff_toNat_le).mpr h)
        omega
      have h_n_minus_ss : (n - s * s).toNat = n.toNat - s.toNat * s.toNat :=
        toNat_sub_mul_self h_cap h_le
      have h_two_s : (2 * s + 1).toNat = 2 * s.toNat + 1 :=
        toNat_two_mul_succ_of_le_cap h_cap
      by_cases h_room : 2 * s + 1 ≤ n - s * s
      · -- Recurse with s + 1.
        rw [ite_eq_left h_room]
        have h_room_nat : 2 * s.toNat + 1 ≤ n.toNat - s.toNat * s.toNat := by
          have := (_root_.UInt64.le_iff_toNat_le).mp h_room
          rw [h_two_s, h_n_minus_ss] at this
          exact this
        have h_add_toNat : (s + 1).toNat = s.toNat + 1 :=
          toNat_add_one_of_lt_cap h_lt
        have h_add_cap : (s + 1).toNat ≤ sqrtRem.cap.toNat := by
          rw [h_add_toNat]; omega
        have h_add_le : (s + 1).toNat * (s + 1).toNat ≤ n.toNat := by
          rw [h_add_toNat]
          have : (s.toNat + 1) * (s.toNat + 1) = s.toNat * s.toNat + (2 * s.toNat + 1) := by ring
          rw [this]
          omega
        have h_add_fuel : sqrtRem.cap.toNat - (s + 1).toNat ≤ fuel' := by
          rw [h_add_toNat]; omega
        exact ih (s + 1) h_add_cap h_add_le h_add_fuel
      · -- 2s + 1 > n - s². Equivalent to (s + 1)² > n.
        rw [ite_eq_right h_room]
        refine ⟨h_cap, h_le, ?_⟩
        -- Translate h_room to Nat side.
        have h_gt_nat : n.toNat - s.toNat * s.toNat < 2 * s.toNat + 1 := by
          by_contra h
          push Not at h
          apply h_room
          rw [_root_.UInt64.le_iff_toNat_le, h_two_s, h_n_minus_ss]
          exact h
        have h_sq : (s.toNat + 1) * (s.toNat + 1)
                  = s.toNat * s.toNat + (2 * s.toNat + 1) := by ring
        rw [h_sq]
        omega

/-- The clamp in `floatGuess` ensures the output never exceeds `cap`. -/
theorem floatGuess_le_cap (n : UInt64) : (sqrtRem.floatGuess n).toNat ≤ sqrtRem.cap.toNat := by
  show (if n.toFloat.sqrt.toUInt64 > sqrtRem.cap then sqrtRem.cap
        else n.toFloat.sqrt.toUInt64).toNat ≤ sqrtRem.cap.toNat
  split_ifs with h
  · exact Nat.le_refl _
  · exact (_root_.UInt64.le_iff_toNat_le).mp (Nat.not_lt.mp h)

/-- Main correctness: `sqrt n` is the integer square root of `n.toNat`. -/
@[simp] theorem toNat_sqrt (n : UInt64) : (sqrt n).toNat = Nat.sqrt n.toNat := by
  have h_s0_cap : (sqrtRem.floatGuess n).toNat ≤ sqrtRem.cap.toNat :=
    floatGuess_le_cap n
  have h_down := correctDown_spec (sqrtRem.floatGuess n) n
    ((sqrtRem.floatGuess n).toNat + 1) h_s0_cap (Nat.le_succ _)
  set s1 := sqrtRem.correctDown (sqrtRem.floatGuess n) n
              ((sqrtRem.floatGuess n).toNat + 1)
  have h_s1_cap : s1.toNat ≤ sqrtRem.cap.toNat := h_down.1.trans h_s0_cap
  have h_s1_le : s1.toNat * s1.toNat ≤ n.toNat := h_down.2
  have h_up := correctUp_spec s1 n (sqrtRem.cap.toNat - s1.toNat + 1)
    h_s1_cap h_s1_le (Nat.le_succ _)
  exact (Nat.eq_sqrt).mpr ⟨h_up.2.1, h_up.2.2⟩

/-- `sqrtRem` returns the integer square root and remainder. -/
@[simp] theorem toNat_sqrtRem_fst (n : UInt64) : (sqrtRem n).1.toNat = Nat.sqrt n.toNat := by
  show (sqrt n).toNat = _; exact toNat_sqrt n

/-- The remainder satisfies `r = n - s²`. -/
@[simp] theorem toNat_sqrtRem_snd (n : UInt64) :
    (sqrtRem n).2.toNat = n.toNat - Nat.sqrt n.toNat * Nat.sqrt n.toNat := by
  show (n - sqrt n * sqrt n).toNat = _
  have h_cap : (sqrt n).toNat ≤ sqrtRem.cap.toNat := by
    -- Sqrt is bounded by cap (since cap = 2^32 - 1 and Nat.sqrt n.toNat ≤ 2^32 - 1).
    have h_n_lt : n.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt n
    rw [toNat_sqrt, cap_toNat]
    -- Need: Nat.sqrt n.toNat ≤ 2^32 - 1, i.e., (Nat.sqrt n.toNat)² ≤ (2^32 - 1)² = 2^64 - 2^33 + 1 ≤ n.toNat ... actually easier:
    -- (Nat.sqrt n.toNat + 1)² > n.toNat ≥ 0; if Nat.sqrt n.toNat ≥ 2^32, then (Nat.sqrt n.toNat)² ≥ 2^64 > n.toNat, contradiction.
    by_contra h
    push Not at h
    have h_ge : 2 ^ 32 ≤ Nat.sqrt n.toNat := by omega
    have h_sq : 2 ^ 64 ≤ Nat.sqrt n.toNat * Nat.sqrt n.toNat := by
      calc 2 ^ 64 = 2 ^ 32 * 2 ^ 32 := by decide
        _ ≤ Nat.sqrt n.toNat * Nat.sqrt n.toNat := Nat.mul_le_mul h_ge h_ge
    have h_sq_le_n : Nat.sqrt n.toNat * Nat.sqrt n.toNat ≤ n.toNat := Nat.sqrt_le n.toNat
    omega
  have h_le : (sqrt n).toNat * (sqrt n).toNat ≤ n.toNat := by
    rw [toNat_sqrt]; exact Nat.sqrt_le n.toNat
  rw [toNat_sub_mul_self h_cap h_le, toNat_sqrt]

end Azurite.UInt64

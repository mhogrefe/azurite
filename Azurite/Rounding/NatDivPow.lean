import Azurite.Rounding.Nat
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Bitwise

/-!
# Shared helpers for rounding `v / 2^sh`

Lemmas about rounding a natural-number ratio `(v : ℕ) / 2 ^ sh` against the
`natBotSet` rounding target. Used by both `AzNat.toNat_shiftRightRound` and
`UInt64.toNat_shiftRightRound`.
-/

namespace Azurite
open RoundingTarget

/-- Uniqueness of `roundFloor`: any witness to `IsGreatest {s ∈ S | s ≤ x} e` equals
the value produced by `roundFloor`. -/
lemma roundFloor_val_of_isGreatest {S : Set EReal} [RoundingTarget S]
    {x : ℝ} {e : EReal} (h : IsGreatest {s | s ∈ S ∧ s ≤ (x : EReal)} e) :
    (roundFloor S x).val = e := by
  unfold roundFloor
  exact (existsGreatestLE (S := S) x).choose_spec.unique h

/-- Uniqueness of `roundCeiling`: any witness to `IsLeast {s ∈ S | x ≤ s} e` equals
the value produced by `roundCeiling`. -/
lemma roundCeiling_val_of_isLeast {S : Set EReal} [RoundingTarget S]
    {x : ℝ} {e : EReal} (h : IsLeast {s | s ∈ S ∧ (x : EReal) ≤ s} e) :
    (roundCeiling S x).val = e := by
  unfold roundCeiling
  exact (existsLeastGE (S := S) x).choose_spec.unique h

/-- For any real `x`, `roundCeiling natBotSet x = ((⌈x⌉₊ : ℝ) : EReal)`. -/
lemma roundCeiling_natBotSet (x : ℝ) :
    (roundCeiling natBotSet x).val = ((⌈x⌉₊ : ℝ) : EReal) := by
  apply roundCeiling_val_of_isLeast
  refine ⟨⟨Or.inr ⟨⌈x⌉₊, rfl⟩, ?_⟩, ?_⟩
  · exact_mod_cast Nat.le_ceil x
  · rintro s ⟨hmem, hge⟩
    rcases hmem with rfl | ⟨n, rfl⟩
    · exact absurd hge (not_le_of_gt (EReal.bot_lt_coe x))
    · have : x ≤ (n : ℝ) := by exact_mod_cast hge
      exact_mod_cast Nat.ceil_le.mpr this

/-- For nonneg real `x`, `roundFloor natBotSet x = ((⌊x⌋₊ : ℝ) : EReal)`. -/
lemma roundFloor_natBotSet_nonneg (x : ℝ) (hx : 0 ≤ x) :
    (roundFloor natBotSet x).val = ((⌊x⌋₊ : ℝ) : EReal) := by
  apply roundFloor_val_of_isGreatest
  refine ⟨⟨Or.inr ⟨⌊x⌋₊, rfl⟩, ?_⟩, ?_⟩
  · exact_mod_cast Nat.floor_le hx
  · rintro s ⟨hmem, hle⟩
    rcases hmem with rfl | ⟨n, rfl⟩
    · exact bot_le
    · have : (n : ℝ) ≤ x := by exact_mod_cast hle
      exact_mod_cast Nat.le_floor this

/-- If `s ∈ natBotSet` has real value `((q : ℝ) : EReal)` for some nat `q`,
then `natBotToNat s = q`. -/
lemma natBotToNat_eq_of_nat_val (q : ℕ) (s : ↥natBotSet)
    (hs : s.val = ((q : ℝ) : EReal)) : natBotToNat s = q := by
  unfold natBotToNat
  have hex : ∃ n : ℕ, ((n : ℝ) : EReal) = s.val := ⟨q, hs.symm⟩
  rw [dite_eq_left hex]
  have h1 := hex.choose_spec
  have h2 : ((hex.choose : ℝ) : EReal) = ((q : ℝ) : EReal) := h1.trans hs
  exact_mod_cast h2

/-- The fractional argument `v / 2 ^ sh` is nonneg. -/
lemma nat_div_pow_nonneg (v : ℕ) (sh : Nat) :
    0 ≤ (v : ℝ) / ((2 : ℝ) ^ sh) := by
  apply div_nonneg
  · exact_mod_cast Nat.zero_le _
  · exact pow_nonneg (by norm_num) _

/-- Floor of `v / 2^sh` is nat division. -/
lemma floor_nat_div_pow (v : ℕ) (sh : Nat) :
    ⌊(v : ℝ) / ((2 : ℝ) ^ sh)⌋₊ = v / 2 ^ sh := by
  have h1 : ((2 : ℝ) ^ sh) = (((2 ^ sh : ℕ) : ℝ)) := by push_cast; rfl
  rw [h1, Nat.floor_div_natCast, Nat.floor_natCast]

/-- Ceiling of `v / 2^sh`, divisible case: equals nat division. -/
lemma ceil_nat_div_pow_of_dvd (v : ℕ) (sh : Nat) (h : 2 ^ sh ∣ v) :
    ⌈(v : ℝ) / ((2 : ℝ) ^ sh)⌉₊ = v / 2 ^ sh := by
  obtain ⟨q, hq⟩ := h
  have heq : (v : ℝ) / ((2 : ℝ) ^ sh) = (q : ℝ) := by
    rw [hq]; push_cast; field_simp
  rw [heq, Nat.ceil_natCast, hq, Nat.mul_div_cancel_left _ (Nat.two_pow_pos sh)]

/-- Ceiling of `v / 2^sh`, non-divisible case: equals nat division plus one. -/
lemma ceil_nat_div_pow_of_not_dvd (v : ℕ) (sh : Nat) (h : ¬ 2 ^ sh ∣ v) :
    ⌈(v : ℝ) / ((2 : ℝ) ^ sh)⌉₊ = v / 2 ^ sh + 1 := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ sh := pow_pos (by norm_num) _
  set q := v / 2 ^ sh with hq_def
  set r := v % 2 ^ sh with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def, Nat.pos_iff_ne_zero]
    intro heq
    exact h (Nat.dvd_of_mod_eq_zero heq)
  have hr_lt : r < 2 ^ sh := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hn : v = q * 2 ^ sh + r := by
    rw [hq_def, hr_def, Nat.mul_comm]
    exact (Nat.div_add_mod v (2 ^ sh)).symm
  have hfloor_lt : ((q : ℝ)) < (v : ℝ) / ((2 : ℝ) ^ sh) := by
    rw [lt_div_iff₀ h2pos, hn]
    push_cast
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr_pos
    linarith
  have hlt_ceil : (v : ℝ) / ((2 : ℝ) ^ sh) < (q + 1 : ℝ) := by
    rw [div_lt_iff₀ h2pos, hn]
    push_cast
    have : ((r : ℝ)) < ((2 : ℝ) ^ sh) := by
      have := hr_lt
      have h2 : ((2 ^ sh : ℕ) : ℝ) = ((2 : ℝ) ^ sh) := by push_cast; rfl
      rw [← h2]; exact_mod_cast this
    linarith
  have h2 : (v : ℝ) / ((2 : ℝ) ^ sh) ≤ ((q + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have h3 : ((q : ℕ) : ℝ) < (v : ℝ) / ((2 : ℝ) ^ sh) := hfloor_lt
  apply le_antisymm
  · exact Nat.ceil_le.mpr h2
  · have := Nat.add_one_le_ceil_iff (n := q)
      (a := (v : ℝ) / ((2 : ℝ) ^ sh))
    exact this.mpr h3

/-- Decomposition: `v = (v / 2^sh) * 2^sh + v % 2^sh`. -/
lemma nat_eq_mul_pow_add_mod (v : ℕ) (sh : Nat) :
    v = (v / 2 ^ sh) * 2 ^ sh + v % 2 ^ sh := by
  conv_lhs => rw [← Nat.div_add_mod v (2 ^ sh)]
  ring

/-- For `v < 2^sh` with `sh > 0`: bit `sh-1` is false iff `v < 2^(sh-1)`. -/
lemma testBit_top_false_iff_lt_half (v sh : ℕ) (hsh : 0 < sh) (hv : v < 2 ^ sh) :
    v.testBit (sh - 1) = false ↔ v < 2 ^ (sh - 1) := by
  refine ⟨?_, Nat.testBit_eq_false_of_lt⟩
  intro h
  by_contra hge
  push Not at hge
  have h_rem_lt : v - 2 ^ (sh - 1) < 2 ^ (sh - 1) := by
    have h_two_pow : 2 ^ sh = 2 ^ (sh - 1) * 2 := by
      conv_lhs => rw [show sh = (sh - 1) + 1 from by omega]
      rw [Nat.pow_succ]
    omega
  have h_v_eq : v = 2 ^ (sh - 1) * 1 + (v - 2 ^ (sh - 1)) := by omega
  rw [h_v_eq, Nat.testBit_two_pow_mul_add _ h_rem_lt (sh - 1)] at h
  simp at h

/-- For `v < 2^sh` with `sh > 0`: bit `sh-1` is true iff `v ≥ 2^(sh-1)`. -/
lemma testBit_top_true_iff_half_le (v sh : ℕ) (hsh : 0 < sh) (hv : v < 2 ^ sh) :
    v.testBit (sh - 1) = true ↔ 2 ^ (sh - 1) ≤ v := by
  rw [show (v.testBit (sh - 1) = true) ↔ ¬ v.testBit (sh - 1) = false from by
    cases v.testBit (sh - 1) <;> simp]
  rw [testBit_top_false_iff_lt_half v sh hsh hv]
  omega

/-- For `v < 2^sh` with `sh > 0`: if bit `sh-1` is true and `v` is a multiple of
`2^(sh-1)`, then `v = 2^(sh-1)`. -/
lemma eq_half_of_testBit_and_dvd (v sh : ℕ) (hsh : 0 < sh) (hv : v < 2 ^ sh)
    (hbit : v.testBit (sh - 1) = true) (hdvd : 2 ^ (sh - 1) ∣ v) :
    v = 2 ^ (sh - 1) := by
  have hge : 2 ^ (sh - 1) ≤ v := (testBit_top_true_iff_half_le v sh hsh hv).mp hbit
  have h_two_pow : 2 ^ sh = 2 ^ (sh - 1) * 2 := by
    conv_lhs => rw [show sh = (sh - 1) + 1 from by omega]
    rw [Nat.pow_succ]
  obtain ⟨q, rfl⟩ := hdvd
  have hq_lt : q < 2 := by
    have h1 : 2 ^ (sh - 1) * q < 2 ^ (sh - 1) * 2 := by rw [← h_two_pow]; exact hv
    exact Nat.lt_of_mul_lt_mul_left h1
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · exfalso; rw [hq0, Nat.mul_zero] at hge
      exact absurd hge (by simp)
    · exact hq0
  have : q = 1 := by omega
  rw [this, Nat.mul_one]

end Azurite

import Mathlib.Data.Nat.Bitwise
import Azurite.UInt64.IsMultipleOfPow2
import Azurite.UInt64.Equiv.Basic

namespace UInt64

/-- The numeric value of the low-`k`-bit mask `(1 <<< k) - 1` in UInt64 is `2^k - 1`. -/
private lemma lowMask_toNat (k : Nat) (hk : k < 64) :
    (((1 : UInt64) <<< UInt64.ofNat k) - 1).toNat = 2 ^ k - 1 := by
  have h1 : ((1 : UInt64) <<< UInt64.ofNat k).toNat = 2 ^ k := by
    rw [_root_.UInt64.toNat_shiftLeft, show ((1 : UInt64).toNat = 1) from rfl]
    have hofNat : (UInt64.ofNat k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [hofNat, Nat.one_shiftLeft, Nat.mod_eq_of_lt hk]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk)
  rw [_root_.UInt64.toNat_sub, h1]
  change (2 ^ 64 - 1 + 2 ^ k) % 2 ^ 64 = 2 ^ k - 1
  have h2pow : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hk
  have h2pos : 0 < 2 ^ k := Nat.two_pow_pos _
  rw [show 2 ^ 64 - 1 + 2 ^ k = 2 ^ 64 + (2 ^ k - 1) from by omega]
  omega

theorem isMultipleOfPow2_iff (u : UInt64) (k : Nat) :
    u.isMultipleOfPow2 k = true ↔ 2 ^ k ∣ u.toNat := by
  unfold isMultipleOfPow2
  by_cases hk : k < 64
  · rw [ite_eq_left hk, beq_iff_eq]
    have h_toNat_eq :
        u &&& (((1 : UInt64) <<< UInt64.ofNat k) - 1) = 0 ↔
          (u &&& (((1 : UInt64) <<< UInt64.ofNat k) - 1)).toNat = 0 :=
      ⟨fun h => h ▸ rfl, fun h => _root_.UInt64.eq_of_toNat_eq (by rw [h]; rfl)⟩
    rw [h_toNat_eq, _root_.UInt64.toNat_and, lowMask_toNat k hk,
        Nat.and_two_pow_sub_one_eq_mod, ← Nat.dvd_iff_mod_eq_zero]
  · rw [ite_eq_right hk, beq_iff_eq]
    push Not at hk
    have hu_lt : u.toNat < 2 ^ k :=
      lt_of_lt_of_le (_root_.UInt64.toNat_lt _)
        (Nat.pow_le_pow_right (by omega) hk)
    constructor
    · intro h
      have : u.toNat = 0 := by rw [h]; rfl
      rw [this]; exact dvd_zero _
    · intro hdvd
      have hu_zero : u.toNat = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hu_lt
      exact _root_.UInt64.eq_of_toNat_eq (by rw [hu_zero]; rfl)

end UInt64

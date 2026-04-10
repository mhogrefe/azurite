import Azurite.AzNat.Basic

namespace Azurite

/-- Construct the AzNat with the lowest `k` bits set, equal to `2 ^ k - 1`. -/
def AzNat.lowMask (k : Nat) : AzNat where
  limbs :=
    let full := Array.replicate (k / 64) ((0 : UInt64) - 1)
    if k % 64 == 0 then full
    else full.push (((1 : UInt64) <<< UInt64.ofNat (k % 64)) - 1)
  last_ne_zero := by
    simp only
    split
    · -- k % 64 == 0
      rename_i h
      simp [BEq.beq] at h
      by_cases hk : k / 64 = 0
      · simp [hk, Array.back?]
      · rw [Array.back?_replicate]
        simp [show k / 64 ≠ 0 from hk]
    · -- k % 64 ≠ 0
      rename_i hne
      rw [Array.back?_push]
      intro h
      have h := Option.some.inj h
      have h1 : (((1 : UInt64) <<< UInt64.ofNat (k % 64)) - 1).toNat = 0 :=
        congrArg UInt64.toNat h
      simp [BEq.beq] at hne
      simp only [UInt64.toNat_sub, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat,
                  show 1 % 2 ^ 64 = 1 from by omega, Nat.one_shiftLeft] at h1
      have hr : k % 64 < 64 := Nat.mod_lt _ (by omega)
      have hmod : (UInt64.ofNat (k % 64)).toNat = k % 64 := by
        show (k % 64) % 2 ^ 64 = k % 64; exact Nat.mod_eq_of_lt (by omega)
      rw [hmod, Nat.mod_eq_of_lt hr] at h1
      have hpow : 2 ^ (k % 64) < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hr
      rw [Nat.mod_eq_of_lt hpow] at h1
      have : 1 < 2 ^ (k % 64) := Nat.one_lt_pow (by omega) (by omega)
      omega

end Azurite

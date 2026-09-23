import Azurite.AzInt.Pow2
import Azurite.AzInt.Equiv.Basic
import Azurite.AzNat.Equiv.Pow2

namespace Azurite.AzInt

theorem toInt_pow2 (k : Nat) : (AzInt.pow2 k).toInt = 2 ^ k := by
  unfold AzInt.pow2 toInt
  simp [AzNat.toNat_pow2]

theorem pow2_eq_ofInt (k : Nat) : AzInt.pow2 k = ofInt (2 ^ k) := by
  have h : (AzInt.pow2 k).toInt = (ofInt (2 ^ k)).toInt := by
    rw [toInt_pow2, toInt_ofInt]
  exact ofInt_toInt (AzInt.pow2 k) ▸ ofInt_toInt (ofInt (2 ^ k)) ▸ congrArg ofInt h

theorem isPowerOfTwo_iff (z : AzInt) :
    z.isPowerOfTwo = true ↔ ∃ k : Nat, z.toInt = 2 ^ k := by
  unfold AzInt.isPowerOfTwo
  simp only [Bool.and_eq_true]
  rw [AzNat.isPowerOfTwo_iff]
  have hpow_pos : ∀ k : Nat, (0 : Int) < 2 ^ k := fun k => by
    have := Nat.two_pow_pos k; exact_mod_cast this
  constructor
  · rintro ⟨hsign, k, hk⟩
    refine ⟨k, ?_⟩
    unfold toInt
    rw [ite_eq_left hsign, hk]
    push_cast
    rfl
  · rintro ⟨k, hk⟩
    have hsign : z.sign = true := by
      by_contra h
      have h' : z.sign = false := by
        match hb : z.sign with
        | true => exact absurd hb h
        | false => rfl
      unfold toInt at hk
      rw [ite_eq_right (by rw [h']; decide)] at hk
      have hnn : (0 : Int) ≤ z.abs.toNat := Int.natCast_nonneg _
      have := hpow_pos k
      omega
    refine ⟨hsign, k, ?_⟩
    unfold toInt at hk
    rw [ite_eq_left hsign] at hk
    have h2 : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
    rw [← h2] at hk
    exact_mod_cast hk

theorem isPowerOfTwo_ofInt (i : Int) :
    (ofInt i).isPowerOfTwo = true ↔ ∃ k : Nat, i = 2 ^ k := by
  rw [isPowerOfTwo_iff, toInt_ofInt]

end Azurite.AzInt

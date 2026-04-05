import Azurite.AzInt.Basic
import Azurite.AzNat.Equiv.Basic

namespace Azurite.AzInt

/-- Convert an `AzInt` to the exact mathematical `Int` that it represents. -/
def toInt (z : AzInt) : Int :=
  if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int)

/-- Compute the corresponding `AzInt` from a mathematical `Int`. -/
def ofInt (i : Int) : AzInt where
  sign := decide (0 ≤ i)
  abs := AzNat.ofNat i.natAbs
  zero_sign := by
    intro h
    have h1 : (AzNat.ofNat i.natAbs).toNat = (0 : AzNat).toNat := congrArg AzNat.toNat h
    rw [Azurite.AzNat.toNat_ofNat] at h1
    have h2 : i.natAbs = 0 := h1
    have h3 : i = 0 := Int.natAbs_eq_zero.mp h2
    subst h3
    exact rfl

-- Provide a default canonical evaluation linking `toInt` and `ofInt` natively.
lemma toInt_ofInt (i : Int) : (ofInt i).toInt = i := by
  unfold ofInt toInt
  simp
  split_ifs with h
  · have h1 : i.natAbs = i := Int.natAbs_of_nonneg h
    rw [Azurite.AzNat.toNat_ofNat, h1]
  · have h_lt : i < 0 := not_le.mp h
    have h1 : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (le_of_lt h_lt)
    rw [Azurite.AzNat.toNat_ofNat, h1, neg_neg]

lemma ofInt_toInt (z : AzInt) : ofInt z.toInt = z := by
  cases z with
  | mk sign abs zero_sign =>
    dsimp [ofInt, toInt]
    split_ifs with h_sign
    · simp
      exact ⟨h_sign, Azurite.AzNat.ofNat_toNat abs⟩
    · simp at h_sign
      simp
      have h1 : abs ≠ 0 := by
        intro h_zero
        have h_true := zero_sign h_zero
        rw [h_sign] at h_true
        contradiction
      have hz : decide (abs.toNat = 0) = false := by
        have h2 : abs.toNat ≠ 0 := by
          intro hh
          have h3 : abs.toNat = (0 : Azurite.AzNat).toNat := by
            have h_zero : (0 : Azurite.AzNat).toNat = 0 := rfl
            rw [hh, h_zero]
          have h4 : Azurite.AzNat.ofNat abs.toNat = Azurite.AzNat.ofNat (0 : Azurite.AzNat).toNat := congrArg Azurite.AzNat.ofNat h3
          rw [Azurite.AzNat.ofNat_toNat, Azurite.AzNat.ofNat_toNat] at h4
          exact h1 h4
        exact decide_eq_false h2
      rw [hz]
      exact ⟨h_sign.symm, Azurite.AzNat.ofNat_toNat abs⟩

/-- The mathematical equivalence between `AzInt` and the standard Lean 4 `Int`. -/
def equivInt : AzInt ≃ Int where
  toFun := toInt
  invFun := ofInt
  left_inv := ofInt_toInt
  right_inv := toInt_ofInt

end Azurite.AzInt

/-
  `Azurite.ExactDiv AzInt` instance: `AzInt.div` (Euclidean division)
  computes exact division when the divisor divides the dividend.
-/
import Azurite.Algorithm.ExactDiv
import Azurite.AzInt.DivMod
import Azurite.AzInt.Equiv.DivMod
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Instances

namespace Azurite

/-- `AzInt.div` is exact when `b ∣ a` and `b ≠ 0`. -/
instance : Azurite.ExactDiv AzInt where
  exactDiv := AzInt.div
  exactDiv_mul_self a b hdvd _hb := by
    -- Translate to `Int` via `toInt`, where `Int.ediv_mul_cancel` applies.
    have h_dvd_Z : b.toInt ∣ a.toInt := by
      rcases hdvd with ⟨c, hc⟩
      exact ⟨c.toInt, by rw [← AzInt.toInt_mul, ← hc]⟩
    have h_int : (AzInt.div a b * b).toInt = a.toInt := by
      rw [AzInt.toInt_mul]
      show (a.ediv b).toInt * b.toInt = a.toInt
      rw [AzInt.toInt_ediv]
      exact Int.ediv_mul_cancel h_dvd_Z
    conv_rhs => rw [← AzInt.ofInt_toInt a]
    rw [← h_int, AzInt.ofInt_toInt]

end Azurite

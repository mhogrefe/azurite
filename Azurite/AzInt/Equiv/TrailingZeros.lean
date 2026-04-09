import Azurite.AzInt.TrailingZeros
import Azurite.AzInt.Equiv.Conversion
import Azurite.AzNat.Equiv.TrailingZeros
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Azurite.AzInt

theorem trailingZeros_zero : (0 : AzInt).trailingZeros = none := by
  unfold AzInt.trailingZeros
  exact AzNat.trailingZeros_zero

theorem trailingZeros_eq_padicValInt (z : AzInt) (hz : z ≠ 0) :
    z.trailingZeros = some (padicValInt 2 z.toInt) := by
  unfold AzInt.trailingZeros
  have h_abs_ne : z.abs ≠ 0 := by
    intro h
    apply hz
    have := z.zero_sign h
    rcases z with ⟨sign, abs, zs⟩
    simp only at h this
    subst h; subst this
    rfl
  rw [AzNat.trailingZeros_eq_padicValNat z.abs h_abs_ne]
  congr 1
  have h1 : z.abs = z.natAbs := rfl
  have h2 : padicValInt 2 z.toInt = padicValNat 2 z.toInt.natAbs := by
    unfold padicValInt; rfl
  rw [h1, h2, toNat_natAbs z]

theorem trailingZeros_ofInt (i : Int) (hi : i ≠ 0) :
    (ofInt i).trailingZeros = some (padicValInt 2 i) := by
  have h : ofInt i ≠ 0 := by
    intro h
    apply hi
    have := congrArg toInt h
    rw [toInt_ofInt, toInt_zero] at this
    exact this
  rw [trailingZeros_eq_padicValInt _ h, toInt_ofInt]

end Azurite.AzInt

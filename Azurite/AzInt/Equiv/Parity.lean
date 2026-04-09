import Azurite.AzInt.Parity
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Equiv.Conversion
import Azurite.AzNat.Equiv.Parity
import Mathlib.Algebra.Ring.Parity

namespace Azurite.AzInt

private lemma even_int_iff_even_natAbs (z : Int) : Even z ↔ Even z.natAbs := by
  rw [Nat.even_iff, Int.even_iff]
  constructor <;> intro h <;> omega

theorem isEven_iff (z : AzInt) : z.isEven = true ↔ Even z.toInt := by
  unfold AzInt.isEven
  rw [even_int_iff_even_natAbs, ← toNat_natAbs]
  exact AzNat.isEven_iff z.abs

private lemma odd_int_iff_odd_natAbs (z : Int) : Odd z ↔ Odd z.natAbs := by
  rw [Nat.odd_iff, Int.odd_iff]
  constructor <;> intro h <;> omega

theorem isOdd_iff (z : AzInt) : z.isOdd = true ↔ Odd z.toInt := by
  unfold AzInt.isOdd
  rw [odd_int_iff_odd_natAbs, ← toNat_natAbs]
  exact AzNat.isOdd_iff z.abs

theorem isEven_ofInt (i : Int) : (ofInt i).isEven = true ↔ Even i := by
  rw [isEven_iff, toInt_ofInt]

theorem isOdd_ofInt (i : Int) : (ofInt i).isOdd = true ↔ Odd i := by
  rw [isOdd_iff, toInt_ofInt]

end Azurite.AzInt

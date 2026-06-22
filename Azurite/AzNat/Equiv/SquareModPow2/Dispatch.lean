import Azurite.AzNat.SquareModPow2.Dispatch
import Azurite.AzNat.Equiv.SquareModPow2.Karatsuba
import Azurite.AzNat.Equiv.SquareModPow2.ToomCook3

/-!
## Correctness of `AzNat.squareDispatchModPow2`
-/

namespace Azurite.AzNat

theorem toNat_squareDispatchModPow2 (a : AzNat) (k : Nat) :
    (squareDispatchModPow2 a k).toNat = a.toNat ^ 2 % 2 ^ k := by
  unfold squareDispatchModPow2
  split
  · exact toNat_squareSchoolbookModPow2 a k
  · split
    · exact toNat_squareKaratsubaModPow2 _ a k
    · exact toNat_squareToomCook3ModPow2 _ _ a k

end Azurite.AzNat

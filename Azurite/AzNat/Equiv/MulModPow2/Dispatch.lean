import Azurite.AzNat.MulModPow2.Dispatch
import Azurite.AzNat.Equiv.MulModPow2.Schoolbook
import Azurite.AzNat.Equiv.MulModPow2.Karatsuba
import Azurite.AzNat.Equiv.MulModPow2.ToomCook3

/-!
## Correctness of `AzNat.mulDispatchModPow2`

Every dispatch branch agrees with `(a.toNat * b.toNat) % 2 ^ k`.
-/

namespace Azurite.AzNat

theorem toNat_mulDispatchModPow2 (a b : AzNat) (k : Nat) :
    (mulDispatchModPow2 a b k).toNat = (a.toNat * b.toNat) % 2 ^ k := by
  unfold mulDispatchModPow2
  split
  · exact toNat_mulSchoolbookModPow2 a b k
  · split
    · exact toNat_mulKaratsubaModPow2 _ a b k
    · exact toNat_mulToomCook3ModPow2 _ _ a b k

end Azurite.AzNat

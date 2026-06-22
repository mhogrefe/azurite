import Azurite.AzNat.Square.ToomCook3
import Azurite.AzNat.Square.Schoolbook
import Azurite.AzNat.SquareModPow2.Schoolbook
import Azurite.AzNat.MulModPow2.ToomCook3
import Azurite.AzNat.AddModPow2
import Azurite.AzNat.OfLimbs

/-!
## `AzNat.squareToomCook3ModPow2` — low (mod `2 ^ k`) Toom-Cook-3 squaring

The same non-recursive low-square assembly as `squareKaratsubaModPow2`
(`a² ≡ A₀² + 2·A₀·A₁·βˢ (mod βᴸ)`), but the corner full square is Toom-Cook 3 and
the cross product is the low Toom-Cook-3 multiply, with the Toom-tuned split
`s = ⌈4·L/5⌉`.
-/

namespace Azurite.AzNat

/-- **Low Toom-Cook-3 squaring.** `(a ^ 2) mod 2 ^ k`, a full Toom-3 square corner
    plus a low Toom-3 cross product, dropping the high square. -/
def squareToomCook3ModPow2 (toomThreshold karaThreshold : Nat) (a : AzNat) (k : Nat) : AzNat :=
  let L := (k + 63) / 64
  let aPad : Array UInt64 := a.limbs ++ Array.replicate (L - a.limbs.size) 0
  have hL : 0 + L ≤ aPad.size := by
    show 0 + L ≤ (a.limbs ++ Array.replicate (L - a.limbs.size) (0 : UInt64)).size
    rw [Array.size_append, Array.size_replicate]; omega
  if h : L < 2 ∨ L < toomThreshold then
    modPow2 (ofLimbs (schoolbookSquareLimbs aPad 0 L (by omega))) k
  else
    let s := min ((4 * L + 4) / 5) (L - 1)
    let m := L - s
    have hs : 0 + s ≤ aPad.size := by have : s ≤ L := by omega
                                      omega
    have hcrossA : 0 + m ≤ aPad.size := by have : m ≤ L := by omega
                                           omega
    have hcrossB : s + m ≤ aPad.size := by have : s + m = L := by omega
                                           omega
    let cornerFull := ofLimbs (toomCook3SquareLimbs toomThreshold karaThreshold aPad 0 s (by omega))
    let cross := toomCook3MulLowLimbs toomThreshold karaThreshold aPad aPad 0 s m hcrossA hcrossB
    let doubled := addModPow2 cross cross (64 * m)
    let shifted := ofLimbs (Array.replicate s 0 ++ doubled.limbs)
    modPow2 (addModPow2 cornerFull shifted (64 * L)) k

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def parse (s : String) : AzNat := (AzNat.parse s).get!

#guard (squareToomCook3ModPow2 2 2 (parse "7") 4).toNat == 49 % 16
#guard (squareToomCook3ModPow2 2 2 (parse "255") 16).toNat == 65025
#guard (squareToomCook3ModPow2 2 2 (parse "0") 32).toNat == 0
#guard (squareToomCook3ModPow2 2 2 (parse "18446744073709551617") 64).toNat == 1
#guard (squareToomCook3ModPow2 2 2 (parse "123456789012345678901234567890") 200).toNat ==
  (123456789012345678901234567890 ^ 2) % (2 ^ 200)
#guard (squareToomCook3ModPow2 3 2 (parse "123456789012345678901234567890") 100).toNat ==
  (123456789012345678901234567890 ^ 2) % (2 ^ 100)
#guard (squareToomCook3ModPow2 2 2
  (parse "31415926535897932384626433832795028841971693993751058209749445923") 333).toNat ==
  (31415926535897932384626433832795028841971693993751058209749445923 ^ 2) % (2 ^ 333)
#guard (squareToomCook3ModPow2 2 2 (parse "123456789012345678901234567890") 150).toNat ==
  (squareSchoolbookModPow2 (parse "123456789012345678901234567890") 150).toNat

end Tests

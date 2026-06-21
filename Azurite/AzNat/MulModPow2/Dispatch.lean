import Azurite.AzNat.MulModPow2.Schoolbook
import Azurite.AzNat.MulModPow2.Karatsuba
import Azurite.AzNat.MulModPow2.ToomCook3

/-!
## `AzNat.mulDispatchModPow2` — size-dispatched low multiplication

Computes `(a * b) mod 2 ^ k` by picking the cheapest low-multiplication algorithm
for the operand size, mirroring the full `mulLimbsParam` dispatcher: schoolbook-low
for small operands, Mulders/Karatsuba-low for medium, Mulders/Toom-3-low for large.
Every branch returns the same value, so the dispatch is a pure performance choice.
-/

namespace Azurite.AzNat

/-- Limb-size cutoff below which schoolbook-low is used (and the Karatsuba-low
    base / fallback).  Untuned default, mirroring `mulDispatchThreshold`. -/
def mulModPow2KaratsubaCutoff : Nat := 16

/-- Limb-size cutoff at/above which Toom-3-low is used (and the Toom-low base).
    Untuned default, mirroring `mulDispatchToomCook3Cutoff`. -/
def mulModPow2ToomCutoff : Nat := 256

/-- Size-dispatched `(a * b) mod 2 ^ k`, choosing among the three low-product
    algorithms by the larger operand's limb count. -/
def mulDispatchModPow2 (a b : AzNat) (k : Nat) : AzNat :=
  if max a.limbs.size b.limbs.size < mulModPow2KaratsubaCutoff then
    mulSchoolbookModPow2 a b k
  else if max a.limbs.size b.limbs.size < mulModPow2ToomCutoff then
    mulKaratsubaModPow2 mulModPow2KaratsubaCutoff a b k
  else
    mulToomCook3ModPow2 mulModPow2ToomCutoff mulModPow2KaratsubaCutoff a b k

end Azurite.AzNat

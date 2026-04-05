import Azurite.AzNat.Basic

namespace Azurite.AzNat

def compareLoop (a b : AzNat) (i : Nat) : Ordering :=
  match Ord.compare a.limbs[i]! b.limbs[i]! with
  | Ordering.eq => match i with | 0 => Ordering.eq | i + 1 => compareLoop a b i
  | ord => ord

def compare (a b : AzNat) : Ordering :=
  match Ord.compare a.limbs.size b.limbs.size with
  | Ordering.eq => match a.limbs.size with | 0 => Ordering.eq | x => compareLoop a b (x - 1)
  | ord => ord

instance instOrdAzNat : Ord AzNat where
  compare := compare

end Azurite.AzNat

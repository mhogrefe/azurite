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

instance : LE AzNat where le a b := compare a b ≠ Ordering.gt
instance : LT AzNat where lt a b := compare a b = Ordering.lt

instance : DecidableRel (α := AzNat) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (compare a b ≠ Ordering.gt))

instance : DecidableRel (α := AzNat) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (compare a b = Ordering.lt))

instance : Max AzNat where max a b := if a ≤ b then b else a
instance : Min AzNat where min a b := if a ≤ b then a else b

end Azurite.AzNat

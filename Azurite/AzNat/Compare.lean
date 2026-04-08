import Azurite.AzNat.Basic

namespace Azurite.AzNat

def compareLoop (a b : AzNat) (i : Nat) (hi : i < a.limbs.size)
    (hs : a.limbs.size = b.limbs.size) : Ordering :=
  have hib : i < b.limbs.size := hs ▸ hi
  match Ord.compare a.limbs[i] b.limbs[i] with
  | Ordering.eq => match i with
    | 0 => Ordering.eq
    | i + 1 => compareLoop a b i (by omega) hs
  | ord => ord

def compare (a b : AzNat) : Ordering :=
  match h : Ord.compare a.limbs.size b.limbs.size with
  | Ordering.eq =>
    have hs : a.limbs.size = b.limbs.size := by
      exact Nat.compare_eq_eq.mp h
    match h2 : a.limbs.size with
    | 0 => Ordering.eq
    | x + 1 => compareLoop a b x (by omega) hs
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

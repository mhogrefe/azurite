import Azurite.UInt64.DivMod

namespace UInt64

/-- The first component of `divMod x y` is `x / y` (Nat-level). -/
theorem toNat_divMod_fst (x y : UInt64) :
    (divMod x y).1.toNat = x.toNat / y.toNat :=
  _root_.UInt64.toNat_div x y

/-- The second component of `divMod x y` is `x % y` (Nat-level). -/
theorem toNat_divMod_snd (x y : UInt64) :
    (divMod x y).2.toNat = x.toNat % y.toNat :=
  _root_.UInt64.toNat_mod x y

end UInt64

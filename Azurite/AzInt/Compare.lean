/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Compare
import Azurite.AzInt.Basic

namespace Azurite.AzInt

def compare (a b : AzInt) : Ordering :=
  if a.sign ≠ b.sign then
    if a.sign then Ordering.gt else Ordering.lt
  else
    if a.sign then
      Ord.compare a.abs b.abs
    else
      Ord.compare b.abs a.abs

instance : Ord AzInt := ⟨compare⟩

instance : LE AzInt where
  le a b := compare a b ≠ Ordering.gt

instance : LT AzInt where
  lt a b := compare a b = Ordering.lt

instance : DecidableRel (α := AzInt) (· ≤ ·) :=
  fun a b => if h : compare a b ≠ Ordering.gt then isTrue h else isFalse h

instance : DecidableRel (α := AzInt) (· < ·) :=
  fun a b => if h : compare a b = Ordering.lt then isTrue h else isFalse h

instance : Max AzInt where
  max a b := if a ≤ b then b else a

instance : Min AzInt where
  min a b := if a ≤ b then a else b

end Azurite.AzInt

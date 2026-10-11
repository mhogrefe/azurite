/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Basic
import Azurite.AzInt.Add
import Azurite.AzInt.Mul
import Azurite.AzInt.Compare
import Azurite.AzNat.CompareProduct
import Azurite.AzInt.Parse
import Azurite.AzInt.ToString

/-!
## Comparing a product with an integer without multiplying

`compareProduct a b c` compares `a · b` with `c`.  The signs settle every case except when
`a · b` and `c` are nonzero and have the same sign, where the magnitudes are compared by
`AzNat.compareProduct`, which multiplies only as a last resort.  (A comparison with `−c` is
`compareProduct a b (-c)`, negation of an integer being one sign flip.)

Correctness: `Equiv/CompareProduct.lean` (`compareProduct_eq`).
-/

namespace Azurite.AzInt

/-- **Compare `a · b` with `c`**, multiplying only as a last resort. -/
def compareProduct (a b c : AzInt) : Ordering :=
  if a.abs = 0 ∨ b.abs = 0 then
    if c.abs = 0 then .eq else if c.sign then .lt else .gt
  else if c.abs = 0 then (if a.sign == b.sign then .gt else .lt)
  else if a.sign == b.sign then
    if c.sign then AzNat.compareProduct a.abs b.abs c.abs else .gt
  else if c.sign then .lt
  else (AzNat.compareProduct a.abs b.abs c.abs).swap

end Azurite.AzInt

/-! ### Tests -/

section Tests

open Azurite Azurite.AzInt

private def Z (s : String) : AzInt := (AzInt.parse s).get!

#guard compareProduct (Z "3") (Z "7") (Z "21") == .eq
#guard compareProduct (Z "-3") (Z "-7") (Z "21") == .eq
#guard compareProduct (Z "-3") (Z "7") (Z "-21") == .eq
#guard compareProduct (Z "3") (Z "7") (Z "-21") == .gt
#guard compareProduct (Z "-3") (Z "7") (Z "21") == .lt
#guard compareProduct (Z "-3") (Z "7") (Z "-20") == .lt
#guard compareProduct (Z "-3") (Z "7") (Z "-22") == .gt
#guard compareProduct (Z "0") (Z "7") (Z "0") == .eq
#guard compareProduct (Z "0") (Z "7") (Z "5") == .lt
#guard compareProduct (Z "0") (Z "-7") (Z "-5") == .gt
#guard compareProduct (Z "3") (Z "7") (Z "0") == .gt
#guard compareProduct (Z "-3") (Z "7") (Z "0") == .lt
-- agreement with the multiplied comparison on a grid
private def grid : List AzInt :=
  ["0", "1", "-1", "2", "-2", "7", "-255", "256", "-65536", "18446744073709551616",
   "-18446744073709551615", "340282366920938463463374607431768211456",
   "-1000000000000000000000000000000000000001"].map Z
#guard grid.all fun a => grid.all fun b => grid.all fun c =>
  compareProduct a b c == AzInt.compare (a * b) c

end Tests

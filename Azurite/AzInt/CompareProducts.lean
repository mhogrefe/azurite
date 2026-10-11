/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.CompareProduct
import Azurite.AzNat.CompareProducts

/-!
## Comparing two products of integers without multiplying

`compareProducts a b c d` compares `a · b` with `c · d`.  The signs settle every case except
when both products are nonzero and have the same sign, where the magnitudes are compared by
`AzNat.compareProducts`, which multiplies only as a last resort.

Correctness: `Equiv/CompareProducts.lean` (`compareProducts_eq`).
-/

namespace Azurite.AzInt

/-- **Compare `a · b` with `c · d`**, multiplying only as a last resort. -/
def compareProducts (a b c d : AzInt) : Ordering :=
  if a.abs = 0 ∨ b.abs = 0 then
    if c.abs = 0 ∨ d.abs = 0 then .eq else if c.sign == d.sign then .lt else .gt
  else if c.abs = 0 ∨ d.abs = 0 then (if a.sign == b.sign then .gt else .lt)
  else if a.sign == b.sign then
    if c.sign == d.sign then AzNat.compareProducts a.abs b.abs c.abs d.abs else .gt
  else if c.sign == d.sign then .lt
  else (AzNat.compareProducts a.abs b.abs c.abs d.abs).swap

end Azurite.AzInt

/-! ### Tests -/

section Tests

open Azurite Azurite.AzInt

private def Z (s : String) : AzInt := (AzInt.parse s).get!

#guard compareProducts (Z "3") (Z "7") (Z "7") (Z "3") == .eq
#guard compareProducts (Z "-3") (Z "-7") (Z "7") (Z "3") == .eq
#guard compareProducts (Z "-3") (Z "7") (Z "-7") (Z "3") == .eq
#guard compareProducts (Z "3") (Z "7") (Z "-4") (Z "5") == .gt
#guard compareProducts (Z "-3") (Z "7") (Z "4") (Z "5") == .lt
#guard compareProducts (Z "-3") (Z "7") (Z "-4") (Z "5") == .lt            -- −21 < −20
#guard compareProducts (Z "-3") (Z "7") (Z "-4") (Z "6") == .gt            -- −21 > −24
#guard compareProducts (Z "0") (Z "7") (Z "0") (Z "-5") == .eq
#guard compareProducts (Z "0") (Z "7") (Z "4") (Z "-5") == .gt
#guard compareProducts (Z "0") (Z "7") (Z "4") (Z "5") == .lt
#guard compareProducts (Z "3") (Z "7") (Z "0") (Z "5") == .gt
#guard compareProducts (Z "3") (Z "-7") (Z "0") (Z "5") == .lt
-- agreement with the multiplied comparison on a grid
private def grid : List AzInt :=
  ["0", "1", "-1", "2", "-2", "7", "-255", "256", "-65536", "18446744073709551616",
   "-18446744073709551615", "340282366920938463463374607431768211456",
   "-1000000000000000000000000000000000000001"].map Z
#guard grid.all fun a => grid.all fun b => grid.all fun c => grid.all fun d =>
  compareProducts a b c d == AzInt.compare (a * b) (c * d)

end Tests

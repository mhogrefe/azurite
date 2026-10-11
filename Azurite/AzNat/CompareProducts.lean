/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Compare
import Azurite.AzNat.Mul
import Azurite.AzNat.Size
import Azurite.AzNat.ToStringBase
import Azurite.AzNat.ParseBase

/-!
## Comparing two products without multiplying

`compareProducts a b c d` compares `a · b` with `c · d`.  Multiplication is the expensive step,
so, as in `AzRat.cmp`, the products are formed only as a last resort, after cheap screens that
decide most cases:

1. a zero factor on either side;
2. the pairing `(a, c), (b, d)`: if the two comparisons agree the products compare the same
   way, and if one of them is an equality the other decides;
3. the same for the other pairing `(a, d), (b, c)`;
4. the bit lengths: `2^(size a + size b − 2) ≤ a · b < 2^(size a + size b)`, so a difference of
   at least `2` between `size a + size b` and `size c + size d` decides;
5. the two multiplications and one comparison.

Correctness: `Equiv/CompareProducts.lean` (`compareProducts_eq`).
-/

namespace Azurite.AzNat

/-- **Compare `a · b` with `c · d`**, multiplying only as a last resort. -/
def compareProducts (a b c d : AzNat) : Ordering :=
  if a = 0 ∨ b = 0 then (if c = 0 ∨ d = 0 then .eq else .lt)
  else if c = 0 ∨ d = 0 then .gt
  else
    let ac := compare a c
    let bd := compare b d
    if ac == bd then ac
    else if ac == .eq then bd
    else if bd == .eq then ac
    else
      let ad := compare a d
      let bc := compare b c
      if ad == bc then ad
      else if ad == .eq then bc
      else if bc == .eq then ad
      else
        let sl := a.size + b.size
        let sr := c.size + d.size
        if sr + 2 ≤ sl then .gt
        else if sl + 2 ≤ sr then .lt
        else compare (a * b) (c * d)

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def C (a b c d : AzNat) : Ordering := compareProducts a b c d

#guard C 0 (N "5") 0 0 == .eq
#guard C 0 (N "5") (N "3") (N "7") == .lt
#guard C (N "3") (N "7") 0 (N "9") == .gt
#guard C (N "3") (N "7") (N "3") (N "7") == .eq
#guard C (N "3") (N "7") (N "7") (N "3") == .eq
#guard C (N "3") (N "7") (N "4") (N "8") == .lt
#guard C (N "3") (N "7") (N "3") (N "8") == .lt
#guard C (N "3") (N "7") (N "2") (N "7") == .gt
#guard C (N "3") (N "7") (N "4") (N "5") == .gt          -- 21 > 20, opposite pairings
#guard C (N "3") (N "7") (N "5") (N "4") == .gt
#guard C (N "3") (N "7") (N "2") (N "11") == .lt         -- 21 < 22
#guard C (N "1000000") (N "1000000") (N "999999") (N "1000001") == .gt   -- the last resort
#guard C (N "123456789012345678901234567890") (N "987654321098765432109876543210")
  (N "123456789012345678901234567891") (N "987654321098765432109876543209") == .lt
-- agreement with the multiplied comparison on a grid
private def grid : List AzNat :=
  [0, 1, N "2", N "3", N "7", N "255", N "256", N "65535", N "4294967296",
   N "18446744073709551615", N "18446744073709551616", N "18446744073709551617",
   N "340282366920938463463374607431768211456", N "1000000000000000000000000000000000000001"]
#guard grid.all fun a => grid.all fun b => grid.all fun c => grid.all fun d =>
  compareProducts a b c d == AzNat.compare (a * b) (c * d)

end Tests

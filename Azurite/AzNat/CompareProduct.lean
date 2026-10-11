/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.CompareProducts

/-!
## Comparing a product with a number without multiplying

`compareProduct a b c` compares `a · b` with `c`.  As in `compareProducts`, the multiplication
is the last resort, after screens that decide most cases:

1. a zero factor, or `c = 0`;
2. a unit factor, `a = 1` or `b = 1`, which reduces to one comparison;
3. a factor that is at least `c`: with the other factor at least `2`, `a · b ≥ 2c > c`;
4. the bit lengths: `2^(size a + size b − 2) ≤ a · b < 2^(size a + size b)` against
   `2^(size c − 1) ≤ c < 2^(size c)`, so `size a + size b ≥ size c + 2` or
   `size a + size b + 1 ≤ size c` decides;
5. the multiplication and one comparison.

Correctness: `Equiv/CompareProduct.lean` (`compareProduct_eq`).
-/

namespace Azurite.AzNat

/-- **Compare `a · b` with `c`**, multiplying only as a last resort. -/
def compareProduct (a b c : AzNat) : Ordering :=
  if a = 0 ∨ b = 0 then (if c = 0 then .eq else .lt)
  else if c = 0 then .gt
  else if a = 1 then compare b c
  else if b = 1 then compare a c
  else if c ≤ a ∨ c ≤ b then .gt
  else
    let s := a.size + b.size
    if c.size + 2 ≤ s then .gt
    else if s + 1 ≤ c.size then .lt
    else compare (a * b) c

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def C (a b c : AzNat) : Ordering := compareProduct a b c

#guard C 0 (N "5") 0 == .eq
#guard C 0 (N "5") (N "3") == .lt
#guard C (N "3") (N "7") 0 == .gt
#guard C 1 (N "7") (N "7") == .eq
#guard C (N "7") 1 (N "8") == .lt
#guard C (N "3") (N "7") (N "21") == .eq
#guard C (N "3") (N "7") (N "20") == .gt
#guard C (N "3") (N "7") (N "22") == .lt
#guard C (N "3") (N "7") (N "5") == .gt                 -- a factor at least `c`
#guard C (N "3") (N "7") (N "100") == .lt                -- the bit lengths
#guard C (N "255") (N "255") (N "65025") == .eq           -- the last resort
#guard C (N "255") (N "255") (N "65024") == .gt
#guard C (N "123456789012345678901234567890") (N "987654321098765432109876543210")
  (N "121932631137021795226185032733622923332237463801111263526900") == .eq
-- agreement with the multiplied comparison on a grid
private def grid : List AzNat :=
  [0, 1, N "2", N "3", N "7", N "255", N "256", N "65535", N "65536", N "4294967296",
   N "18446744073709551615", N "18446744073709551616", N "18446744073709551617",
   N "340282366920938463463374607431768211456", N "340282366920938463463374607431768211457",
   N "1000000000000000000000000000000000000001"]
#guard grid.all fun a => grid.all fun b => grid.all fun c =>
  compareProduct a b c == AzNat.compare (a * b) c
#guard grid.all fun a => grid.all fun b =>
  compareProduct a b (a * b) == .eq && compareProduct a b (a * b + 1) == .lt

end Tests

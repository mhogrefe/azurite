/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.ExtendedGcd.Binary
import Azurite.AzInt.ExtendedGcd.HalfBinary

/-!
## Extended GCD

`AzInt.egcd a b = (g, s, t)` with `g = gcd(a, b)` and `s·a + t·b = g`.  Like `AzNat.gcd` it
dispatches on the operand size: the quadratic extended binary GCD (`ExtendedGcd/Binary.lean`,
HAC Algorithm 14.61) up to `egcdHalfBinaryThreshold` bits, the subquadratic extended half-binary
GCD (`ExtendedGcd/HalfBinary.lean`) above.  The coefficients are signed, hence `AzInt`; the
intended use is modular inversion (`AzNat.invMod`, `AzZMod.inv`).
-/

namespace Azurite.AzInt

/-- **Extended GCD.**  Returns `(g, s, t)` where `g = gcd(a, b)` and `s·a + t·b = g` over `ℤ`;
quadratic below `egcdHalfBinaryThreshold` bits, subquadratic above. -/
def egcd (a b : AzNat) : AzNat × AzInt × AzInt :=
  if max a.size b.size ≤ egcdHalfBinaryThreshold then egcdBinary a b else egcdHalfBinary a b

end Azurite.AzInt

/-! ### Tests -/

section Tests

open Azurite Azurite.AzInt

private def N (s : String) : AzNat := (AzNat.parse s).get!

/-- Bézout check for a result `(g, s, t)` of an extended GCD of `a`, `b`: `g` is the expected
value and `s·a + t·b = g` in `AzInt` arithmetic. -/
private def ok (r : AzNat × AzInt × AzInt) (a b g : AzNat) : Bool :=
  r.1 == g && (r.2.1 * a.toAzInt + r.2.2 * b.toAzInt == g.toAzInt)

private def E (a b g : AzNat) : Bool := ok (egcd a b) a b g
-- the extended half-binary GCD with a tiny base case, forcing the recursion (`Q`) or the
-- quadratic word rounds (`H`)
private def Q (a b g : AzNat) : Bool := ok (egcdHalfBinaryWith 8 0 a b) a b g
private def H (a b g : AzNat) : Bool := ok (egcdHalfBinaryWith 8 1000000 a b) a b g

-- small inputs through the dispatcher
#guard E (N "0") (N "0") (N "0")
#guard E (N "0") (N "7") (N "7")
#guard E (N "7") (N "0") (N "7")
#guard E (N "6") (N "4") (N "2")
#guard E (N "7") (N "15") (N "1")
#guard E (N "1024") (N "512") (N "512")
#guard E (N "18446744073709551615") (N "4294967295") (N "4294967295")
-- the three driver regimes on small inputs
#guard Q (N "0") (N "0") (N "0")
#guard Q (N "0") (N "12") (N "12")
#guard Q (N "12") (N "0") (N "12")
#guard Q (N "1") (N "1") (N "1")
#guard Q (N "7") (N "15") (N "1")
#guard Q (N "935") (N "714") (N "17")
#guard Q (N "1889826700059") (N "421872857844") (N "3")
#guard Q (N "18446744073709551615") (N "4294967295") (N "4294967295")
#guard Q (N "340282366920938463463374607431768211455") (N "18446744073709551615")
  (N "18446744073709551615")
#guard Q (N "340282366920938463463374607431768211457") (N "340282366920938463463374607431768211455")
  (N "1")
#guard H (N "0") (N "12") (N "12")
#guard H (N "19") (N "2") (N "1")
#guard H (N "935") (N "714") (N "17")
#guard H (N "1889826700059") (N "421872857844") (N "3")
#guard H (N "18446744073709551615") (N "4294967295") (N "4294967295")
#guard H (N "340282366920938463463374607431768211455") (N "18446744073709551615")
  (N "18446744073709551615")
-- powers of two and planted factors
private def big : AzNat := (N "123456789012345678901234567890123456789") <<< 200
#guard Q (big * N "1000003") (big * N "1000004") big
#guard H (big * N "1000003") (big * N "1000004") big
#guard Q (N "3" <<< 300) (N "9" <<< 280) (N "3" <<< 280)
#guard H (N "3" <<< 300) (N "9" <<< 280) (N "3" <<< 280)
#guard Q (N "6" <<< 300) ((N "9" <<< 280) + N "3") (N "3")
#guard H (N "6" <<< 300) ((N "9" <<< 280) + N "3") (N "3")
-- the dispatcher above its threshold: the quadratic word rounds …
private def huge : AzNat := big <<< 900
private def oddHuge : AzNat := huge + N "1"
#guard E (huge * N "1000003") (huge * N "1000004") huge
#guard E (oddHuge * N "1000003") (oddHuge * N "1000004") oddHuge
#guard E (N "7" <<< 1500) (N "5" <<< 1500) (N "1" <<< 1500)
#guard E (N "1" <<< 1400) ((N "1" <<< 1400) + N "1") (N "1")
#guard E ((N "1" <<< 1300) + N "3") ((N "1" <<< 1300) + N "4") (N "1")
-- … and the subquadratic recursion (operands above `halfBinaryGcdQuadraticThreshold` bits)
private def vast : AzNat := (N "1" <<< 70000) + N "1"
#guard E (vast * N "1000003") (vast * N "1000004") vast
#guard E (vast * N "6") (vast * N "4") (vast * N "2")
#guard E vast (vast + N "2") (N "1")
#guard E (vast <<< 100) ((vast + N "2") <<< 300) (N "1" <<< 100)

end Tests

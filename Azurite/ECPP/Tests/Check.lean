/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Check
import Azurite.AzNat.ParseBase

/-!
# Tests: the checker of elliptic curve primality certificates

The certificates were made outside the library: a curve with nonzero `b` over `ℤ/1000003` by
counting points, and curves `y² = x³ + ax` (whose orders are `n + 1 ± 2α`, `n + 1 ± 2β` for
`n = α² + β²`) for the larger numbers.
-/

namespace Azurite.ECPP.Tests

private def N (s : String) : AzNat := (AzNat.parse s).get!

private def step (a b u v q : String) : StepCert := ⟨N a, N b, N u, N v, N q⟩

-- a curve with `b ≠ 0`; the order is `3 · 333631`
private def c6 : StepCert := step "173914" "914786" "247198" "381021" "333631"

#guard check (N "1000003") [c6]
#guard checkStep (N "1000003") c6
-- another modulus, a point off the curve, a point of another order, a wrong `q`
#guard !checkStep (N "1000033") c6
#guard !checkStep (N "1000003") (step "173914" "914786" "247199" "381021" "333631")
#guard !checkStep (N "1000003") (step "173914" "914786" "247198" "381022" "333631")
#guard !checkStep (N "1000003") (step "173914" "914787" "247198" "381021" "333631")
#guard !checkStep (N "1000003") (step "173914" "914786" "247198" "381021" "333667")
-- `q` below the bound: the point `(0, 1)` has order 3 on `y² = x³ + 1`
#guard !checkStep (N "1000003") (step "0" "1" "0" "1" "3")
-- the modulus must be coprime to 6 and greater than 1
#guard !checkStep (N "1") c6
#guard !checkStep (N "0") c6
#guard !checkStep (N "1000002") c6
-- no step: `AzNat.isPrime`
#guard check (N "1000003") []
#guard !check (N "1000001") []

-- two steps: 655863716953 → 177741281 → 88883581
private def c12 : List StepCert :=
  [step "74261205725" "0" "141632497152" "95577941200" "177741281",
   step "79961501" "0" "84561495" "4498185" "88883581"]

#guard check (N "655863716953") c12
#guard check (N "655863716953") (c12.take 1)
#guard !check (N "655863716953") c12.reverse
#guard !check (N "655863716955") c12

-- two steps from 30 digits
#guard check (N "675904957021146642687026859253")
  [step "179999414637019889720414430427" "0" "52759796313871983505721415992"
     "625922244857558221929032254185" "337952478510572547831157813289",
   step "113364672056544925143747657778" "0" "232170387539697294189649133727"
     "206359497137176438339990905799" "108876442819127414877734389"]

-- one step from 60 digits
#guard check (N "620925886039477519841017904112262126384143904079370477911981")
  [step "356207431874751067910708745824196307542825672609913845424393" "0"
     "151155553841340715913715121357847029136602654116519035188598"
     "434754823870339537161683145455318825137341031553048339579574"
     "486894074431636410212794230419582583712515600013"]

end Azurite.ECPP.Tests

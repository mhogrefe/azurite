/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBracket

/-!
## The bracket of `log₂ x`

`log₂ x = ln x / ln 2`: the quotient of the bracket of `ln x` (`lnBracket`, one AGM run) by the
bracket of `ln 2` (`ln2Bracket`), with directed rounding.  The sign of the numerator decides which
end of the `ln 2` bracket makes the quotient an outer bound: for the lower end `⌊a/d⌋` if `a ≥ 0`
and `⌊a/c⌋` if `a < 0` (`c ≤ ln 2 ≤ d`), symmetrically for the upper end.  Exact powers of two
are handled by `log2PrecRound` itself and never reach the bracket.
-/

namespace Azurite.AzFloat

/-- The bracket of `log₂ x` for a positive finite float `x` of exponent `e` at working precision
`w`. -/
def log2Approx (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := lnBracket x e w
  let c := ln2Bracket w
  let lo := if b.1.isNegative then (divPrecRound b.1 c.1 w .Floor).1
    else (divPrecRound b.1 c.2 w .Floor).1
  let hi := if b.2.isNegative then (divPrecRound b.2 c.2 w .Ceiling).1
    else (divPrecRound b.2 c.1 w .Ceiling).1
  (fun p mode => setPrecRound lo p mode, fun p mode => setPrecRound hi p mode)

end Azurite.AzFloat

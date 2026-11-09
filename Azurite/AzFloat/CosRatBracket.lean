/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosBracket
import Azurite.AzFloat.PowRatBracket

/-!
## The bracket of `cos q` for a rational `q`

`cosRatBracket q w` encloses `cos q` for an `AzRat` `q` at Ziv level `w`: with
`eq = ratExpBound q` (`|q| < 2^(eq − 1)`) and `W = cosWork eq w`, the floats `⌊q⌋_W ≤ q ≤ ⌈q⌉_W`
are within `2|q| 2^(−W)` of `q`; `cosBracket ⌊q⌋_W eq w` encloses `cos ⌊q⌋_W`, and the Lipschitz
bound `|cos q − cos ⌊q⌋_W| ≤ ⌈q⌉_W − ⌊q⌋_W ≤ E` (`E` the 64-bit ceiling of the difference)
widens it to enclose `cos q`.  `cosRatApprox` is the pair of `Roundable`s for the Ziv loop
(`AzFloat/CosRat.lean`).
-/

namespace Azurite.AzFloat

/-- The bracket of `cos q` at Ziv level `w` for a rational `q`. -/
def cosRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let eq := ratExpBound q
  let W := cosWork eq w
  let xlo := (ofAzRatRound q W .Floor).1
  let xhi := (ofAzRatRound q W .Ceiling).1
  let E := (subPrecRound xhi xlo 64 .Ceiling).1
  Encl.widen W (cosBracket xlo eq w) (Encl.exact E)

/-- `cosRatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def cosRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := cosRatBracket q w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat

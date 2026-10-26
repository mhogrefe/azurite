/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiBracket
import Azurite.AzFloat.LogBaseFloatBracket

/-!
## The bracket of `1/π`

`oneDivPiBracket w` is the reciprocal of the bracket of `π` (`piBracket w`) by
`divBracketByPosBracket`, the lower end of the `π` bracket first raised to `2 < π` so that the
proven width bound never pushes it to zero; `oneDivPiApprox` is the pair of `Roundable`s for the
Ziv loop.  `2/π` is an exact shift (`AzFloat/PiConstants`).
-/

namespace Azurite.AzFloat

/-- The bracket of `1/π`. -/
def oneDivPiBracket (w : Nat) : AzFloat × AzFloat :=
  let b := piBracket w
  divBracketByPosBracket (one, one) (maxOf b.1 two, b.2) w

/-- The two ends of the `1/π` bracket, rounded at any requested precision. -/
def oneDivPiApprox (w : Nat) : Roundable × Roundable :=
  let b := oneDivPiBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat

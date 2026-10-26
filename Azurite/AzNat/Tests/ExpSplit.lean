/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ExpSplit
import Azurite.AzNat.ToStringBase

/-!
# Tests for the binary splitting of the exponential series

`expNumDen p s N = (num, den)` with `num / (den · 2^(sN)) = ∑_{m ≤ N} (p/2^s)^m / m!`: the
partial sums `65/24` (`x = 1`, four terms), `79/48` (`x = 1/2`, three terms) and `65/32`
(`x = 3/4`, two terms).
-/

namespace Azurite.AzNat

private def S (p s N : Nat) : String × String :=
  let r := expNumDen (ofNat p) s N
  (toString r.1, toString r.2)

#guard S 1 0 4 == ("65", "24")
#guard S 1 1 3 == ("79", "6")
#guard S 3 2 2 == ("65", "2")
#guard S 1 0 0 == ("1", "1")
#guard S 7 3 1 == ("15", "1")

/-- The fraction does not depend on the tree shape: the sequential fallback (fuel `0`) agrees. -/
private def T3 (st : SplitState) : String × String × String :=
  (toString st.1, toString st.2.1, toString st.2.2)

#guard T3 (expSplitFuel (ofNat 5) 3 0 0 6) == T3 (expSplit (ofNat 5) 3 0 6)
#guard T3 (expSplitFuel (ofNat 5) 3 1 2 7) == T3 (expSplit (ofNat 5) 3 2 7)
#guard T3 (expSplitFuel (ofNat 123) 10 2 0 9) == T3 (expSplit (ofNat 123) 10 0 9)

end Azurite.AzNat

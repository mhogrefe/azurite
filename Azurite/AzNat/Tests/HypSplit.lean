/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.HypSplit
import Azurite.AzNat.ToStringBase

/-!
# Tests for the hypergeometric binary splitting

The reference values are the unreduced fractions `3 T(0, N) / (8 Q(0, N))` of
`(3/8) ∑_{k<N} 1/((2k+1)² C(2k,k))` and `T(0, N) / (4 B(0, N) Q(0, N))` of
`(1/4) ∑_{k<N} 1/((2k+1) 3^{k+1})`, checked against exact rational sums
(`422071/1058400` and `269/2835` in lowest terms for the two five- and four-term cases).
-/

namespace Azurite.AzNat

private def S (r : AzNat × AzNat) : String × String :=
  (ToString.toString r.1, ToString.toString r.2)

#guard S (catalanNumDen 0) == ("0", "8")
#guard S (catalanNumDen 1) == ("3", "8")
#guard S (catalanNumDen 5) == ("45583668", "114307200")
#guard S (atanhSqrtThreeNumDen 4) == ("3228", "34020")

/-- The fraction does not depend on the tree shape: the sequential fallback (fuel `0`) agrees. -/
private def T3 (s : HypState) : String × String × String :=
  (ToString.toString s.1, ToString.toString s.2.1, ToString.toString s.2.2)

#guard T3 (hypSplitFuel catalanLeaf 0 0 9) == T3 (hypSplit catalanLeaf 0 9)
#guard T3 (hypSplitFuel catalanLeaf 1 2 7) == T3 (hypSplit catalanLeaf 2 7)
#guard T3 (hypSplitFuel catalanLeaf 2 2 7) == T3 (hypSplit catalanLeaf 2 7)

end Azurite.AzNat

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.SignedSplit
import Azurite.AzInt.ToString
import Azurite.AzNat.ToStringBase

/-!
# Tests for the signed binary splitting of Sweeney's series

The reference values are the unreduced fractions `T(0, N) / Q(0, N)²` from an independent model
of the same recursion (checked there against
`∑_{k<N} (−1)^k n^(k+1) / ((k+1) (k+1)!)`).
-/

namespace Azurite.AzInt

private def S (n N : Nat) : String × String :=
  let r := sweeneyNumDen n N
  (ToString.toString r.1, ToString.toString r.2)

#guard S 1 1 == ("1", "1")
#guard S 1 2 == ("3", "4")
#guard S 2 3 == ("52", "36")
#guard S 3 5 == ("26082", "14400")
#guard S 10 8 == ("-251982336000", "1625702400")
#guard S 7 13 == ("112765420830799860480", "38775788043632640000")

/-- The fraction does not depend on the tree shape: the sequential fallback (fuel `0`) agrees. -/
private def T4 (s : SignedSplitState) : String × String × String :=
  (ToString.toString s.1, ToString.toString s.2.1, ToString.toString s.2.2)

#guard T4 (signedSplitFuelOf (sweeneyLeaf (AzNat.ofNat 3)) 0 0 5)
  == T4 (signedSplitOf (sweeneyLeaf (AzNat.ofNat 3)) 0 5)
#guard T4 (signedSplitFuelOf (sweeneyLeaf (AzNat.ofNat 10)) 1 2 9)
  == T4 (signedSplitOf (sweeneyLeaf (AzNat.ofNat 10)) 2 9)
#guard T4 (signedSplitFuelOf (sweeneyLeaf (AzNat.ofNat 10)) 2 2 9)
  == T4 (signedSplitOf (sweeneyLeaf (AzNat.ofNat 10)) 2 9)

end Azurite.AzInt

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.AtanhSplit
import Azurite.AzNat.ToStringBase

/-!
# Tests for the binary splitting of `atanh(1/q)`

The reference values are the unreduced fractions `q · T(0, N) / (B(0, N) Q(0, N))` from an
independent model of the same recursion (and checked there against `∑ 1/((2k+1) q^(2k+1))`).
-/

namespace Azurite.AzNat

private def S (q N : Nat) : String × String :=
  let r := atanhNumDen q N
  (toString r.1, toString r.2)

#guard S 3 1 == ("3", "9")
#guard S 3 2 == ("84", "243")
#guard S 3 3 == ("3789", "10935")
#guard S 3 5 == ("19339227", "55801305")
#guard S 26 4 == ("843756286126", "21926841780480")
#guard S 26 7 == ("335456071086231948751782", "8717555431530060497141760")

/-- The fraction does not depend on the tree shape: the sequential fallback (fuel `0`) agrees. -/
private def T3 (s : SplitState) : String × String × String :=
  (toString s.1, toString s.2.1, toString s.2.2)

#guard T3 (atanhSplitFuel (ofNat 9) 0 0 5) == T3 (atanhSplit (ofNat 9) 0 5)
#guard T3 (atanhSplitFuel (ofNat 676) 1 3 9) == T3 (atanhSplit (ofNat 676) 3 9)
#guard T3 (atanhSplitFuel (ofNat 676) 2 3 9) == T3 (atanhSplit (ofNat 676) 3 9)

end Azurite.AzNat

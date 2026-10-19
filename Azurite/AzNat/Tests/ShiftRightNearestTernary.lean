/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ParseBase
import Azurite.AzNat.ShiftRightNearestTernary
import Azurite.AzNat.ToStringBase
import Azurite.AzInt.Parse
import Azurite.AzInt.ToString

/-!
# Tests for the ternary-aware nearest right shift
-/

namespace Azurite

private def parse (s : String) : AzNat := (AzNat.parse s).get!
private def N (s : String) (o : Ordering) (sh : Nat) : String :=
  AzNat.toString ((parse s).shiftRightNearestTernary o sh)
private def Z (s : String) (o : Ordering) (sh : Nat) : String :=
  AzInt.toString ((AzInt.parse s).get!.shiftRightNearestTernary o sh)

-- no tie: the ternary is irrelevant
#guard N "13" .eq 2 == "3"    -- 3.25
#guard N "13" .lt 2 == "3"
#guard N "15" .gt 2 == "4"    -- 3.75
#guard N "12" .lt 2 == "3"    -- exact
#guard N "0" .lt 5 == "0"
#guard N "7" .gt 0 == "7"
-- a tie: `.eq` rounds to even, `.lt` (true value above) up, `.gt` (true value below) down
#guard N "6" .eq 2 == "2"     -- 1.5 → 2
#guard N "10" .eq 2 == "2"    -- 2.5 → 2
#guard N "10" .lt 2 == "3"
#guard N "10" .gt 2 == "2"
#guard N "6" .gt 2 == "1"
#guard N "2" .eq 2 == "0"     -- 0.5 → 0
#guard N "2" .lt 2 == "1"
-- a large shift
#guard N "340282366920938463463374607431768211456" .eq 128 == "1"      -- 2^128
#guard N "170141183460469231731687303715884105728" .eq 128 == "0"      -- 2^127: tie → 0
#guard N "170141183460469231731687303715884105728" .lt 128 == "1"
#guard N "510423550381407695195061911147652317184" .eq 128 == "2"      -- 3·2^127: tie → 2
#guard N "510423550381407695195061911147652317184" .gt 128 == "1"
-- signed: the ternary compares the stored value with the true value, so it swaps for negatives
#guard Z "-10" .eq 2 == "-2"
#guard Z "-10" .lt 2 == "-2"  -- true value above −2.5: toward −2
#guard Z "-10" .gt 2 == "-3"  -- true value below −2.5: toward −3
#guard Z "-13" .lt 2 == "-3"
#guard Z "-15" .lt 2 == "-4"
#guard Z "10" .lt 2 == "3"
#guard Z "0" .gt 3 == "0"

end Azurite

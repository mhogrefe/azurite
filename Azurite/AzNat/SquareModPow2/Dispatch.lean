/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.SquareModPow2.Schoolbook
import Azurite.AzNat.SquareModPow2.Karatsuba
import Azurite.AzNat.SquareModPow2.ToomCook3
import Azurite.AzNat.MulModPow2.Dispatch

/-!
## `AzNat.squareDispatchModPow2` — size-dispatched low squaring

Picks the cheapest low-squaring algorithm for the operand size, mirroring
`mulDispatchModPow2` (and reusing its cutoffs).  Every branch returns the same
value, so the dispatch is a pure performance choice.
-/

namespace Azurite.AzNat

/-- Limb-size cutoff below which schoolbook-low squaring is used.  Tuned via
    `az_nat_square_mod_pow2_algorithms`: unlike products, the Karatsuba-low tier
    *is* useful for squares (its corner is a symmetric full square), overtaking
    schoolbook-low at ~128 limbs. -/
def squareModPow2KaratsubaCutoff : Nat := 128

/-- Limb-size cutoff at/above which Toom-3-low squaring is used.  Tuned: for
    squares Toom-3-low only ties Karatsuba-low in the measured range, so the
    switch is deferred to where Toom-3's asymptotic edge should eventually tell. -/
def squareModPow2ToomCutoff : Nat := 1024

/-- Size-dispatched `(a ^ 2) mod 2 ^ k`, choosing among the three low-square
    algorithms by the operand's limb count. -/
def squareDispatchModPow2 (a : AzNat) (k : Nat) : AzNat :=
  if a.limbs.size < squareModPow2KaratsubaCutoff then
    squareSchoolbookModPow2 a k
  else if a.limbs.size < squareModPow2ToomCutoff then
    squareKaratsubaModPow2 mulModPow2KaraCorner a k
  else
    squareToomCook3ModPow2 mulModPow2ToomCorner mulModPow2KaraCorner a k

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def parse (s : String) : AzNat := (AzNat.parse s).get!

#guard (squareDispatchModPow2 (parse "123456789012345678901234567890") 200).toNat ==
  (123456789012345678901234567890 ^ 2) % (2 ^ 200)
#guard (squareDispatchModPow2 (parse "7") 4).toNat == 49 % 16
#guard (squareDispatchModPow2 (parse "0") 32).toNat == 0

end Tests

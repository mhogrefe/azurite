/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.MulModPow2.Schoolbook
import Azurite.AzNat.MulModPow2.Karatsuba
import Azurite.AzNat.MulModPow2.ToomCook3

/-!
## `AzNat.mulDispatchModPow2` — size-dispatched low multiplication

Computes `(a * b) mod 2 ^ k` by picking the cheapest low-multiplication algorithm
for the operand size, mirroring the full `mulLimbsParam` dispatcher: schoolbook-low
for small operands, Mulders/Karatsuba-low for medium, Mulders/Toom-3-low for large.
Every branch returns the same value, so the dispatch is a pure performance choice.
-/

namespace Azurite.AzNat

/-- Corner full-multiply fallbacks used *inside* the split low-product algorithms
    (the tuned full-mul thresholds: full Karatsuba falls to schoolbook below 16
    limbs, full Toom-3 to Karatsuba below 256).  These are independent of the
    tier cutoffs below — the tier cutoff says which low-product *algorithm* to
    run; the corner threshold keeps that algorithm's inner full multiply fast. -/
def mulModPow2KaraCorner : Nat := 16
/-- See `mulModPow2KaraCorner`. -/
def mulModPow2ToomCorner : Nat := 256

/-- Limb-size cutoff below which schoolbook-low is used.  Tuned via
    `az_nat_mul_mod_pow2_algorithms`: schoolbook-low's top-half-skipping beats the
    split algorithms up to ~256 limbs, so for products the Karatsuba-low tier is
    dominated — schoolbook-low directly hands off to Toom-3-low at 256. -/
def mulModPow2KaratsubaCutoff : Nat := 256

/-- Limb-size cutoff at/above which Toom-3-low is used.  Tuned: Toom-3-low (with
    a Karatsuba/Toom corner) overtakes schoolbook-low at ~256 limbs. -/
def mulModPow2ToomCutoff : Nat := 256

/-- Size-dispatched `(a * b) mod 2 ^ k`, choosing among the three low-product
    algorithms by the larger operand's limb count. -/
def mulDispatchModPow2 (a b : AzNat) (k : Nat) : AzNat :=
  if max a.limbs.size b.limbs.size < mulModPow2KaratsubaCutoff then
    mulSchoolbookModPow2 a b k
  else if max a.limbs.size b.limbs.size < mulModPow2ToomCutoff then
    mulKaratsubaModPow2 mulModPow2KaraCorner a b k
  else
    mulToomCook3ModPow2 mulModPow2ToomCorner mulModPow2KaraCorner a b k

end Azurite.AzNat

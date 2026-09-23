/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **The production primality test**: Miller–Rabin for fast rejection,
  APR-CL for the deterministic verdict, trial division as the total
  fallback — with the same proven characterization as the naive test it
  supersedes (`isPrime_eq_true_iff : isPrime n = true ↔ Nat.Prime n.toNat`,
  in `Azurite/AzNat/Equiv/IsPrime.lean`).

  Layering: small inputs (up to 32 bits) go straight to trial division
  (at most `2^16` divisions of a one-limb number).  Larger inputs run the
  twelve fixed Miller–Rabin bases first: composites — including the
  semiprimes with two huge factors, the worst case for trial division —
  are almost always rejected in `O(log³ n)`.  Survivors go to the APR-CL
  test with the (5.5)-selected certificate (`aprclTestSel`), whose
  `some true`/`some false` verdicts are both proven; only when it gives up
  (`none`: a certificate witness outside the generator's search lists, or
  a missing (6.4) source — never observed on any input) does the
  trial-division confirmation run.  The result is total: no `none`.

  The iff survives because every layer is a theorem: `false` from
  Miller–Rabin proves compositeness (`millerRabin_eq_true_of_prime`
  contrapositive), both APR-CL verdicts are sound (`aprclTestSel_true`,
  `aprclTestSel_false`), and the trial-division verdict is an iff
  (`isPrimeNaive_eq_true_iff`).
-/
import Azurite.AzNat.Primality
import Azurite.AzNat.MillerRabin
import Azurite.AzNat.Size
import Azurite.APRCL.Select

namespace Azurite

namespace AzNat

/-- The APR-CL verdict, with trial division as the fallback when it gives up. -/
def aprclOrNaive (n : AzNat) : Bool :=
  match APRCL.aprclTestSel n with
  | some b => b
  | none => isPrimeNaive n

/-- **Primality test**: Miller–Rabin rejection (twelve fixed bases,
deterministic), then the APR-CL verdict, then trial division if APR-CL
gives up; small inputs skip straight to trial division.  Proven:
`isPrime n = true ↔ Nat.Prime n.toNat`. -/
def isPrime (n : AzNat) : Bool :=
  if n.size ≤ 32 then isPrimeNaive n
  else millerRabin n 0 0 && aprclOrNaive n

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

private def parse' (s : String) : AzNat := (AzNat.parse s).get!

-- the trial-division path
#guard isPrime (parse' "0") == false
#guard isPrime (parse' "1") == false
#guard isPrime (parse' "2") == true
#guard isPrime (parse' "97") == true
#guard isPrime (parse' "7919") == true
#guard isPrime (parse' "104729") == true
#guard isPrime (parse' "104730") == false
#guard isPrime (parse' "2147483647") == true          -- 2^31 − 1
#guard isPrime (parse' "2147483649") == false         -- 3·715827883
#guard isPrime (parse' "825265") == false             -- Carmichael, 5 factors
-- above the cutoff: Miller–Rabin rejections (a semiprime, 2^64 + 1)
#guard isPrime (parse' "4295360521") == false         -- 65539·65539
#guard isPrime (parse' "18446744073709551617") == false
-- above the cutoff: APR-CL verdicts
#guard isPrime (parse' "4294967311") == true          -- least prime above 2^32
#guard isPrime (parse' "2305843009213693951") == true -- 2^61 − 1
#guard isPrime (parse' "1000000000000000009") == true
-- a strong pseudoprime to the first twelve prime bases: passes Miller–Rabin, refuted by APR-CL
#guard isPrime (parse' "3317044064679887385961981") == false

end Tests

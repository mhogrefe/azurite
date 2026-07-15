/-
  **The production primality test**: Miller–Rabin for fast rejection,
  trial division for the deterministic confirmation — with the same
  proven characterization as the naive test it supersedes
  (`isPrime_eq_true_iff : isPrime n = true ↔ Nat.Prime n.toNat`, in
  `Azurite/AzNat/Equiv/IsPrime.lean`).

  Layering: tiny inputs (below 20 bits) go straight to trial division
  (cheaper than the modular powers there).  Larger inputs run the twelve
  fixed Miller–Rabin bases first: composites — including the semiprimes
  with two huge factors, the worst case for trial division — are almost
  always rejected in `O(log³ n)`, and only survivors (in practice,
  primes) pay the trial-division confirmation.  The `&&` short-circuits,
  so a Miller–Rabin rejection never reaches the naive test.

  The iff survives because both directions are theorems: `false` from
  Miller–Rabin proves compositeness (`millerRabin_eq_true_of_prime`
  contrapositive), and the trial-division verdict is an iff
  (`isPrimeNaive_eq_true_iff`).
-/
import Azurite.AzNat.Primality
import Azurite.AzNat.MillerRabin
import Azurite.AzNat.Size

namespace Azurite

namespace AzNat

/-- **Primality test**: Miller–Rabin rejection (twelve fixed bases,
deterministic), then trial-division confirmation; tiny inputs skip
straight to trial division.  Proven: `isPrime n = true ↔ Nat.Prime
n.toNat`. -/
def isPrime (n : AzNat) : Bool :=
  if n.size ≤ 20 then isPrimeNaive n
  else millerRabin n 0 0 && isPrimeNaive n

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

private def parse' (s : String) : AzNat := (AzNat.parse s).get!

-- both layers: small (trial-division path) and large (Miller–Rabin path)
#guard isPrime (parse' "0") == false
#guard isPrime (parse' "1") == false
#guard isPrime (parse' "2") == true
#guard isPrime (parse' "97") == true
#guard isPrime (parse' "7919") == true
#guard isPrime (parse' "104729") == true
#guard isPrime (parse' "104730") == false
-- above the cutoff: a prime, a semiprime (the trial-division worst case
-- — here Miller–Rabin rejects instantly), and a Carmichael number
#guard isPrime (parse' "2147483647") == true          -- 2^31 − 1
#guard isPrime (parse' "2147483649") == false         -- 3·715827883
#guard isPrime (parse' "4295360521") == false         -- 65539·65539
#guard isPrime (parse' "825265") == false             -- Carmichael, 5 factors

end Tests

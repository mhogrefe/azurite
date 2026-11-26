/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.IsPrime
import Azurite.AzNat.Equiv.IsPrimeAprcl
import Azurite.ECPP.Equiv.Search

/-!
# Correctness of the production primality test

**`isPrime_eq_true_iff : isPrime n = true ↔ Nat.Prime n.toNat`.**  Every layer is a theorem:
the APR-CL test is an iff (`isPrimeAprcl_eq_true_iff`, `aprclOrNaive_eq_true_iff`), primes
pass Miller–Rabin (`millerRabin_eq_true_of_prime`), and an accepted elliptic curve certificate
proves primality (`ECPP.provePrime_sound`) — the search for it is not verified and need not
be: when it finds nothing the APR-CL verdict decides.
-/

namespace Azurite

namespace AzNat

/-- **Correctness of `isPrime`**: `true` exactly on primes. -/
theorem isPrime_eq_true_iff (n : AzNat) :
    isPrime n = true ↔ Nat.Prime n.toNat := by
  rw [isPrime]
  by_cases hsize : n.size ≤ 80
  · rw [ite_eq_left hsize, isPrimeAprcl_eq_true_iff]
  · rw [ite_eq_right hsize, Bool.and_eq_true, Bool.or_eq_true, aprclOrNaive_eq_true_iff]
    constructor
    · rintro ⟨-, h | h⟩
      · exact ECPP.provePrime_sound h
      · exact h
    · exact fun hp => ⟨millerRabin_eq_true_of_prime hp 0 0, Or.inr hp⟩

/-- `ofNat`-phrased correctness. -/
theorem isPrime_ofNat_eq_true_iff (k : Nat) :
    isPrime (ofNat k) = true ↔ Nat.Prime k := by
  rw [isPrime_eq_true_iff, toNat_ofNat]

end AzNat

end Azurite

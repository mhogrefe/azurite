/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.IsPrime
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.IsPrimeAprcl
import Azurite.AzNat.Equiv.IsPrimeWord
import Azurite.AzNat.Equiv.Size
import Azurite.ECPP.Equiv.Search

/-!
# Correctness of the production primality test

**`isPrime_eq_true_iff : isPrime n = true ↔ Nat.Prime n.toNat`.**  Every layer is a theorem:
the APR-CL layer is an iff with either fallback (`aprclOrEcpp_eq_true_iff`,
`aprclOrNaive_eq_true_iff`), trial division is an iff (`isPrimeNaive_eq_true_iff`), primes
pass Miller–Rabin (`millerRabin_eq_true_of_prime`), and an accepted elliptic curve certificate
proves primality (`ECPP.provePrime_sound`) — the search for it is not verified and need not
be: when it finds nothing the APR-CL verdict decides.
-/

namespace Azurite

namespace AzNat

/-- The fallback of APR-CL is an iff. -/
theorem ecppOrNaive_eq_true_iff (n : AzNat) :
    ecppOrNaive n = true ↔ Nat.Prime n.toNat := by
  rw [ecppOrNaive, Bool.or_eq_true, Bool.and_eq_true, isPrimeNaive_eq_true_iff]
  constructor
  · rintro (⟨-, h⟩ | h)
    · exact ECPP.provePrime_sound h
    · exact h
  · exact Or.inr

/-- The APR-CL layer with its fallback is an iff. -/
theorem aprclOrEcpp_eq_true_iff (n : AzNat) :
    aprclOrEcpp n = true ↔ Nat.Prime n.toNat := by
  unfold aprclOrEcpp
  rcases h : APRCL.aprclTestSel n with _ | b
  · exact ecppOrNaive_eq_true_iff n
  · cases b
    · simp only [Bool.false_eq_true, false_iff]
      exact APRCL.aprclTestSel_false h
    · simp only [true_iff]
      exact APRCL.aprclTestSel_true h

/-- **Correctness of `isPrime`**: `true` exactly on primes. -/
theorem isPrime_eq_true_iff (n : AzNat) :
    isPrime n = true ↔ Nat.Prime n.toNat := by
  rw [isPrime]
  by_cases h32 : n.size ≤ 32
  · rw [ite_eq_left h32]
    rcases hw : isPrimeWord n.toUInt64 with _ | b
    · exact isPrimeNaive_eq_true_iff n
    · have hlt : n.toNat < 2 ^ 32 := by
        rw [← size_toNat] at h32
        exact lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) h32)
      have hto : n.toUInt64.toNat = n.toNat := by
        rw [toUInt64_toNat]
        show n.toNat % 2 ^ 64 = n.toNat
        exact Nat.mod_eq_of_lt (by omega)
      have := isPrimeWord_eq_some hw
      rw [hto] at this
      exact this
  rw [ite_eq_right h32]
  by_cases hsize : n.size ≤ 80
  · rw [ite_eq_left hsize, Bool.and_eq_true, aprclOrEcpp_eq_true_iff]
    exact ⟨fun h => h.2, fun hp => ⟨millerRabin_eq_true_of_prime hp 0 0, hp⟩⟩
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

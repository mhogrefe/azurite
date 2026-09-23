/-
  **Correctness of the production primality test**:
  `isPrime n = true ↔ Nat.Prime n.toNat` — the same characterization the
  naive test carried, now for the Miller–Rabin / APR-CL / trial-division
  layering.  Every layer is a theorem: the trial-division verdict is an
  iff (`isPrimeNaive_eq_true_iff`), primes always pass Miller–Rabin
  (`millerRabin_eq_true_of_prime`), and both APR-CL verdicts are sound
  (`aprclTestSel_true`, `aprclTestSel_false`), so the `none` fallback is
  the only case that needs the naive test.
-/
import Azurite.AzNat.IsPrime
import Azurite.AzNat.Equiv.Primality
import Azurite.AzNat.Equiv.MillerRabin
import Azurite.APRCL.Equiv.Test

namespace Azurite

namespace AzNat

/-- The APR-CL layer with its trial-division fallback is an iff. -/
theorem aprclOrNaive_eq_true_iff (n : AzNat) :
    aprclOrNaive n = true ↔ Nat.Prime n.toNat := by
  unfold aprclOrNaive
  rcases h : APRCL.aprclTestSel n with _ | b
  · exact isPrimeNaive_eq_true_iff n
  · cases b
    · simp only [Bool.false_eq_true, false_iff]
      exact APRCL.aprclTestSel_false h
    · simp only [true_iff]
      exact APRCL.aprclTestSel_true h

/-- **Correctness of `isPrime`**: `true` exactly on primes. -/
theorem isPrime_eq_true_iff (n : AzNat) :
    isPrime n = true ↔ Nat.Prime n.toNat := by
  rw [isPrime]
  by_cases hsize : n.size ≤ 32
  · rw [if_pos hsize, isPrimeNaive_eq_true_iff]
  · rw [if_neg hsize, Bool.and_eq_true, aprclOrNaive_eq_true_iff]
    constructor
    · exact fun h => h.2
    · exact fun hp => ⟨millerRabin_eq_true_of_prime hp 0 0, hp⟩

/-- `ofNat`-phrased correctness. -/
theorem isPrime_ofNat_eq_true_iff (k : Nat) :
    isPrime (ofNat k) = true ↔ Nat.Prime k := by
  rw [isPrime_eq_true_iff, toNat_ofNat]

end AzNat

end Azurite

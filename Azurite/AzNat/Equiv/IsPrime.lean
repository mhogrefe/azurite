/-
  **Correctness of the production primality test**:
  `isPrime n = true ↔ Nat.Prime n.toNat` — the same characterization the
  naive test carried, now for the Miller–Rabin-accelerated layering.
  Both branches are immediate: the trial-division verdict is an iff
  (`isPrimeNaive_eq_true_iff`), and primes always pass Miller–Rabin
  (`millerRabin_eq_true_of_prime`), so the conjunction loses nothing.
-/
import Azurite.AzNat.IsPrime
import Azurite.AzNat.Equiv.Primality
import Azurite.AzNat.Equiv.MillerRabin

namespace Azurite

namespace AzNat

/-- **Correctness of `isPrime`**: `true` exactly on primes. -/
theorem isPrime_eq_true_iff (n : AzNat) :
    isPrime n = true ↔ Nat.Prime n.toNat := by
  rw [isPrime]
  by_cases hsize : n.size ≤ 20
  · rw [if_pos hsize, isPrimeNaive_eq_true_iff]
  · rw [if_neg hsize, Bool.and_eq_true, isPrimeNaive_eq_true_iff]
    constructor
    · exact fun h => h.2
    · exact fun hp => ⟨millerRabin_eq_true_of_prime hp 0 0, hp⟩

/-- `ofNat`-phrased correctness. -/
theorem isPrime_ofNat_eq_true_iff (k : Nat) :
    isPrime (ofNat k) = true ↔ Nat.Prime k := by
  rw [isPrime_eq_true_iff, toNat_ofNat]

end AzNat

end Azurite

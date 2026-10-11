/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.PrimeSieve
import Azurite.AzNat.Mul
import Azurite.AzNat.Compare
import Azurite.AzNat.Conversion
import Azurite.AzNat.ToStringBase
import Mathlib.Data.Nat.Log

/-!
## Landau's function

`landauFunctionPrefix n = [g(0), g(1), …, g(n − 1)]`, where `g(m)` is Landau's function: the
maximal order of an element of the symmetric group `S_m`, equivalently the largest `M ≥ 1` with
`ℓ(M) ≤ m`, where `ℓ(M) = Σ p^{v_p(M)}` is the sum of the prime powers in the factorization of
`M` (Landau, 1903).  `g(0), …, g(12) = 1, 1, 2, 3, 4, 6, 6, 12, 15, 20, 30, 30, 60`.

**The basic algorithm** (Deléglise, Nicolas and Zimmermann, §2.1).  Let `g_j(m)` be the maximum
over the `M` whose prime factors are among the first `j` primes with `ℓ(M) ≤ m`.  Then
`g_0(m) = 1` and

`g_j(m) = max (g_{j−1}(m), p_j g_{j−1}(m − p_j), p_j² g_{j−1}(m − p_j²), …)`

over the powers `p_j^k ≤ m`: either `p_j` does not divide the optimum, or it divides it exactly
`k` times and the cofactor is optimal for `m − p_j^k`.  The table `g(0), …, g(n − 1)` is
therefore updated once per prime `p ≤ n` (`landauStep`), each update reading only the previous
table, and the final table is `g` itself since every prime factor of an `M` with `ℓ(M) ≤ m` is at
most `m`.  The running time is `O(n² / log n)` multiplications and comparisons of numbers of
`O(√(n log n))` bits; the paper cuts the primes at Grantham's bound `1.328 √(n log n)` on the
largest prime factor of `g(n)`, which is not formalized here and so not used.  The paper's main
contribution, the superchampion method for a single large `n`, is a different algorithm.

### References

* M. Deléglise, J.-L. Nicolas and P. Zimmermann, *Landau's function for one million billions*,
  Journal de Théorie des Nombres de Bordeaux 20 (2008), 625–671, <https://arxiv.org/abs/0803.2160>
  — §2.1, "The basic algorithm" (Algorithm 1 and the induction relation (2.3)); §1.1 for the
  definitions (1.1), (1.2) and Grantham's bound (1.11).
* *Landau's function*, Wikipedia, <https://en.wikipedia.org/wiki/Landau%27s_function>.
* E. Landau, *Über die Maximalordnung der Permutationen gegebenen Grades*, Archiv der Mathematik
  und Physik 5 (1903), 92–103 — `g(n) = max { M : ℓ(M) ≤ n }`.

No library code was consulted.
-/

namespace Azurite.AzNat

/-- The candidates `p^k · g[m − p^k]` for `k = 1, …, ⌊log_p m⌋`. -/
def landauCandidates (g : Array AzNat) (p m : Nat) : List AzNat :=
  (List.range (Nat.log p m)).map fun i => ofNat (p ^ (i + 1)) * g.getD (m - p ^ (i + 1)) 1

/-- One prime: `g'[m] = max (g[m], p g[m − p], p² g[m − p²], …)`, from the previous table. -/
def landauStep (g : Array AzNat) (p : Nat) : Array AzNat :=
  Array.ofFn fun (m : Fin g.size) => (landauCandidates g p m).foldl max g[m]

/-- **Landau's function** `g(0), g(1), …, g(n − 1)`. -/
def landauFunctionPrefix (n : Nat) : List AzNat :=
  ((primesUpTo n).toList.foldl landauStep (Array.replicate n 1)).toList

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def L (n : Nat) : List String := (landauFunctionPrefix n).map AzNat.toString

#guard L 0 == []
#guard L 1 == ["1"]
#guard L 13 == ["1", "1", "2", "3", "4", "6", "6", "12", "15", "20", "30", "30", "60"]
-- OEIS A000793
#guard L 30 == ["1", "1", "2", "3", "4", "6", "6", "12", "15", "20", "30", "30", "60", "60",
  "84", "105", "140", "210", "210", "420", "420", "420", "420", "840", "840", "1260", "1260",
  "1540", "2310", "2520"]
#guard (L 60).drop 50 == ["180180", "180180", "180180", "360360", "360360", "360360", "360360",
  "471240", "510510", "556920"]
#guard (L 101).getLast! == "232792560"
#guard (landauFunctionPrefix 500).length == 500
-- `g` is nondecreasing, and `g(m) ≤ g(m − 1) · m`
#guard
  let g := (landauFunctionPrefix 300).toArray
  (List.range 299).all fun m => g[m]! ≤ g[m + 1]! && g[m + 1]! ≤ g[m]! * ofNat (m + 1)

end Tests

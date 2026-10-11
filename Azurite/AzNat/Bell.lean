/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Binomial
import Azurite.AzNat.Pow
import Azurite.AzNat.Div
import Azurite.AzNat.Sub
import Azurite.AzNat.ToStringBase

/-!
## Bell numbers

`bellNumbersPrefix n = [B₀, B₁, …, B_{n−1}]`, the Bell numbers: `Bₙ` counts the partitions of
a set of `n` elements, `B₀, B₁, … = 1, 1, 2, 5, 15, 52, 203, …`, and satisfies
`B_{n+1} = Σ_{k ≤ n} C(n, k) B_k` (Mathlib's `Nat.bell`).

**The Bell triangle** (Aitken's array, Peirce's triangle).  Row `0` is `[B₀]`; row `n + 1`
starts with the last entry of row `n` and then adds the entries of row `n` one by one:
`a(n+1, 0) = a(n, n)`, `a(n+1, k+1) = a(n+1, k) + a(n, k)`.  The first entry of row `n` is `Bₙ`
(and its last entry `B_{n+1}`), so the first `n` Bell numbers cost `n(n−1)/2` additions of
numbers of `O(n log n)` bits, with no multiplication.  The invariant behind the triangle is
`a(n, k) = Σ_{i ≤ k} C(k, i) B_{n−i}`: the recurrence is Pascal's rule, and for `k = n` it is
the recurrence of the Bell numbers.

For a prefix the triangle is the natural method, every entry being produced by one addition.

**A single Bell number** (`bellNumber n`) uses Dobinski's formula `Bₙ = e⁻¹ Σ_{k ≥ 0} kⁿ / k!`
in exact arithmetic: with `P = N! Σ_{k ≤ N} kⁿ / k!` and `Q = N! Σ_{k ≤ N} 1 / k!` (both
integers, `N! / k! = N (N−1) ⋯ (k+1)`), `Bₙ = ⌈P / Q⌉ = (P + Q − 1) / Q` once the truncation
`N` is large enough.  The proof of that (`bellNumber_spec`) is purely algebraic: expanding
`kⁿ = Σ_j S(n, j) k (k−1) ⋯ (k−j+1)` with the Stirling numbers of the second kind gives
`Q Bₙ − P = Σ_j S(n, j) Σ_{N−j < m ≤ N} N! / m!`, which lies in `[0, Q)` as soon as
`(N − n + 1)! > n^{n+1}`, using `Bₙ ≤ nⁿ`.  So `N = n + M − 1` with `M` the least integer with
`M! > n^{n+1}` (about `1.15 n`), found by running the factorial up; the `N + 1` terms
`kⁿ · N!/k!` are then accumulated with the quotients `N!/k!` built downward by one small
multiplication each.  The cost is `N` powers, `O(N log n · M(n log n))`, with `O(1)` large
numbers in memory, against the triangle's `n²` additions and `O(n² log n)` bits of memory.

### References

* *Bell triangle*, Wikipedia, <https://en.wikipedia.org/wiki/Bell_triangle> — the array, its
  recurrence and the identity `a(n, k) = Σ_i C(k, i) B_{n−i}`.
* *Bell number*, Wikipedia, <https://en.wikipedia.org/wiki/Bell_number> — the recurrence
  `B_{n+1} = Σ C(n, k) B_k`, `Bₙ = Σ_k S(n, k)`, and Dobinski's formula.
* *Dobinski's formula*, Wikipedia, <https://en.wikipedia.org/wiki/Dobi%C5%84ski%27s_formula>
  — the series and its derivation from `kⁿ = Σ_j S(n, j) k^{(j)}`, which is also the algebraic
  identity behind the truncation bound used here.

No library code was consulted.
-/

namespace Azurite.AzNat

/-- The next row of the Bell triangle: start from the last entry of `r` and add the entries of
`r` one by one (`List.scanl`). -/
def bellRowNext (r : List AzNat) : List AzNat := List.scanl (· + ·) (r[r.length - 1]?.getD 1) r

/-- `k` more rows: push the first entry of the current row, then advance. -/
def bellNumbersPrefix.go : Nat → List AzNat → Array AzNat → Array AzNat
  | 0, _, acc => acc
  | k + 1, r, acc => bellNumbersPrefix.go k (bellRowNext r) (acc.push (r[0]?.getD 1))

/-- **The Bell numbers** `B₀, B₁, …, B_{n−1}`. -/
def bellNumbersPrefix (n : Nat) : List AzNat := (bellNumbersPrefix.go n [1] #[]).toList

/-! ### A single Bell number by Dobinski's formula -/

/-- The least `M` with `M! > bound`, running the factorial up from `M!` (`fuel` steps). -/
def dobinskiTerms.go (bound : AzNat) : Nat → AzNat → Nat → Nat
  | 0, _, M => M
  | fuel + 1, fact, M =>
    if bound < fact then M else dobinskiTerms.go bound fuel (fact * ofNat (M + 1)) (M + 1)

/-- The least `M` with `M! > n^(n+1)`. -/
def dobinskiTerms (n : Nat) : Nat := dobinskiTerms.go ((ofNat n).pow (n + 1)) (2 * n + 2) 1 0

/-- `P = Σ_{i ≤ N} (N − i)ⁿ · N!/(N−i)!` and `Q = Σ_{i ≤ N} N!/(N−i)!`, accumulated for
`i = 0, 1, …` with `F = N!/(N−i)! = N (N−1) ⋯ (N−i+1)`. -/
def dobinskiSums.go (n N : Nat) : Nat → Nat → AzNat → AzNat → AzNat → AzNat × AzNat
  | 0, _, _, P, Q => (P, Q)
  | k + 1, i, F, P, Q =>
    dobinskiSums.go n N k (i + 1) (F * ofNat (N - i)) (P + (ofNat (N - i)).pow n * F) (Q + F)

/-- The pair `(P, Q)` of Dobinski's truncated sums. -/
def dobinskiSums (n N : Nat) : AzNat × AzNat := dobinskiSums.go n N (N + 1) 0 1 0 0

/-- **The Bell number** `Bₙ`, by Dobinski's formula in exact arithmetic. -/
def bellNumber (n : Nat) : AzNat :=
  if n = 0 then 1
  else
    let N := n + dobinskiTerms n - 1
    let PQ := dobinskiSums n N
    (PQ.1 + PQ.2 - 1) / PQ.2

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def B (n : Nat) : List String := (bellNumbersPrefix n).map AzNat.toString

#guard B 0 == []
#guard B 1 == ["1"]
#guard B 6 == ["1", "1", "2", "5", "15", "52"]
#guard B 16 == ["1", "1", "2", "5", "15", "52", "203", "877", "4140", "21147", "115975", "678570",
  "4213597", "27644437", "190899322", "1382958545"]
#guard (B 21).getLast! == "51724158235372"
#guard (B 31).getLast! == "846749014511809332450147"
#guard (B 41).getLast! == "157450588391204931289324344702531067"
#guard (bellNumbersPrefix 500).length == 500
-- the recurrence `B_{n+1} = Σ_{k ≤ n} C(n, k) B_k`
#guard
  let b := (bellNumbersPrefix 80).toArray
  (List.range 79).all fun n =>
    b[n + 1]! == sum ((List.range (n + 1)).map fun k => binomial (ofNat n) k * b[k]!)
-- the single-value function agrees with the prefix
#guard AzNat.toString (bellNumber 0) == "1"
#guard AzNat.toString (bellNumber 1) == "1"
#guard AzNat.toString (bellNumber 5) == "52"
#guard AzNat.toString (bellNumber 20) == "51724158235372"
#guard AzNat.toString (bellNumber 40) == "157450588391204931289324344702531067"
#guard
  let b := (bellNumbersPrefix 120).toArray
  (List.range 120).all fun n => bellNumber n == b[n]!
#guard bellNumber 300 == (bellNumbersPrefix 301).getLast!
#guard dobinskiTerms 1 == 2       -- `2! > 1`
#guard dobinskiTerms 10 == 15     -- `15! > 10^11 > 14!`

end Tests

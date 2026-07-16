/-
  **Algorithm 4.2.7 (the Lucas–Lehmer test)**, Crandall–Pomerance:
  given an odd prime `p`, decide primality of the Mersenne number
  `M_p = 2^p − 1`.

  Set `v = 4` and iterate `v := (v² − 2) mod M_p` exactly `p − 2`
  times; then `M_p` is prime if and only if `v = 0`.  This is the
  computable rail of Theorem 4.2.6
  (`Azurite.CP.theorem_4_2_6`; correctness in
  `Azurite/AzNat/Equiv/LucasLehmerTest.lean`) — the workhorse behind
  every Mersenne-prime record since 1876.

  All arithmetic is limb-level: `AzNat.square` (the fast three-way
  dispatch), addition, and division-with-remainder.  The step is
  computed as `(v² + (M_p − 2)) mod M_p` — congruent to `v² − 2` and
  free of natural-subtraction underflow at `v ≤ 1` — which is also
  the exact recurrence of Mathlib's kernel-friendly
  `LucasLehmer.norm_num_ext.sModNat`, so the correctness bridge is a
  one-line induction.  Reducing modulo `2^p − 1` by shift-and-fold
  instead of general division is a future optimization.
-/
import Azurite.AzNat.Square
import Azurite.AzNat.Div
import Azurite.AzNat.Pow2
import Azurite.AzNat.Equiv.Basic

namespace Azurite

namespace AzNat

/-- The Lucas–Lehmer iteration: starting from `v = 4 mod M`, apply
`v := (v² + s) mod M` a total of `k` times, where the caller passes
`s = M − 2` so that the step is `v² − 2` modulo `M`. -/
def lucasLehmerLoop (M s : AzNat) : ℕ → AzNat
  | 0 => ofNat 4 % M
  | k + 1 => (square (lucasLehmerLoop M s k) + s) % M

/-- **Algorithm 4.2.7 (the Lucas–Lehmer test)**: for an odd prime `p`,
returns `true` exactly when `2^p − 1` is prime
(`lucasLehmerTest_eq_true_iff`). -/
def lucasLehmerTest (p : ℕ) : Bool :=
  let M := pow2 p - 1
  lucasLehmerLoop M (M - ofNat 2) (p - 2) == 0

section Tests

-- the nine Mersenne primes with single- or double-limb `M_p`
#guard lucasLehmerTest 3
#guard lucasLehmerTest 5
#guard lucasLehmerTest 7
#guard lucasLehmerTest 13
#guard lucasLehmerTest 17
#guard lucasLehmerTest 19
#guard lucasLehmerTest 31
#guard lucasLehmerTest 61
#guard lucasLehmerTest 89

-- composite Mersenne numbers with prime exponent are rejected
#guard !lucasLehmerTest 11    -- 2047 = 23 · 89
#guard !lucasLehmerTest 23    -- 8388607 = 47 · 178481
#guard !lucasLehmerTest 29    -- 536870911 = 233 · 1103 · 2089
#guard !lucasLehmerTest 37
#guard !lucasLehmerTest 41
#guard !lucasLehmerTest 43
#guard !lucasLehmerTest 47
#guard !lucasLehmerTest 53
#guard !lucasLehmerTest 59

end Tests

end AzNat

end Azurite

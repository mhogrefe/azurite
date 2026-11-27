/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Gcd
import Azurite.AzNat.Montgomery
import Azurite.AzNat.Parity
import Azurite.AzNat.RhoTwoWord

/-!
# Pollard's rho method with Brent's cycle finding

A divisor finder for `AzNat.factor` (`Azurite/AzNat/Factor.lean`), after R. P. Brent, *An
improved Monte Carlo factorization algorithm*, BIT 20 (1980), 176–184 (algorithm `P₂″` of
§7).  It is a search: nothing is proven about it, and what it returns is checked by its
caller.

The sequence `y ← f(y)`, `f(y) = y² + c mod n`, is eventually periodic modulo every prime
factor `p` of `n`, with tail and period of about `√p` terms.  Brent's cycle finding keeps
`x = y_r` for `r = 1, 2, 4, …` and looks at `gcd(x − y_k, n)` for `3r/2 ≤ k < 2r`: a prime
`p` divides `x − y_k` as soon as the period modulo `p` divides `k − r`.  The differences are
multiplied together modulo `n` and one gcd is taken for every `batch` of them; when that gcd
is `n` itself (all the prime factors arrived in one batch) the batch is gone through again
one term at a time.  The expected cost of finding `p` is about `3.1 √p` multiplications
modulo `n`.

Everything is done in Montgomery form (`MontCtx`): `y ↦ y² R⁻¹ + c` is as good a quadratic
map as `y² + c`, and the factor `R⁻¹` that each product of differences picks up is a unit
modulo `n`, which the gcd does not see.
-/

namespace Azurite.AzNat

/-- `|a − b|`. -/
def absDiff (a b : AzNat) : AzNat := if b ≤ a then a - b else b - a

/-- One term of the sequence: `y² R⁻¹ + c mod n`, for `y, c < n`. -/
def rhoNext (ctx : MontCtx) (n c y : AzNat) : AzNat :=
  let s := ctx.sqr y + c
  if n ≤ s then s - n else s

/-- **Brent's algorithm `P₂″`** for an odd `n`, with the constant `c` and the starting value
`x₀` (both below `n`), `batch` differences per gcd, and at most about `budget` terms of the
sequence.  Returns a divisor `g` of `n` with `1 < g < n` if it finds one, and the number of
terms computed.  `none`: the budget ran out, or every prime factor showed up at the same
term (try another `c`). -/
def rhoBrent (n c x₀ : AzNat) (batch budget : Nat) : Option AzNat × Nat := Id.run do
  let ctx := MontCtx.make n
  let mut y := x₀
  let mut q : AzNat := 1
  let mut r := 1
  let mut used := 0
  for _ in [0:64] do
    if used ≥ budget then return (none, used)
    let x := y
    for _ in [0:r] do
      y := rhoNext ctx n c y
    used := used + r
    let mut k := 0
    let mut g : AzNat := 1
    let mut ys := y
    for _ in [0:r] do
      if k ≥ r || g ≠ 1 then break
      ys := y
      let lim := min batch (r - k)
      for _ in [0:lim] do
        y := rhoNext ctx n c y
        q := ctx.mul q (absDiff x y)
      g := gcd q n
      k := k + lim
      used := used + lim
    if g ≠ 1 then
      if g = n then
        -- the batch again, one term at a time
        g := 1
        for _ in [0:batch + 1] do
          if g ≠ 1 then break
          ys := rhoNext ctx n c ys
          g := gcd (absDiff x ys) n
      return (if g = n || g = 1 then none else some g, used)
    r := 2 * r
  return (none, used)

/-- The number of differences per gcd. -/
def rhoBatch : Nat := 128

/-- **Pollard's rho method**: a divisor of the odd composite `n` strictly between `1` and
`n`, if one is found with `c = 1, 2, …, tries` (and `x₀ = 2`) within `budget` terms of the
sequence each.  Numbers of 64 to 126 bits are done in two machine words
(`TwoWord.rhoBrent`), the others on `AzNat`. -/
def pollardRho (n : AzNat) (tries budget : Nat) : Option AzNat :=
  if n.isEven || n.size ≤ 2 then none
  else if 63 < n.size ∧ n.size ≤ 126 then
    (List.range tries).findSome? fun i =>
      (TwoWord.rhoBrent n (i + 1).toUInt64 rhoBatch budget).1
  else
    (List.range tries).findSome? fun i =>
      (rhoBrent n (ofNat (i + 1)) (ofNat 2) rhoBatch budget).1

end Azurite.AzNat

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

private def N (k : Nat) : AzNat := ofNat k

/-- Does `pollardRho` split `n` (into a divisor strictly between `1` and `n`)? -/
private def splits (n : Nat) : Bool :=
  match pollardRho (N n) 8 1000000 with
  | some d => 1 < d.toNat && d.toNat < n && n % d.toNat == 0
  | none => false

#guard splits (10007 * 10009)
#guard splits (65537 * 4294967311)
#guard splits (1000003 * 1000033)
#guard splits (1000003 * 1000003 * 1000033)
#guard splits ((2 ^ 31 - 1) * (2 ^ 61 - 1))
#guard splits (104729 * (10 ^ 30 + 57))
#guard splits (1000003 * (10 ^ 50 + 151))
-- more than 126 bits: on `AzNat`
#guard splits (1000003 * (10 ^ 40 + 121))
#guard (rhoBrent (N (1000003 * (10 ^ 30 + 57))) (N 1) (N 2) 128 1000000).1.isSome
-- the fifth Fermat number
#guard (pollardRho (N (2 ^ 32 + 1)) 8 1000000).map toNat == some 641
-- nothing to find: primes (the budget runs out), even numbers, numbers below 4
#guard pollardRho (N 1000003) 2 2000 == none
#guard pollardRho (N (2 * 1000003)) 2 2000 == none
#guard pollardRho (N 3) 2 2000 == none && pollardRho (N 1) 2 2000 == none
#guard splits 15 && splits 9 && splits (3 * 1000003)
#guard absDiff (N 3) (N 10) == N 7 && absDiff (N 10) (N 3) == N 7

end Tests

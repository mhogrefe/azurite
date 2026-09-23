/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.TrailingZeros
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Sub
import Azurite.AzNat.Compare
import Azurite.AzNat.Parity
import Azurite.AzNat.ParseBase
import Azurite.AzInt.Add
import Azurite.AzInt.Sub
import Azurite.AzInt.Mul
import Azurite.AzInt.ShiftRight
import Azurite.AzInt.Parity
import Azurite.AzInt.Compare

namespace Azurite.AzInt

open Azurite (AzNat)

/-!
## Extended binary GCD (Bézout coefficients) — limb-level

Computes `gcd(a, b)` together with integer coefficients `s, t` such that
`s·a + t·b = gcd(a, b)` (the coefficients are signed, hence `AzInt`).  Intended
as the engine for modular inversion (`a⁻¹ mod m` from `egcd a m = (1, s, t)` with
`s·a + t·m = 1`, so `a⁻¹ ≡ s (mod m)`).

This is the **binary** extended GCD (HAC Algorithm 14.61), the extended analogue
of the subtractive binary GCD in `AzNat/Gcd.lean`: it uses only shifts (halving),
additions, subtractions and comparisons — **no `/` or `%`**.

The common power of two is factored out first (`k = min (v₂ a) (v₂ b)`), reducing
to `x = a / 2^k`, `y = b / 2^k` (not both even); the loop maintains
`A·x + B·y = u` and `C·x + D·y = v`, halving `u`/`v` to odd and subtracting the
smaller from the larger.  When `u` reaches `0`, `v` is `gcd(x, y)` and `(C, D)` are
its coefficients.  Since `x = a / 2^k`, `y = b / 2^k`, those same `(C, D)` satisfy
`C·a + D·b = 2^k · v = gcd(a, b)`.

The halving of `u` updates `(A, B)` by: if both even, halve directly; otherwise
`A ← (A + y) / 2`, `B ← (B − x) / 2` — both numerators are even (parity of `x`, `y`
and the invariant `A·x + B·y = u` with `u` even force it), and
`(A+y)/2·x + (B−x)/2·y = (A·x + B·y)/2 = u/2`, so the invariant is preserved.
-/

/-- Halve `u` until it is odd, updating Bézout coefficients `(A, B)` for the
reduced inputs `x, y` so that the invariant `A·x + B·y = u` is preserved.
`fuel` bounds the number of halvings (the bit length of `u` is safe). -/
def egcdMakeOdd (x y : AzNat) (fuel : Nat) (u : AzNat) (A B : AzInt) :
    AzNat × AzInt × AzInt :=
  match fuel with
  | 0 => (u, A, B)
  | fuel + 1 =>
    if u.isEven && !(u.limbs.size == 0) then
      let u' := u >>> 1
      let AB : AzInt × AzInt :=
        if A.isEven && B.isEven then (A >>> 1, B >>> 1)
        else ((A + AzInt.mkNorm true y) >>> 1, (B - AzInt.mkNorm true x) >>> 1)
      egcdMakeOdd x y fuel u' AB.1 AB.2
    else (u, A, B)

/-- The subtractive main loop.  Invariants: `A·x + B·y = u`, `C·x + D·y = v`.
Each iteration makes both `u` and `v` odd, then replaces the larger by the
difference (which becomes even, to be halved next iteration).  Terminates when
`u = 0`, returning `(v, C, D)` = `(gcd(x, y), coefficients of v)`. -/
def egcdLoop (x y : AzNat) (innerFuel : Nat) (fuel : Nat)
    (u v : AzNat) (A B C D : AzInt) : AzNat × AzInt × AzInt :=
  match fuel with
  | 0 => (v, C, D)
  | fuel + 1 =>
    let su := egcdMakeOdd x y innerFuel u A B
    let u := su.1; let A := su.2.1; let B := su.2.2
    let sv := egcdMakeOdd x y innerFuel v C D
    let v := sv.1; let C := sv.2.1; let D := sv.2.2
    if AzNat.compare u v = Ordering.lt then
      -- v ← v − u, C ← C − A, D ← D − B
      egcdLoop x y innerFuel fuel u (v - u) A B (C - A) (D - B)
    else
      -- u ≥ v: u ← u − v, A ← A − C, B ← B − D
      let u' := u - v
      if u'.limbs.size == 0 then (v, C, D)
      else egcdLoop x y innerFuel fuel u' v (A - C) (B - D) C D

/-- **Extended binary GCD.**  Returns `(g, s, t)` where `g = gcd(a, b)` and
`s·a + t·b = g` over `ℤ` (with `s, t : AzInt`). -/
def egcd (a b : AzNat) : AzNat × AzInt × AzInt :=
  if a.limbs.size = 0 then (b, 0, 1)        -- 0·a + 1·b = b
  else if b.limbs.size = 0 then (a, 1, 0)   -- 1·a + 0·b = a
  else
    let k := min ((a.trailingZeros).getD 0) ((b.trailingZeros).getD 0)
    let x := a >>> k
    let y := b >>> k
    let fuel := 128 * (a.limbs.size + b.limbs.size) + 64
    let r := egcdLoop x y fuel fuel x y 1 0 0 1
    (r.1 <<< k, r.2.1, r.2.2)

end Azurite.AzInt

/-! ### Tests -/

section Tests

open Azurite Azurite.AzInt

/-- Parse a decimal string into an `AzNat` (exercises the real parse path;
works for any size). -/
private def parse (s : String) : AzNat := (AzNat.parse s).get!

/-- Bézout check: with `egcd a b = (g, s, t)`, verify `g = gcd` and
`s·a + t·b = g` using the computable `AzInt` arithmetic. -/
private def bezoutOk (a b g : AzNat) : Bool :=
  let r := egcd a b
  let s := r.2.1
  let t := r.2.2
  (r.1 == g) &&
    (AzInt.compare (s * AzInt.mkNorm true a + t * AzInt.mkNorm true b)
      (AzInt.mkNorm true g) == Ordering.eq)

-- gcd value + Bézout identity together
#guard bezoutOk (parse "0") (parse "0") (parse "0")
#guard bezoutOk (parse "0") (parse "7") (parse "7")
#guard bezoutOk (parse "7") (parse "0") (parse "7")
#guard bezoutOk (parse "1") (parse "1") (parse "1")
#guard bezoutOk (parse "6") (parse "4") (parse "2")
#guard bezoutOk (parse "12") (parse "8") (parse "4")
#guard bezoutOk (parse "54") (parse "24") (parse "6")
#guard bezoutOk (parse "48") (parse "18") (parse "6")
#guard bezoutOk (parse "100") (parse "75") (parse "25")
#guard bezoutOk (parse "17") (parse "13") (parse "1")
#guard bezoutOk (parse "1024") (parse "512") (parse "512")
#guard bezoutOk (parse "255") (parse "85") (parse "85")
#guard bezoutOk (parse "10000") (parse "2500") (parse "2500")
-- Coprime: coefficients give a Bézout identity for 1 (the modular-inverse case)
#guard bezoutOk (parse "7") (parse "15") (parse "1")
#guard bezoutOk (parse "9") (parse "4") (parse "1")
#guard bezoutOk (parse "35") (parse "64") (parse "1")
-- Powers of two: 2^128 vs 2^64 (gcd 2^64)
#guard bezoutOk (parse "340282366920938463463374607431768211456")
  (parse "18446744073709551616") (parse "18446744073709551616")
-- Multi-limb: 2^128−1 vs 2^64−1 (gcd 2^64−1)
#guard bezoutOk (parse "340282366920938463463374607431768211455")
  (parse "18446744073709551615") (parse "18446744073709551615")
-- 2^256·3·7 vs 2^256·5·7 (gcd 2^256·7)
#guard bezoutOk
  (parse "2431633873983640103894990685182446064918669677978451844828609264166175722438656")
  (parse "4052723123306066839824984475304076774864449463297419741381015440276959537397760")
  (parse "810544624661213367964996895060815354972889892659483948276203088055391907479552")
-- 2^128+1 vs 2^128−1 (coprime)
#guard bezoutOk (parse "340282366920938463463374607431768211457")
  (parse "340282366920938463463374607431768211455") (parse "1")

end Tests

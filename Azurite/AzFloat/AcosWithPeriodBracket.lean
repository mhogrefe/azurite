/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosRatBracket
import Azurite.AzFloat.AsinRatWithPeriodBracket
import Azurite.AzFloat.Atan2WithPeriodBracket

/-!
## The bracket of `arccos (x) u / (2π)`

The arccosine measured in `u`ths of a turn, `ψ = arccos (x) u / (2π) ∈ (0, u/2)` for
`0 < |x| < 1`.  With `a = |x|`, `S_s = arcsin (a) u / (2π)` and `S_c = arccos (a) u / (2π)`:

| | `a ≤ 1/2` (`small`) | `a > 1/2` |
|---|---|---|
| `x > 0` | `ψ = u/4 − S_s` | `ψ = S_c` |
| `x < 0` | `ψ = u/4 + S_s` | `ψ = u/2 − S_c` |

The quarter and half turns are **exact** floats (`turnShift`), and each of `S_s`, `S_c` is used
where it is small and relatively accurate: for a tiny `x` the value is within `2^(−|e|)` of the
float `u/4`, and next to `−1` it approaches `u/2`.  `acosPeriodOrientOf` is the orientation of
the Ziv loop (as in `AzFloat/Atan2WithPeriodBracket.lean`): the loop runs on the negative value
except for `ψ = u/4 + S_s`, so that an end of the enclosure that is an exact float is always
the lower one.

`acosPeriodOf` is the generic combination over three (lazy) enclosures of `arcsin a` and
`arccos a`; `acosPeriodBracket` is the instance for a float and `acosRatPeriodBracket` the one
for a rational.

The proofs are in `Equiv/AcosWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bracket of `arccos (± a) u / (2π)` (`xpos`: the sign is `+`) from enclosures `As8` of
`arcsin a` at level `w + 8`, `Acw` and `Ac8` of `arccos a` at levels `w` and `w + 8`; `small`
selects the arcsine form.  The enclosures are thunks: only one is computed. -/
def acosPeriodOf (small xpos : Bool) (As8 Acw Ac8 : Unit → Encl) (u : AzNat) (w : Nat) : Encl :=
  let V := w + 72
  if small then
    turnShift (ofAzNat u <<< AzInt.ofInt (-2)) (!xpos) (atanPeriodScale (As8 ()) u V) V
  else if xpos then atanPeriodScale (Acw ()) u (w + 64)
  else turnShift (ofAzNat u <<< AzInt.ofInt (-1)) false (atanPeriodScale (Ac8 ()) u V) V

/-- The orientation of the Ziv loop: `true` when it runs on the negative value. -/
def acosPeriodOrientOf (small xpos : Bool) : Bool := xpos || !small

/-- The bracket of `arccos (x) u / (2π)` at Ziv level `w` for a finite float `x` with
`0 < |x| < 1` of exponent `ex`; `xpos`: `x > 0`. -/
def acosPeriodBracket (xpos : Bool) (x : AzFloat) (ex : AzInt) (u : AzNat) (w : Nat) : Encl :=
  acosPeriodOf (le x.abs (one <<< AzInt.ofInt (-1))) xpos (fun _ => asinAbsEncl x ex (w + 8))
    (fun _ => acosBracket false x w) (fun _ => acosBracket false x (w + 8)) u w

/-- The bracket of `± arccos (x) u / (2π)` as a pair of `Roundable`s (`o`: the negative
value). -/
def acosPeriodApprox (o xpos : Bool) (x : AzFloat) (ex : AzInt) (u : AzNat) (w : Nat) :
    Roundable × Roundable :=
  enclApprox o (acosPeriodBracket xpos x ex u w)

/-- `|q| ≤ 1/2` for a rational, decided on `|q| + |q|`. -/
def ratAbsLeHalf (q : AzRat) : Bool := decide ((q.abs + q.abs).num ≤ (q.abs + q.abs).den)

/-- The bracket of `arccos (q) u / (2π)` at Ziv level `w` for a rational `0 < |q| < 1`. -/
def acosRatPeriodBracket (q : AzRat) (u : AzNat) (w : Nat) : Encl :=
  acosPeriodOf (ratAbsLeHalf q) q.sign (fun _ => asinRatAbsEncl q (w + 8))
    (fun _ => acosRatBracket false q w) (fun _ => acosRatBracket false q (w + 8)) u w

/-- The bracket of `± arccos (q) u / (2π)` as a pair of `Roundable`s (`o`: the negative
value). -/
def acosRatPeriodApprox (o : Bool) (q : AzRat) (u : AzNat) (w : Nat) : Roundable × Roundable :=
  enclApprox o (acosRatPeriodBracket q u w)

end Azurite.AzFloat

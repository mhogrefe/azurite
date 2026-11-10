/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.RatPowRatBracket
import Azurite.AzFloat.RatPow

/-!
## `q^r` for rationals `q` and `r`

`ratPowRatPrecRound q r p mode` is `q^r` for `AzRat`s `q` and `r`, correctly rounded to precision
`p` in `mode`, with the comparison against the exact value; `ratPowRat q r p` rounds to nearest.
The structure combines `ratPowPrecRound` (rational base) and `powRatPrecRound` (rational
exponent), with `q = ±a/b` and `r = ±N/D` in lowest terms:

* **Integer exponents** (`D = 1`): `ratPowIntOrZiv` with `n = ±N` — the exact `(a/b)^n` through
  one correctly rounded division when `ratPowIntCheap` allows, Ziv's loop on `exp (n ln (a/b))`
  otherwise, with the sign `(−1)^n` for `q < 0`.
* **Non-integer exponents** (`D ≥ 2`), `q > 0`: `ratPowRatExact?` decides whether `q^r` is
  rational — exactly when `a` and `b` are both `D`-th powers (`natRootD?`) — and gives
  `q^r = (u/v)^(±N)`, handled as an integer power; otherwise `q^r` is irrational
  (`irrational_div_rpow_of_not_pow_gen`) and Ziv's loop on `ratPowRatApprox` (the bracket of
  `exp (r ln q)` from the floats below `q` and `r`) is certified.  `q < 0` gives `NaN`.
* **Special values** as for `powPrecRound`: `q^0 = 1`; `0^r = 0` for `r > 0`, `+∞` for `r < 0`;
  `1^r = 1`; `(−1)^n = ±1` by the parity of an integer `n`.  The specification
  `ratPowRatPrecRound_eq` is in `Equiv/RatPowRat.lean`:
  `roundVal p mode (Spec.pow (some q) (some r))`.
-/

namespace Azurite.AzFloat

/-- `q^r` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or an infinity). -/
def ratPowRatPrecRound (q r : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hr0 : r.num = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
  else if hq0 : q.num = 0 then (if r.sign then (zero, .eq) else (infinity true, .eq))
  else if hp : p = 0 then (nan, .eq)
  else if q.sign ∧ q.num = q.den then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
    if hd : r.den = 1 then
      ratPowIntOrZiv (!q.sign && (AzInt.mkNorm r.sign r.num).abs.isOdd) q.num q.den hq0 q.den_nz
        hcop (AzInt.mkNorm r.sign r.num) (mkNorm_ne_zero hr0) p mode
    else if hsq : q.sign = false then (nan, .eq)
    else
      have hs : q.sign = true := by revert hsq; cases q.sign <;> simp
      match expNearOne? (r.sign == decide (q.den.toNat < q.num.toNat))
        (nearOneExp (ratTinyExp r) (q.num.size + q.den.size)) p mode with
      | some r' => r'
      | none =>
      match hex : ratPowRatExact? q.num q.den r with
      | some (u, v, N) =>
        have h := ratPowRatExact?_some hq0 q.den_nz hcop r hr0 hex
        ratPowIntOrZiv false u v h.1 h.2.1 h.2.2.1 N
          (fun h0 => h.2.2.2.1 (by rw [h0, AzInt.toInt_zero])) p mode
      | none =>
        zivLoopCertified (ratPowRatApprox false q r) p mode (ratPowRatStart r q p)
          (ratPowRatApprox_isSome_exists p mode false q hs hq0 r
            (by
              simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul]
              rw [coe_toRat_eq_div_pos q hs]
              exact not_mem_floatSet_of_irrational p
                (irrational_of_ratPowRatExact?_none hq0 q.den_nz hcop r hr0 hd hex))
            (ratPowRatStart r q p) (by unfold ratPowRatStart zivGuardBits; omega))

/-- `q^r` rounded to nearest at precision `p`. -/
def ratPowRat (q r : AzRat) (p : Nat) : AzFloat := (ratPowRatPrecRound q r p .Nearest).1

end Azurite.AzFloat

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.AzNat.Compare
import Azurite.AzNat.Conversion
import Azurite.AzNat.Div
import Azurite.AzNat.ModPow2
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Size
import Azurite.AzNat.TrailingZeros
import Mathlib.NumberTheory.Padics.PadicVal.Defs

namespace Azurite.AzNat

/-!
The Jacobi symbol `(a/n)` for odd `n`, by the binary algorithm — Phase A3
of the APR-CL implementation plan (`docs/aprcl_implementation_plan.md`).

  ```
  J(a, n):                      (n odd; J(a, 1) = 1)
    a ← a mod n;  if a = 0 return 0
    write a = 2^t · a' with a' odd
    s ← 1 if t even, else (2/n) = +1 if n ≡ ±1 (mod 8), −1 otherwise
    if a' = 1 return s
    return s · (−1)^[a' ≡ n ≡ 3 (mod 4)] · J(n mod a', a')
  ```

The three ingredients are Mathlib's: `J(2 | n) = χ₈(n)` (`jacobiSym.at_two`),
quadratic reciprocity for odd coprime arguments
(`jacobiSym.quadratic_reciprocity_if`), and reduction of the top argument
(`jacobiSym.mod_left`).  The modulus strictly decreases (`a' ≤ a mod n < n`),
so the ℕ reference `jacobiNat` recurses on it; the `AzNat` port `jacobi`
uses fuel `2^size(n) ≥ n`, never approached.  Correctness against Mathlib's
`jacobiSym` is in `Equiv/JacobiSym.lean`.

Uses in the primality arc: the (4.4)(c2) search for `u` with
`((u² + 4)/n) = −1`, the soundness hypotheses of Test (4.3) and Remark (4.10)
(`CL.not_isSquare_disc`), and the `n ≡ 1 (mod 4)` route of (11.5).
-/

/-- **The Jacobi symbol, ℕ reference** (binary algorithm; `J(a | n)` for
odd `n`, with `J(a | 0) = J(a | 1) = 1` as in Mathlib). -/
def jacobiNat (a n : ℕ) : ℤ :=
  if n ≤ 1 then 1
  else if a % n = 0 then 0
  else
    let t := padicValNat 2 (a % n)
    let a' := a % n / 2 ^ t
    let s : ℤ := if t % 2 = 0 then 1 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1
    if a' = 1 then s
    else s * (if a' % 4 = 3 ∧ n % 4 = 3 then -1 else 1) * jacobiNat (n % a') a'
termination_by n
decreasing_by
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by omega))

/-- **The Jacobi symbol on `AzNat` — the loop** (fuel-bounded mirror of
`jacobiNat`; the `AzNat` operations are `%`, `trailingZeros`, `>>>`, and
the low-bit masks `modPow2`). -/
def jacobi.loop (a n : AzNat) : ℕ → ℤ
  | 0 => 1
  | fuel + 1 =>
    if n ≤ 1 then 1
    else
      let a₁ := a % n
      if a₁ = 0 then 0
      else
        match a₁.trailingZeros with
        | none => 1
        | some t =>
          let a' := a₁ >>> t
          let s : ℤ := if t % 2 = 0 then 1
            else if n.modPow2 3 = ofNat 1 ∨ n.modPow2 3 = ofNat 7 then 1 else -1
          if a' = 1 then s
          else s * (if a'.modPow2 2 = ofNat 3 ∧ n.modPow2 2 = ofNat 3 then -1 else 1)
            * jacobi.loop (n % a') a' fuel

/-- **The Jacobi symbol `(a/n)` on `AzNat`** (for odd `n`). -/
def jacobi (a n : AzNat) : ℤ := jacobi.loop a n ((1 : ℕ) <<< n.size)

-- ℕ reference sanity: Legendre values, `(2/n)`, non-coprime, the classic `(1001/9907) = −1`
#guard jacobiNat 2 7 = 1
#guard jacobiNat 2 3 = -1
#guard jacobiNat 3 7 = -1
#guard jacobiNat 5 103 = -1
#guard jacobiNat 2 101 = -1
#guard jacobiNat 7 1 = 1
#guard jacobiNat 0 9 = 0
#guard jacobiNat 3 9 = 0
#guard jacobiNat 1001 9907 = -1
#guard jacobiNat 19 45 = 1
#guard jacobiNat 8 21 = -1

-- `AzNat` port agrees on the same values
#guard jacobi (ofNat 2) (ofNat 7) = 1
#guard jacobi (ofNat 2) (ofNat 3) = -1
#guard jacobi (ofNat 3) (ofNat 7) = -1
#guard jacobi (ofNat 5) (ofNat 103) = -1
#guard jacobi (ofNat 2) (ofNat 101) = -1
#guard jacobi (ofNat 7) (ofNat 1) = 1
#guard jacobi (ofNat 0) (ofNat 9) = 0
#guard jacobi (ofNat 3) (ofNat 9) = 0
#guard jacobi (ofNat 1001) (ofNat 9907) = -1
#guard jacobi (ofNat 19) (ofNat 45) = 1
#guard jacobi (ofNat 8) (ofNat 21) = -1

end Azurite.AzNat

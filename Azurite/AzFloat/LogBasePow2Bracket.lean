/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2Bracket

/-!
# The brackets of `log_{2^k} x` and `log_{2^k} q`

`divBracketByInt B k w` divides a bracket `B` of some value `L` by a nonzero integer `k`: the
ends are divided by the exact float `|k|` with directed rounding, and negated (and swapped) for
`k < 0`, giving a bracket of `L / k`.  `logBasePow2Approx x e k w` applies it to the bracket of
`log₂ x` (`log2Quotients` of `lnBracket`) for a positive finite float `x` of exponent `e`, and
`logBasePow2RatApprox q k w` to the bracket of `log₂ q` for a positive rational `q`.
-/

namespace Azurite.AzFloat

/-- A bracket of `L / k` from a bracket `B` of `L`, for `k ≠ 0`. -/
def divBracketByInt (B : AzFloat × AzFloat) (k : AzInt) (w : Nat) : Roundable × Roundable :=
  let K := ofAzNat k.abs
  let lo := (divPrecRound B.1 K w .Floor).1
  let hi := (divPrecRound B.2 K w .Ceiling).1
  if k.sign then (fun p mode => setPrecRound lo p mode, fun p mode => setPrecRound hi p mode)
  else (fun p mode => setPrecRound (-hi) p mode, fun p mode => setPrecRound (-lo) p mode)

/-- The bracket of `log_{2^k} x` at working precision `w`. -/
def logBasePow2Approx (x : AzFloat) (e k : AzInt) (w : Nat) : Roundable × Roundable :=
  divBracketByInt (log2Quotients (lnBracket x e w) w) k w

/-- The bracket of `log_{2^k} q` for a positive rational `q` at working precision `w`. -/
def logBasePow2RatApprox (q : AzRat) (k : AzInt) (w : Nat) : Roundable × Roundable :=
  divBracketByInt (log2Quotients (lnFloorBracket (ofAzRatRound q w .Floor).1 w) w) k w

end Azurite.AzFloat

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div.Schoolbook

namespace Azurite.AzNat

/-! ### Constant-folded `divModUInt64 _ 6`

Toom-Cook 3-way multiplication interpolates via a `t1_num / 6` step.
This file specializes `divModUInt64` to that fixed small divisor,
hardcoding:

* the divisor `d = 6`,
* its normalized form `d' = 6 <<< 61 = 0xC000000000000000`,
* the Möller–Granlund reciprocal of `d'`
  (`#eval`'d once from `UInt64.reciprocal d'`),
* the leading-zero shift `k = 61` (so each per-limb step also needs a
  3-bit carry-shift, unlike `divMod10p19`'s `k = 0` fast path).

The recursive inner loop is `divModLimb.go` reused with `k = 61` and
`lo = 0`; the hardcoded constants flow in as parameters, avoiding the
kernel-unfolding hazard from global UInt64 literals inside recursive
bodies (see `feedback_kernel_runaway_global_constants`). -/

/-- Normalized divisor constant: `6 <<< 61 = 0xC000000000000000`.  This is
    the "actual divisor" the inner loop sees after Möller–Granlund
    normalization; the unnormalized constant `6` only appears in the
    single-limb fast path. -/
def divBy6_dNorm : UInt64 := 13835058055282163712

/-- Möller–Granlund reciprocal of `divBy6_dNorm = 6 <<< 61`.  Hardcoded
    literal; the correctness proof in `Equiv/DivBy6.lean` checks this
    against `UInt64.reciprocal divBy6_dNorm`. -/
def divBy6_inv : UInt64 := 6148914691236517205

/-- Divide an `AzNat` by `6`.  Equivalent to `divModUInt64 U 6 (by decide)`,
    but with all constants folded in.  Multi-limb case feeds the top
    limb's high `3` bits as the initial running remainder, runs the
    `k = 61, lo = 0` specialization of `divModLimb.go`, and shifts the
    final remainder right by `61` to recover the actual remainder mod `6`. -/
def divBy6 (U : AzNat) : AzNat × UInt64 :=
  if _h0 : U.limbs.size = 0 then (0, 0)
  else if h1 : U.limbs.size = 1 then
    have h_pos : 0 < U.limbs.size := h1 ▸ Nat.one_pos
    let qr := UInt64.divMod (U.limbs[0]'h_pos) 6
    (ofLimbs #[qr.1], qr.2)
  else
    have h_top : U.limbs.size - 1 < U.limbs.size := by omega
    let r0 := (U.limbs[U.limbs.size - 1]'h_top) >>> (3 : UInt64)
    let res := divModLimb.go divBy6_dNorm divBy6_inv 61 (by omega)
      U.limbs 0 U.limbs.size r0 (by omega)
    (ofLimbs res.1, res.2 >>> (61 : UInt64))

end Azurite.AzNat

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Basic

/-!
# Tests for Newton–Barrett division

`divModNewton base fftFrom U V` is compared with `Nat` division; `base = 2` forces the Newton recursion
down to two-limb reciprocals, so every path (the reciprocal recursion, its correction loop, the
Barrett corrections, the block loop with and without a partial top block, the normalization
shift) runs even on small inputs; `fftFrom = 0` (`chkF`) forces the FFT-range tricks on as well.  The
last test crosses `divNewtonThreshold` so the dispatcher
itself takes the Newton path.
-/

namespace Azurite.AzNat

private def chk (base : Nat) (u v : Nat) : Bool :=
  let r := divModNewton base 999999 32 (ofNat u) (ofNat v)
  r.1.toNat == u / v && r.2.toNat == u % v

/-- The FFT-range path (wrap-around product, cached transforms, modular remainder) forced on. -/
private def chkF (base : Nat) (u v : Nat) : Bool :=
  let r := divModNewton base 0 32 (ofNat u) (ofNat v)
  r.1.toNat == u / v && r.2.toNat == u % v

#guard chk 2 (2 ^ 640 + 12345) (2 ^ 320 + 1)
#guard chk 2 (2 ^ 1280 + 999) (2 ^ 640 + 17)
#guard chk 2 (2 ^ 2048 - 1) (2 ^ 512 + 7)
#guard chk 2 (3 ^ 1000) (7 ^ 100)
#guard chk 2 (2 ^ 5000 + 1) (2 ^ 4999 + 12345678901234567)
#guard chk 2 (2 ^ 5000 + 1) (2 ^ 4096 + 1)
#guard chk 3 (2 ^ 20000 + 5) (2 ^ 3001 - 1)
#guard chk 2 (2 ^ 999) (2 ^ 1000 + 1)
#guard chk 2 (2 ^ 1000 + 1) (2 ^ 1000 + 1)
#guard chk 2 (2 ^ 1023 + 2 ^ 500) (2 ^ 1023)
#guard chk 2 (2 ^ 130 - 1) (2 ^ 65 - 1)
#guard chk 2 (2 ^ 64 * 3) (2 ^ 64)
#guard chk 2 (7 ^ 2000 + 11 ^ 500) (13 ^ 300 + 1)
#guard chk 2 (2 ^ (64 * 17) + 3) (2 ^ (64 * 5) + 2 ^ (64 * 3) + 9)
#guard chk 2 (2 ^ (64 * 18) - 1) (2 ^ (64 * 6) - 1)
#guard (divModNewton 2 999999 32 (ofNat 100) 0) == (0, ofNat 100)

/-- Short products with a tiny base case, so that Mulders' recursion runs on small inputs. -/
private def chkS (u v : Nat) : Bool :=
  let r := divModNewton 2 999999 4 (ofNat u) (ofNat v)
  r.1.toNat == u / v && r.2.toNat == u % v

#guard chkS (2 ^ 640 + 12345) (2 ^ 320 + 1)
#guard chkS (2 ^ 2048 - 1) (2 ^ 512 + 7)
#guard chkS (3 ^ 1000) (7 ^ 100)
#guard chkS (2 ^ 5000 + 1) (2 ^ 4999 + 12345678901234567)
#guard chkS (2 ^ 20000 + 5) (2 ^ 3001 - 1)
#guard chkS (2 ^ 1023 + 2 ^ 500) (2 ^ 1023)
#guard chkS (7 ^ 2000 + 11 ^ 500) (13 ^ 300 + 1)
#guard chkS (2 ^ (64 * 40) - 1) (2 ^ (64 * 9) - 1)

#guard chkF 2 (2 ^ 640 + 12345) (2 ^ 320 + 1)
#guard chkF 2 (2 ^ 2048 - 1) (2 ^ 512 + 7)
#guard chkF 2 (3 ^ 1000) (7 ^ 100)
#guard chkF 2 (2 ^ 5000 + 1) (2 ^ 4999 + 12345678901234567)
#guard chkF 3 (2 ^ 20000 + 5) (2 ^ 3001 - 1)
#guard chkF 2 (2 ^ 1023 + 2 ^ 500) (2 ^ 1023)
#guard chkF 2 (2 ^ 130 - 1) (2 ^ 65 - 1)
#guard chkF 2 (7 ^ 2000 + 11 ^ 500) (13 ^ 300 + 1)
#guard chkF 2 (2 ^ (64 * 18) - 1) (2 ^ (64 * 6) - 1)
#guard chkF 4 (5 ^ 3000 + 1) (3 ^ 1500 + 2)

-- Through the dispatcher: a divisor of 4100 limbs and a dividend of 17000 limbs take the Newton
-- path with the FFT-range tricks (`useNewtonDiv`, `newtonFFTThreshold`).
#guard useNewtonDiv (ofNat (2 ^ (64 * 17000) + 3)) (ofNat (2 ^ (64 * 4100) + 5)) = true
#guard useNewtonDiv (ofNat (2 ^ (64 * 9000) + 3)) (ofNat (2 ^ (64 * 4100) + 5)) = false
-- Below the FFT range the dispatcher takes the Newton path with short products for an 8× dividend.
#guard useNewtonDiv (ofNat (2 ^ (64 * 9000) + 3)) (ofNat (2 ^ (64 * 1100) + 5)) = true
#guard (ofNat (2 ^ (64 * 9000) + 3) / ofNat (2 ^ (64 * 1100) + 5)).toNat
  = (2 ^ (64 * 9000) + 3) / (2 ^ (64 * 1100) + 5)
#guard (ofNat (2 ^ (64 * 17000) + 3) / ofNat (2 ^ (64 * 4100) + 5)).toNat
  = (2 ^ (64 * 17000) + 3) / (2 ^ (64 * 4100) + 5)
#guard (ofNat (2 ^ (64 * 17000) + 3) % ofNat (2 ^ (64 * 4100) + 5)).toNat
  = (2 ^ (64 * 17000) + 3) % (2 ^ (64 * 4100) + 5)

end Azurite.AzNat

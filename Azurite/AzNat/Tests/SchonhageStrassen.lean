/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul
import Azurite.AzNat.Square
import Azurite.AzNat.Div
import Azurite.AzNat.ParseBase

/-!
# Tests for the Fermat ring and the Schönhage–Strassen multiplication
-/

open Azurite Azurite.AzNat Azurite.AzFermat

private def P (s : String) : AzNat := (AzNat.parse s).get!
private def big (n : Nat) : AzNat := P (String.ofList (List.replicate n '7'))   -- n digits of 7

/-! ## `AzFermat 64`: residues modulo `2^64 + 1` -/

private def F (s : String) : AzFermat 64 := ofAzNat 64 (P s)
-- `2^64 ≡ −1`, so `2^64 + 5 ≡ 4`
#guard (F "18446744073709551621").val == P "4"
-- `(2^64 − 1) + 2 = 2^64 + 1 ≡ 0`
#guard (F "18446744073709551615" + F "2").val == 0
-- `3 − 5 ≡ 2^64 + 1 − 2 = 2^64 − 1`
#guard (F "3" - F "5").val == P "18446744073709551615"
-- `2^63 · 2^3 = 2^66 = 4 · 2^64 ≡ −4 ≡ 2^64 − 3`
#guard (mulPow2 3 (F "9223372036854775808")).val == P "18446744073709551613"
-- `2^{−3} · 2^3 = 1`
#guard (mulPow2 3 (divPow2 3 (F "12345"))).val == P "12345"
-- `mulPow2` with an exponent beyond `2N` wraps: `2^{130} = 2^{128} · 4 ≡ 4`
#guard (mulPow2 130 (F "1")).val == P "4"
-- a product reduced: `(2^64) · (2^64) ≡ 1`
#guard (mulWith (fun x y => x * y) (F "18446744073709551616") (F "18446744073709551616")).val == 1

/-! ## `fftMul` and `fftSquare` with the Toom ladder for the pointwise products -/

private def th : MulThresholds := { schoolbook := 2, toomCook3 := 3, toomCook4 := 4, unbalanced := 2 }
private def fm (a b : AzNat) : AzNat := fftMul (toomLadderMul th) a b
private def fs (a : AzNat) : AzNat := fftSquare (toomSquareLadder 2 3 4) a

#guard fm (big 20) (big 20) == big 20 * big 20
#guard fm (big 300) (big 150) == big 300 * big 150
#guard fm (big 1000) (big 999) == big 1000 * big 999
#guard fm (big 5000) (big 5000) == big 5000 * big 5000
#guard fm (big 300) 0 == 0
#guard fm 0 (big 300) == 0
#guard fm 1 (big 300) == big 300
#guard fs (big 20) == big 20 * big 20
#guard fs (big 1000) == big 1000 * big 1000
#guard fs (big 5000) == big 5000 * big 5000
#guard fs 0 == 0

-- explicit small parameters: `K = 2` digits of one limb (`k = 0`, `w = 1`), the case `n < N`
#guard fftMulMod 0 1 (by decide) (toomLadderMul th) (P "18446744073709551615") (P "18446744073709551615")
  == P "340282366920938463426481119284349108225" % (AzNat.pow2 128 + 1)
-- `K = 4` digits of two limbs
#guard fftMulMod 1 2 (by decide) (toomLadderMul th) (big 150) (big 150)
  == (big 150 * big 150) % (AzNat.pow2 512 + 1)

/-! ## The dispatchers with the FFT branch forced -/

private def thf : MulThresholds :=
  { schoolbook := 2, toomCook3 := 3, toomCook4 := 4, unbalanced := 2, fft := 8 }
private def dm (a b : AzNat) : AzNat :=
  ofLimbs (mulLimbsWith thf a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size (by simp) (by simp))
#guard dm (big 300) (big 300) == big 300 * big 300
#guard dm (big 2000) (big 1999) == big 2000 * big 1999
#guard dm (big 2000) (big 700) == big 2000 * big 700
private def ds (a : AzNat) : AzNat := squareDispatchParam 2 3 4 8 a
#guard ds (big 300) == big 300 * big 300
#guard ds (big 2000) == big 2000 * big 2000

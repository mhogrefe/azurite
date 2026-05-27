import Azurite.AzNat.DivRecursiveLimbs
import Azurite.AzNat.ParseBase

namespace Azurite.AzNat

private def show2 (qr : AzNat × UInt64) : Nat × Nat :=
  (qr.1.toNat, qr.2.toNat)

-- 2^64 = 18446744073709551616. Multi-limb dividends.

-- 2^64 / 3 = 6148914691236517205 r 1
#guard show2 (divModUInt64 (AzNat.parse "18446744073709551616").get! 3 (by decide))
  = (6148914691236517205, 1)

-- 2^65 / 7 = 5270498306774157604 r 4
#guard show2 (divModUInt64 (AzNat.parse "36893488147419103232").get! 7 (by decide))
  = (5270498306774157604, 4)

-- (2^64 + 12345) / 1000000 = 18446744073709 r 563951
#guard show2 (divModUInt64 (AzNat.parse "18446744073709563961").get! 1000000 (by decide))
  = (18446744073709, 563961)

-- 2^128 / 2 = 2^127 = 170141183460469231731687303715884105728
#guard show2 (divModUInt64 (AzNat.parse "340282366920938463463374607431768211456").get! 2 (by decide))
  = (170141183460469231731687303715884105728, 0)

-- 10^20 / 7 = 14285714285714285714 r 2
#guard show2 (divModUInt64 (AzNat.parse "100000000000000000000").get! 7 (by decide))
  = (14285714285714285714, 2)

-- 10^25 / (10^9 - 1) = 10^16 + 10^7 r 10^7
#guard show2 (divModUInt64 (AzNat.parse "10000000000000000000000000").get! 999999999 (by decide))
  = (10000000010000000, 10000000)

-- Edge case: dividend much bigger, divisor = 1.
-- 2^100 / 1 = 2^100, remainder = 0
#guard show2 (divModUInt64 (AzNat.parse "1267650600228229401496703205376").get! 1 (by decide))
  = (1267650600228229401496703205376, 0)

private def showQR (qr : AzNat × AzNat) : Nat × Nat :=
  (qr.1.toNat, qr.2.toNat)

-- 1-limb divisor (delegates to divModUInt64).
#guard showQR (divMod (AzNat.parse "100").get! (AzNat.parse "7").get!) = (14, 2)
#guard showQR (divMod (AzNat.parse "18446744073709551616").get! (AzNat.parse "3").get!) =
  (6148914691236517205, 1)

-- Division by zero convention.
#guard showQR (divMod (AzNat.parse "42").get! (AzNat.parse "0").get!) = (0, 42)

-- Divisor larger than dividend.
#guard showQR (divMod (AzNat.parse "5").get! (AzNat.parse "18446744073709551616").get!) =
  (0, 5)

-- 2-limb divisor (uses divModLimb2 with normalization).
-- 2^128 / (2^64 + 1) = 2^64 - 1 r 1, since (2^64-1)(2^64+1) = 2^128 - 1.
#guard showQR
    (divMod (AzNat.parse "340282366920938463463374607431768211456").get!
            (AzNat.parse "18446744073709551617").get!) =
  (18446744073709551615, 1)

-- (2^64)^2 / (2^64 - 1) — both 2-limb.
-- 2^128 = (2^64-1)(2^64+1) + 1, so 2^128 / (2^64-1) = 2^64 + 1, r = 1.
#guard showQR
    (divMod (AzNat.parse "340282366920938463463374607431768211456").get!
            (AzNat.parse "18446744073709551615").get!) =
  (18446744073709551617, 1)

-- 3-limb divisor (uses schoolbookDivModLimbs).
-- 2^192 / (2^128 + 1) = 2^64 - 1, r = 2^128 - 2^64 + 1.
#guard showQR
    (divMod
      (AzNat.parse "6277101735386680763835789423207666416102355444464034512896").get!
      (AzNat.parse "340282366920938463463374607431768211457").get!) =
  (18446744073709551615, 340282366920938463444927863358058659841)

-- Division by 1 — n-limb dividend, n-limb quotient, zero remainder.
#guard showQR (divMod (AzNat.parse "12345678901234567890").get! (AzNat.parse "1").get!) =
  (12345678901234567890, 0)

-- Equal dividend and divisor.
#guard showQR (divMod (AzNat.parse "999999999999999999999999999999").get!
                       (AzNat.parse "999999999999999999999999999999").get!) =
  (1, 0)

end Azurite.AzNat

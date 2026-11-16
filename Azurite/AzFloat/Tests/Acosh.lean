/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acosh
import Azurite.AzFloat.Ln
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acosh x`

The special values (`NaN`; `NaN` below `1`, including `0`, negative arguments and `−∞`;
`+∞`; `acosh 1 = 0`; `p = 0`), the correctly rounded 53-bit values from `1 + 2^(−52)` to
`2^100` in three modes — among them `1 + 2^(−51)`, where the value is within a relative
`2^(−54)` of the float `2^(−25)` — 1-, 2-, 20-, 113-, 120- and 200-bit results, a 201-bit
argument `1 + 2^(−200)`, 200-bit strings, and huge arguments `2^(2^30)` (where `acosh x`
rounds like `ln (2x)`).  References: an independent 6000-bit fixed-point evaluation of
`ln (x + √(x² − 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acoshPrecRound x p m
/-- `1 + 2^(−200)` at 201 bits. -/
private def x200 : AzFloat := (addPrecRound (F "1" 53) (h (F "1" 53) (-200)) 201 .Floor).1

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (infinity true, .eq)
#guard A (infinity true) 0 == (infinity true, .eq)
#guard A (infinity false) 53 == (nan, .eq)
#guard A zero 53 == (nan, .eq)
#guard A (F "1/2" 53) 53 == (nan, .eq)
#guard A (F "9007199254740991/9007199254740992" 53) 53 == (nan, .eq)
#guard A (F "-1" 53) 53 == (nan, .eq)
#guard A (F "-3" 53) 53 == (nan, .eq)
#guard A (h (F "1" 53) (-1000)) 53 == (nan, .eq)
#guard A (F "1" 53) 53 == (zero, .eq)
#guard A (F "1" 200) 1 .Floor == (zero, .eq)
#guard A (F "1" 53) 0 == (zero, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "2" 53) 53 == (F "5931051093853237/4503599627370496" 53, .gt)
#guard A (F "3/2" 53) 53 == (F "4334370792049413/4503599627370496" 53, .gt)
#guard A (F "5/4" 53) 53 == (F "6243314768165359/9007199254740992" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "8160300771249005/4503599627370496" 53, .gt)
#guard A (F "10" 53) 53 == (F "1685034661806453/562949953421312" 53, .lt)
#guard A (F "100" 53) 53 == (F "5965346880865831/1125899906842624" 53, .gt)
#guard A (F "1000000000000" 53) 53 == (F "498284038225175/17592186044416" 53, .gt)
#guard A (F "700" 53) 53 == (F "4078137255262709/562949953421312" 53, .gt)
#guard A (F "4503599627370497/4503599627370496" 53) 53
  == (F "1592262918131443/75557863725914323419136" 53, .lt)
#guard A (F "2251799813685249/2251799813685248" 53) 53 == (F "1/33554432" 53, .gt)
#guard A (F "1048577/1048576" 53) 53 == (F "6369051166359131/4611686018427387904" 53, .lt)
#guard A (F "9007199254740991/4503599627370496" 53) 53
  == (F "1482762773463309/1125899906842624" 53, .lt)
#guard A (F "1267650600228229401496703205376" 53) 53
  == (F "4926365559255479/70368744177664" 53, .gt)
#guard A (F "2" 53) 53 .Floor == (F "1482762773463309/1125899906842624" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "8668741584098825/9007199254740992" 53, .lt)
#guard A (F "4503599627370497/4503599627370496" 53) 53 .Floor
  == (F "1592262918131443/75557863725914323419136" 53, .lt)
#guard A (F "2251799813685249/2251799813685248" 53) 53 .Floor
  == (F "9007199254740991/302231454903657293676544" 53, .lt)
#guard A (F "100" 53) 53 .Floor == (F "2982673440432915/562949953421312" 53, .lt)
#guard A (F "2" 53) 53 .Ceiling == (F "5931051093853237/4503599627370496" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "4334370792049413/4503599627370496" 53, .gt)
#guard A (F "4503599627370497/4503599627370496" 53) 53 .Ceiling
  == (F "6369051672525773/302231454903657293676544" 53, .gt)
#guard A (F "2251799813685249/2251799813685248" 53) 53 .Ceiling == (F "1/33554432" 53, .gt)
#guard A (F "100" 53) 53 .Ceiling == (F "5965346880865831/1125899906842624" 53, .gt)
#guard A (F "2" 53) 20 == (F "690465/524288" 20, .lt)
#guard A (F "2" 53) 1 == (F "1" 1, .lt)
#guard A (F "3/2" 53) 2 == (F "1" 2, .gt)
#guard A (F "3/2" 53) 113
  == (F "9994378590187160089544165381728455/10384593717069655257060992658440192" 113, .lt)
#guard A (F "4/3" 200) 200
  == (h (F "159762877341286584990001853615392401845879581658605860638835" 200) (-197), .lt)
#guard A (F "4/3" 200) 10 .Floor == (F "407/512" 10, .lt)
#guard A (F "10" 53) 120
  == (F "994668901173547730150415254073001523/332306998946228968225951765070086144" 120, .lt)
#guard A x200 53 == (F "6369051672525773/5708990770823839524233143877797980545530986496" 53, .gt)
#guard A x200 53 .Floor
  == (F "1592262918131443/1427247692705959881058285969449495136382746624" 53, .lt)
#guard A x200 53 .Ceiling
  == (F "6369051672525773/5708990770823839524233143877797980545530986496" 53, .gt)
#guard acosh (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (acoshPrecRound (F "2" 200) 200 .Nearest).1).startsWith
  "1.316957896924816708625046347307968444026981971467516479"
#guard (toString (acoshPrecRound (F "3/2" 200) 200 .Nearest).1).startsWith
  "0.962423650119206894995517826848736846270368668771321039"

-- huge arguments: `acosh x` rounds like `ln (2x)`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  A x p m == lnPrecRound (h x 1) p m
#guard big (h (F "1" 53) 1073741824) 53 .Nearest && big (h (F "3" 53) 1073741824) 53 .Floor
#guard big (h (F "5" 53) 100000) 113 .Ceiling

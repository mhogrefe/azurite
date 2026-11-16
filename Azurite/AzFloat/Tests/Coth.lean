/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Coth
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `coth x`

The special values (`NaN`, `±∞ ↦ ±1`, `coth 0 = +∞`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `700` in three modes, the transition to `±1` (`18` to `40`), 1-, 2-,
20-, 113-, 120- and 200-bit results, 200-bit strings, oddness, tiny arguments `±2^(−1000)`,
`±2^(−2^30)` (the value is just outside `1/x`, at no cost), and large arguments `±1000`,
`±2^20`, `±2^(2^30)` (the value is just outside `±1`, at no cost).  References: an independent
6000-bit fixed-point evaluation of `(e^(2x) + 1)/(e^(2x) − 1)` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cothPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (F "1" 53, .eq)
#guard A (infinity false) 53 == (F "-1" 53, .eq)
#guard A (infinity false) 1 .Floor == (F "-1" 1, .eq)
#guard A (infinity true) 0 == (nan, .eq)
#guard A zero 53 == (infinity true, .eq)
#guard A zero 0 == (infinity true, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "5913385222499101/4503599627370496" 53, .lt)
#guard A (F "-1" 53) 53 == (F "-5913385222499101/4503599627370496" 53, .gt)
#guard A (F "2" 53) 53 == (F "1167912547433629/1125899906842624" 53, .gt)
#guard A (F "1/2" 53) 53 == (F "4872789893880255/2251799813685248" 53, .gt)
#guard A (F "-1/3" 53) 53 == (F "-7003765483672909/2251799813685248" 53, .gt)
#guard A (F "3/2" 53) 53 == (F "1243884526439543/1125899906842624" 53, .gt)
#guard A (F "-7/5" 53) 53 == (F "-2543395969564869/2251799813685248" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "2260204441214337/2251799813685248" 53, .gt)
#guard A (F "10" 53) 53 == (F "4503599645935717/4503599627370496" 53, .lt)
#guard A (F "-100" 53) 53 == (F "-1" 53, .gt)
#guard A (F "1/1000" 53) 53 == (F "2199023988559703/2199023255552" 53, .gt)
#guard A (F "-1/1000000000000" 53) 53 == (F "-1000000000000" 53, .gt)
#guard A (F "1/1125899906842624" 53) 53 == (F "1125899906842624" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53
  == (F "1267650600228229401496703205376" 53, .lt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "-535646014752996728779660432739556678793109967729782270459904" 53, .gt)
#guard A (F "30" 53) 53 == (F "1" 53, .lt)
#guard A (F "-37" 53) 53 == (F "-1" 53, .gt)
#guard A (F "700" 53) 53 == (F "1" 53, .lt)
#guard A (F "1" 53) 53 .Floor == (F "5913385222499101/4503599627370496" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "-2956692611249551/2251799813685248" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "4975538105758171/4503599627370496" 53, .lt)
#guard A (F "-7/5" 53) 53 .Floor == (F "-2543395969564869/2251799813685248" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "8796095954238811/8796093022208" 53, .lt)
#guard A (F "-100" 53) 53 .Floor == (F "-4503599627370497/4503599627370496" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "1267650600228229401496703205376" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "2956692611249551/2251799813685248" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "-5913385222499101/4503599627370496" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "1243884526439543/1125899906842624" 53, .gt)
#guard A (F "-7/5" 53) 53 .Ceiling == (F "-5086791939129737/4503599627370496" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "2199023988559703/2199023255552" 53, .gt)
#guard A (F "-100" 53) 53 .Ceiling == (F "-1" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "1267650600228229682971679916032" 53, .gt)
#guard A (F "1" 53) 20 == (F "688409/524288" 20, .gt)
#guard A (F "1" 53) 1 == (F "1" 1, .lt)
#guard A (F "-3/2" 53) 2 == (F "-1" 2, .gt)
#guard A (F "3/2" 53) 113
  == (F "1434101219779853192131440796678933/1298074214633706907132624082305024" 113, .lt)
#guard A (F "1/3" 200) 200
  == (h (F "1249513515853225029983243978531903249213771550283493086355373" 200) (-198), .lt)
#guard A (F "1/3" 200) 10 .Floor == (F "199/64" 10, .lt)
#guard A (F "10" 53) 120
  == (F "664614000632201040657758381029055673/664613997892457936451903530140172288" 120, .gt)
#guard coth (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (cothPrecRound (F "1" 200) 200 .Nearest).1).startsWith
  "1.313035285499331303636161246930847832912013941240452655"
#guard (toString (cothPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "-1.10479139298251190394399878919951011040780499760965974"

-- the transition to `±1`
#guard A (F "18" 53) 53 == (F "2251799813685249/2251799813685248" 53, .lt)
#guard A (F "18" 53) 53 .Floor == (F "2251799813685249/2251799813685248" 53, .lt)
#guard A (F "18" 53) 53 .Ceiling == (F "4503599627370499/4503599627370496" 53, .gt)
#guard A (F "-19" 53) 53 == (F "-1" 53, .gt)
#guard A (F "-19" 53) 53 .Floor == (F "-4503599627370497/4503599627370496" 53, .lt)
#guard A (F "-19" 53) 53 .Ceiling == (F "-1" 53, .gt)
#guard A (F "20" 53) 53 == (F "1" 53, .lt)
#guard A (F "20" 53) 53 .Floor == (F "1" 53, .lt)
#guard A (F "20" 53) 53 .Ceiling == (F "4503599627370497/4503599627370496" 53, .gt)
#guard A (F "40" 53) 53 == (F "1" 53, .lt)
#guard A (F "40" 53) 53 .Floor == (F "1" 53, .lt)
#guard A (F "40" 53) 53 .Ceiling == (F "4503599627370497/4503599627370496" 53, .gt)
#guard A (F "75/4" 53) 53 == (F "1" 53, .lt)
#guard A (F "75/4" 53) 53 .Floor == (F "1" 53, .lt)
#guard A (F "75/4" 53) 53 .Ceiling == (F "4503599627370497/4503599627370496" 53, .gt)

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (F "3/2" 53) 53 .Nearest && odd (F "3/2" 53) 53 .Floor
#guard odd (F "100" 53) 20 .Ceiling && odd (F "1/1000" 53) 113 .Floor
#guard odd (h (F "1" 53) (-1000)) 53 .Ceiling && odd (h (F "1" 53) 1000) 53 .Ceiling

-- tiny arguments: just outside `1/x`
private def tinyOk (k : Int) : Bool :=
  let x := h (F "1" 53) (-k)
  let y := h (F "1" 53) k
  A x 53 == (y, .lt) && A x 53 .Floor == (y, .lt) && A x 53 .Ceiling == (h up k, .gt)
    && A (-x) 53 == (-y, .gt) && A (-x) 53 .Ceiling == (-y, .gt)
    && A (-x) 53 .Floor == (-(h up k), .lt)
#guard tinyOk 100
#guard tinyOk 1000
#guard tinyOk 1073741824

-- large arguments: just outside `±1`
private def bigOk (x : AzFloat) : Bool :=
  A x 53 == (F "1" 53, .lt) && A x 53 .Floor == (F "1" 53, .lt) && A x 53 .Ceiling == (up, .gt)
    && A (-x) 53 == (F "-1" 53, .gt) && A (-x) 53 .Ceiling == (F "-1" 53, .gt)
    && A (-x) 53 .Floor == (-up, .lt) && A x 1 .Ceiling == (F "2" 1, .gt)
    && A x 200 .Nearest == (F "1" 200, .lt)
#guard bigOk (F "1000" 53)
#guard bigOk (F "1048576" 53)
#guard bigOk (h (F "1" 53) 1073741824)
#guard bigOk (h (F "3" 53) 1073741824)
#guard A (F "100" 53) 53 == (F "1" 53, .lt)
#guard A (F "100" 53) 53 .Ceiling == (up, .gt)

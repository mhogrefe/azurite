/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cosh
import Azurite.AzFloat.Exp
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `cosh x`

The special values (`NaN`, `±∞ ↦ +∞`, `cosh 0 = 1`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `700` in three modes, 1-, 2-, 20-, 113-, 120- and 200-bit results,
200-bit strings, evenness, tiny arguments `±2^(−1000)`, `±2^(−2^30)` (the value is just above
`1`, at no cost), and large arguments (`±2^20`, where `cosh x` rounds like `exp |x| / 2`).
References: an independent 6000-bit fixed-point evaluation of `(e^x + e^(−x))/2` rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := coshPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (infinity true, .eq)
#guard A (infinity false) 53 == (infinity true, .eq)
#guard A (infinity false) 0 == (infinity true, .eq)
#guard A zero 53 == (F "1" 53, .eq)
#guard A zero 1 .Floor == (F "1" 1, .eq)
#guard A zero 0 == (nan, .eq)
#guard A (F "2" 53) 0 == (nan, .eq)

-- correctly rounded values
#guard A (F "1" 53) 53 == (F "434338585747285/281474976710656" 53, .lt)
#guard A (F "-1" 53) 53 == (F "434338585747285/281474976710656" 53, .lt)
#guard A (F "2" 53) 53 == (F "2117927889057391/562949953421312" 53, .lt)
#guard A (F "1/2" 53) 53 == (F "317398492294797/281474976710656" 53, .lt)
#guard A (F "-1/3" 53) 53 == (F "4756124870435379/4503599627370496" 53, .gt)
#guard A (F "3/2" 53) 53 == (F "2648577766658065/1125899906842624" 53, .lt)
#guard A (F "-7/5" 53) 53 == (F "4843392763628159/2251799813685248" 53, .lt)
#guard A (F "22/7" 53) 53 == (F "6533915678609191/562949953421312" 53, .lt)
#guard A (F "10" 53) 53 == (F "6054588827529517/549755813888" 53, .lt)
#guard A (F "-100" 53) 53 == (F "13440585709080678047126700217981451777343488" 53, .gt)
#guard A (F "1/1000" 53) 53 == (F "4503601879170497/4503599627370496" 53, .lt)
#guard A (F "-1/1000000000000" 53) 53 == (F "1" 53, .lt)
#guard A (F "1/1125899906842624" 53) 53 == (F "1" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 == (F "1" 53, .lt)
#guard A (F "-3/1606938044258990275541962092341162602522202993782792835301376" 53) 53
  == (F "1" 53, .lt)
#guard A (F "30" 53) 53 == (F "5471474985740525/1024" 53, .gt)
#guard A (F "-37" 53) 53 == (F "5859571186401306" 53, .gt)
#guard A (F "700" 53) 53
  == (h (F "4162952793716295" 53) (957), .lt)
#guard A (F "1" 53) 53 .Floor == (F "434338585747285/281474976710656" 53, .lt)
#guard A (F "-1" 53) 53 .Floor == (F "434338585747285/281474976710656" 53, .lt)
#guard A (F "3/2" 53) 53 .Floor == (F "2648577766658065/1125899906842624" 53, .lt)
#guard A (F "-7/5" 53) 53 .Floor == (F "4843392763628159/2251799813685248" 53, .lt)
#guard A (F "1/1000" 53) 53 .Floor == (F "4503601879170497/4503599627370496" 53, .lt)
#guard A (F "-100" 53) 53 .Floor == (F "13440585709080675571246621647220901979095040" 53, .lt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Floor == (F "1" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "6949417371956561/4503599627370496" 53, .gt)
#guard A (F "-1" 53) 53 .Ceiling == (F "6949417371956561/4503599627370496" 53, .gt)
#guard A (F "3/2" 53) 53 .Ceiling == (F "5297155533316131/2251799813685248" 53, .gt)
#guard A (F "-7/5" 53) 53 .Ceiling == (F "37839005965845/17592186044416" 53, .gt)
#guard A (F "1/1000" 53) 53 .Ceiling == (F "2251800939585249/2251799813685248" 53, .gt)
#guard A (F "-100" 53) 53 .Ceiling == (F "13440585709080678047126700217981451777343488" 53, .gt)
#guard A (F "1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "4503599627370497/4503599627370496" 53, .gt)
#guard A (F "1" 53) 20 == (F "809019/524288" 20, .gt)
#guard A (F "1" 53) 1 == (F "2" 1, .gt)
#guard A (F "-3/2" 53) 2 == (F "2" 2, .lt)
#guard A (F "3/2" 53) 113
  == (F "1526801131901829456394156011364521/649037107316853453566312041152512" 113, .gt)
#guard A (F "1/3" 200) 200
  == (h (F "848521030943790835643122317314502186401856171949208065828775" 200) (-199), .lt)
#guard A (F "1/3" 200) 10 .Floor == (F "135/128" 10, .lt)
#guard A (F "10" 53) 120
  == (F "893499604583825484669482024008005561/81129638414606681695789005144064" 120, .gt)
#guard cosh (F "3/2" 53) == (A (F "3/2" 53) 53).1
#guard (toString (coshPrecRound (F "1" 200) 200 .Nearest).1).startsWith
  "1.543080634815243778477905620757061682601529112365"
#guard (toString (coshPrecRound (F "-3/2" 200) 200 .Nearest).1).startsWith
  "2.352409615243247325767667965441644170173960748865"

-- evenness
private def even (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool := A (-x) p m == A x p m
#guard even (F "3/2" 53) 53 .Nearest && even (F "3/2" 53) 53 .Floor
#guard even (F "100" 53) 20 .Ceiling && even (h (F "1" 53) (-1000)) 53 .Ceiling

-- tiny arguments: just above `1`
private def tinyOk (x : AzFloat) : Bool :=
  A x 53 == (F "1" 53, .lt) && A x 53 .Floor == (F "1" 53, .lt) && A x 53 .Ceiling == (up, .gt)
    && A (-x) 53 .Ceiling == (up, .gt) && A x 1 .Ceiling == (F "2" 1, .gt)
#guard tinyOk (h (F "1" 53) (-100))
#guard tinyOk (h (F "1" 53) (-1000))
#guard tinyOk (h (F "3" 53) (-1073741824))
-- `cosh (2^(−26)) = 1 + 2^(−53) + …`: just above the midpoint
#guard A (h (F "1" 53) (-26)) 53 == (up, .gt)
#guard A (h (F "1" 53) (-26)) 53 .Floor == (F "1" 53, .lt)
#guard A (h (F "1" 53) (-27)) 53 == (F "1" 53, .lt)

-- large arguments: `cosh x` rounds like `exp |x| / 2`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expPrecRound x p m
  A x p m == (h r.1 (-1), r.2) && A (-x) p m == (h r.1 (-1), r.2)
#guard big (F "1048576" 53) 53 .Nearest && big (F "1048576" 53) 53 .Floor
#guard big (F "123456789/8" 53) 20 .Ceiling && big (F "1000" 53) 113 .Nearest

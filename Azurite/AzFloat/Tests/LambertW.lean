/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LambertW
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the real branches of the Lambert `W` function

The special values (`NaN`, `±∞`, `0`, below the branch point — including the 53-bit float nearest
`−e⁻¹`, which lies below it —, `p = 0`), `W₀` on positive floats (`1/2`, `1` (the omega
constant), `3`, `10¹⁰`, `2^±100`, `1/3`, `5/2`) and on `(−e⁻¹, 0)`, `W₋₁` on `(−e⁻¹, 0)`
(`−1/10`, `−9/25`, `−1/4`, `−2^(−100)`, `−1/8`, `−1/1000`, `−0.3678`), the float one ulp above
the 53-bit float nearest `−e⁻¹` (`q = 1 + e x ≈ 1.17·10⁻¹⁶`, both branches), all in the three
modes with 120-digit references at the exact float arguments, and 200-bit values.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def W0 (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := lambertW0PrecRound x p m
private def Wm (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  lambertWm1PrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- The 53-bit float nearest `−e⁻¹` (below it). -/
private def nearBranch : AzFloat := F "-828390857088487/2251799813685248" 53
/-- One ulp above `nearBranch`: in the domain, `q ≈ 1.17·10⁻¹⁶`. -/
private def aboveBranch (p : Nat) : AzFloat := F "-6627126856707895/18014398509481984" p

-- special values
#guard W0 nan 53 == (nan, .eq)
#guard W0 pinf 53 == (pinf, .eq)
#guard W0 ninf 53 == (nan, .eq)
#guard W0 zero 53 == (zero, .eq)
#guard W0 (F "-1" 53) 53 == (nan, .eq)
#guard W0 (F "-1/2" 53) 53 == (nan, .eq)
#guard W0 nearBranch 53 == (nan, .eq)
#guard W0 (F "1" 53) 0 == (nan, .eq)
#guard W0 zero 0 == (zero, .eq)
#guard Wm nan 53 == (nan, .eq)
#guard Wm pinf 53 == (nan, .eq)
#guard Wm ninf 53 == (nan, .eq)
#guard Wm zero 53 == (ninf, .eq)
#guard Wm (F "1" 53) 53 == (nan, .eq)
#guard Wm (F "-1" 53) 53 == (nan, .eq)
#guard Wm nearBranch 53 == (nan, .eq)
#guard Wm (F "-1/4" 53) 0 == (nan, .eq)
#guard Wm zero 0 == (ninf, .eq)

-- `W₀`, `x > 0`
#guard W0 (F "1/2" 53) 53 == (F "24751059545555/70368744177664" 53, .gt)
#guard W0 (F "1/2" 53) 53 .Floor == (F "6336271243662079/18014398509481984" 53, .lt)
#guard W0 (F "1" 53) 53 == (F "5108372622710359/9007199254740992" 53, .lt)
#guard W0 (F "1" 53) 53 .Ceiling == (F "638546577838795/1125899906842624" 53, .gt)
#guard W0 (F "3" 53) 53 == (F "1182092327033255/1125899906842624" 53, .gt)
#guard W0 (F "3" 53) 53 .Floor == (F "4728369308133019/4503599627370496" 53, .lt)
#guard W0 (F "10000000000" 53) 53 == (F "5637573760255067/281474976710656" 53, .gt)
#guard W0 (F "1267650600228229401496703205376" 53) 53
  == (F "2291846904728127/35184372088832" 53, .lt)
#guard W0 (F "1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "4583693809456255/70368744177664" 53, .gt)
#guard W0 (F "1/1267650600228229401496703205376" 53) 53
  == (F "1/1267650600228229401496703205376" 53, .gt)
#guard W0 (F "1/1267650600228229401496703205376" 53) 53 .Floor
  == (F "9007199254740991/11417981541647679048466287755595961091061972992" 53, .lt)
#guard W0 (F "1/3" 53) 53 == (F "2320503604550259/9007199254740992" 53, .lt)
#guard W0 (F "5/2" 53) 53 == (F "1079272289741457/1125899906842624" 53, .gt)

-- `W₀`, `−e⁻¹ < x < 0`
#guard W0 (F "-1/10" 53) 53 == (F "-8058385148099113/72057594037927936" 53, .gt)
#guard W0 (F "-1/10" 53) 53 .Floor == (F "-4029192574049557/36028797018963968" 53, .lt)
#guard W0 (F "-9/25" 53) 53 == (F "-7260562050070751/9007199254740992" 53, .lt)
#guard W0 (F "-9/25" 53) 53 .Ceiling == (F "-3630281025035375/4503599627370496" 53, .gt)
#guard W0 (F "-1/4" 53) 53 == (F "-6438399281118467/18014398509481984" 53, .gt)
#guard W0 (F "-1/1267650600228229401496703205376" 53) 53
  == (F "-1/1267650600228229401496703205376" 53, .gt)
#guard W0 (F "-1/8" 53) 53 == (F "-5203327617395453/36028797018963968" 53, .gt)
#guard W0 (F "-1/1000" 53) 53 == (F "-2308152317148371/2305843009213693952" 53, .lt)
#guard W0 (F "-3678/10000" 53) 53 == (F "-1102662137736347/1125899906842624" 53, .gt)
#guard W0 (aboveBranch 53) 53 == (F "-4503599558446263/4503599627370496" 53, .lt)
#guard W0 (aboveBranch 53) 53 .Ceiling == (F "-9007199116892525/9007199254740992" 53, .gt)

-- `W₋₁`
#guard Wm (F "-1/10" 53) 53 == (F "-4027515175571421/1125899906842624" 53, .gt)
#guard Wm (F "-1/10" 53) 53 .Floor == (F "-8055030351142843/2251799813685248" 53, .lt)
#guard Wm (F "-9/25" 53) 53 == (F "-1376716779936343/1125899906842624" 53, .lt)
#guard Wm (F "-9/25" 53) 53 .Ceiling == (F "-5506867119745371/4503599627370496" 53, .gt)
#guard Wm (F "-1/4" 53) 53 == (F "-4848783344313553/2251799813685248" 53, .lt)
#guard Wm (F "-1/1267650600228229401496703205376" 53) 53
  == (F "-161877902060443/2199023255552" 53, .lt)
#guard Wm (F "-1/1267650600228229401496703205376" 53) 53 .Ceiling
  == (F "-5180092865934175/70368744177664" 53, .gt)
#guard Wm (F "-1/8" 53) 53 == (F "-3672331608414589/1125899906842624" 53, .gt)
#guard Wm (F "-1/1000" 53) 53 == (F "-1283245329452111/140737488355328" 53, .lt)
#guard Wm (F "-3678/10000" 53) 53 == (F "-2298923767488339/2251799813685248" 53, .lt)
#guard Wm (aboveBranch 53) 53 == (F "-2251799848147365/2251799813685248" 53, .lt)
#guard Wm (aboveBranch 53) 53 .Ceiling == (F "-4503599696294729/4503599627370496" 53, .gt)

-- 200 bits
#guard W0 (F "1" 200) 200
  == (F ("227841032476426663099079751600042627130329070727104284459813/"
      ++ "401734511064747568885490523085290650630550748445698208825344") 200, .gt)
#guard Wm (F "-1/4" 200) 200
  == (F ("-432525927537662856011902604319053757720456710040947497833457/"
      ++ "200867255532373784442745261542645325315275374222849104412672") 200, .lt)
#guard W0 (aboveBranch 200) 200
  == (F ("-401734504916500519363838464157987097728614760642047728360695/"
      ++ "401734511064747568885490523085290650630550748445698208825344") 200, .gt)
#guard Wm (aboveBranch 200) 200
  == (F ("-803469034425989362273400164930641479323559745246445132178595/"
      ++ "803469022129495137770981046170581301261101496891396417650688") 200, .gt)

-- the nearest wrappers and the omega constant
#guard lambertW0Float (F "1" 53) == (W0 (F "1" 53) 53).1
#guard lambertWm1Float (F "-1/4" 53) == (Wm (F "-1/4" 53) 53).1
#guard toString (lambertW0Float (F "1" 200))
  == "0.567143290409783872999968662210355549753815787186512508135131"

-- tiny arguments of `W₀` (`W₀ x = x − x² + ⋯`): rounded by one test, at a cost independent of
-- the exponent (the Ziv loop would need about `|e|` bits to see the side of `x`)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
private def third200 : AzFloat := (F "1/3" 53) <<< AzInt.ofInt (-200)
#guard W0 tinyX 53 == (tinyX, .gt)
#guard W0 tinyX 53 .Ceiling == (tinyX, .gt)
#guard (W0 tinyX 53 .Floor).2 == .lt
#guard (W0 tinyX 53 .Floor).1 != tinyX
#guard W0 (-tinyX) 53 .Ceiling == (-tinyX, .gt)
#guard (W0 (-tinyX) 53).2 == .gt
#guard W0 ((F "3/2" 100) <<< tinyE) 53 == ((F "3/2" 53) <<< tinyE, .gt)
#guard lambertW0Float tinyX == tinyX
#guard W0 third200 53 == (third200, .gt)
#guard W0 third200 53 .Floor
  == ((F "1501199875790165/4503599627370496" 53) <<< AzInt.ofInt (-200), .lt)
#guard W0 (-third200) 53 == (-third200, .gt)
#guard W0 (-third200) 53 .Floor
  == ((F "-3002399751580331/9007199254740992" 53) <<< AzInt.ofInt (-200), .lt)

-- huge arguments of `W₀` and arguments of `W₋₁` near `0⁻`, far outside the `Float` range
-- (references: the root of `w + ln |w| = ln |x|` at 80 digits)
#guard W0 ((F "1" 53) <<< AzInt.ofInt (2 ^ 30)) 53 == (F "6243314596803693/8388608" 53, .lt)
#guard W0 ((F "1" 53) <<< AzInt.ofInt (2 ^ 62)) 53 == (F "3196577161300663808" 53, .lt)
#guard Wm ((F "-1" 53) <<< tinyE) 53 == (F "-3121657469763513/4194304" 53, .lt)
#guard Wm ((F "-1" 53) <<< AzInt.ofInt (-(2 ^ 62 : Int))) 53
  == (F "-3196577161300663808" 53, .gt)

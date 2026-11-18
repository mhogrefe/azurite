/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosPi
import Azurite.AzFloat.AcosRat
import Azurite.AzFloat.Acos
import Azurite.AzFloat.AcosWithPeriod
import Azurite.AzFloat.AcosRatWithPeriod
import Azurite.AzFloat.AcoshRat
import Azurite.AzFloat.Acot
import Azurite.AzFloat.Acosh
import Azurite.AzFloat.AcotRat
import Azurite.AzFloat.AcotWithPeriod
import Azurite.AzFloat.AcotPi
import Azurite.AzFloat.Acsc
import Azurite.AzFloat.AcothRat
import Azurite.AzFloat.AcscWithPeriod
import Azurite.AzFloat.AcscRat
import Azurite.AzFloat.Acoth
import Azurite.AzFloat.AcscPi
import Azurite.AzFloat.AcschRat
import Azurite.AzFloat.Acsch
import Azurite.AzFloat.AsecPi
import Azurite.AzFloat.Asec
import Azurite.AzFloat.Asech
import Azurite.AzFloat.AsecWithPeriod
import Azurite.AzFloat.AsecRat
import Azurite.AzFloat.AsechRat
import Azurite.AzFloat.AsinRatWithPeriod
import Azurite.AzFloat.Asin
import Azurite.AzFloat.AsinRat
import Azurite.AzFloat.Asinh
import Azurite.AzFloat.AsinPi
import Azurite.AzFloat.AsinWithPeriod
import Azurite.AzFloat.Atan2
import Azurite.AzFloat.AsinhRat
import Azurite.AzFloat.Atan
import Azurite.AzFloat.Atan2Pi
import Azurite.AzFloat.Atan2Rat
import Azurite.AzFloat.Atan2RatWithPeriod
import Azurite.AzFloat.Atan2WithPeriod
import Azurite.AzFloat.AtanPi
import Azurite.AzFloat.AtanRat
import Azurite.AzFloat.AtanRatWithPeriod
import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.Atanh
import Azurite.AzFloat.AtanhRat
import Azurite.AzFloat.Cos
import Azurite.AzFloat.Cosh
import Azurite.AzFloat.CosPi
import Azurite.AzFloat.CosWithPeriod
import Azurite.AzFloat.CosRatWithPeriod
import Azurite.AzFloat.CoshRat
import Azurite.AzFloat.Csc
import Azurite.AzFloat.Coth
import Azurite.AzFloat.CschRat
import Azurite.AzFloat.Csch
import Azurite.AzFloat.CosRat
import Azurite.AzFloat.Cot
import Azurite.AzFloat.CothRat
import Azurite.AzFloat.Dottie
import Azurite.AzFloat.Gd
import Azurite.AzFloat.GdInvRat
import Azurite.AzFloat.GdInv
import Azurite.AzFloat.GdRat
import Azurite.AzFloat.Sech
import Azurite.AzFloat.Sin
import Azurite.AzFloat.SinCosRat
import Azurite.AzFloat.SinCosPi
import Azurite.AzFloat.SecWithPeriod
import Azurite.AzFloat.SinRatWithPeriod
import Azurite.AzFloat.SechRat
import Azurite.AzFloat.SinCosWithPeriod
import Azurite.AzFloat.SinCos
import Azurite.AzFloat.SinhCosh
import Azurite.AzFloat.SinPi
import Azurite.AzFloat.Tan
import Azurite.AzFloat.Sec
import Azurite.AzFloat.SinWithPeriod
import Azurite.AzFloat.Sinh
import Azurite.AzFloat.Tanh
import Azurite.AzFloat.TanRat
import Azurite.AzFloat.SinhCoshRat
import Azurite.AzFloat.TreeT
import Azurite.AzFloat.SinCosRatWithPeriod
import Azurite.AzFloat.SinRat
import Azurite.AzFloat.SinhRat
import Azurite.AzFloat.TanRatWithPeriod
import Azurite.AzFloat.TanPi
import Azurite.AzFloat.TanWithPeriod
import Azurite.AzFloat.TanhRat
import Azurite.AzFloat.Exp
import Azurite.AzFloat.ExpM1
import Azurite.AzFloat.Ln
import Azurite.AzFloat.LambertW
import Azurite.AzFloat.LogBaseExact
import Azurite.AzFloat.Beta
import Azurite.AzFloat.BetaRat
import Azurite.AzFloat.LnBetaRat
import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.DigammaRat
import Azurite.AzFloat.PsiZero
import Azurite.AzFloat.WrightOmega
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Parse
import Azurite.AzRat.Shift
import Azurite.Benchmark.Common

/-!
# The elementary families: timings by function and argument

`az_float_families`: one table per family, one row per function and argument, one column per
precision `P` (bits): the time (ms, median of three passes) of the function rounded to nearest
at `P` bits.  A float argument is the rational `q · 2^k` of the row rounded to `max P prec` bits
(`prec = 64` unless the row needs more, next to `±1`); a rational function gets `q · 2^k`
itself.  The first rows of a family are reference functions.

Config: `bits` (default `53/200/1000`), `family` (default all; one of `hyperbolic`,
`inv_hyperbolic`, `gd`, `inv_trig`, `inv_recip_trig`, `recip_trig`, `trig_variants`, `misc`).
-/

open Azurite Azurite.AzFloat Azurite.Benchmark

namespace Azurite.Benchmark.Families

private def padL (s : String) (w : Nat) : String := "".pushn ' ' (w - s.length) ++ s

private def padR (s : String) (w : Nat) : String := s.pushn ' ' (w - s.length)

@[noinline] private def timeMed {α : Type} (f : Unit → α) (size : α → Nat) : IO UInt64 := do
  let pass : IO UInt64 := do
    let t0 ← monoNanos
    let acc := size (f ())
    let t1 ← monoNanos
    if acc = 0 then IO.eprintln "(zero checksum)"
    return t1 - t0
  let a ← pass
  let b ← pass
  let c ← pass
  return median3 a b c

private def msStr (ns : UInt64) : String :=
  let us := ns.toNat / 1000
  s!"{us / 1000}.{padL s!"{us % 1000}" 3 |>.replace " " "0"}"

private def fsz (r : AzFloat × Ordering) : Nat := r.1.precision?.getD 0 + 1

/-- An argument `q · 2^shift`; as a float it has `max P prec` bits. -/
private structure Arg where
  q : String
  shift : Int := 0
  prec : Nat := 64
  label : String := ""

private def Arg.show (a : Arg) : String :=
  if a.label != "" then a.label
  else if a.shift = 0 then a.q else s!"{a.q}*2^{a.shift}"

private def Arg.rat (a : Arg) : AzRat :=
  let q := (AzRat.parse a.q).get!
  if 0 ≤ a.shift then q <<< a.shift.toNat else q >>> (-a.shift).toNat

private def Arg.float (a : Arg) (P : Nat) : AzFloat :=
  ofAzRat ((AzRat.parse a.q).get!) (max P a.prec) <<< AzInt.ofInt a.shift

private abbrev FloatFn := AzFloat → Nat → RoundingMode → AzFloat × Ordering
private abbrev RatFn := AzRat → Nat → RoundingMode → AzFloat × Ordering

private inductive Fn
  | flt (f : FloatFn)
  | rat (f : RatFn)

private structure Entry where
  name : String
  fn : Fn
  args : List Arg

private def F (name : String) (f : FloatFn) (args : List Arg) : Entry := ⟨name, .flt f, args⟩
private def R (name : String) (f : RatFn) (args : List Arg) : Entry := ⟨name, .rat f, args⟩

/-- The first component of a joint function. -/
private def fst {α : Type}
    (f : α → Nat → RoundingMode → (AzFloat × Ordering) × (AzFloat × Ordering)) :
    α → Nat → RoundingMode → AzFloat × Ordering :=
  fun x p m => (f x p m).1

private def a (q : String) : Arg := { q := q }
private def sh (q : String) (k : Int) : Arg := { q := q, shift := k }
/-- `1 + 2^(−100)` and `1 − 2^(−100)`. -/
private def onePlus : Arg :=
  { q := "1267650600228229401496703205377/1267650600228229401496703205376", prec := 128,
    label := "1+2^-100" }
private def oneMinus : Arg :=
  { q := "1267650600228229401496703205375/1267650600228229401496703205376", prec := 128,
    label := "1-2^-100" }
private def tiny : Arg := sh "1/3" (-100)
private def tinier : Arg := sh "1/3" (-10000)
private def huge : Arg := sh "3" 10000

private def three : AzFloat := ofAzNat (AzNat.ofNat 3)
private def threeQ : AzRat := (AzRat.parse "3").get!

private def hyperbolic : List Entry :=
  let fl := [a "1/3", a "3/2", a "1000", tiny, tinier, sh "3" 40]
  let rl := [a "1/3", a "1000", tiny, sh "3" 40]
  [F "exp" expPrecRound [a "1/3", a "1000", sh "3" 40],
   F "expM1" expM1PrecRound [a "1/3", tiny],
   F "sinh" sinhPrecRound fl, F "cosh" coshPrecRound fl,
   F "tanh" tanhPrecRound (fl ++ [huge]), F "sech" sechPrecRound fl,
   F "csch" cschPrecRound fl, F "coth" cothPrecRound (fl ++ [huge]),
   F "sinhCosh" (fst sinhCoshPrecRound) fl,
   R "sinhRat" sinhRatPrecRound rl, R "coshRat" coshRatPrecRound rl,
   R "tanhRat" tanhRatPrecRound rl, R "sechRat" sechRatPrecRound rl,
   R "cschRat" cschRatPrecRound rl, R "cothRat" cothRatPrecRound rl,
   R "sinhCoshRat" (fst sinhCoshRatPrecRound) rl]

private def invHyperbolic : List Entry :=
  [F "ln" lnPrecRound [a "1/3", a "1000", huge],
   F "asinh" asinhPrecRound [a "1/3", a "3/2", a "1000", tiny, tinier, huge],
   F "acosh" acoshPrecRound [a "3/2", a "1000", onePlus, huge],
   F "atanh" atanhPrecRound [a "1/3", a "9/10", oneMinus, tiny, tinier],
   F "asech" asechPrecRound [a "1/3", a "9/10", oneMinus, tiny, tinier],
   F "acsch" acschPrecRound [a "1/3", a "3/2", a "1000", tinier, huge],
   F "acoth" acothPrecRound [a "3/2", a "1000", onePlus, huge],
   R "asinhRat" asinhRatPrecRound [a "1/3", a "1000", tiny, huge],
   R "acoshRat" acoshRatPrecRound [a "3/2", a "1000", onePlus, huge],
   R "atanhRat" atanhRatPrecRound [a "1/3", a "9/10", oneMinus, tiny],
   R "asechRat" asechRatPrecRound [a "1/3", a "9/10", oneMinus, tiny],
   R "acschRat" acschRatPrecRound [a "1/3", a "1000", tiny, huge],
   R "acothRat" acothRatPrecRound [a "3/2", a "1000", onePlus, huge]]

private def gdFamily : List Entry :=
  [F "atan" atanPrecRound [a "1/3"], F "exp" expPrecRound [a "1/3"],
   F "gd" gdPrecRound [a "1/3", a "3/2", a "30", a "1000", a "100000", tiny, tinier],
   R "gdRat" gdRatPrecRound [a "1/3", a "30", a "1000", tiny],
   F "gdInv" gdInvPrecRound [a "1/3", a "3/2", a "1570796/1000000", tiny, tinier],
   R "gdInvRat" gdInvRatPrecRound [a "1/3", a "3/2", a "1570796/1000000", tiny]]

private def invTrig : List Entry :=
  let fl := [a "1/3", a "9/10", oneMinus, tiny, tinier]
  let rl := [a "1/3", a "9/10", oneMinus, tiny, tinier]
  let wl := [a "1/3", a "9/10", a "1/2", a "1"]
  let al := [a "1/3", a "1000", a "1", huge]
  let yl := [a "1/3", a "1000", tiny, huge]
  [F "atan" atanPrecRound [a "1/3", a "1000", huge],
   F "asin" asinPrecRound fl, F "acos" acosPrecRound fl,
   R "asinRat" asinRatPrecRound rl, R "acosRat" acosRatPrecRound rl,
   F "asinWithPeriod 360" (asinWithPeriodPrecRound · 360) wl,
   F "acosWithPeriod 360" (acosWithPeriodPrecRound · 360) wl,
   R "asinRatWithPeriod 360" (asinRatWithPeriodPrecRound · 360) wl,
   R "acosRatWithPeriod 360" (acosRatWithPeriodPrecRound · 360) wl,
   F "asinPi" asinPiPrecRound wl, F "acosPi" acosPiPrecRound wl,
   R "asinPiRat" asinPiRatPrecRound wl, R "acosPiRat" acosPiRatPrecRound wl,
   R "atanRat" atanRatPrecRound al,
   F "atanWithPeriod 360" (atanWithPeriodPrecRound · 360) al,
   R "atanRatWithPeriod 360" (atanRatWithPeriodPrecRound · 360) al,
   F "atanPi" atanPiPrecRound al, R "atanPiRat" atanPiRatPrecRound al,
   F "atan2 y 3" (atan2PrecRound · three) yl,
   F "atan2 y (-3)" (atan2PrecRound · (-three)) yl,
   R "atan2Rat y (-3)" (atan2RatPrecRound · (-threeQ)) yl,
   F "atan2WithPeriod y (-3) 360" (atan2WithPeriodPrecRound · (-three) 360) yl,
   R "atan2RatWithPeriod y (-3) 360" (atan2RatWithPeriodPrecRound · (-threeQ) 360) yl,
   F "atan2Pi y (-3)" (atan2PiPrecRound · (-three)) yl,
   R "atan2PiRat y (-3)" (atan2PiRatPrecRound · (-threeQ)) yl]

private def invRecipTrig : List Entry :=
  let fl := [a "3/2", a "1000", onePlus, huge]
  let cl := [a "1/3", a "3/2", a "1000", tiny, huge]
  let wl := [a "3/2", a "2", a "1000"]
  [F "atan" atanPrecRound [a "1/3"],
   F "asec" asecPrecRound fl, F "acsc" acscPrecRound fl, F "acot" acotPrecRound cl,
   R "asecRat" asecRatPrecRound fl, R "acscRat" acscRatPrecRound fl,
   R "acotRat" acotRatPrecRound cl,
   F "asecWithPeriod 360" (asecWithPeriodPrecRound · 360) wl,
   F "acscWithPeriod 360" (acscWithPeriodPrecRound · 360) wl,
   F "acotWithPeriod 360" (acotWithPeriodPrecRound · 360) (wl ++ [a "1"]),
   R "asecRatWithPeriod 360" (asecRatWithPeriodPrecRound · 360) wl,
   R "acscRatWithPeriod 360" (acscRatWithPeriodPrecRound · 360) wl,
   R "acotRatWithPeriod 360" (acotRatWithPeriodPrecRound · 360) (wl ++ [a "1"]),
   F "asecPi" asecPiPrecRound wl, F "acscPi" acscPiPrecRound wl, F "acotPi" acotPiPrecRound wl,
   R "asecPiRat" asecPiRatPrecRound wl, R "acscPiRat" acscPiRatPrecRound wl,
   R "acotPiRat" acotPiRatPrecRound wl]

private def recipTrig : List Entry :=
  let fl := [a "1/3", a "3/2", a "1000", a "355/113", a "355/226", tiny, tinier, sh "3" 1000]
  let rl := [a "1/3", a "1000", a "355/113", a "355/226", tiny]
  let wl := [a "1/3", a "100/3", a "45", a "1000001/7"]
  let pl := [a "1/3", a "1/4", a "1000001/7", tiny]
  [F "sin" sinPrecRound [a "1/3", a "1000", sh "3" 1000], F "tan" tanPrecRound [a "1/3"],
   F "sec" secPrecRound fl, F "csc" cscPrecRound fl, F "cot" cotPrecRound fl,
   R "secRat" secRatPrecRound rl, R "cscRat" cscRatPrecRound rl, R "cotRat" cotRatPrecRound rl,
   F "secWithPeriod 360" (secWithPeriodPrecRound · 360) wl,
   F "cscWithPeriod 360" (cscWithPeriodPrecRound · 360) wl,
   F "cotWithPeriod 360" (cotWithPeriodPrecRound · 360) wl,
   R "secRatWithPeriod 360" (secRatWithPeriodPrecRound · 360) wl,
   R "cscRatWithPeriod 360" (cscRatWithPeriodPrecRound · 360) wl,
   R "cotRatWithPeriod 360" (cotRatWithPeriodPrecRound · 360) wl,
   F "secPi" secPiPrecRound pl, F "cscPi" cscPiPrecRound pl, F "cotPi" cotPiPrecRound pl,
   R "secPiRat" secPiRatPrecRound pl, R "cscPiRat" cscPiRatPrecRound pl,
   R "cotPiRat" cotPiRatPrecRound pl]

private def trigVariants : List Entry :=
  let fl := [a "1/3", a "1000", tiny, sh "3" 1000]
  let rl := [a "1/3", a "1000", a "355/113", tiny, sh "3" 1000]
  let wl := [a "1/3", a "100/3", a "30", a "1000001/7", sh "3" 1000]
  let pl := [a "1/3", a "1/6", a "1000001/7", tiny]
  [F "sin" sinPrecRound fl, F "cos" cosPrecRound fl, F "tan" tanPrecRound fl,
   F "sinCos" (fst sinCosPrecRound) fl,
   R "sinRat" sinRatPrecRound rl, R "cosRat" cosRatPrecRound rl, R "tanRat" tanRatPrecRound rl,
   R "sinCosRat" (fst sinCosRatPrecRound) rl,
   F "sinWithPeriod 360" (sinWithPeriodPrecRound · 360) wl,
   F "cosWithPeriod 360" (cosWithPeriodPrecRound · 360) wl,
   F "tanWithPeriod 360" (tanWithPeriodPrecRound · 360) wl,
   F "sinCosWithPeriod 360" (fst (sinCosWithPeriodPrecRound · 360)) wl,
   R "sinRatWithPeriod 360" (sinRatWithPeriodPrecRound · 360) wl,
   R "cosRatWithPeriod 360" (cosRatWithPeriodPrecRound · 360) wl,
   R "tanRatWithPeriod 360" (tanRatWithPeriodPrecRound · 360) wl,
   R "sinCosRatWithPeriod 360" (fst (sinCosRatWithPeriodPrecRound · 360)) wl,
   F "sinPi" sinPiPrecRound pl, F "cosPi" cosPiPrecRound pl, F "tanPi" tanPiPrecRound pl,
   F "sinCosPi" (fst sinCosPiPrecRound) pl,
   R "sinPiRat" sinPiRatPrecRound pl, R "cosPiRat" cosPiRatPrecRound pl,
   R "tanPiRat" tanPiRatPrecRound pl, R "sinCosPiRat" (fst sinCosPiRatPrecRound) pl]

/-- `logBaseExactCore? · 3` as a timed function (the value is discarded). -/
private def logExact3 : FloatFn := fun x _ _ =>
  match logBaseExactCore? x (AzNat.ofNat 3) with
  | some _ => (one, .eq)
  | none => (one, .lt)

private def fifty : AzFloat := ofAzNat (AzNat.ofNat 50)
private def fiveHalves : AzFloat := ofAzRat (AzRat.parse "5/2").get! 64
private def sevenThirds : AzFloat := ofAzRat (AzRat.parse "7/3").get! 1100

private def misc : List Entry :=
  let tl := [a "1/3", a "1/10", a "-1/3", tiny]
  let dl := [a "1/3", a "3/2", a "150", a "-201/2", a "-1099511627777/1099511627776", tiny]
  let wl := [a "1/3", a "-10", a "-1000", a "1000", a "1000000000000000000000000000001/3"]
  let big : Nat := 3 ^ 1000
  let ex (n : Nat) (label : String) : Arg := { q := toString n, prec := 2000, label := label }
  [F "cos" cosPrecRound [a "1/3"], F "lambertW0" lambertW0PrecRound [a "-1/3"],
   F "dottie" (fun _ => dottiePrecRound) [a "1"],
   F "ln" lnPrecRound [a "1/3"], F "exp" expPrecRound [a "-1000"],
   F "wrightOmega" wrightOmegaPrecRound wl, R "wrightOmegaRat" wrightOmegaRatPrecRound wl,
   F "digamma" digammaPrecRound dl, R "digammaRat" digammaRatPrecRound dl,
   F "lnGamma" lnGammaPrecRound [a "1/3", a "150"],
   F "beta x 5/2" (fun x => betaPrecRound x fiveHalves) [a "1/3", a "150", a "-7/3"],
   F "beta x -7/3" (fun x => betaPrecRound x (-sevenThirds)) [a "1/3", a "-1/3"],
   F "lnAbsBeta x 5/2" (fun x p m => (lnAbsBetaPrecRound x fiveHalves p m).1)
     [a "1/3", a "150", a "-7/3", sh "3" 100, sh "3" 1000],
   F "lnAbsBeta x 1" (fun x p m => (lnAbsBetaPrecRound x one p m).1) [a "1/3"],
   R "lnAbsBetaRat q 5/2" (fun q p m => (lnAbsBetaRatPrecRound q (AzRat.parse "5/2").get! p m).1)
     [a "1/3", a "-7/3"],
   R "betaRat q 5/2" (fun q => betaRatPrecRound q (AzRat.parse "5/2").get!)
     [a "1/3", a "150", a "-7/3"],
   R "betaRat q -7/3" (fun q => betaRatPrecRound q (AzRat.parse "-7/3").get!)
     [a "1/3", a "-1/3"],
   R "betaRat q 50" (fun q => betaRatPrecRound q (AzRat.parse "50").get!) [a "1/3", a "40"],
   F "beta x 3" (fun x => betaPrecRound x three) [a "1/3", a "-7/3"],
   F "beta x 50" (fun x => betaPrecRound x fifty) [a "1/3", a "40"],
   F "psiZero 0" (fun _ => psiZeroPrecRound 0) [a "1"],
   F "psiZero 1" (fun _ => psiZeroPrecRound 1) [a "1"],
   F "psiZero 1000" (fun _ => psiZeroPrecRound 1000) [a "1"],
   F "treeT0" treeT0PrecRound tl, R "treeT0Rat" treeT0RatPrecRound tl,
   F "treeTm1" treeTm1PrecRound [a "1/3", a "1/10", tiny],
   R "treeTm1Rat" treeTm1RatPrecRound [a "1/3", a "1/10", tiny],
   F "logBaseExactCore? x 3" logExact3
     [ex big "3^1000", ex (big + 2) "3^1000+2", ex (big * 2 ^ 300) "3^1000*2^300", a "1/3"]]

private def families : List (String × List Entry) :=
  [("hyperbolic", hyperbolic), ("inv_hyperbolic", invHyperbolic), ("gd", gdFamily),
   ("inv_trig", invTrig), ("inv_recip_trig", invRecipTrig), ("recip_trig", recipTrig),
   ("trig_variants", trigVariants), ("misc", misc)]

/-- Run the `az_float_families` benchmark. -/
def run (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) : IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 200, 1000]
  for (fam, entries) in families do
    if (cfg["family"]?).all (· == fam) then
      IO.println s!"[AzFloat-Families: {fam}] ms per call (median of 3 passes)"
      IO.println (bitsList.foldl (fun s P => s ++ padL s!"@{P}" 11)
        (padR "function" 31 ++ padR "argument" 18))
      for e in entries do
        for arg in e.args do
          let mut line := padR e.name 31 ++ padR (arg.show.take 17).toString 18
          for P in bitsList do
            let ns ← match e.fn with
              | .flt f =>
                let x := arg.float P
                timeMed (fun _ => f x P .Nearest) fsz
              | .rat f =>
                let q := arg.rat
                timeMed (fun _ => f q P .Nearest) fsz
            line := line ++ padL (msStr ns) 11
          IO.println line
          (← IO.getStdout).flush

end Azurite.Benchmark.Families

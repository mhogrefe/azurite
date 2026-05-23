import Azurite.Benchmark.RatCmp
import Azurite.Benchmark.AzPolynomialMul
import Azurite.Benchmark.AzPolynomialKaratsuba
import Azurite.Benchmark.AzNatAdd
import Azurite.Benchmark.AzNatSub
import Azurite.Benchmark.AzNatMul
import Azurite.Benchmark.AzNatMulCompare
import Azurite.Benchmark.AzNatSquare
import Azurite.Benchmark.AzNatSquareCompare
import Azurite.Benchmark.AzNatDivMod
import Azurite.AzPolynomial.Tune
import Azurite.AzNat.Tune

-- ── Config parsing ──────────────────────────────────────────────────────────

def parseConfig (s : String) : Std.HashMap String String :=
  s.splitOn "," |>.foldl (init := {}) fun m entry =>
    match entry.splitOn ":" with
    | [k, v] => m.insert k.trimAscii.toString v.trimAscii.toString
    | _      => m

-- ── Main ────────────────────────────────────────────────────────────────────

def validBenchmarks : List String :=
  ["rat_cmp", "az_polynomial_mul", "az_polynomial_karatsuba",
   "az_nat_add", "az_nat_sub", "az_nat_mul", "az_nat_mul_compare", "az_nat_div_mod",
   "az_nat_square", "az_nat_square_compare",
   "tune_karatsuba", "tune_karatsuba_rat", "tune_karatsuba_zmod", "tune_karatsuba_all",
   "tune_karatsuba_aznat", "tune_karatsuba_aznat_2d",
   "tune_aznat_square"]

def main (args : List String) : IO Unit := do
  -- Usage: benchmark <name> <limit> [config]
  -- config example: "meanBitLength:64"
  match args with
  | name :: limitStr :: rest =>
    let seed : UInt64 := 1337
    let cfg := parseConfig (rest.headD "")
    match limitStr.toNat? with
    | none =>
      IO.eprintln s!"Error: limit must be a natural number, got '{limitStr}'"
    | some limit =>
      match name with
      | "rat_cmp" => runRatCmp limit cfg seed
      | "az_polynomial_mul" => runAzPolynomialMul limit cfg seed
      | "az_polynomial_karatsuba" => runAzPolynomialKaratsuba limit cfg seed
      | "az_nat_add" => runAzNatAdd limit cfg seed
      | "az_nat_sub" => runAzNatSub limit cfg seed
      | "az_nat_mul" => runAzNatMul limit cfg seed
      | "az_nat_mul_compare" => runAzNatMulCompare limit cfg seed
      | "az_nat_div_mod" => runAzNatDivMod limit cfg seed
      | "az_nat_square" => runAzNatSquare limit cfg seed
      | "az_nat_square_compare" => runAzNatSquareCompare limit cfg seed
      | "tune_karatsuba" =>
        let meanDegree := configGetRat cfg "meanDegree" 256
        let nPairs := configGetNat cfg "nPairs" 200
        let _ ← tuneKaratsuba (nPairs := nPairs) (meanDegree := meanDegree) (seed := seed)
      | "tune_karatsuba_rat" =>
        let meanDegree := configGetRat cfg "meanDegree" 256
        let nPairs := configGetNat cfg "nPairs" 200
        let _ ← tuneKaratsubaRat (nPairs := nPairs) (meanDegree := meanDegree) (seed := seed)
      | "tune_karatsuba_zmod" =>
        let meanDegree := configGetRat cfg "meanDegree" 256
        let nPairs := configGetNat cfg "nPairs" 200
        let _ ← tuneKaratsubaZMod (nPairs := nPairs) (meanDegree := meanDegree) (seed := seed)
      | "tune_karatsuba_all" =>
        let meanDegree := configGetRat cfg "meanDegree" 256
        let nPairs := configGetNat cfg "nPairs" 200
        tuneKaratsubaAll (nPairs := nPairs) (meanDegree := meanDegree) (seed := seed)
      | "tune_karatsuba_aznat" =>
        let meanBitLength := configGetRat cfg "meanBitLength" 100000
        let nPairs := configGetNat cfg "nPairs" 200
        let balanceRatio := configGetNat cfg "balanceRatio" 50
        let lo := configGetNat cfg "lo" 2
        let hi := configGetNat cfg "hi" 128
        let _ ← tuneAzNatKaratsuba (lo := lo) (hi := hi) (nPairs := nPairs)
                  (meanBitLength := meanBitLength) (balanceRatio := balanceRatio)
                  (seed := seed)
      | "tune_karatsuba_aznat_2d" =>
        -- 2-D grid sweep over (minThreshold, kPercent). No balance filter:
        -- the ratio dimension is part of what's being tuned.
        let meanBitLength := configGetRat cfg "meanBitLength" 100000
        let nPairs := configGetNat cfg "nPairs" 400
        let _ ← tuneAzNatDispatch2D (nPairs := nPairs)
                  (meanBitLength := meanBitLength) (seed := seed)
      | "tune_aznat_square" =>
        -- 1-D grid sweep over `squareDispatchThreshold` (squaring has no
        -- ratio dimension).
        let meanBitLength := configGetRat cfg "meanBitLength" 100000
        let nInputs := configGetNat cfg "nInputs" 400
        let _ ← tuneAzNatSquareDispatch (nInputs := nInputs)
                  (meanBitLength := meanBitLength) (seed := seed)
      | _ =>
        IO.eprintln s!"Unknown benchmark: '{name}'"
        IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
  | _ =>
    IO.eprintln "Usage: benchmark <name> <limit> [config]"
    IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
    IO.eprintln "Config example:   meanBitLength:64"

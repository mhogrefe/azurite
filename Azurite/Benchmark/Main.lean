import Azurite.Benchmark.RatCmp
import Azurite.Benchmark.AzPolynomialMul
import Azurite.Benchmark.AzPolynomialKaratsuba
import Azurite.AzPolynomial.Tune

-- ── Config parsing ──────────────────────────────────────────────────────────

def parseConfig (s : String) : Std.HashMap String String :=
  s.splitOn "," |>.foldl (init := {}) fun m entry =>
    match entry.splitOn ":" with
    | [k, v] => m.insert k.trimAscii.toString v.trimAscii.toString
    | _      => m

-- ── Main ────────────────────────────────────────────────────────────────────

def validBenchmarks : List String :=
  ["rat_cmp", "az_polynomial_mul", "az_polynomial_karatsuba",
   "tune_karatsuba", "tune_karatsuba_rat", "tune_karatsuba_zmod", "tune_karatsuba_all"]

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
      | _ =>
        IO.eprintln s!"Unknown benchmark: '{name}'"
        IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
  | _ =>
    IO.eprintln "Usage: benchmark <name> <limit> [config]"
    IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
    IO.eprintln "Config example:   meanBitLength:64"

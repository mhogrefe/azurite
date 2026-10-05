/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Benchmark.Common
import Azurite.Benchmark.AzPolynomialMul
import Azurite.Benchmark.AzPolynomialKaratsuba
import Azurite.Benchmark.CauchyIndexAlgorithms
import Azurite.Benchmark.AzNatAdd
import Azurite.Benchmark.AzNatAddModPow2
import Azurite.Benchmark.AzNatAddModPow2Residue
import Azurite.Benchmark.AzNatSubModPow2Residue
import Azurite.Benchmark.AzNatMulModPow2Residue
import Azurite.Benchmark.AzNatMulModPow2Algorithms
import Azurite.Benchmark.AzNatSquareModPow2Algorithms
import Azurite.Benchmark.AzNatSub
import Azurite.Benchmark.AzNatMulAlgorithms
import Azurite.Benchmark.AzNatMulAlgorithmsToomCook3
import Azurite.Benchmark.AzNatMulVsNat
import Azurite.Benchmark.AzNatSquareAlgorithms
import Azurite.Benchmark.AzNatSquareAlgorithmsToomCook3
import Azurite.Benchmark.AzNatSquareVsMul
import Azurite.Benchmark.AzNatSquareVsNat
import Azurite.Benchmark.AzNatPowAlgorithms
import Azurite.Benchmark.AzNatDivAlgorithms
import Azurite.Benchmark.AzNatDivCross
import Azurite.Benchmark.AzNatGcd
import Azurite.Benchmark.AzFloatToString
import Azurite.Benchmark.AzRatProfile
import Azurite.Benchmark.AzNatDivMod
import Azurite.Benchmark.AzNatDivVsDivMod
import Azurite.Benchmark.AzNatModVsDivMod
import Azurite.Benchmark.AzIntDivVsDivMod
import Azurite.Benchmark.AzIntModVsDivMod
import Azurite.Benchmark.UInt64SqrtRem
import Azurite.Benchmark.AzNatSqrtRemAlgorithms
import Azurite.Benchmark.AzNatSqrtVsNat
import Azurite.Benchmark.Aprcl
import Azurite.Benchmark.LimbWidth
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
  ["az_polynomial_mul", "az_polynomial_karatsuba", "cauchy_index_algorithms",
   "az_nat_add", "az_nat_add_mod_pow2", "az_nat_add_mod_pow2_residue",
   "az_nat_sub_mod_pow2_residue", "az_nat_mul_mod_pow2_residue",
   "az_nat_mul_mod_pow2_algorithms", "az_nat_square_mod_pow2_algorithms",
   "az_nat_sub", "az_nat_mul_vs_nat", "az_nat_mul_algorithms",
   "az_nat_mul_algorithms_toomcook3", "az_nat_div_algorithms", "az_nat_div_cross",
   "az_float_to_string", "az_rat_profile", "az_nat_gcd",
   "az_nat_div_mod", "az_nat_div_vs_div_mod",
   "az_nat_mod_vs_div_mod", "az_int_div_vs_div_mod", "az_int_mod_vs_div_mod",
   "uint64_sqrt_rem", "az_nat_sqrt_rem_algorithms", "az_nat_sqrt_vs_nat",
   "az_nat_square_vs_mul", "az_nat_square_algorithms",
   "az_nat_square_algorithms_toomcook3", "az_nat_square_vs_nat",
   "az_nat_pow_algorithms", "aprcl",
   "tune_karatsuba", "tune_karatsuba_rat", "tune_karatsuba_zmod", "tune_karatsuba_all",
   "tune_karatsuba_aznat", "tune_karatsuba_aznat_2d",
   "tune_aznat_square", "tune_aznat_mul_toomcook3", "tune_aznat_square_toomcook3",
   "tune_aznat_mul_toomcook4", "tune_aznat_square_toomcook4", "tune_aznat_unbalanced",
   "tune_aznat_mul_dispatch_compare", "tune_aznat_mul_toomcook4_dispatch",
   "tune_aznat_square_toomcook4_dispatch", "tune_aznat_karatsuba_crossover",
   "tune_aznat_toomcook3_crossover", "tune_aznat_square_karatsuba_crossover",
   "tune_aznat_square_toomcook3_crossover", "tune_aznat_mul_ladder_2d",
   "tune_aznat_square_ladder_2d", "tune_aznat_fft_crossover", "tune_aznat_square_fft_crossover",
   "tune_aznat_fft_dispatch", "az_nat_fft_profile", "az_fermat_ops_profile",
   "limb_width_experiment"]

/-- `MulThresholds` from the config keys `schoolbook`, `toomCook3`, `toomCook4`, `unbalanced`
(defaults: the production values). -/
def mulThresholdsFromConfig (cfg : Std.HashMap String String) : Azurite.AzNat.MulThresholds :=
  let d := Azurite.AzNat.defaultMulThresholds
  { schoolbook := configGetNat cfg "schoolbook" d.schoolbook,
    toomCook3 := configGetNat cfg "toomCook3" d.toomCook3,
    toomCook4 := configGetNat cfg "toomCook4" d.toomCook4,
    unbalanced := configGetNat cfg "unbalanced" d.unbalanced,
    fft := configGetNat cfg "fft" d.fft }

/-- A `/`-separated list of naturals from the config, e.g. `sizes:1024/2048/4096`. -/
def configGetNatList (cfg : Std.HashMap String String) (key : String) (default : Array Nat) :
    Array Nat :=
  match cfg[key]? with
  | some v => ((v.splitOn "/").filterMap fun t => t.trimAscii.toString.toNat?).toArray
  | none => default

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
      | "az_polynomial_mul" => runAzPolynomialMul limit cfg seed
      | "az_polynomial_karatsuba" => runAzPolynomialKaratsuba limit cfg seed
      | "cauchy_index_algorithms" => runCauchyIndexAlgorithms limit cfg seed
      | "aprcl" => Azurite.Benchmark.Aprcl.run limit cfg
      | "az_nat_add" => runAzNatAdd limit cfg seed
      | "az_nat_add_mod_pow2" => runAzNatAddModPow2 limit cfg seed
      | "az_nat_add_mod_pow2_residue" => runAzNatAddModPow2Residue limit cfg seed
      | "az_nat_sub_mod_pow2_residue" => runAzNatSubModPow2Residue limit cfg seed
      | "az_nat_mul_mod_pow2_residue" => runAzNatMulModPow2Residue limit cfg seed
      | "az_nat_mul_mod_pow2_algorithms" => runAzNatMulModPow2Algorithms limit cfg seed
      | "az_nat_square_mod_pow2_algorithms" => runAzNatSquareModPow2Algorithms limit cfg seed
      | "az_nat_sub" => runAzNatSub limit cfg seed
      | "az_nat_mul_vs_nat" => runAzNatMulVsNat limit cfg seed
      | "az_nat_mul_algorithms" => runAzNatMulAlgorithms limit cfg seed
      | "az_nat_mul_algorithms_toomcook3" => runAzNatMulAlgorithmsToomCook3 limit cfg seed
      | "az_nat_div_algorithms" => runAzNatDivAlgorithms limit cfg seed
      | "az_nat_div_cross" => Azurite.Benchmark.runAzNatDivCross limit cfg seed
      | "az_float_to_string" => Azurite.Benchmark.runAzFloatToString limit cfg seed
      | "az_rat_profile" => Azurite.Benchmark.runAzRatProfile limit cfg seed
      | "az_nat_gcd" => Azurite.Benchmark.runAzNatGcd limit cfg seed
      | "az_nat_div_mod" => runAzNatDivMod limit cfg seed
      | "az_nat_div_vs_div_mod" => runAzNatDivVsDivMod limit cfg seed
      | "az_nat_mod_vs_div_mod" => runAzNatModVsDivMod limit cfg seed
      | "az_int_div_vs_div_mod" => runAzIntDivVsDivMod limit cfg seed
      | "az_int_mod_vs_div_mod" => runAzIntModVsDivMod limit cfg seed
      | "uint64_sqrt_rem" => runUInt64SqrtRem limit cfg seed
      | "az_nat_sqrt_rem_algorithms" => runAzNatSqrtRemAlgorithms limit cfg seed
      | "az_nat_sqrt_vs_nat" => runAzNatSqrtVsNat limit cfg seed
      | "az_nat_square_vs_mul" => runAzNatSquareVsMul limit cfg seed
      | "az_nat_square_algorithms" => runAzNatSquareAlgorithms limit cfg seed
      | "az_nat_square_algorithms_toomcook3" =>
        runAzNatSquareAlgorithmsToomCook3 limit cfg seed
      | "az_nat_square_vs_nat" => runAzNatSquareVsNat limit cfg seed
      | "az_nat_pow_algorithms" => runAzNatPowAlgorithms limit cfg seed
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
      | "tune_aznat_mul_toomcook3" =>
        -- 1-D grid sweep over the Karatsuba ↔ Toom-Cook 3 dispatch cutoff
        -- (in limbs).  The heatmap suggests ~35 limbs (~2200 bits).
        let meanBitLength := configGetRat cfg "meanBitLength" 32768
        let nPairs := configGetNat cfg "nPairs" 200
        let _ ← tuneAzNatMulToomCook3 (nPairs := nPairs)
                  (meanBitLength := meanBitLength) (seed := seed)
      | "tune_aznat_square_toomcook3" =>
        -- 1-D grid sweep over the Karatsuba ↔ Toom-Cook 3 squaring dispatch
        -- cutoff (in limbs).  Mirrors `tune_aznat_mul_toomcook3` but
        -- single-input.
        let meanBitLength := configGetRat cfg "meanBitLength" 32768
        let nInputs := configGetNat cfg "nInputs" 400
        let _ ← tuneAzNatSquareToomCook3 (nInputs := nInputs)
                  (meanBitLength := meanBitLength) (seed := seed)
      | "tune_aznat_mul_toomcook4" =>
        -- Per-size Toom-3 vs top-level Toom-4 table (milestone 5 of the Toom ladder).
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let workLimbs := configGetNat cfg "workLimbs" 16384
        tuneAzNatMulToomCook4 (th := th) (workLimbs := workLimbs) (seed := seed)
      | "tune_aznat_square_toomcook4" =>
        let workLimbs := configGetNat cfg "workLimbs" 16384
        tuneAzNatSquareToomCook4 (workLimbs := workLimbs) (seed := seed)
      | "tune_aznat_unbalanced" =>
        -- Ratio-band table for the unbalanced strategies.
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let workLimbs := configGetNat cfg "workLimbs" 8192
        tuneAzNatUnbalanced (th := th) (workLimbs := workLimbs) (seed := seed)
      | "tune_aznat_mul_toomcook4_dispatch" =>
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let meanBitLength := configGetRat cfg "meanBitLength" 65536
        let nPairs := configGetNat cfg "nPairs" 200
        let balanceRatio := configGetNat cfg "balanceRatio" 75
        tuneAzNatMulToomCook4Dispatch (th := th) (nPairs := nPairs) (meanBitLength := meanBitLength)
          (balanceRatio := balanceRatio) (seed := seed)
      | "tune_aznat_square_toomcook4_dispatch" =>
        let meanBitLength := configGetRat cfg "meanBitLength" 65536
        let nInputs := configGetNat cfg "nInputs" 400
        let sb := configGetNat cfg "squareSchoolbook" Azurite.AzNat.squareDispatchThreshold
        let t3 := configGetNat cfg "squareToomCook3" Azurite.AzNat.squareDispatchToomCook3Cutoff
        tuneAzNatSquareToomCook4Dispatch (schoolbook := sb) (toomCook3 := t3) (nInputs := nInputs)
          (meanBitLength := meanBitLength) (seed := seed)
      | "tune_aznat_karatsuba_crossover" =>
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let workLimbs := configGetNat cfg "workLimbs" 65536
        tuneAzNatKaratsubaCrossover (th := th) (workLimbs := workLimbs) (seed := seed)
      | "tune_aznat_toomcook3_crossover" =>
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let workLimbs := configGetNat cfg "workLimbs" 65536
        tuneAzNatToomCook3Crossover (th := th) (workLimbs := workLimbs) (seed := seed)
      | "tune_aznat_square_karatsuba_crossover" =>
        let workLimbs := configGetNat cfg "workLimbs" 65536
        tuneAzNatSquareKaratsubaCrossover (workLimbs := workLimbs) (seed := seed)
      | "tune_aznat_square_toomcook3_crossover" =>
        let workLimbs := configGetNat cfg "workLimbs" 65536
        let kara := configGetNat cfg "squareSchoolbook" Azurite.AzNat.squareDispatchThreshold
        tuneAzNatSquareToomCook3Crossover (karatsubaCutoff := kara) (workLimbs := workLimbs)
          (seed := seed)
      | "tune_aznat_mul_ladder_2d" =>
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let meanBitLength := configGetRat cfg "meanBitLength" 16384
        let nPairs := configGetNat cfg "nPairs" 200
        let balanceRatio := configGetNat cfg "balanceRatio" 75
        tuneAzNatMulLadder2D (th := th) (nPairs := nPairs) (meanBitLength := meanBitLength)
          (balanceRatio := balanceRatio) (seed := seed)
      | "tune_aznat_square_ladder_2d" =>
        let meanBitLength := configGetRat cfg "meanBitLength" 16384
        let nInputs := configGetNat cfg "nInputs" 400
        let t4 := configGetNat cfg "squareToomCook4" Azurite.AzNat.squareDispatchToomCook4Cutoff
        tuneAzNatSquareLadder2D (toomCook4Cutoff := t4) (nInputs := nInputs)
          (meanBitLength := meanBitLength) (seed := seed)
      | "tune_aznat_mul_dispatch_compare" =>
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let nPairs := configGetNat cfg "nPairs" 100
        tuneAzNatMulDispatchCompare (th := th) (nPairs := nPairs) (seed := seed)
      | "tune_aznat_fft_crossover" =>
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let workLimbs := configGetNat cfg "workLimbs" 65536
        let kAdj := configGetNat cfg "kAdj" Azurite.AzNat.ssKAdjust
        let sizes := configGetNatList cfg "sizes"
          #[1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384, 32768]
        tuneAzNatFFTCrossover (th := th) (kAdj := kAdj) (sizes := sizes) (workLimbs := workLimbs)
          (seed := seed)
      | "limb_width_experiment" =>
        let sizes := configGetNatList cfg "sizes" #[4, 16, 64, 256, 1024]
        Azurite.Benchmark.LimbWidth.run sizes seed
      | "az_fermat_ops_profile" =>
        -- Micro-profile of the Fermat-ring primitives at `N` bits.
        let n := configGetNat cfg "N" 8704
        let count := configGetNat cfg "count" 2000
        profileAzFermatOps n count seed
      | "az_nat_fft_profile" =>
        -- Stage-by-stage profile of `fftMul` at one size and digit-count adjustment.
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let n := configGetNat cfg "n" 32768
        let kAdj := configGetNat cfg "kAdj" Azurite.AzNat.ssKAdjust
        let reps := configGetNat cfg "reps" 4
        profileAzNatFFT n kAdj th reps seed
      | "tune_aznat_square_fft_crossover" =>
        let workLimbs := configGetNat cfg "workLimbs" 65536
        let sb := configGetNat cfg "squareSchoolbook" Azurite.AzNat.squareDispatchThreshold
        let t3 := configGetNat cfg "squareToomCook3" Azurite.AzNat.squareDispatchToomCook3Cutoff
        let t4 := configGetNat cfg "squareToomCook4" Azurite.AzNat.squareDispatchToomCook4Cutoff
        let sizes := configGetNatList cfg "sizes"
          #[1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384, 32768]
        let kAdj := configGetNat cfg "kAdj" Azurite.AzNat.ssKAdjust
        tuneAzNatSquareFFTCrossover (schoolbook := sb) (toomCook3 := t3) (toomCook4 := t4)
          (kAdj := kAdj) (sizes := sizes) (workLimbs := workLimbs) (seed := seed)
      | "tune_aznat_fft_dispatch" =>
        let th : Azurite.AzNat.MulThresholds := mulThresholdsFromConfig cfg
        let meanBitLength := configGetRat cfg "meanBitLength" 524288
        let nPairs := configGetNat cfg "nPairs" 40
        let balanceRatio := configGetNat cfg "balanceRatio" 75
        tuneAzNatFFTDispatch (th := th) (nPairs := nPairs) (meanBitLength := meanBitLength)
          (balanceRatio := balanceRatio) (seed := seed)
      | _ =>
        IO.eprintln s!"Unknown benchmark: '{name}'"
        IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
  | _ =>
    IO.eprintln "Usage: benchmark <name> <limit> [config]"
    IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
    IO.eprintln "Config example:   meanBitLength:64"

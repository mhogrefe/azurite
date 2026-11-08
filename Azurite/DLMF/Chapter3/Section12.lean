/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.ConstantKernel
import Azurite.DLMF.Chapter3.Section11LebesgueNum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# DLMF §3.12: Mathematical constants

Formalizations of <https://dlmf.nist.gov/3.12>.

* 3.12.1: `π = 3.14159 26535 89793 23846 …` (`dlmf_3_12_1`, all 20 decimals, from the AzFloat
  enclosure `Encl.pi 128`, computed in the kernel: `pi128_data`).
* 3.12.2: `π = 4 ∫₀¹ dt/(1 + t²)` (`dlmf_3_12_2`).
* 3.12.3: `e = 2.71828 18284 59045 23536 …` (`dlmf_3_12_3`, `e = exp 1` as in §4.2(ii), all 20
  decimals, from AzFloat's correctly rounded `ePrecRound 80` rounded down and up, evaluated in the
  kernel through Ziv's loop with fuel: `e80_data`, `const_eq_zivLoop`).
* 3.12.4: `γ = 0.57721 56649 01532 86060 …` (`Real.eulerMascheroniConstant`, the limit of
  `H_n − ln n` as in §5.2(ii): `dlmf_3_12_4_def`). Only the first five decimals are certified
  (`dlmf_3_12_4_partial`, from the bounds `euler_bounds` of §3.11(ii)); the full 20 decimals are
  deferred until Euler's constant can be computed to that precision.

Sloane (2003) and Finch (2003) are references.
-/

open Real Finset

namespace Azurite.DLMF

open Azurite.AzFloat Encl

set_option maxRecDepth 100000 in
/-- The ends of the 128-bit AzFloat enclosure of `π`. -/
theorem pi128_data :
    (valData (Encl.pi 128).1, valData (Encl.pi 128).2) =
      (some (true, 73463084912771502742156883195892978055257890456097,
          23384026197294446691258957323460528314494920687616),
        some (true, 73463084912771502742156883195892978055275070325281,
          23384026197294446691258957323460528314494920687616)) := by
  decide +kernel

/-- **DLMF 3.12.1**: `π = 3.14159 26535 89793 23846 …`. -/
theorem dlmf_3_12_1 : 3.14159265358979323846 < π ∧ π < 3.14159265358979323847 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj pi128_data
  obtain ⟨l, u⟩ := (enclosesPos_pi (w := 128) (by norm_num)).encloses0.encloses.bounds d1 d2
  simp only [signedVal, ite_true] at l u
  refine ⟨lt_of_lt_of_le ?_ l, lt_of_le_of_lt u ?_⟩ <;> norm_num

/-- **DLMF 3.12.2**: `π = 4 ∫₀¹ dt/(1 + t²)`. -/
theorem dlmf_3_12_2 : π = 4 * ∫ t in (0 : ℝ)..1, 1 / (1 + t ^ 2) := by
  rw [integral_one_div_one_add_sq, arctan_one, arctan_zero]
  ring

set_option maxRecDepth 100000 in
/-- `e` at 80 bits, rounded down and up (Ziv's loop with fuel, first attempt at 144 bits). -/
theorem e80_data :
    (valData (zivLoop (expApprox one 1) 80 .Floor 3 144).1,
        valData (zivLoop (expApprox one 1) 80 .Ceiling 3 144).1) =
      (some (true, 205387567963337755372535, 75557863725914323419136),
        some (true, 821550271853351021490141, 302231454903657293676544)) := by
  decide +kernel

/-- **DLMF 3.12.3**: `e = 2.71828 18284 59045 23536 …` (`e = exp 1`, §4.2(ii)), from AzFloat's
correctly rounded `ePrecRound 80`, rounded down and up. -/
theorem dlmf_3_12_3 :
    2.71828182845904523536 < Real.exp 1 ∧ Real.exp 1 < 2.71828182845904523537 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj e80_data
  have hF := const_eq_zivLoop eApprox_ok (ePrecRound_eq_liftVal₀ 80 .Floor) (by norm_num) d1
  have hC := const_eq_zivLoop eApprox_ok (ePrecRound_eq_liftVal₀ 80 .Ceiling) (by norm_num) d2
  have l := le_of_floor_data (ePrecRound_eq_liftVal₀ 80 .Floor) (hF ▸ d1)
  have u := ge_of_ceiling_data (ePrecRound_eq_liftVal₀ 80 .Ceiling) (hC ▸ d2)
  push_cast at l u
  exact ⟨lt_of_lt_of_le (by norm_num) l, lt_of_le_of_lt u (by norm_num)⟩

/-- **DLMF 3.12.4**, definition (§5.2(ii)): `γ = lim (1 + 1/2 + ⋯ + 1/n − ln n)`. -/
theorem dlmf_3_12_4_def :
    Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - log n) Filter.atTop
      (nhds eulerMascheroniConstant) :=
  tendsto_harmonic_sub_log

/-- **DLMF 3.12.4**, first five decimals: `γ = 0.57721 …`. The full 20 decimals
`0.57721 56649 01532 86060 …` are deferred. -/
theorem dlmf_3_12_4_partial :
    0.57721 < eulerMascheroniConstant ∧ eulerMascheroniConstant < 0.57722 := by
  obtain ⟨h1, h2⟩ := euler_bounds
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

end Azurite.DLMF

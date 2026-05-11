import Azurite.UInt64.Equiv.Basic
import Azurite.UInt64.Equiv.IsMultipleOfPow2
import Azurite.UInt64.Equiv.ShiftRightRound
import Azurite.UInt64.Equiv.WideMul
import Azurite.UInt64.Reciprocal
import Mathlib.Tactic.LinearCombination

namespace UInt64

/-! ### toNat-level identities for the `compute*` helpers. -/

/-- `computeD9 d` reads as `d.toNat / 2^55` on the Nat side. -/
theorem toNat_computeD9 (d : UInt64) :
    (computeD9 d).toNat = d.toNat / 2 ^ 55 := by
  unfold computeD9
  rw [_root_.UInt64.toNat_shiftRight]
  have h55 : ((55 : UInt64).toNat) = 55 := rfl
  rw [h55, Nat.shiftRight_eq_div_pow]

/-- `computeD40 d` reads as `d.toNat / 2^24 + 1` on the Nat side. -/
theorem toNat_computeD40 (d : UInt64) :
    (computeD40 d).toNat = d.toNat / 2 ^ 24 + 1 := by
  unfold computeD40
  rw [_root_.UInt64.toNat_add, _root_.UInt64.toNat_shiftRight]
  have h24 : ((24 : UInt64).toNat) = 24 := rfl
  rw [h24, Nat.shiftRight_eq_div_pow, show ((1 : UInt64).toNat = 1) from rfl]
  have hd : d.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hq : d.toNat / 2 ^ 24 < 2 ^ 40 := by
    have h1 : d.toNat / 2 ^ 24 * 2 ^ 24 ≤ d.toNat := Nat.div_mul_le_self _ _
    have hlt : d.toNat / 2 ^ 24 * 2 ^ 24 < 2 ^ 64 := lt_of_le_of_lt h1 hd
    have h2pow : (2 : ℕ) ^ 64 = 2 ^ 40 * 2 ^ 24 := by norm_num
    rw [h2pow] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hbound : d.toNat / 2 ^ 24 + 1 < 2 ^ 64 := by
    have : (2 : ℕ) ^ 40 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  exact Nat.mod_eq_of_lt hbound

/-- Bounds on `d9` when `d` is normalized (top bit set). -/
theorem computeD9_bounds (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    256 ≤ (computeD9 d).toNat ∧ (computeD9 d).toNat ≤ 511 := by
  rw [toNat_computeD9]
  have hd_lt : d.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  refine ⟨?_, ?_⟩
  · calc 256 = 2 ^ 63 / 2 ^ 55 := by norm_num
      _ ≤ d.toNat / 2 ^ 55 := Nat.div_le_div_right hd
  · have h1 : d.toNat / 2 ^ 55 * 2 ^ 55 ≤ d.toNat := Nat.div_mul_le_self _ _
    have h2pow : (2 : ℕ) ^ 64 = 2 ^ 9 * 2 ^ 55 := by norm_num
    have hlt : d.toNat / 2 ^ 55 * 2 ^ 55 < 2 ^ 64 := lt_of_le_of_lt h1 hd_lt
    rw [h2pow] at hlt
    have : d.toNat / 2 ^ 55 < 2 ^ 9 := Nat.lt_of_mul_lt_mul_right hlt
    omega

/-- Bounds on `d40` when `d` is normalized. -/
theorem computeD40_bounds (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    2 ^ 39 + 1 ≤ (computeD40 d).toNat ∧ (computeD40 d).toNat ≤ 2 ^ 40 := by
  rw [toNat_computeD40]
  have hd_lt : d.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  refine ⟨?_, ?_⟩
  · have h1 : 2 ^ 63 / 2 ^ 24 ≤ d.toNat / 2 ^ 24 := Nat.div_le_div_right hd
    have heq : (2 : ℕ) ^ 63 / 2 ^ 24 = 2 ^ 39 := by norm_num
    omega
  · have h1 : d.toNat / 2 ^ 24 * 2 ^ 24 ≤ d.toNat := Nat.div_mul_le_self _ _
    have h2pow : (2 : ℕ) ^ 64 = 2 ^ 40 * 2 ^ 24 := by norm_num
    have hlt : d.toNat / 2 ^ 24 * 2 ^ 24 < 2 ^ 64 := lt_of_le_of_lt h1 hd_lt
    rw [h2pow] at hlt
    have : d.toNat / 2 ^ 24 < 2 ^ 40 := Nat.lt_of_mul_lt_mul_right hlt
    omega

/-- `d40 = 2^31 · d9 + d'` with `1 ≤ d' ≤ 2^31`. -/
theorem computeD40_split (d : UInt64) (_hd : 2 ^ 63 ≤ d.toNat) :
    (computeD40 d).toNat = 2 ^ 31 * (computeD9 d).toNat +
      ((computeD40 d).toNat - 2 ^ 31 * (computeD9 d).toNat) ∧
    1 ≤ (computeD40 d).toNat - 2 ^ 31 * (computeD9 d).toNat ∧
    (computeD40 d).toNat - 2 ^ 31 * (computeD9 d).toNat ≤ 2 ^ 31 := by
  rw [toNat_computeD40, toNat_computeD9]
  have hd_lt : d.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  -- d.toNat / 2^24 = 2^31 * (d.toNat / 2^55) + ((d.toNat / 2^24) mod 2^31).
  have hdd : d.toNat / 2 ^ 24 / 2 ^ 31 = d.toNat / 2 ^ 55 := by
    rw [Nat.div_div_eq_div_mul]; norm_num
  have hmod_lt : d.toNat / 2 ^ 24 % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hsplit : d.toNat / 2 ^ 24 =
      2 ^ 31 * (d.toNat / 2 ^ 55) + d.toNat / 2 ^ 24 % 2 ^ 31 := by
    have := Nat.div_add_mod (d.toNat / 2 ^ 24) (2 ^ 31)
    omega
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- `computeD0 d` reads as `d.toNat % 2` on the Nat side. -/
theorem toNat_computeD0 (d : UInt64) :
    (computeD0 d).toNat = d.toNat % 2 := by
  unfold computeD0
  rw [_root_.UInt64.toNat_and, show ((1 : UInt64).toNat = 1) from rfl, Nat.and_one_is_mod]

/-- `computeD63 d` reads as `⌈d.toNat / 2⌉ = (d.toNat + 1) / 2` on the Nat side. -/
theorem toNat_computeD63 (d : UInt64) :
    (computeD63 d).toNat = (d.toNat + 1) / 2 := by
  unfold computeD63
  rw [shiftRightRound_fst]
  by_cases h : d.isMultipleOfPow2 1 = true
  · rw [if_pos h, toNat_shiftRightSat]
    have hdvd : 2 ^ 1 ∣ d.toNat := (isMultipleOfPow2_iff d 1).mp h
    omega
  · rw [if_neg h, toNat_shiftRightSat_add_one d 1 (by omega)]
    have hndvd : ¬ (2 ^ 1 ∣ d.toNat) :=
      fun hdvd => h ((isMultipleOfPow2_iff d 1).mpr hdvd)
    omega

set_option maxRecDepth 2000 in
/-- `(computeV0 d9 h).toNat = (2^19 − 3·2^8) / d9.toNat` when `d9 ∈ [256, 511]`. -/
theorem toNat_computeV0 (d9 : UInt64) (h : (d9 - 256).toNat < 256)
    (h256 : 256 ≤ d9.toNat) (h511 : d9.toNat ≤ 511) :
    (computeV0 d9 h).toNat = (2 ^ 19 - 3 * 2 ^ 8) / d9.toNat := by
  unfold computeV0
  have hsize : (d9 - 256).toNat < reciprocalTable.size :=
    reciprocalTable_size.symm ▸ h
  -- Convert proof-bounded access to `[...]!` so the rewrite below goes through.
  rw [show reciprocalTable[(d9 - 256).toNat]'hsize
        = reciprocalTable[(d9 - 256).toNat]! from
      (getElem!_pos reciprocalTable (d9 - 256).toNat hsize).symm]
  rw [reciprocalTable_eq]
  have hidx_size : (d9 - 256).toNat < (Array.ofFn (n := 256)
      fun i => ((2 ^ 19 - 3 * 2 ^ 8) / (i.val + 256) : Nat).toUInt16).size := by
    simpa using h
  rw [getElem!_pos _ (d9 - 256).toNat hidx_size, Array.getElem_ofFn]
  have hsub_eq : (d9 - 256).toNat + 256 = d9.toNat := by
    rw [_root_.UInt64.toNat_sub]
    show ((2 ^ 64 - (256 : UInt64).toNat + d9.toNat) % 2 ^ 64) + 256 = d9.toNat
    have h256' : ((256 : UInt64).toNat) = 256 := rfl
    rw [h256']
    have hstep : 2 ^ 64 - 256 + d9.toNat = 2 ^ 64 + (d9.toNat - 256) := by omega
    rw [hstep, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [hsub_eq]
  have hval_lt : (2 ^ 19 - 3 * 2 ^ 8) / d9.toNat < 2 ^ 16 := by
    have h1 : (2 ^ 19 - 3 * 2 ^ 8) / d9.toNat ≤ (2 ^ 19 - 3 * 2 ^ 8) / 256 :=
      Nat.div_le_div_left h256 (by norm_num)
    have h2 : (2 ^ 19 - 3 * 2 ^ 8) / 256 = 2045 := by norm_num
    omega
  show ((2 ^ 19 - 3 * 2 ^ 8) / d9.toNat) % 2 ^ 16 = _
  exact Nat.mod_eq_of_lt hval_lt

/-! ### The error `e0 = 2^50 − v_0 d_{40}` and Bound 6. -/

/-- `e0 = 2^50 − v_0 · d_{40}` as an integer (can be negative). -/
def e0 (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) : ℤ :=
  (2 ^ 50 : ℤ) -
    ((computeV0 (computeD9 d) (computeD9_sub_256_lt d hd)).toNat : ℤ)
      * ((computeD40 d).toNat : ℤ)

/-- Bound 6 from Möller–Granlund: `|e0| < 5·2^39` (i.e. `(5/8)·2^42`), assuming
`d` is normalized (`2^63 ≤ d`). -/
theorem abs_e0_lt (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    |e0 d hd| < 5 * 2 ^ 39 := by
  -- Set up Nat variables for d9, d40, v0.
  set d9 := (computeD9 d).toNat with hd9_def
  set d40 := (computeD40 d).toNat with hd40_def
  set v0 := (computeV0 (computeD9 d) (computeD9_sub_256_lt d hd)).toNat with hv0_def
  -- Bounds on d9.
  obtain ⟨hd9_lo, hd9_hi⟩ := computeD9_bounds d hd
  -- Bounds on d40, and the split d40 = 2^31·d9 + d'.
  obtain ⟨hd40_lo, hd40_hi⟩ := computeD40_bounds d hd
  obtain ⟨hd40_split, hd'_lo, hd'_hi⟩ := computeD40_split d hd
  set d' := d40 - 2 ^ 31 * d9 with hd'_def
  -- v0 = T / d9 where T = 2^19 - 3·2^8.
  have hv0_eq : v0 = (2 ^ 19 - 3 * 2 ^ 8) / d9 :=
    toNat_computeV0 _ (computeD9_sub_256_lt d hd) hd9_lo hd9_hi
  set T : ℕ := 2 ^ 19 - 3 * 2 ^ 8 with hT_def
  set r : ℕ := T % d9 with hr_def
  have hT_val : T = 523520 := by norm_num [hT_def]
  have hr_lt : r < d9 := Nat.mod_lt _ (by omega)
  -- v0 · d9 = T − r.
  have hv0_d9 : v0 * d9 = T - r := by
    have h := Nat.div_add_mod T d9
    rw [hv0_eq, hr_def, Nat.mul_comm]
    omega
  -- v0 ≤ 2045.
  have hv0_le : v0 ≤ 2045 := by
    have h1 : T / d9 ≤ T / 256 := Nat.div_le_div_left hd9_lo (by norm_num)
    have hT256 : T / 256 = 2045 := by norm_num [hT_def]
    omega
  -- Unfold e0 and substitute v0, d40.
  unfold e0
  rw [← hd40_def, ← hv0_def]
  -- Replace d40 = 2^31·d9 + d' (at ℤ level).
  have hd40_eq : (d40 : ℤ) = (2 ^ 31 : ℤ) * d9 + d' := by exact_mod_cast hd40_split
  rw [hd40_eq]
  -- Algebraic identity: 2^50 − v0·(2^31·d9 + d') = 3·2^39 + r·2^31 − v0·d'.
  have hv0d9 : (v0 : ℤ) * d9 = T - r := by
    have hle_Tr : r ≤ T := Nat.le_of_lt (lt_of_lt_of_le hr_lt (by omega))
    have hint : ((v0 * d9 : ℕ) : ℤ) = ((T - r : ℕ) : ℤ) := by exact_mod_cast hv0_d9
    rw [Int.ofNat_sub hle_Tr] at hint
    push_cast at hint
    linarith
  have hT31 : (T : ℤ) * 2 ^ 31 = 2 ^ 50 - 3 * 2 ^ 39 := by
    have : (T : ℤ) = 523520 := by exact_mod_cast hT_val
    rw [this]; norm_num
  have hkey :
      (2 ^ 50 : ℤ) - v0 * (2 ^ 31 * d9 + d') = 3 * 2 ^ 39 + r * 2 ^ 31 - v0 * d' := by
    have h1 : (v0 : ℤ) * (2 ^ 31 * d9 + d') = v0 * d9 * 2 ^ 31 + v0 * d' := by ring
    rw [h1, hv0d9]
    have h2 : ((T - r : ℤ)) * 2 ^ 31 = T * 2 ^ 31 - r * 2 ^ 31 := by ring
    rw [h2, hT31]; ring
  rw [hkey]
  -- Upper bound on r·2^31.
  have h_r31 : (r : ℤ) * 2 ^ 31 < 2 * 2 ^ 39 := by
    have hr_le_510 : (r : ℤ) ≤ 510 := by
      have hr_int : (r : ℤ) < (d9 : ℤ) := by exact_mod_cast hr_lt
      have hd9_int : (d9 : ℤ) ≤ 511 := by exact_mod_cast hd9_hi
      linarith
    have h510_31 : (510 : ℤ) * 2 ^ 31 < 2 * 2 ^ 39 := by norm_num
    have : (r : ℤ) * 2 ^ 31 ≤ 510 * 2 ^ 31 := by
      have : (0 : ℤ) ≤ 2 ^ 31 := by norm_num
      nlinarith
    linarith
  -- Lower bound: v0·d' ≤ 2045·2^31 < 8·2^39.
  have h0v : (0 : ℤ) ≤ (v0 : ℤ) := Int.natCast_nonneg _
  have h0d' : (0 : ℤ) ≤ (d' : ℤ) := Int.natCast_nonneg _
  have h0r : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg _
  have h_v0d'_lt : (v0 : ℤ) * d' < 8 * 2 ^ 39 := by
    have hv0_le_int : (v0 : ℤ) ≤ 2045 := by exact_mod_cast hv0_le
    have hd'_le_int : (d' : ℤ) ≤ 2 ^ 31 := by exact_mod_cast hd'_hi
    calc (v0 : ℤ) * d' ≤ 2045 * 2 ^ 31 := by nlinarith
      _ < 8 * 2 ^ 39 := by norm_num
  have h_v0d'_nn : (0 : ℤ) ≤ (v0 : ℤ) * d' := mul_nonneg h0v h0d'
  have h_r31_nn : (0 : ℤ) ≤ (r : ℤ) * 2 ^ 31 := mul_nonneg h0r (by norm_num)
  rw [abs_lt]
  refine ⟨?_, ?_⟩ <;> linarith

/-! ### The error `e1 = 2^60 − v_1 d_{40}` and Bound 7. -/

/-- `toNat` identity for `computeV1`, assuming no overflow / underflow.
The hypotheses match the invariants used in Möller–Granlund: `v0 ≤ 2045`
(so `v0 < 2^11`), `d40 ≤ 2^40`, and the second-estimate stays non-negative
after the `−1`. -/
theorem toNat_computeV1 (v0 : UInt16) (d40 : UInt64)
    (hv0 : v0.toNat ≤ 2045)
    (hd40 : d40.toNat ≤ 2 ^ 40)
    (h_under : v0.toNat ^ 2 * d40.toNat / 2 ^ 40 + 1 ≤ v0.toNat * 2 ^ 11) :
    (computeV1 v0 d40).toNat =
      v0.toNat * 2 ^ 11 - v0.toNat ^ 2 * d40.toNat / 2 ^ 40 - 1 := by
  set V : ℕ := v0.toNat with hV_def
  set D : ℕ := d40.toNat with hD_def
  have hVcast : v0.toUInt64.toNat = V := UInt16.toNat_toUInt64 v0
  -- Rewrite computeV1 into a flat concrete form.
  have hV1_form : computeV1 v0 d40 =
      v0.toUInt64 <<< 11 - (v0.toUInt64 * v0.toUInt64 * d40) >>> 40 - 1 := by
    unfold computeV1; rfl
  rw [hV1_form]
  -- v0*v0 doesn't overflow: V² ≤ 2045² < 2^22 < 2^64.
  have hV2_lt : V * V < 2 ^ 64 := by nlinarith
  have hsq : (v0.toUInt64 * v0.toUInt64).toNat = V * V := by
    rw [_root_.UInt64.toNat_mul, hVcast, Nat.mod_eq_of_lt hV2_lt]
  -- v0² * d40 doesn't overflow: ≤ 2^22 · 2^40 = 2^62 < 2^64.
  have hVVD_lt : V * V * D < 2 ^ 64 := by nlinarith
  have hprod : (v0.toUInt64 * v0.toUInt64 * d40).toNat = V * V * D := by
    rw [_root_.UInt64.toNat_mul, hsq, Nat.mod_eq_of_lt hVVD_lt]
  -- (prod >>> 40).toNat = V² · D / 2^40.
  have h40 : ((40 : UInt64).toNat) = 40 := rfl
  have hshr : ((v0.toUInt64 * v0.toUInt64 * d40) >>> 40).toNat = V * V * D / 2 ^ 40 := by
    rw [_root_.UInt64.toNat_shiftRight, hprod, h40]
    show (V * V * D) >>> ((40 : ℕ) % 64) = V * V * D / 2 ^ 40
    rw [show (40 : ℕ) % 64 = 40 from rfl, Nat.shiftRight_eq_div_pow]
  -- (v0 <<< 11).toNat = V · 2^11, no overflow.
  have h11 : ((11 : UInt64).toNat) = 11 := rfl
  have hshl_bd : V * 2 ^ 11 < 2 ^ 64 := by nlinarith
  have hshl : (v0.toUInt64 <<< 11).toNat = V * 2 ^ 11 := by
    rw [_root_.UInt64.toNat_shiftLeft, hVcast, h11]
    show V <<< ((11 : ℕ) % 64) % 2 ^ 64 = V * 2 ^ 11
    rw [show (11 : ℕ) % 64 = 11 from rfl, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt hshl_bd
  -- h_under as V·V·D form.
  have hVV_eq : V ^ 2 * D = V * V * D := by ring
  rw [hVV_eq] at h_under
  have h_under_le : V * V * D / 2 ^ 40 ≤ V * 2 ^ 11 := by omega
  -- First subtraction: (v0 <<< 11) - (prod >>> 40).
  have hinter :
      (v0.toUInt64 <<< 11 - (v0.toUInt64 * v0.toUInt64 * d40) >>> 40).toNat
        = V * 2 ^ 11 - V * V * D / 2 ^ 40 := by
    rw [_root_.UInt64.toNat_sub, hshl, hshr]
    have hstep : 2 ^ 64 - V * V * D / 2 ^ 40 + V * 2 ^ 11
        = 2 ^ 64 + (V * 2 ^ 11 - V * V * D / 2 ^ 40) := by omega
    rw [hstep, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  -- Final subtraction: ... - 1.
  rw [_root_.UInt64.toNat_sub]
  have h1_toNat : ((1 : UInt64).toNat) = 1 := rfl
  rw [h1_toNat, hinter]
  have hstep2 : 2 ^ 64 - 1 + (V * 2 ^ 11 - V * V * D / 2 ^ 40)
      = 2 ^ 64 + (V * 2 ^ 11 - V * V * D / 2 ^ 40 - 1) := by omega
  rw [hstep2, Nat.add_mod_left]
  have hmod_lt : V * 2 ^ 11 - V * V * D / 2 ^ 40 - 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hmod_lt]
  have : V ^ 2 * D = V * V * D := by ring
  omega

/-- `e1 = 2^60 − v_1 · d_{40}` as an integer. -/
def e1 (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) : ℤ :=
  (2 ^ 60 : ℤ) -
    ((computeV1 (computeV0 (computeD9 d) (computeD9_sub_256_lt d hd))
        (computeD40 d)).toNat : ℤ) *
    ((computeD40 d).toNat : ℤ)

/-- Bound 7 from Möller–Granlund: `0 < e1 < 29·2^38` (i.e. `(29/32)·2^43`),
assuming `d` is normalized (`2^63 ≤ d`). -/
theorem e1_pos_and_lt (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    0 < e1 d hd ∧ e1 d hd < 29 * 2 ^ 38 := by
  set d9 := (computeD9 d).toNat with hd9_def
  set d40 := (computeD40 d).toNat with hd40_def
  set v0 := computeV0 (computeD9 d) (computeD9_sub_256_lt d hd) with hv0_def
  set V : ℕ := v0.toNat with hV_def
  obtain ⟨hd9_lo, hd9_hi⟩ := computeD9_bounds d hd
  obtain ⟨hd40_lo, hd40_hi⟩ := computeD40_bounds d hd
  have hV_eq : V = (2 ^ 19 - 3 * 2 ^ 8) / d9 :=
    toNat_computeV0 _ (computeD9_sub_256_lt d hd) hd9_lo hd9_hi
  have hV_le : V ≤ 2045 := by
    have h1 : (2 ^ 19 - 3 * 2 ^ 8) / d9 ≤ (2 ^ 19 - 3 * 2 ^ 8) / 256 :=
      Nat.div_le_div_left hd9_lo (by norm_num)
    have h2 : (2 ^ 19 - 3 * 2 ^ 8) / 256 = 2045 := by norm_num
    omega
  -- Bound 6 gives |e0| < 5·2^39.
  have habs := abs_e0_lt d hd
  have he0_def : e0 d hd = (2 ^ 50 : ℤ) - (V : ℤ) * (d40 : ℤ) := rfl
  rw [he0_def, abs_lt] at habs
  obtain ⟨he0_lo, he0_hi⟩ := habs
  -- V · d40 < 2^51.
  have hVd40_lt_nat : V * d40 < 2 ^ 50 + 5 * 2 ^ 39 := by
    have : (V : ℤ) * d40 < 2 ^ 50 + 5 * 2 ^ 39 := by linarith
    exact_mod_cast this
  have hVd40_lt51 : V * d40 < 2 ^ 51 := by omega
  -- V > 0: V·d40 > 2^50 - 5·2^39 > 0 implies V > 0.
  have hV_pos : 0 < V := by
    rcases Nat.eq_zero_or_pos V with hV0 | hV1
    · exfalso
      have hpos_lb : (2 ^ 50 : ℤ) - 5 * 2 ^ 39 < (V : ℤ) * d40 := by linarith
      have hV0_int : (V : ℤ) = 0 := by exact_mod_cast hV0
      rw [hV0_int] at hpos_lb
      norm_num at hpos_lb
    · exact hV1
  -- V² · d40 < V · 2^51.
  have hV2d40_lt : V ^ 2 * d40 < V * 2 ^ 51 := by
    have hVV : V ^ 2 * d40 = V * (V * d40) := by ring
    rw [hVV]; nlinarith [hVd40_lt51, hV_pos]
  -- h_under: V² · d40 / 2^40 + 1 ≤ V · 2^11.
  have h_under : V ^ 2 * d40 / 2 ^ 40 + 1 ≤ V * 2 ^ 11 := by
    have hdiv : V ^ 2 * d40 / 2 ^ 40 < V * 2 ^ 11 := by
      apply Nat.div_lt_of_lt_mul
      have heq : 2 ^ 40 * (V * 2 ^ 11) = V * 2 ^ 51 := by ring
      rw [heq]; exact hV2d40_lt
    omega
  -- Apply toNat_computeV1.
  have hV1_eq : (computeV1 v0 (computeD40 d)).toNat
      = V * 2 ^ 11 - V ^ 2 * d40 / 2 ^ 40 - 1 :=
    toNat_computeV1 v0 (computeD40 d) hV_le hd40_hi h_under
  -- Simplify e1 to the chosen V, d40 vars.
  unfold e1
  rw [← hd40_def, ← hv0_def, hV1_eq]
  set V1 : ℕ := V * 2 ^ 11 - V ^ 2 * d40 / 2 ^ 40 - 1 with hV1_def
  set q1 : ℕ := V ^ 2 * d40 / 2 ^ 40 with hq1_def
  set r1 : ℕ := V ^ 2 * d40 % 2 ^ 40 with hr1_def
  have hr1_lt : r1 < 2 ^ 40 := Nat.mod_lt _ (by norm_num)
  have hqr : V ^ 2 * d40 = q1 * 2 ^ 40 + r1 := by
    have h := Nat.div_add_mod (V ^ 2 * d40) (2 ^ 40)
    omega
  -- V1 as Int identity.
  have hV1_int : (V1 : ℤ) = (V : ℤ) * 2 ^ 11 - (q1 : ℤ) - 1 := by
    have hnat_id : V1 + q1 + 1 = V * 2 ^ 11 := by
      show V * 2 ^ 11 - V ^ 2 * d40 / 2 ^ 40 - 1 + q1 + 1 = V * 2 ^ 11
      omega
    have h_cast : ((V1 + q1 + 1 : ℕ) : ℤ) = ((V * 2 ^ 11 : ℕ) : ℤ) := by
      exact_mod_cast hnat_id
    push_cast at h_cast
    linarith
  set E1 : ℤ := (2 ^ 60 : ℤ) - (V1 : ℤ) * (d40 : ℤ) with hE1_def
  show 0 < E1 ∧ E1 < 29 * 2 ^ 38
  -- Set up the key identity: 2^40·E1 = e0² + (2^40 − r1)·d40.
  have hqr_int : (V : ℤ) ^ 2 * d40 = (q1 : ℤ) * 2 ^ 40 + r1 := by exact_mod_cast hqr
  have hr1_lt_int : (r1 : ℤ) < 2 ^ 40 := by exact_mod_cast hr1_lt
  have hd40_pos_int : (0 : ℤ) < d40 := by
    have : 1 ≤ d40 := by omega
    exact_mod_cast this
  have hr1_nn : (0 : ℤ) ≤ r1 := Int.natCast_nonneg _
  have hE1_identity : (2 ^ 40 : ℤ) * E1 =
      ((2 ^ 50 : ℤ) - (V : ℤ) * d40) ^ 2 + (2 ^ 40 - r1) * d40 := by
    rw [hE1_def, hV1_int]
    have h_qr : (q1 : ℤ) * 2 ^ 40 = (V : ℤ) ^ 2 * d40 - r1 := by linarith
    nlinarith [h_qr, sq_nonneg ((2 ^ 50 : ℤ) - (V : ℤ) * d40)]
  -- Lower bound: E1 > 0.
  have he0_sq_nn : (0 : ℤ) ≤ ((2 ^ 50 : ℤ) - (V : ℤ) * d40) ^ 2 := sq_nonneg _
  have h_factor_pos : (0 : ℤ) < (2 ^ 40 - r1) * d40 :=
    mul_pos (by linarith) hd40_pos_int
  have hE1_mul_pos : (0 : ℤ) < (2 ^ 40 : ℤ) * E1 := by linarith
  have h240_pos : (0 : ℤ) < (2 ^ 40 : ℤ) := by norm_num
  have hE1_pos : (0 : ℤ) < E1 := by
    by_contra hle
    have hle' : E1 ≤ 0 := not_lt.mp hle
    have : (2 ^ 40 : ℤ) * E1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h240_pos) hle'
    linarith
  -- Upper bound: E1 < 29·2^38.
  have hd40_le_int : (d40 : ℤ) ≤ 2 ^ 40 := by exact_mod_cast hd40_hi
  have hd40_nn : (0 : ℤ) ≤ d40 := le_of_lt hd40_pos_int
  clear_value E1 V1 q1 r1 V d40
  clear hd9_def hd40_def hv0_def hV_def hV_eq hV_le hd9_lo hd9_hi hd40_lo
    hVd40_lt_nat hVd40_lt51 hV_pos hV2d40_lt hV1_eq h_under hV1_def hq1_def
    hr1_def hr1_lt hqr hqr_int he0_def he0_sq_nn h_factor_pos hE1_mul_pos
    hE1_def hV1_int
  have he0_sq_lt : ((2 ^ 50 : ℤ) - (V : ℤ) * d40) ^ 2 < 25 * 2 ^ 78 := by
    have hsq_bd : ((2 ^ 50 : ℤ) - (V : ℤ) * d40) ^ 2 < (5 * 2 ^ 39) ^ 2 :=
      sq_lt_sq' (by linarith only [he0_lo]) (by linarith only [he0_hi])
    have h25 : ((5 : ℤ) * 2 ^ 39) ^ 2 = 25 * 2 ^ 78 := by norm_num
    linarith only [hsq_bd, h25]
  have hfactor_step1 : (2 ^ 40 - r1 : ℤ) * d40 ≤ 2 ^ 40 * d40 :=
    mul_le_mul_of_nonneg_right (by linarith only [hr1_nn]) hd40_nn
  have hfactor_step2 : (2 ^ 40 : ℤ) * d40 ≤ 2 ^ 40 * 2 ^ 40 :=
    mul_le_mul_of_nonneg_left hd40_le_int (by norm_num)
  have h_factor_le : (2 ^ 40 - r1 : ℤ) * d40 ≤ 2 ^ 80 := by
    have h3 : (2 ^ 40 : ℤ) * 2 ^ 40 = 2 ^ 80 := by norm_num
    linarith only [hfactor_step1, hfactor_step2, h3]
  have h_sum_lt : (2 ^ 40 : ℤ) * E1 < 29 * 2 ^ 78 := by
    have hconst : (29 : ℤ) * 2 ^ 78 = 25 * 2 ^ 78 + 2 ^ 80 := by norm_num
    linarith only [hE1_identity, he0_sq_lt, h_factor_le, hconst]
  have hE1_lt : E1 < 29 * 2 ^ 38 := by
    have hprod_eq : (2 ^ 40 : ℤ) * (29 * 2 ^ 38) = 29 * 2 ^ 78 := by ring
    have h_conv : (2 ^ 40 : ℤ) * E1 < 2 ^ 40 * (29 * 2 ^ 38) := by
      linarith only [h_sum_lt, hprod_eq]
    exact lt_of_mul_lt_mul_left h_conv (le_of_lt h240_pos)
  exact ⟨hE1_pos, hE1_lt⟩

/-! ### The error `e2 = 2^97 − v_2 d` and Bound 8. -/

/-- `toNat` identity for `computeV2`, assuming no overflow.
The hypotheses are those satisfied along the Möller–Granlund path:
`v_1 < 2^{21}`, `d_{40} ≤ 2^{40}`, `v_1 · d_{40} ≤ 2^{60}` (so `e_1 ≥ 0`), and
`v_1 · (2^{60} − v_1 d_{40}) < 2^{64}` (which follows from Bound 7). -/
theorem toNat_computeV2 (v1 d40 : UInt64)
    (hv1 : v1.toNat < 2 ^ 21)
    (h_vd_le : v1.toNat * d40.toNat ≤ 2 ^ 60)
    (h_prod_lt : v1.toNat * (2 ^ 60 - v1.toNat * d40.toNat) < 2 ^ 64) :
    (computeV2 v1 d40).toNat =
      v1.toNat * 2 ^ 13 +
      v1.toNat * (2 ^ 60 - v1.toNat * d40.toNat) / 2 ^ 47 := by
  set V : ℕ := v1.toNat with hV_def
  set D : ℕ := d40.toNat with hD_def
  have hform : computeV2 v1 d40 =
      v1 <<< 13 + (v1 * (((1 : UInt64) <<< 60) - v1 * d40)) >>> 47 := by
    unfold computeV2; rfl
  rw [hform]
  have hVD_lt64 : V * D < 2 ^ 64 := by
    have h : (2 : ℕ) ^ 60 < 2 ^ 64 := by norm_num
    omega
  have hvd : (v1 * d40).toNat = V * D := by
    rw [_root_.UInt64.toNat_mul]; exact Nat.mod_eq_of_lt hVD_lt64
  have h_one_shl : ((1 : UInt64) <<< 60).toNat = 2 ^ 60 := by
    rw [_root_.UInt64.toNat_shiftLeft]
    show (1 : ℕ) <<< ((60 : UInt64).toNat % 64) % 2 ^ 64 = 2 ^ 60
    rw [show ((60 : UInt64).toNat) = 60 from rfl,
        show (60 : ℕ) % 64 = 60 from rfl, Nat.shiftLeft_eq]
    decide
  have h_e : (((1 : UInt64) <<< 60) - v1 * d40).toNat = 2 ^ 60 - V * D := by
    rw [_root_.UInt64.toNat_sub, hvd, h_one_shl]; omega
  have hprod : (v1 * (((1 : UInt64) <<< 60) - v1 * d40)).toNat =
      V * (2 ^ 60 - V * D) := by
    rw [_root_.UInt64.toNat_mul, h_e]; exact Nat.mod_eq_of_lt h_prod_lt
  have h47 : ((47 : UInt64).toNat) = 47 := rfl
  have hshr : ((v1 * (((1 : UInt64) <<< 60) - v1 * d40)) >>> 47).toNat =
      V * (2 ^ 60 - V * D) / 2 ^ 47 := by
    rw [_root_.UInt64.toNat_shiftRight, hprod, h47]
    show (V * (2 ^ 60 - V * D)) >>> ((47 : ℕ) % 64) = _
    rw [show (47 : ℕ) % 64 = 47 from rfl, Nat.shiftRight_eq_div_pow]
  have h13 : ((13 : UInt64).toNat) = 13 := rfl
  have hV_2_13_lt : V * 2 ^ 13 < 2 ^ 64 := by nlinarith [hv1]
  have hshl : (v1 <<< 13).toNat = V * 2 ^ 13 := by
    rw [_root_.UInt64.toNat_shiftLeft, h13]
    show V <<< ((13 : ℕ) % 64) % 2 ^ 64 = V * 2 ^ 13
    rw [show (13 : ℕ) % 64 = 13 from rfl, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt hV_2_13_lt
  have hdiv_lt : V * (2 ^ 60 - V * D) / 2 ^ 47 < 2 ^ 17 := by
    apply Nat.div_lt_of_lt_mul
    have h64 : (2 : ℕ) ^ 17 * 2 ^ 47 = 2 ^ 64 := by norm_num
    omega
  have hsum_lt : V * 2 ^ 13 + V * (2 ^ 60 - V * D) / 2 ^ 47 < 2 ^ 64 := by
    nlinarith [hv1, hdiv_lt]
  rw [_root_.UInt64.toNat_add, hshl, hshr]
  exact Nat.mod_eq_of_lt hsum_lt

/-- `e2 = 2^97 − v_2 · d` as an integer. -/
def e2 (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) : ℤ :=
  (2 ^ 97 : ℤ) -
    ((computeV2
        (computeV1 (computeV0 (computeD9 d) (computeD9_sub_256_lt d hd))
                   (computeD40 d))
        (computeD40 d)).toNat : ℤ) * (d.toNat : ℤ)

/-- Bound 8 from Möller–Granlund: `0 < e2 < (873/1024)·2^63 + d`, i.e.,
`0 < e2 < 873·2^53 + d`, assuming `d` is normalized (`2^63 ≤ d`). -/
theorem e2_pos_and_lt (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    0 < e2 d hd ∧ e2 d hd < 873 * 2 ^ 53 + d.toNat := by
  obtain ⟨hE1_pos, hE1_lt⟩ := e1_pos_and_lt d hd
  set D : ℕ := d.toNat with hD_def
  set d40N : ℕ := (computeD40 d).toNat with hd40N_def
  set v1 : UInt64 := computeV1 (computeV0 (computeD9 d) (computeD9_sub_256_lt d hd))
    (computeD40 d) with hv1_def
  set V1N : ℕ := v1.toNat with hV1N_def
  obtain ⟨hd40N_lo, hd40N_hi⟩ := computeD40_bounds d hd
  -- Unfold e1 in bounds.
  have hE1_val : e1 d hd = (2 ^ 60 : ℤ) - (V1N : ℤ) * d40N := rfl
  rw [hE1_val] at hE1_pos hE1_lt
  -- V1*d40 bounds (Nat).
  have hV1d40_lt_int : (V1N : ℤ) * d40N < 2 ^ 60 := by linarith
  have hV1d40_lt : V1N * d40N < 2 ^ 60 := by exact_mod_cast hV1d40_lt_int
  have hV1d40_le : V1N * d40N ≤ 2 ^ 60 := le_of_lt hV1d40_lt
  have he1_nat_lt : 2 ^ 60 - V1N * d40N < 29 * 2 ^ 38 := by
    have h1 : ((2 ^ 60 - V1N * d40N : ℕ) : ℤ) = (2 ^ 60 : ℤ) - V1N * d40N := by
      rw [Int.ofNat_sub hV1d40_le]; push_cast; ring
    have h2 : ((2 ^ 60 - V1N * d40N : ℕ) : ℤ) < 29 * 2 ^ 38 := by rw [h1]; linarith
    exact_mod_cast h2
  -- V1 < 2^21.
  have hV1_lt : V1N < 2 ^ 21 := by
    by_contra h
    have h' : 2 ^ 21 ≤ V1N := not_lt.mp h
    have h1 : 2 ^ 21 * (2 ^ 39 + 1) ≤ V1N * d40N := Nat.mul_le_mul h' hd40N_lo
    have h2 : (2 : ℕ) ^ 21 * (2 ^ 39 + 1) > 2 ^ 60 := by norm_num
    omega
  -- V1 * (2^60 - V1*d40) < 2^64.
  have hprod_lt : V1N * (2 ^ 60 - V1N * d40N) < 2 ^ 64 := by
    have hle : (2 ^ 60 - V1N * d40N) ≤ 29 * 2 ^ 38 := by omega
    have h1 : V1N * (2 ^ 60 - V1N * d40N) ≤ V1N * (29 * 2 ^ 38) :=
      Nat.mul_le_mul_left _ hle
    have h2 : V1N * (29 * 2 ^ 38) < 2 ^ 21 * (29 * 2 ^ 38) :=
      (Nat.mul_lt_mul_right (by norm_num : (0 : ℕ) < 29 * 2 ^ 38)).mpr hV1_lt
    have h3 : (2 : ℕ) ^ 21 * (29 * 2 ^ 38) < 2 ^ 64 := by norm_num
    linarith
  -- V2 Nat form.
  have hV2_eq : (computeV2 v1 (computeD40 d)).toNat =
      V1N * 2 ^ 13 + V1N * (2 ^ 60 - V1N * d40N) / 2 ^ 47 :=
    toNat_computeV2 v1 (computeD40 d) hV1_lt hV1d40_le hprod_lt
  -- q2, r2 as Nat.
  set q2N : ℕ := V1N * (2 ^ 60 - V1N * d40N) / 2 ^ 47 with hq2N_def
  set r2N : ℕ := V1N * (2 ^ 60 - V1N * d40N) % 2 ^ 47 with hr2N_def
  have hr2N_lt : r2N < 2 ^ 47 := Nat.mod_lt _ (by norm_num)
  have hVE_nat : V1N * (2 ^ 60 - V1N * d40N) = q2N * 2 ^ 47 + r2N := by
    have := Nat.div_add_mod (V1N * (2 ^ 60 - V1N * d40N)) (2 ^ 47)
    omega
  -- D'N in ℕ: 2^24 * d40 = D + D'N, 1 ≤ D'N ≤ 2^24.
  have hd40N_eq : d40N = D / 2 ^ 24 + 1 := toNat_computeD40 d
  set D'N : ℕ := 2 ^ 24 * d40N - D with hD'N_def
  have hDmod_lt : D % 2 ^ 24 < 2 ^ 24 := Nat.mod_lt _ (by norm_num)
  have hD_divmod : D = 2 ^ 24 * (D / 2 ^ 24) + D % 2 ^ 24 :=
    (Nat.div_add_mod D (2 ^ 24)).symm
  have hD_le : D ≤ 2 ^ 24 * d40N := by rw [hd40N_eq]; linarith
  have hDD'N : 2 ^ 24 * d40N = D + D'N := by omega
  have hD'N_pos : 1 ≤ D'N := by
    have h1 : 2 ^ 24 * d40N = 2 ^ 24 * (D / 2 ^ 24) + 2 ^ 24 := by rw [hd40N_eq]; ring
    omega
  have hD'N_hi : D'N ≤ 2 ^ 24 := by
    have h1 : 2 ^ 24 * d40N = 2 ^ 24 * (D / 2 ^ 24) + 2 ^ 24 := by rw [hd40N_eq]; ring
    omega
  -- Change goal to integer form using hV2_eq.
  show 0 < e2 d hd ∧ e2 d hd < 873 * 2 ^ 53 + (D : ℤ)
  unfold e2
  rw [hV2_eq, ← hD_def]
  -- Integer variables.
  set V1_Z : ℤ := (V1N : ℤ) with hV1_Z_def
  set d40_Z : ℤ := (d40N : ℤ) with hd40_Z_def
  set D_Z : ℤ := (D : ℤ) with hD_Z_def
  set q2_Z : ℤ := (q2N : ℤ) with hq2_Z_def
  set r2_Z : ℤ := (r2N : ℤ) with hr2_Z_def
  set D'_Z : ℤ := 2 ^ 24 * d40_Z - D_Z with hD'_Z_def
  set E1_Z : ℤ := 2 ^ 60 - V1_Z * d40_Z with hE1_Z_def
  -- Bounds on integer quantities.
  have hV1_Z_nn : 0 ≤ V1_Z := Int.natCast_nonneg _
  have hd40_Z_nn : 0 ≤ d40_Z := Int.natCast_nonneg _
  have hV1_Z_lt : V1_Z < 2 ^ 21 := by
    show (V1N : ℤ) < 2 ^ 21; exact_mod_cast hV1_lt
  have hd40_Z_lo : (2 : ℤ) ^ 39 + 1 ≤ d40_Z := by
    show (2 : ℤ) ^ 39 + 1 ≤ (d40N : ℤ); exact_mod_cast hd40N_lo
  have hd40_Z_hi : d40_Z ≤ 2 ^ 40 := by
    show (d40N : ℤ) ≤ 2 ^ 40; exact_mod_cast hd40N_hi
  have hD_Z_pos : 0 < D_Z := by
    have : (2 : ℤ) ^ 63 ≤ D_Z := by
      show (2 : ℤ) ^ 63 ≤ (D : ℤ); exact_mod_cast hd
    linarith [show (2 : ℤ) ^ 63 > 0 by norm_num]
  have hD_Z_nn : 0 ≤ D_Z := le_of_lt hD_Z_pos
  have hr2_Z_nn : 0 ≤ r2_Z := Int.natCast_nonneg _
  have hr2_Z_lt : r2_Z < 2 ^ 47 := by
    show (r2N : ℤ) < 2 ^ 47; exact_mod_cast hr2N_lt
  have hE1_Z_pos : 0 < E1_Z := hE1_pos
  have hE1_Z_lt : E1_Z < 29 * 2 ^ 38 := hE1_lt
  have hE1_Z_le : 1 ≤ E1_Z := hE1_Z_pos
  -- D' bounds (integer).
  have hD'_Z_eq_nat : D'_Z = (D'N : ℤ) := by
    rw [hD'_Z_def]
    have h_eq : 2 ^ 24 * d40_Z - D_Z = ((2 ^ 24 * d40N - D : ℕ) : ℤ) := by
      rw [Int.ofNat_sub hD_le]; push_cast; ring
    rw [h_eq]
  have hD'_Z_lo : 1 ≤ D'_Z := by rw [hD'_Z_eq_nat]; exact_mod_cast hD'N_pos
  have hD'_Z_hi : D'_Z ≤ 2 ^ 24 := by rw [hD'_Z_eq_nat]; exact_mod_cast hD'N_hi
  have hD'_Z_nn : 0 ≤ D'_Z := by linarith
  -- Integer form of hVE_nat.
  have hVE_Z : V1_Z * E1_Z = q2_Z * 2 ^ 47 + r2_Z := by
    have h_cast : ((V1N * (2 ^ 60 - V1N * d40N) : ℕ) : ℤ)
        = ((q2N * 2 ^ 47 + r2N : ℕ) : ℤ) := by exact_mod_cast hVE_nat
    have h_LHS : ((V1N * (2 ^ 60 - V1N * d40N) : ℕ) : ℤ) = V1_Z * E1_Z := by
      rw [Nat.cast_mul, Int.ofNat_sub hV1d40_le]; push_cast; ring
    have h_RHS : ((q2N * 2 ^ 47 + r2N : ℕ) : ℤ) = q2_Z * 2 ^ 47 + r2_Z := by
      push_cast; ring
    rw [h_LHS, h_RHS] at h_cast; exact h_cast
  -- D relation.
  have hDZ_eq : D_Z = 2 ^ 24 * d40_Z - D'_Z := by linarith [hD'_Z_def]
  have hE1_eq : E1_Z = 2 ^ 60 - V1_Z * d40_Z := hE1_Z_def
  -- Key integer identity.
  have hKey : (2 ^ 47 : ℤ) * (2 ^ 97 - ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) * D_Z)
      = 2 ^ 24 * E1_Z ^ 2 + V1_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z + r2_Z * D_Z := by
    have h_cast_V2 : ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) = V1_Z * 2 ^ 13 + q2_Z := by
      push_cast; ring
    rw [h_cast_V2]
    rw [hE1_eq, hDZ_eq]
    linear_combination (2 ^ 24 * d40_Z - D'_Z) * hVE_Z
  -- Shrink context: drop Nat-only hypotheses and hide `set` values to speed up
  -- subsequent integer-arithmetic tactics.
  clear hE1_val hV1d40_lt_int hV1d40_lt hV1d40_le he1_nat_lt hV1_lt hprod_lt
    hV2_eq hVE_nat hd40N_eq hDmod_lt hD_divmod hD_le hDD'N hD'N_pos hD'N_hi
    hD'_Z_eq_nat hVE_Z hDZ_eq hE1_eq
  clear_value V1_Z d40_Z D_Z q2_Z r2_Z D'_Z E1_Z
  -- Lower bound: 0 < e2.
  have hE1_sq_pos : (1 : ℤ) ≤ E1_Z ^ 2 := by
    have h1 : (1 : ℤ) * 1 ≤ E1_Z * E1_Z :=
      mul_le_mul hE1_Z_le hE1_Z_le (by norm_num) (by linarith)
    rw [sq]; linarith
  have h_term1_pos : (0 : ℤ) < 2 ^ 24 * E1_Z ^ 2 := by
    have h224 : (0 : ℤ) < 2 ^ 24 := by norm_num
    have := mul_lt_mul_of_pos_left (by linarith : (0 : ℤ) < E1_Z ^ 2) h224
    linarith
  have hV1f_nn : (0 : ℤ) ≤ V1_Z * (2 ^ 61 - V1_Z * d40_Z) := by
    have hfactor : (0 : ℤ) ≤ 2 ^ 61 - V1_Z * d40_Z := by
      have : V1_Z * d40_Z < 2 ^ 60 := by linarith
      linarith
    exact mul_nonneg hV1_Z_nn hfactor
  have h_term2_nn : (0 : ℤ) ≤ V1_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z :=
    mul_nonneg hV1f_nn hD'_Z_nn
  have h_term3_nn : (0 : ℤ) ≤ r2_Z * D_Z := mul_nonneg hr2_Z_nn hD_Z_nn
  have h_2_47_pos : (0 : ℤ) < 2 ^ 47 := by norm_num
  have hE2_pos_mul : (0 : ℤ) < 2 ^ 47
      * (2 ^ 97 - ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) * D_Z) := by
    rw [hKey]; linarith
  have hE2_pos : (0 : ℤ) < 2 ^ 97 - ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) * D_Z := by
    by_contra h
    have hle : 2 ^ 97 - ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) * D_Z ≤ 0 := not_lt.mp h
    have : 2 ^ 47 * (2 ^ 97 - ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) * D_Z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_2_47_pos) hle
    linarith
  -- Upper bound: e2 < 873*2^53 + D.
  -- (A) 2^24 * E1^2 < 841 * 2^100.
  have h_term1_lt : 2 ^ 24 * E1_Z ^ 2 < 841 * 2 ^ 100 := by
    have hE1_nn : 0 ≤ E1_Z := le_of_lt hE1_Z_pos
    have hE1_sq_lt : E1_Z ^ 2 < (29 * 2 ^ 38) ^ 2 := by
      rw [sq, sq]
      exact mul_lt_mul'' hE1_Z_lt hE1_Z_lt hE1_nn hE1_nn
    have h29_sq : ((29 : ℤ) * 2 ^ 38) ^ 2 = 841 * 2 ^ 76 := by ring
    have h2_24_pos : (0 : ℤ) < 2 ^ 24 := by norm_num
    have h_shift : 2 ^ 24 * E1_Z ^ 2 < 2 ^ 24 * (29 * 2 ^ 38) ^ 2 :=
      mul_lt_mul_of_pos_left hE1_sq_lt h2_24_pos
    have h_rewrite : (2 : ℤ) ^ 24 * ((29 * 2 ^ 38) ^ 2) = 841 * 2 ^ 100 := by ring
    linarith
  -- (B) V1*(2^61 - V1*d40)*D' < 2^105.
  have h_term2_lt : V1_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z < 2 ^ 105 := by
    -- AM-GM: V1*d40 * (2^61 - V1*d40) ≤ 2^120. Via (V1*d40 - 2^60)^2 ≥ 0.
    have h_amgm : V1_Z * d40_Z * (2 ^ 61 - V1_Z * d40_Z) ≤ 2 ^ 120 := by
      nlinarith [sq_nonneg (V1_Z * d40_Z - 2 ^ 60)]
    -- Multiply by D' ≥ 0: V1*d40*(2^61 - V1*d40) * D' ≤ 2^120 * D'.
    have h_step1 : V1_Z * d40_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z ≤ 2 ^ 120 * D'_Z :=
      mul_le_mul_of_nonneg_right h_amgm hD'_Z_nn
    -- D' ≤ 2^24, so 2^120 * D' ≤ 2^144.
    have h_step2 : (2 : ℤ) ^ 120 * D'_Z ≤ 2 ^ 144 := by
      have h2120_pos : (0 : ℤ) < 2 ^ 120 := by norm_num
      have : 2 ^ 120 * D'_Z ≤ 2 ^ 120 * 2 ^ 24 :=
        mul_le_mul_of_nonneg_left hD'_Z_hi (le_of_lt h2120_pos)
      have hpow : (2 : ℤ) ^ 120 * 2 ^ 24 = 2 ^ 144 := by norm_num
      linarith
    have h_prod_le : V1_Z * d40_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z ≤ 2 ^ 144 := by
      linarith
    -- Rearrange: V1*(2^61-V1*d40)*D' * d40 = V1*d40*(2^61-V1*d40)*D'.
    have h_reorder : V1_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z * d40_Z
        = V1_Z * d40_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z := by ring
    have h_mul_le : V1_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z * d40_Z ≤ 2 ^ 144 := by
      rw [h_reorder]; exact h_prod_le
    -- d40 ≥ 2^39 + 1, so if V1*(2^61-V1*d40)*D' ≥ 2^105, then 2^105*(2^39+1) ≤ 2^144.
    -- But 2^105*(2^39+1) = 2^144 + 2^105 > 2^144. Contradiction.
    by_contra h
    have hge : 2 ^ 105 ≤ V1_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z := not_lt.mp h
    have h_105_nn : (0 : ℤ) ≤ 2 ^ 105 := by norm_num
    have h_mul_lo : (2 : ℤ) ^ 105 * d40_Z ≤ V1_Z * (2 ^ 61 - V1_Z * d40_Z) * D'_Z * d40_Z :=
      mul_le_mul_of_nonneg_right hge hd40_Z_nn
    have h_105_d40_lo : (2 : ℤ) ^ 105 * (2 ^ 39 + 1) ≤ 2 ^ 105 * d40_Z :=
      mul_le_mul_of_nonneg_left hd40_Z_lo h_105_nn
    have hpow_sum : (2 : ℤ) ^ 105 * (2 ^ 39 + 1) = 2 ^ 144 + 2 ^ 105 := by ring
    linarith
  -- (C) r2 * D < 2^47 * D.
  have h_term3_lt : r2_Z * D_Z < 2 ^ 47 * D_Z :=
    mul_lt_mul_of_pos_right hr2_Z_lt hD_Z_pos
  -- Combine: 2^47 * e2 < 873 * 2^100 + 2^47 * D.
  have hE2_upper_mul : 2 ^ 47 * (2 ^ 97 - ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) * D_Z)
      < 873 * 2 ^ 100 + 2 ^ 47 * D_Z := by
    rw [hKey]
    have h_sum : (841 : ℤ) * 2 ^ 100 + 2 ^ 105 = 873 * 2 ^ 100 := by norm_num
    linarith
  have h_e2_upper : 2 ^ 97 - ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) * D_Z < 873 * 2 ^ 53 + D_Z := by
    have h_mul : (2 : ℤ) ^ 47 * (873 * 2 ^ 53 + D_Z) = 873 * 2 ^ 100 + 2 ^ 47 * D_Z := by ring
    have h_lt : 2 ^ 47 * (2 ^ 97 - ((V1N * 2 ^ 13 + q2N : ℕ) : ℤ) * D_Z)
        < 2 ^ 47 * (873 * 2 ^ 53 + D_Z) := by rw [h_mul]; exact hE2_upper_mul
    exact lt_of_mul_lt_mul_left h_lt (le_of_lt h_2_47_pos)
  exact ⟨hE2_pos, h_e2_upper⟩

/-! ### The error `e3 = 2^128 − (2^64 + v_3) d` and Bound 9. -/

/-- `toNat` identity for `computeE`: extracting `V2/2 * D0 − V2·D63` mod 2^64.
Requires `d_0 ∈ {0, 1}` (which holds whenever `d_0 = d mod 2`). -/
theorem toNat_computeE (v2 d63 d0 : UInt64) (hd0 : d0.toNat ≤ 1) :
    (computeE v2 d63 d0).toNat =
      (v2.toNat / 2 * d0.toNat + 2 ^ 64 - v2.toNat * d63.toNat % 2 ^ 64) % 2 ^ 64 := by
  have h_and : ((v2 >>> 1) &&& ((0 : UInt64) - d0)).toNat = v2.toNat / 2 * d0.toNat := by
    rw [_root_.UInt64.toNat_and, _root_.UInt64.toNat_shiftRight,
        show ((1 : UInt64).toNat = 1) from rfl,
        show (1 : ℕ) % 64 = 1 from rfl, Nat.shiftRight_eq_div_pow,
        _root_.UInt64.toNat_sub, show ((0 : UInt64).toNat = 0) from rfl,
        Nat.add_zero]
    have hv_lt : v2.toNat / 2 < 2 ^ 64 := by
      have : v2.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
      omega
    rcases (show d0.toNat = 0 ∨ d0.toNat = 1 by omega) with hD0 | hD0
    · rw [hD0]; simp
    · rw [hD0]
      rw [show (2 ^ 64 - 1 : ℕ) % 2 ^ 64 = 2 ^ 64 - 1 from Nat.mod_eq_of_lt (by omega),
          Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv_lt]
      ring
  show ((v2 >>> 1 &&& (0 - d0)) - v2 * d63).toNat = _
  rw [_root_.UInt64.toNat_sub, _root_.UInt64.toNat_mul, h_and]
  have hmod_le : v2.toNat * d63.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  congr 1; omega

/-- `toNat` identity for `computeV3`: `(v_2 · 2^31 + ⌊v_2 · e / 2^65⌋) mod 2^64`. -/
theorem toNat_computeV3 (v2 e : UInt64) :
    (computeV3 v2 e).toNat =
      (v2.toNat * 2 ^ 31 + v2.toNat * e.toNat / 2 ^ 65) % 2 ^ 64 := by
  unfold computeV3
  set V2 := v2.toNat with hV2_def
  set E := e.toNat with hE_def
  have h_wm := toNat_wideMul v2 e
  have hlo_lt : (wideMul v2 e).2.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hhi_eq : (wideMul v2 e).1.toNat = V2 * E / 2 ^ 64 := by
    have h_sum : V2 * E = (wideMul v2 e).2.toNat + (wideMul v2 e).1.toNat * 2 ^ 64 := by
      rw [← h_wm]; ring
    rw [h_sum, Nat.add_mul_div_right _ _ (by norm_num : (0 : ℕ) < 2 ^ 64),
        Nat.div_eq_of_lt hlo_lt, Nat.zero_add]
  rw [_root_.UInt64.toNat_add, _root_.UInt64.toNat_shiftLeft,
      show ((31 : UInt64).toNat = 31) from rfl,
      show (31 : ℕ) % 64 = 31 from rfl,
      Nat.shiftLeft_eq,
      _root_.UInt64.toNat_shiftRight, hhi_eq,
      show ((1 : UInt64).toNat = 1) from rfl,
      show (1 : ℕ) % 64 = 1 from rfl,
      Nat.shiftRight_eq_div_pow]
  have hrewrite : V2 * E / 2 ^ 64 / 2 ^ 1 = V2 * E / 2 ^ 65 := by
    rw [Nat.div_div_eq_div_mul]; norm_num
  rw [hrewrite, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- `e3 = 2^128 − (2^64 + v_3) · d` as an integer. -/
def e3 (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) : ℤ :=
  let v0 := computeV0 (computeD9 d) (computeD9_sub_256_lt d hd)
  let v1 := computeV1 v0 (computeD40 d)
  let v2 := computeV2 v1 (computeD40 d)
  let e  := computeE v2 (computeD63 d) (computeD0 d)
  let v3 := computeV3 v2 e
  (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + (v3.toNat : ℤ)) * (d.toNat : ℤ)

/-- Bound 9 from Möller–Granlund: `0 < e3 < 2·d`, assuming `d` is normalized
(`2^63 ≤ d`). -/
theorem e3_pos_and_lt (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    0 < e3 d hd ∧ e3 d hd < 2 * d.toNat := by
  obtain ⟨hE2_pos, hE2_lt⟩ := e2_pos_and_lt d hd
  -- Nat shortcuts.
  set D : ℕ := d.toNat with hD_def
  set v2' : UInt64 :=
    computeV2
      (computeV1 (computeV0 (computeD9 d) (computeD9_sub_256_lt d hd)) (computeD40 d))
      (computeD40 d) with hv2'_def
  set V2N : ℕ := v2'.toNat with hV2N_def
  set D63N : ℕ := (computeD63 d).toNat with hD63N_def
  set D0N : ℕ := (computeD0 d).toNat with hD0N_def
  set e' : UInt64 := computeE v2' (computeD63 d) (computeD0 d) with he'_def
  set EN : ℕ := e'.toNat with hEN_def
  set v3' : UInt64 := computeV3 v2' e' with hv3'_def
  set V3N : ℕ := v3'.toNat with hV3N_def
  -- D bounds.
  have hD_lt : D < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD_ge : 2 ^ 63 ≤ D := hd
  have hD_pos : 0 < D := by omega
  -- D0 = D mod 2.
  have hD0N_eq : D0N = D % 2 := toNat_computeD0 d
  have hD0N_le : D0N ≤ 1 := by rw [hD0N_eq]; omega
  -- D63 = (D+1)/2.
  have hD63N_eq : D63N = (D + 1) / 2 := toNat_computeD63 d
  -- 2·D63 = D + D0.
  have h2D63 : 2 * D63N = D + D0N := by rw [hD63N_eq, hD0N_eq]; omega
  -- E2 bounds (cast from e2_pos_and_lt, unfolding e2).
  have hE2_val : e2 d hd = (2 ^ 97 : ℤ) - (V2N : ℤ) * D := rfl
  rw [hE2_val] at hE2_pos hE2_lt
  have hV2D_lt_int : (V2N : ℤ) * D < 2 ^ 97 := by linarith
  have hV2D_lt_nat : V2N * D < 2 ^ 97 := by exact_mod_cast hV2D_lt_int
  -- V2 < 2^34.
  have hV2N_lt : V2N < 2 ^ 34 := by
    by_contra h
    have h1 : 2 ^ 34 ≤ V2N := not_lt.mp h
    have h2 : 2 ^ 34 * 2 ^ 63 ≤ V2N * D := Nat.mul_le_mul h1 hd
    have h3 : (2 : ℕ) ^ 34 * 2 ^ 63 = 2 ^ 97 := by norm_num
    omega
  -- Integer variables.
  set V2_Z : ℤ := (V2N : ℤ) with hV2_Z_def
  set D_Z : ℤ := (D : ℤ) with hD_Z_def
  set D0_Z : ℤ := (D0N : ℤ) with hD0_Z_def
  set D63_Z : ℤ := (D63N : ℤ) with hD63_Z_def
  set E2_Z : ℤ := (2 ^ 97 : ℤ) - V2_Z * D_Z with hE2_Z_def
  set eps_Z : ℤ := D0_Z * (V2_Z - 2 * (V2_Z / 2)) with heps_Z_def
  have hV2_Z_nn : 0 ≤ V2_Z := Int.natCast_nonneg _
  have hD_Z_nn : 0 ≤ D_Z := Int.natCast_nonneg _
  have hD_Z_pos : 0 < D_Z := by
    show 0 < (D : ℤ); exact_mod_cast hD_pos
  have hD_Z_lt : D_Z < 2 ^ 64 := by
    show (D : ℤ) < 2 ^ 64; exact_mod_cast hD_lt
  have hD_Z_ge : (2 : ℤ) ^ 63 ≤ D_Z := by
    show (2 : ℤ) ^ 63 ≤ (D : ℤ); exact_mod_cast hD_ge
  have hV2_Z_lt : V2_Z < 2 ^ 34 := by
    show (V2N : ℤ) < 2 ^ 34; exact_mod_cast hV2N_lt
  have hD0_Z_le : D0_Z ≤ 1 := by show (D0N : ℤ) ≤ 1; exact_mod_cast hD0N_le
  have hD0_Z_nn : 0 ≤ D0_Z := Int.natCast_nonneg _
  -- eps_Z ∈ {0, 1}.
  have hV2_mod2 : V2_Z - 2 * (V2_Z / 2) = (V2N % 2 : ℕ) := by
    have h1 : V2_Z / 2 = (V2N / 2 : ℕ) := by
      rw [hV2_Z_def]; exact_mod_cast rfl
    rw [h1]
    have h2 : (V2N : ℤ) - 2 * (V2N / 2 : ℕ) = (V2N % 2 : ℕ) := by
      have h3 := Nat.div_add_mod V2N 2
      have h4 : V2N = 2 * (V2N / 2) + V2N % 2 := by omega
      have : (V2N : ℤ) = 2 * (V2N / 2 : ℕ) + (V2N % 2 : ℕ) := by exact_mod_cast h4
      linarith
    exact h2
  have hV2_mod2_le : V2_Z - 2 * (V2_Z / 2) ≤ 1 := by
    rw [hV2_mod2]; exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
  have hV2_mod2_nn : 0 ≤ V2_Z - 2 * (V2_Z / 2) := by
    rw [hV2_mod2]; exact_mod_cast Nat.zero_le _
  have heps_Z_le : eps_Z ≤ 1 := by
    rw [heps_Z_def]
    rcases (show D0N = 0 ∨ D0N = 1 by omega) with h | h
    · rw [show D0_Z = 0 from by rw [hD0_Z_def]; exact_mod_cast h]; linarith
    · rw [show D0_Z = 1 from by rw [hD0_Z_def]; exact_mod_cast h]
      linarith [hV2_mod2_le, hV2_mod2_nn]
  have heps_Z_nn : 0 ≤ eps_Z := mul_nonneg hD0_Z_nn hV2_mod2_nn
  -- V2_Z * D_Z = 2^97 - E2_Z.
  have hH1 : V2_Z * D_Z = 2 ^ 97 - E2_Z := by rw [hE2_Z_def]; ring
  -- E_math_Z: the integer mathematical E.
  set E_math_Z : ℤ := 2 ^ 96 - V2_Z * D63_Z + (V2_Z / 2) * D0_Z with hE_math_Z_def
  -- 2*E_math_Z = E2_Z - eps_Z.
  have h2D63_Z : 2 * D63_Z = D_Z + D0_Z := by
    show 2 * (D63N : ℤ) = (D : ℤ) + (D0N : ℤ); exact_mod_cast h2D63
  have hE_math_eq : 2 * E_math_Z = E2_Z - eps_Z := by
    rw [hE_math_Z_def, hE2_Z_def, heps_Z_def]
    have hA : 2 * (V2_Z * D63_Z) = V2_Z * (D_Z + D0_Z) := by
      rw [← h2D63_Z]; ring
    linarith [hA]
  -- E2_Z bounds: 1 ≤ E2_Z < 873*2^53 + D_Z < 2^65.
  have hE2_Z_ge : 1 ≤ E2_Z := hE2_pos
  have hE2_Z_lt_nat : E2_Z < 873 * 2 ^ 53 + D_Z := hE2_lt
  have hE2_Z_lt_2D : E2_Z < 2 * D_Z := by
    have h1 : (873 : ℤ) * 2 ^ 53 < 2 ^ 63 := by norm_num
    linarith
  have hE2_Z_lt_2_65 : E2_Z < 2 ^ 65 := by
    have : (2 : ℤ) * D_Z < 2 ^ 65 := by linarith
    linarith
  -- E_math_Z bounds: 0 ≤ E_math_Z < 2^64.
  have hE_math_nn : 0 ≤ E_math_Z := by
    have : 2 * E_math_Z ≥ 0 := by linarith [hE2_Z_ge, heps_Z_le]
    linarith
  have hE_math_lt : E_math_Z < 2 ^ 64 := by
    have : 2 * E_math_Z < 2 ^ 65 := by linarith [heps_Z_nn]
    linarith
  -- Show (EN : ℤ) = E_math_Z.
  have hEN_val : (EN : ℤ) = E_math_Z := by
    have hraw := toNat_computeE v2' (computeD63 d) (computeD0 d) hD0N_le
    have hEN_nat : EN = (V2N / 2 * D0N + 2 ^ 64 - V2N * D63N % 2 ^ 64) % 2 ^ 64 := hraw
    -- Show both sides mod 2^64 are equal, both in [0, 2^64).
    set A : ℕ := V2N / 2 * D0N with hA_def
    set M : ℕ := V2N * D63N with hM_def
    have hMmod_lt : M % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
    have hA_lt_2_64 : A < 2 ^ 64 := by
      rw [hA_def]
      rcases (show D0N = 0 ∨ D0N = 1 by omega) with h | h
      · rw [h]; omega
      · rw [h]
        have : V2N / 2 ≤ V2N := Nat.div_le_self _ _
        have : V2N / 2 * 1 = V2N / 2 := by ring
        omega
    have hsubok : M % 2 ^ 64 ≤ A + 2 ^ 64 := by omega
    -- Cast Nat expression to Int.
    have hEN_int : (EN : ℤ) = ((A + 2 ^ 64 - M % 2 ^ 64 : ℕ) : ℤ) % (2 ^ 64 : ℤ) := by
      rw [hEN_nat]
      push_cast
      rfl
    rw [hEN_int]
    have hsubInt : ((A + 2 ^ 64 - M % 2 ^ 64 : ℕ) : ℤ) = (A : ℤ) + 2 ^ 64 - (M % 2 ^ 64 : ℕ) := by
      rw [Int.ofNat_sub hsubok]; push_cast; ring
    rw [hsubInt]
    -- Express (M % 2^64 : ℕ) as Int: M - 2^64 * (M / 2^64 : ℕ).
    have hMqr : M = 2 ^ 64 * (M / 2 ^ 64) + M % 2 ^ 64 :=
      (Nat.div_add_mod M (2 ^ 64)).symm
    have hMmod_int : ((M % 2 ^ 64 : ℕ) : ℤ) = (M : ℤ) - 2 ^ 64 * (M / 2 ^ 64 : ℕ) := by
      have h_cast : (M : ℤ) = 2 ^ 64 * ((M / 2 ^ 64 : ℕ) : ℤ) + ((M % 2 ^ 64 : ℕ) : ℤ) := by
        exact_mod_cast hMqr
      linarith
    rw [hMmod_int]
    have hRHS_eq :
        ((A : ℤ) + 2 ^ 64 - ((M : ℤ) - 2 ^ 64 * (M / 2 ^ 64 : ℕ))) % (2 ^ 64 : ℤ)
          = E_math_Z := by
      have hSum : (A : ℤ) + 2 ^ 64 - ((M : ℤ) - 2 ^ 64 * (M / 2 ^ 64 : ℕ))
          = (E_math_Z) + 2 ^ 64 * ((M / 2 ^ 64 : ℕ) - (2 ^ 32) + 1) := by
        rw [hE_math_Z_def, hA_def, hM_def]
        push_cast
        ring
      rw [hSum, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hE_math_nn hE_math_lt]
    exact hRHS_eq
  -- V2_Z * EN_Z < 2^98.
  set EN_Z : ℤ := (EN : ℤ) with hEN_Z_def
  have hEN_Z_nn : 0 ≤ EN_Z := Int.natCast_nonneg _
  have hEN_Z_lt : EN_Z < 2 ^ 64 := by rw [hEN_val]; exact hE_math_lt
  have hV2EN_Z_lt : V2_Z * EN_Z < 2 ^ 98 := by
    have h1 : V2_Z * EN_Z < 2 ^ 34 * 2 ^ 64 := by
      rcases eq_or_lt_of_le hEN_Z_nn with h | h
      · rw [← h]; simp
      · calc V2_Z * EN_Z < 2 ^ 34 * EN_Z := by
              apply mul_lt_mul_of_pos_right hV2_Z_lt h
            _ ≤ 2 ^ 34 * 2 ^ 64 := by
              apply mul_le_mul_of_nonneg_left (le_of_lt hEN_Z_lt) (by norm_num)
    have h2 : (2 : ℤ) ^ 34 * 2 ^ 64 = 2 ^ 98 := by norm_num
    linarith
  have hV2EN_Z_nn : 0 ≤ V2_Z * EN_Z := mul_nonneg hV2_Z_nn hEN_Z_nn
  have hV2EN_nat_lt : V2N * EN < 2 ^ 98 := by
    have h : (V2N * EN : ℤ) < (2 ^ 98 : ℤ) := by
      push_cast; exact hV2EN_Z_lt
    exact_mod_cast h
  -- Define q3, r3 (Nat).
  set q3N : ℕ := V2N * EN / 2 ^ 65 with hq3N_def
  set r3N : ℕ := V2N * EN % 2 ^ 65 with hr3N_def
  have hr3N_lt : r3N < 2 ^ 65 := Nat.mod_lt _ (by norm_num)
  have hVE_divmod : V2N * EN = q3N * 2 ^ 65 + r3N := by
    have := Nat.div_add_mod (V2N * EN) (2 ^ 65)
    omega
  set q3_Z : ℤ := (q3N : ℤ) with hq3_Z_def
  set r3_Z : ℤ := (r3N : ℤ) with hr3_Z_def
  have hq3_Z_nn : 0 ≤ q3_Z := Int.natCast_nonneg _
  have hr3_Z_nn : 0 ≤ r3_Z := Int.natCast_nonneg _
  have hr3_Z_lt : r3_Z < 2 ^ 65 := by show (r3N : ℤ) < 2 ^ 65; exact_mod_cast hr3N_lt
  have hH2 : V2_Z * EN_Z = q3_Z * 2 ^ 65 + r3_Z := by
    have := hVE_divmod
    rw [hV2_Z_def, hEN_Z_def, hq3_Z_def, hr3_Z_def]
    exact_mod_cast this
  -- V3N = (V2*2^31 + q3) mod 2^64.
  have hV3N_eq : V3N = (V2N * 2 ^ 31 + V2N * EN / 2 ^ 65) % 2 ^ 64 :=
    toNat_computeV3 v2' e'
  -- v'_3_Z (Int).
  set v3m_Z : ℤ := V2_Z * 2 ^ 31 + q3_Z with hv3m_Z_def
  -- Key identity.
  have hH3 : 2 * EN_Z = E2_Z - eps_Z := by rw [hEN_val]; exact hE_math_eq
  have hKey :
      (2 ^ 66 : ℤ) * (2 ^ 128 - v3m_Z * D_Z)
        = E2_Z ^ 2 + eps_Z * (2 ^ 97 - E2_Z) + 2 * r3_Z * D_Z := by
    rw [hv3m_Z_def]
    linear_combination (eps_Z - E2_Z - 2 ^ 97) * hH1 + (2 * D_Z) * hH2 + (-D_Z * V2_Z) * hH3
  -- e'_3_Z := 2^128 - v3m_Z * D_Z.
  set e3m_Z : ℤ := 2 ^ 128 - v3m_Z * D_Z with he3m_Z_def
  have hKey' : (2 ^ 66 : ℤ) * e3m_Z = E2_Z ^ 2 + eps_Z * (2 ^ 97 - E2_Z) + 2 * r3_Z * D_Z :=
    hKey
  -- Shrink the context: drop now-unused hypotheses and hide `set` definitions to
  -- keep subsequent tactics cheap.
  clear hV2_mod2 hV2_mod2_le hV2_mod2_nn hH1 hH3 hKey hE_math_eq hEN_val
    hE_math_nn hE_math_lt hD0_Z_le hD0_Z_nn hD0N_eq hD63N_eq h2D63 h2D63_Z
    hV2D_lt_int hV2D_lt_nat hV2EN_Z_nn hV2EN_nat_lt hVE_divmod
  clear_value E2_Z eps_Z E_math_Z D0_Z D63_Z q3_Z r3_Z EN_Z v3m_Z e3m_Z
  -- RHS > 0.
  have hE2sq_ge : (1 : ℤ) ≤ E2_Z ^ 2 := by
    have h1 : (1 : ℤ) * 1 ≤ E2_Z * E2_Z := mul_le_mul hE2_Z_ge hE2_Z_ge (by norm_num) (by linarith)
    rw [sq]; linarith
  have h_97_sub_E2_pos : (0 : ℤ) ≤ 2 ^ 97 - E2_Z := by
    have : E2_Z < 2 ^ 97 := by linarith
    linarith
  have heps_mul_nn : 0 ≤ eps_Z * (2 ^ 97 - E2_Z) := mul_nonneg heps_Z_nn h_97_sub_E2_pos
  have h2r3D_nn : 0 ≤ 2 * r3_Z * D_Z := by
    have : 0 ≤ 2 * r3_Z := by linarith
    exact mul_nonneg this hD_Z_nn
  have hRHS_ge_1 : (1 : ℤ) ≤ E2_Z ^ 2 + eps_Z * (2 ^ 97 - E2_Z) + 2 * r3_Z * D_Z := by
    linarith
  have h_2_66_pos : (0 : ℤ) < 2 ^ 66 := by norm_num
  have he3m_pos : 0 < e3m_Z := by
    by_contra h
    have hle : e3m_Z ≤ 0 := not_lt.mp h
    have : (2 : ℤ) ^ 66 * e3m_Z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_2_66_pos) hle
    linarith
  -- RHS < 2^67 * D.
  have hE2sq_lt : E2_Z ^ 2 < (873 * 2 ^ 53 + D_Z) ^ 2 := by
    have h_E2_pos_l : (0 : ℤ) ≤ E2_Z := by linarith
    have h_bnd_pos : (0 : ℤ) ≤ 873 * 2 ^ 53 + D_Z := by linarith
    rw [sq, sq]
    exact mul_lt_mul'' hE2_Z_lt_nat hE2_Z_lt_nat h_E2_pos_l h_E2_pos_l
  have heps_mul_le : eps_Z * (2 ^ 97 - E2_Z) ≤ 2 ^ 97 - E2_Z := by
    have h := mul_le_mul_of_nonneg_right heps_Z_le h_97_sub_E2_pos
    linarith
  have h2r3_le : 2 * r3_Z ≤ 2 ^ 66 := by linarith
  have h2r3D_le : 2 * r3_Z * D_Z ≤ 2 ^ 66 * D_Z :=
    mul_le_mul_of_nonneg_right h2r3_le hD_Z_nn
  have hRHS_le :
      E2_Z ^ 2 + eps_Z * (2 ^ 97 - E2_Z) + 2 * r3_Z * D_Z
        ≤ (873 * 2 ^ 53 + D_Z) ^ 2 + (2 ^ 97 - E2_Z) + 2 ^ 66 * D_Z := by
    linarith [hE2sq_lt, heps_mul_le, h2r3D_le]
  have hRHS_lt_2_67_D :
      E2_Z ^ 2 + eps_Z * (2 ^ 97 - E2_Z) + 2 * r3_Z * D_Z < 2 ^ 67 * D_Z := by
    have hD_sq : D_Z ^ 2 < 2 ^ 64 * D_Z := by
      have h := mul_lt_mul_of_pos_right hD_Z_lt hD_Z_pos
      rw [sq]; linarith
    have hexp1 : (873 * 2 ^ 53 + D_Z) ^ 2
        = 873 ^ 2 * 2 ^ 106 + 2 * 873 * 2 ^ 53 * D_Z + D_Z ^ 2 := by ring
    -- 873^2 = 762129 < 2^20, so 873^2 * 2^106 < 2^126.
    have hconst1 : (873 : ℤ) ^ 2 * 2 ^ 106 < 2 ^ 126 := by norm_num
    have hconst2 : (2 : ℤ) ^ 126 ≤ 2 ^ 63 * D_Z := by
      have h1 : (2 : ℤ) ^ 63 * 2 ^ 63 ≤ 2 ^ 63 * D_Z :=
        mul_le_mul_of_nonneg_left hD_Z_ge (by norm_num)
      have hp : (2 : ℤ) ^ 63 * 2 ^ 63 = 2 ^ 126 := by norm_num
      linarith
    have h97_le : (2 : ℤ) ^ 97 ≤ 2 ^ 34 * D_Z := by
      have h1 : (2 : ℤ) ^ 34 * 2 ^ 63 ≤ 2 ^ 34 * D_Z :=
        mul_le_mul_of_nonneg_left hD_Z_ge (by norm_num)
      have hp : (2 : ℤ) ^ 34 * 2 ^ 63 = 2 ^ 97 := by norm_num
      linarith
    -- Step A: bound (873*2^53+D)^2 by 2^126 + 2*873*2^53*D + 2^64*D.
    have hstepA : (873 * 2 ^ 53 + D_Z) ^ 2 < 2 ^ 126 + 2 * 873 * 2 ^ 53 * D_Z + 2 ^ 64 * D_Z := by
      linarith [hexp1, hconst1, hD_sq]
    -- Step B: total ≤ 2^126 + 2*873*2^53*D + 2^64*D + 2^97 + 2^66*D.
    have hstepB :
        E2_Z ^ 2 + eps_Z * (2 ^ 97 - E2_Z) + 2 * r3_Z * D_Z
          ≤ 2 ^ 126 + 2 * 873 * 2 ^ 53 * D_Z + 2 ^ 64 * D_Z + 2 ^ 97 + 2 ^ 66 * D_Z := by
      have he2lt : E2_Z ^ 2 < 2 ^ 126 + 2 * 873 * 2 ^ 53 * D_Z + 2 ^ 64 * D_Z :=
        lt_of_lt_of_le hE2sq_lt (le_of_lt hstepA)
      linarith [heps_mul_le, h2r3D_le, he2lt]
    -- Step C: 2^126 ≤ 2^63*D and 2^97 ≤ 2^34*D, combine.
    have hstepC :
        2 ^ 126 + 2 * 873 * 2 ^ 53 * D_Z + 2 ^ 64 * D_Z + 2 ^ 97 + 2 ^ 66 * D_Z
          ≤ 2 ^ 63 * D_Z + 2 * 873 * 2 ^ 53 * D_Z + 2 ^ 64 * D_Z + 2 ^ 34 * D_Z + 2 ^ 66 * D_Z := by
      linarith [hconst2, h97_le]
    -- Step D: combine coefficients and show < 2^67*D.
    have hstepD :
        2 ^ 63 * D_Z + 2 * 873 * 2 ^ 53 * D_Z + 2 ^ 64 * D_Z + 2 ^ 34 * D_Z + 2 ^ 66 * D_Z
          = (2 ^ 63 + 2 * 873 * 2 ^ 53 + 2 ^ 64 + 2 ^ 34 + 2 ^ 66) * D_Z := by ring
    have hconst3 : (2 : ℤ) ^ 63 + 2 * 873 * 2 ^ 53 + 2 ^ 64 + 2 ^ 34 + 2 ^ 66 < 2 ^ 67 := by norm_num
    have hstepE :
        (2 ^ 63 + 2 * 873 * 2 ^ 53 + 2 ^ 64 + 2 ^ 34 + 2 ^ 66) * D_Z < 2 ^ 67 * D_Z :=
      mul_lt_mul_of_pos_right hconst3 hD_Z_pos
    linarith only [hstepB, hstepC, hstepD, hstepE]
  have he3m_lt : e3m_Z < 2 * D_Z := by
    have h1 : (2 ^ 66 : ℤ) * e3m_Z < 2 ^ 67 * D_Z := by rw [hKey']; exact hRHS_lt_2_67_D
    have h2 : (2 ^ 67 : ℤ) * D_Z = 2 ^ 66 * (2 * D_Z) := by ring
    rw [h2] at h1
    exact lt_of_mul_lt_mul_left h1 (le_of_lt h_2_66_pos)
  -- v3m_Z ∈ [2^64, 2^65).
  have hv3mD_lt : v3m_Z * D_Z < 2 ^ 128 := by
    rw [he3m_Z_def] at he3m_pos; linarith only [he3m_pos]
  have hv3mD_gt : 2 ^ 128 - 2 * D_Z < v3m_Z * D_Z := by
    rw [he3m_Z_def] at he3m_lt; linarith only [he3m_lt]
  have hv3m_lt_2_65 : v3m_Z < 2 ^ 65 := by
    have h_conv : v3m_Z * D_Z < 2 ^ 65 * D_Z := by
      have h1 : (2 : ℤ) ^ 65 * D_Z ≥ 2 ^ 65 * 2 ^ 63 :=
        mul_le_mul_of_nonneg_left hD_Z_ge (by norm_num)
      have hp : (2 : ℤ) ^ 65 * 2 ^ 63 = 2 ^ 128 := by norm_num
      linarith only [h1, hp, hv3mD_lt]
    exact lt_of_mul_lt_mul_right h_conv hD_Z_nn
  have hv3m_ge_2_64 : 2 ^ 64 ≤ v3m_Z := by
    by_contra h
    have h1 : v3m_Z ≤ 2 ^ 64 - 1 := by linarith only [not_le.mp h]
    have h2 : v3m_Z * D_Z ≤ (2 ^ 64 - 1) * D_Z := by
      by_cases hvnn : 0 ≤ v3m_Z
      · exact mul_le_mul_of_nonneg_right h1 hD_Z_nn
      · push Not at hvnn
        have hvD_neg : v3m_Z * D_Z < 0 := mul_neg_of_neg_of_pos hvnn hD_Z_pos
        have hmul_nn : (0 : ℤ) ≤ (2 ^ 64 - 1) * D_Z :=
          mul_nonneg (by norm_num) hD_Z_nn
        linarith only [hvD_neg, hmul_nn]
    have h3 : (2 ^ 64 - 1) * D_Z = 2 ^ 64 * D_Z - D_Z := by ring
    have h4 : (2 : ℤ) ^ 64 * D_Z ≤ 2 ^ 128 - D_Z := by
      have h5 : D_Z ≤ 2 ^ 64 - 1 := by linarith only [hD_Z_lt]
      have h6 : 2 ^ 64 * D_Z ≤ 2 ^ 64 * (2 ^ 64 - 1) :=
        mul_le_mul_of_nonneg_left h5 (by norm_num)
      have h7 : (2 : ℤ) ^ 64 * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 64 := by ring
      linarith only [h6, h7]
    have h8 : v3m_Z * D_Z ≤ 2 ^ 128 - 2 * D_Z := by linarith only [h2, h3, h4]
    linarith only [h8, hv3mD_gt]
  -- V3N.toNat = v3m_Z - 2^64.
  have hV3N_val : (V3N : ℤ) = v3m_Z - 2 ^ 64 := by
    rw [hV3N_eq]
    -- (V2N * 2^31 + V2N * EN / 2^65) % 2^64 in Nat.
    set S : ℕ := V2N * 2 ^ 31 + V2N * EN / 2 ^ 65 with hS_def
    have hS_int : (S : ℤ) = v3m_Z := by
      rw [hv3m_Z_def, hV2_Z_def, hq3_Z_def, hq3N_def, hS_def]
      push_cast; ring
    -- S mod 2^64 = v3m_Z - 2^64 (since S ∈ [2^64, 2^65)).
    have hS_lt : (S : ℤ) < 2 ^ 65 := by rw [hS_int]; exact hv3m_lt_2_65
    have hS_ge : (2 : ℤ) ^ 64 ≤ S := by rw [hS_int]; exact hv3m_ge_2_64
    have hS_ge_nat : 2 ^ 64 ≤ S := by exact_mod_cast hS_ge
    have hS_lt_nat : S < 2 ^ 65 := by exact_mod_cast hS_lt
    have hSmod : S % 2 ^ 64 = S - 2 ^ 64 := by omega
    have hSmod_int : ((S % 2 ^ 64 : ℕ) : ℤ) = (S : ℤ) - 2 ^ 64 := by
      rw [hSmod]
      rw [Int.ofNat_sub (by exact_mod_cast hS_ge)]
      push_cast; ring
    rw [hSmod_int, hS_int]
  -- Connect e3 d hd to e3m_Z.
  have he3_eq : e3 d hd = e3m_Z := by
    unfold e3
    show (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + (V3N : ℤ)) * D_Z = e3m_Z
    rw [hV3N_val, he3m_Z_def]; ring
  refine ⟨?_, ?_⟩
  · rw [he3_eq]; exact he3m_pos
  · rw [he3_eq]; show e3m_Z < 2 * (D : ℤ); exact he3m_lt

/-- `computeV4` modular identity: `v_3 ≡ v_4 + d + hi + carry (mod 2^64)`, where
`(hi, lo) = wideMul v_3 d` and `carry = 1` iff `lo + d` overflows (i.e.
`lo.toNat + d.toNat ≥ 2^64`). -/
theorem computeV4_add_mod_eq (v3 d : UInt64) :
    ((computeV4 v3 d).toNat + d.toNat + (wideMul v3 d).1.toNat
        + (if 2 ^ 64 ≤ (wideMul v3 d).2.toNat + d.toNat then 1 else 0)) % 2 ^ 64
      = v3.toNat := by
  have hLO_lt : (wideMul v3 d).2.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hHI_lt : (wideMul v3 d).1.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hV3_lt : v3.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD_lt : d.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  -- Express computeV4 with wideMul destructured.
  have hV4_eq : computeV4 v3 d =
      v3 - d - (wideMul v3 d).1 -
        (if (wideMul v3 d).2 + d < d then (1 : UInt64) else 0) := by
    unfold computeV4; rfl
  rw [hV4_eq]
  -- Convert UInt64 carry to Nat carry.
  have hcarry_eq : (if (wideMul v3 d).2 + d < d then (1 : UInt64) else 0).toNat =
      (if 2 ^ 64 ≤ (wideMul v3 d).2.toNat + d.toNat then 1 else 0) := by
    have hLO'_toNat : ((wideMul v3 d).2 + d).toNat
        = ((wideMul v3 d).2.toNat + d.toNat) % 2 ^ 64 :=
      _root_.UInt64.toNat_add _ _
    by_cases h : 2 ^ 64 ≤ (wideMul v3 d).2.toNat + d.toNat
    · have hlt : (wideMul v3 d).2 + d < d := by
        rw [_root_.UInt64.lt_iff_toNat_lt, hLO'_toNat]
        have hmod : ((wideMul v3 d).2.toNat + d.toNat) % 2 ^ 64
            = (wideMul v3 d).2.toNat + d.toNat - 2 ^ 64 := by omega
        rw [hmod]; omega
      rw [if_pos hlt, if_pos h]; rfl
    · have hsum_lt : (wideMul v3 d).2.toNat + d.toNat < 2 ^ 64 := by
        push Not at h; exact h
      have hLO'_eq : ((wideMul v3 d).2 + d).toNat = (wideMul v3 d).2.toNat + d.toNat := by
        rw [hLO'_toNat, Nat.mod_eq_of_lt hsum_lt]
      have hnlt : ¬ (wideMul v3 d).2 + d < d := by
        rw [_root_.UInt64.lt_iff_toNat_lt, hLO'_eq]; omega
      rw [if_neg hnlt, if_neg h]; rfl
  rw [_root_.UInt64.toNat_sub, _root_.UInt64.toNat_sub, _root_.UInt64.toNat_sub, hcarry_eq]
  set V3N : ℕ := v3.toNat
  set DN : ℕ := d.toNat
  set HIN : ℕ := (wideMul v3 d).1.toNat
  set LON : ℕ := (wideMul v3 d).2.toNat
  set carryN : ℕ := if 2 ^ 64 ≤ LON + DN then 1 else 0 with hcarryN_def
  have hcarryN_le : carryN ≤ 1 := by rw [hcarryN_def]; split <;> omega
  show (((2 ^ 64 - carryN + ((2 ^ 64 - HIN + ((2 ^ 64 - DN + V3N) % 2 ^ 64)) % 2 ^ 64)) % 2 ^ 64)
      + DN + HIN + carryN) % 2 ^ 64 = V3N
  omega

/-- `e4 = 2^128 − (2^64 + v_4) · d` as an integer. -/
def e4 (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) : ℤ :=
  let v0 := computeV0 (computeD9 d) (computeD9_sub_256_lt d hd)
  let v1 := computeV1 v0 (computeD40 d)
  let v2 := computeV2 v1 (computeD40 d)
  let e  := computeE v2 (computeD63 d) (computeD0 d)
  let v3 := computeV3 v2 e
  let v4 := computeV4 v3 d
  (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + (v4.toNat : ℤ)) * (d.toNat : ℤ)

/-- Pure arithmetic core of Bound 10: given the key identities relating `V4N`, `V3N`,
`HIN`, `LON`, `carryN` from the algorithm, deduce `0 < e4 ≤ D`. -/
private lemma e4_core
    (V3N V4N D HI LON carryN : ℕ)
    (hD_lt : D < 2 ^ 64) (hD_ge : 2 ^ 63 ≤ D)
    (hV3N_lt : V3N < 2 ^ 64) (hV4N_lt : V4N < 2 ^ 64)
    (hHI_lt : HI < 2 ^ 64) (hLON_lt : LON < 2 ^ 64)
    (hcarryN_def : carryN = if 2 ^ 64 ≤ LON + D then 1 else 0)
    (hwide : HI * 2 ^ 64 + LON = V3N * D)
    (hV4mod : (V4N + D + HI + carryN) % 2 ^ 64 = V3N)
    (he3_pos : 0 < (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + V3N) * D)
    (he3_lt : (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + V3N) * D < 2 * (D : ℤ)) :
    0 < (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + V4N) * D ∧
      (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + V4N) * D ≤ (D : ℤ) := by
  have hD_pos : 0 < D := by omega
  have hcarryN_le : carryN ≤ 1 := by rw [hcarryN_def]; split <;> omega
  -- Nat version of e3 bounds: (2^64 + V3N) * D ≤ 2^128 - 1 and ≥ 2^128 - 2*D + 1.
  have hV3D_lt_Z : ((2 ^ 64 + V3N : ℕ) : ℤ) * D < 2 ^ 128 := by push_cast; linarith
  have hV3D_lt_nat : (2 ^ 64 + V3N) * D < 2 ^ 128 := by exact_mod_cast hV3D_lt_Z
  -- hV4mod as integer identity.
  have hk_eq_nat : V4N + D + HI + carryN =
      V3N + ((V4N + D + HI + carryN) / 2 ^ 64) * 2 ^ 64 := by
    have := Nat.div_add_mod (V4N + D + HI + carryN) (2 ^ 64)
    omega
  set kN : ℕ := (V4N + D + HI + carryN) / 2 ^ 64 with hkN_def
  -- Case split on e3 ≤ D (Case A) vs e3 > D (Case B).
  by_cases hcase : (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + V3N) * D ≤ D
  · -- Case A: e3 ≤ D.
    -- Nat: (2^128 + V3N) * D ≥ 2^128 - D.
    have hV3D_ge_nat : 2 ^ 128 ≤ (2 ^ 64 + V3N) * D + D := by
      have h : (2 ^ 128 : ℤ) ≤ ((2 ^ 64 + V3N : ℕ) : ℤ) * D + D := by push_cast; linarith
      exact_mod_cast h
    -- (2^64 + V3N)*D = 2^64*D + V3N*D = 2^64*(D + HI) + LON.
    have hmul_expand : (2 ^ 64 + V3N) * D = 2 ^ 64 * (D + HI) + LON := by
      have : (2 ^ 64 + V3N) * D = 2 ^ 64 * D + V3N * D := by ring
      rw [this, ← hwide]; ring
    -- Thus: 2^128 - D ≤ 2^64*(D+HI) + LON < 2^128, so D + HI = 2^64 - 1.
    have hDHI : D + HI = 2 ^ 64 - 1 := by
      rw [hmul_expand] at hV3D_ge_nat hV3D_lt_nat
      -- 2^128 - D ≤ 2^64*(D+HI) + LON ≤ 2^128 - 1
      -- Both D + HI = 2^64 - 1 and D + HI = 2^64 need to be considered.
      -- D + HI = 2^64 would make 2^128 ≤ 2^128 + LON ≤ 2^128 - 1, impossible since LON ≥ 0.
      -- (Note we need strict < from hV3D_lt_nat.)
      omega
    -- LON = 2^64 - e3 (so 0 < LON ≤ 2^64 - 1; specifically LON ≥ 2^64 - D).
    -- From hmul_expand with D+HI = 2^64 - 1: (2^64+V3N)*D = 2^64*(2^64 - 1) + LON = 2^128 - 2^64 + LON.
    -- So e3 = 2^128 - (2^128 - 2^64 + LON) = 2^64 - LON.
    -- Case A: e3 ≤ D so LON ≥ 2^64 - D, so LON + D ≥ 2^64, so carryN = 1.
    have hLON_ge : 2 ^ 64 ≤ LON + D := by
      have h1 : (2 ^ 64 + V3N) * D = 2 ^ 128 - 2 ^ 64 + LON := by
        rw [hmul_expand, hDHI]; ring
      -- From he3_pos and hcase (e3 ≤ D):
      -- 0 < 2^128 - (2^128 - 2^64 + LON) = 2^64 - LON, so LON < 2^64 (already known).
      -- 2^128 - (2^128 - 2^64 + LON) ≤ D, so 2^64 - LON ≤ D, so LON ≥ 2^64 - D.
      have hLON_ge_Z : (2 ^ 64 : ℤ) - D ≤ LON := by
        have hh : (2 ^ 128 : ℤ) - ((2 ^ 64 + V3N : ℕ) : ℤ) * D ≤ D := by push_cast; linarith
        have hh1_Z : ((2 ^ 64 + V3N : ℕ) : ℤ) * D + (2 ^ 64 : ℤ) = 2 ^ 128 + LON := by
          have h1' : (2 ^ 64 + V3N) * D + 2 ^ 64 = 2 ^ 128 + LON := by
            have hbig : 2 ^ 128 ≥ 2 ^ 64 := by norm_num
            omega
          exact_mod_cast h1'
        linarith
      have h_nat : 2 ^ 64 ≤ LON + D := by
        have : (2 ^ 64 : ℤ) ≤ (LON : ℤ) + D := by linarith
        have hh : (2 ^ 64 : ℕ) ≤ LON + D := by exact_mod_cast this
        exact hh
      exact h_nat
    have hcarryN_val : carryN = 1 := by rw [hcarryN_def]; rw [if_pos hLON_ge]
    -- Now V4N + D + HI + 1 = V3N + kN * 2^64.
    -- D + HI = 2^64 - 1, so V4N + 2^64 = V3N + kN * 2^64.
    -- With 0 ≤ V4N < 2^64 and 0 ≤ V3N < 2^64, kN = 1 and V4N = V3N.
    have hV4_eq : V4N = V3N := by
      rw [hcarryN_val] at hk_eq_nat
      -- V4N + D + HI + 1 = V3N + kN * 2^64
      -- D + HI = 2^64 - 1, so V4N + 2^64 = V3N + kN * 2^64
      have : V4N + 2 ^ 64 = V3N + kN * 2 ^ 64 := by omega
      -- Hence V4N - V3N = (kN - 1) * 2^64, and |V4N - V3N| < 2^64, so kN = 1, V4N = V3N.
      omega
    -- Conclude e4 = e3, and use he3_pos, hcase.
    rw [hV4_eq]
    exact ⟨he3_pos, hcase⟩
  · -- Case B: e3 > D.
    push Not at hcase
    -- Nat: (2^64 + V3N) * D ≤ 2^128 - D - 1 and ≥ 2^128 - 2*D + 1.
    have hV3D_le_nat : (2 ^ 64 + V3N) * D + D + 1 ≤ 2 ^ 128 := by
      have h : ((2 ^ 64 + V3N : ℕ) : ℤ) * D + D + 1 ≤ 2 ^ 128 := by push_cast; linarith
      exact_mod_cast h
    have hV3D_gt_nat : 2 ^ 128 < (2 ^ 64 + V3N) * D + 2 * D := by
      have h : (2 ^ 128 : ℤ) < ((2 ^ 64 + V3N : ℕ) : ℤ) * D + 2 * D := by push_cast; linarith
      exact_mod_cast h
    -- V3N + 1 < 2^64 (from Case B and D ≥ 2^63).
    have hV3N_succ_lt : V3N + 1 < 2 ^ 64 := by
      -- (2^65 - 1) * D ≥ 2^128 - D - 1 would require V3N = 2^64 - 1 in Case B, but D ≥ 2^63 gives contradiction.
      by_contra habs
      push Not at habs
      have hV3N_eq : V3N = 2 ^ 64 - 1 := by omega
      -- (2^64 + V3N) * D = (2^65 - 1) * D = 2^65 * D - D.
      -- Case B: (2^65 - 1) * D ≤ 2^128 - D - 1, so 2^65 * D ≤ 2^128 - 1, so D ≤ (2^128 - 1)/2^65 < 2^63. Contradicts D ≥ 2^63.
      have : 2 ^ 65 * D ≤ 2 ^ 128 - 1 := by
        have := hV3D_le_nat
        rw [hV3N_eq] at this
        have h2 : 2 ^ 64 + (2 ^ 64 - 1) = 2 ^ 65 - 1 := by norm_num
        rw [h2] at this
        have : (2 ^ 65 - 1) * D + D + 1 ≤ 2 ^ 128 := this
        have h3 : (2 ^ 65 - 1) * D + D = 2 ^ 65 * D := by ring
        omega
      omega
    -- (2^64 + V3N)*D = 2^64*(D + HI) + LON.
    have hmul_expand : (2 ^ 64 + V3N) * D = 2 ^ 64 * (D + HI) + LON := by
      have : (2 ^ 64 + V3N) * D = 2 ^ 64 * D + V3N * D := by ring
      rw [this, ← hwide]; ring
    rw [hmul_expand] at hV3D_le_nat hV3D_gt_nat
    -- 2^128 - 2*D + 1 ≤ 2^64*(D+HI) + LON ≤ 2^128 - D - 1.
    -- So D + HI ∈ {2^64 - 2, 2^64 - 1}.
    have hDHI_range : D + HI = 2 ^ 64 - 1 ∨ D + HI = 2 ^ 64 - 2 := by omega
    -- In either case, HI + D + carryN = 2^64 - 1.
    have hHDsum : HI + D + carryN = 2 ^ 64 - 1 := by
      rcases hDHI_range with h | h
      · -- D + HI = 2^64 - 1: then LON ≤ 2^64 - D - 1 < 2^64 - D, so LON + D < 2^64, carryN = 0.
        have hLON_bound : LON ≤ 2 ^ 64 - D - 1 := by
          rw [h] at hV3D_le_nat; omega
        have hnot : ¬ 2 ^ 64 ≤ LON + D := by omega
        have hcarryN_val : carryN = 0 := by rw [hcarryN_def]; rw [if_neg hnot]
        omega
      · -- D + HI = 2^64 - 2: then LON ≥ 2^64 + ... and LON + D ≥ 2^64, carryN = 1.
        -- hV3D_gt_nat: 2^128 < 2^64*(D+HI) + LON + 2*D = 2^128 - 2*2^64 + LON + 2*D, so LON > 2*2^64 - 2*D.
        have hLON_large : 2 * 2 ^ 64 - 2 * D + 1 ≤ LON := by
          rw [h] at hV3D_gt_nat
          have : 2 ^ 128 + 1 ≤ 2 ^ 64 * (2 ^ 64 - 2) + LON + 2 * D := by omega
          have h2 : 2 ^ 64 * (2 ^ 64 - 2) = 2 ^ 128 - 2 * 2 ^ 64 := by ring
          omega
        -- D ≥ 2^63, so 2 * 2^64 - 2*D ≤ 2*2^64 - 2*2^63 = 2^64, so LON ≥ 2^64 - something.
        have hLON_plus_D : 2 ^ 64 ≤ LON + D := by
          -- LON ≥ 2*2^64 - 2*D + 1, so LON + D ≥ 2*2^64 - D + 1 ≥ 2^64 + 1 (since D ≤ 2^64 - 1).
          omega
        have hcarryN_val : carryN = 1 := by rw [hcarryN_def]; rw [if_pos hLON_plus_D]
        omega
    -- hk_eq: V4N + D + HI + carryN = V3N + kN * 2^64, with HI + D + carryN = 2^64 - 1.
    -- So V4N + 2^64 - 1 = V3N + kN * 2^64, V4N = V3N + 1 + (kN - 1)*2^64.
    -- With V4N, V3N+1 < 2^64 and V4N ≥ 0: kN = 1 and V4N = V3N + 1.
    have hV4_eq : V4N = V3N + 1 := by
      have hh : V4N + (HI + D + carryN) = V3N + kN * 2 ^ 64 := by
        have := hk_eq_nat; omega
      rw [hHDsum] at hh
      omega
    rw [hV4_eq]
    -- e4 = 2^128 - (2^64 + V3N + 1) * D = e3 - D.
    have he4_eq_Z : (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + (V3N + 1 : ℕ)) * D
        = (2 ^ 128 - (2 ^ 64 + (V3N : ℤ)) * D) - D := by push_cast; ring
    rw [he4_eq_Z]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith

/-- Bound 10 from Möller–Granlund: `0 < e4 ≤ d`, assuming `d` is normalized
(`2^63 ≤ d`). -/
theorem e4_pos_and_le (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    0 < e4 d hd ∧ e4 d hd ≤ d.toNat := by
  obtain ⟨he3_pos, he3_lt⟩ := e3_pos_and_lt d hd
  set D : ℕ := d.toNat with hD_def
  set v2' : UInt64 :=
    computeV2
      (computeV1 (computeV0 (computeD9 d) (computeD9_sub_256_lt d hd)) (computeD40 d))
      (computeD40 d) with hv2'_def
  set e' : UInt64 := computeE v2' (computeD63 d) (computeD0 d) with he'_def
  set v3' : UInt64 := computeV3 v2' e' with hv3'_def
  set V3N : ℕ := v3'.toNat with hV3N_def
  set v4' : UInt64 := computeV4 v3' d with hv4'_def
  set V4N : ℕ := v4'.toNat with hV4N_def
  set HIN : ℕ := (wideMul v3' d).1.toNat with hHIN_def
  set LON : ℕ := (wideMul v3' d).2.toNat with hLON_def
  have hD_lt : D < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD_ge : 2 ^ 63 ≤ D := hd
  have hV3_lt : V3N < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hV4_lt : V4N < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hHI_lt : HIN < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hLO_lt : LON < 2 ^ 64 := _root_.UInt64.toNat_lt _
  set carryN : ℕ := if 2 ^ 64 ≤ LON + D then 1 else 0 with hcarryN_def
  have hwide : HIN * 2 ^ 64 + LON = V3N * D := toNat_wideMul v3' d
  have hV4mod : (V4N + D + HIN + carryN) % 2 ^ 64 = V3N :=
    computeV4_add_mod_eq v3' d
  have he3_val : e3 d hd = (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + (V3N : ℤ)) * (D : ℤ) := rfl
  have he4_val : e4 d hd = (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + (V4N : ℤ)) * (D : ℤ) := rfl
  rw [he3_val] at he3_pos he3_lt
  rw [he4_val]
  exact e4_core V3N V4N D HIN LON carryN hD_lt hD_ge hV3_lt hV4_lt hHI_lt hLO_lt
    hcarryN_def hwide hV4mod he3_pos he3_lt

/-- Main correctness theorem for `reciprocal` (Möller–Granlund Algorithm 2):
for a normalized 64-bit divisor `d` (`2^63 ≤ d.toNat`), the returned value equals
`⌊(2^128 − 1) / d⌋ − 2^64`. -/
theorem toNat_reciprocal (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    (reciprocal d hd).toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64 := by
  obtain ⟨he4_pos, he4_le⟩ := e4_pos_and_le d hd
  set v4 : ℕ := (reciprocal d hd).toNat with hv4_def
  have he4_rfl : e4 d hd = (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + (v4 : ℤ)) * (d.toNat : ℤ) := rfl
  rw [he4_rfl] at he4_pos he4_le
  have hv4_lt : v4 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD_lt : d.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD_pos : 0 < d.toNat := by omega
  have hv4d_lt : (2 ^ 64 + v4) * d.toNat < 2 ^ 128 := by
    have : (((2 ^ 64 + v4 : ℕ) : ℤ)) * d.toNat < 2 ^ 128 := by push_cast; linarith
    exact_mod_cast this
  have hv4d_ge : 2 ^ 128 ≤ (2 ^ 64 + v4 + 1) * d.toNat := by
    have : (2 ^ 128 : ℤ) ≤ (((2 ^ 64 + v4 + 1 : ℕ) : ℤ)) * d.toNat := by push_cast; linarith
    exact_mod_cast this
  have hdiv_eq : (2 ^ 128 - 1) / d.toNat = 2 ^ 64 + v4 := by
    apply Nat.div_eq_of_lt_le
    · show (2 ^ 64 + v4) * d.toNat ≤ 2 ^ 128 - 1
      omega
    · show 2 ^ 128 - 1 < (2 ^ 64 + v4 + 1) * d.toNat
      omega
  omega

end UInt64

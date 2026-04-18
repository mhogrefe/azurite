import Azurite.UInt64.Equiv.Basic
import Azurite.UInt64.Reciprocal

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

set_option maxRecDepth 2000 in
/-- `(computeV0 d9).toNat = (2^19 − 3·2^8) / d9.toNat` when `d9 ∈ [256, 511]`. -/
theorem toNat_computeV0 (d9 : UInt64) (h256 : 256 ≤ d9.toNat) (h511 : d9.toNat ≤ 511) :
    (computeV0 d9).toNat = (2 ^ 19 - 3 * 2 ^ 8) / d9.toNat := by
  unfold computeV0
  rw [reciprocalTable_eq]
  have hidx_lt : (d9 - 256).toNat < 256 := by
    rw [_root_.UInt64.toNat_sub]
    show (2 ^ 64 - (256 : UInt64).toNat + d9.toNat) % 2 ^ 64 < 256
    have h256' : ((256 : UInt64).toNat) = 256 := rfl
    rw [h256']
    have : 2 ^ 64 - 256 + d9.toNat = 2 ^ 64 + (d9.toNat - 256) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega
  have hidx_size : (d9 - 256).toNat < (Array.ofFn (n := 256)
      fun i => ((2 ^ 19 - 3 * 2 ^ 8) / (i.val + 256) : Nat).toUInt16).size := by
    simpa using hidx_lt
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
def e0 (d : UInt64) : ℤ :=
  (2 ^ 50 : ℤ) -
    ((computeV0 (computeD9 d)).toNat : ℤ) * ((computeD40 d).toNat : ℤ)

/-- Bound 6 from Möller–Granlund: `|e0| < 5·2^39` (i.e. `(5/8)·2^42`), assuming
`d` is normalized (`2^63 ≤ d`). -/
theorem abs_e0_lt (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    |e0 d| < 5 * 2 ^ 39 := by
  -- Set up Nat variables for d9, d40, v0.
  set d9 := (computeD9 d).toNat with hd9_def
  set d40 := (computeD40 d).toNat with hd40_def
  set v0 := (computeV0 (computeD9 d)).toNat with hv0_def
  -- Bounds on d9.
  obtain ⟨hd9_lo, hd9_hi⟩ := computeD9_bounds d hd
  -- Bounds on d40, and the split d40 = 2^31·d9 + d'.
  obtain ⟨hd40_lo, hd40_hi⟩ := computeD40_bounds d hd
  obtain ⟨hd40_split, hd'_lo, hd'_hi⟩ := computeD40_split d hd
  set d' := d40 - 2 ^ 31 * d9 with hd'_def
  -- v0 = T / d9 where T = 2^19 - 3·2^8.
  have hv0_eq : v0 = (2 ^ 19 - 3 * 2 ^ 8) / d9 := toNat_computeV0 _ hd9_lo hd9_hi
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
def e1 (d : UInt64) : ℤ :=
  (2 ^ 60 : ℤ) -
    ((computeV1 (computeV0 (computeD9 d)) (computeD40 d)).toNat : ℤ) *
    ((computeD40 d).toNat : ℤ)

set_option maxHeartbeats 400000 in
/-- Bound 7 from Möller–Granlund: `0 < e1 < 29·2^38` (i.e. `(29/32)·2^43`),
assuming `d` is normalized (`2^63 ≤ d`). -/
theorem e1_pos_and_lt (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    0 < e1 d ∧ e1 d < 29 * 2 ^ 38 := by
  set d9 := (computeD9 d).toNat with hd9_def
  set d40 := (computeD40 d).toNat with hd40_def
  set v0 := computeV0 (computeD9 d) with hv0_def
  set V : ℕ := v0.toNat with hV_def
  obtain ⟨hd9_lo, hd9_hi⟩ := computeD9_bounds d hd
  obtain ⟨hd40_lo, hd40_hi⟩ := computeD40_bounds d hd
  have hV_eq : V = (2 ^ 19 - 3 * 2 ^ 8) / d9 := toNat_computeV0 _ hd9_lo hd9_hi
  have hV_le : V ≤ 2045 := by
    have h1 : (2 ^ 19 - 3 * 2 ^ 8) / d9 ≤ (2 ^ 19 - 3 * 2 ^ 8) / 256 :=
      Nat.div_le_div_left hd9_lo (by norm_num)
    have h2 : (2 ^ 19 - 3 * 2 ^ 8) / 256 = 2045 := by norm_num
    omega
  -- Bound 6 gives |e0| < 5·2^39.
  have habs := abs_e0_lt d hd
  have he0_def : e0 d = (2 ^ 50 : ℤ) - (V : ℤ) * (d40 : ℤ) := rfl
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
  have he0_sq_lt : ((2 ^ 50 : ℤ) - (V : ℤ) * d40) ^ 2 < 25 * 2 ^ 78 := by
    have hsq_bd : ((2 ^ 50 : ℤ) - (V : ℤ) * d40) ^ 2 < (5 * 2 ^ 39) ^ 2 :=
      sq_lt_sq' (by linarith) (by linarith)
    have h25 : ((5 : ℤ) * 2 ^ 39) ^ 2 = 25 * 2 ^ 78 := by norm_num
    linarith
  have hd40_le_int : (d40 : ℤ) ≤ 2 ^ 40 := by exact_mod_cast hd40_hi
  have hd40_nn : (0 : ℤ) ≤ d40 := le_of_lt hd40_pos_int
  have hfactor_step1 : (2 ^ 40 - r1 : ℤ) * d40 ≤ 2 ^ 40 * d40 :=
    mul_le_mul_of_nonneg_right (by linarith) hd40_nn
  have hfactor_step2 : (2 ^ 40 : ℤ) * d40 ≤ 2 ^ 40 * 2 ^ 40 :=
    mul_le_mul_of_nonneg_left hd40_le_int (by norm_num)
  have h_factor_le : (2 ^ 40 - r1 : ℤ) * d40 ≤ 2 ^ 80 := by
    have h3 : (2 ^ 40 : ℤ) * 2 ^ 40 = 2 ^ 80 := by norm_num
    linarith [hfactor_step1, hfactor_step2, h3]
  have h_sum_lt : (2 ^ 40 : ℤ) * E1 < 29 * 2 ^ 78 := by
    have hconst : (29 : ℤ) * 2 ^ 78 = 25 * 2 ^ 78 + 2 ^ 80 := by norm_num
    linarith [hE1_identity, he0_sq_lt, h_factor_le, hconst]
  have hE1_lt : E1 < 29 * 2 ^ 38 := by
    have hprod_eq : (2 ^ 40 : ℤ) * (29 * 2 ^ 38) = 29 * 2 ^ 78 := by ring
    have h_conv : (2 ^ 40 : ℤ) * E1 < 2 ^ 40 * (29 * 2 ^ 38) := by
      linarith [h_sum_lt, hprod_eq]
    exact lt_of_mul_lt_mul_left h_conv (le_of_lt h240_pos)
  exact ⟨hE1_pos, hE1_lt⟩

end UInt64

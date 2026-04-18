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

end UInt64

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Float64
import Azurite.AzFloat.Equiv.RoundScaled
import Azurite.AzInt.Equiv.ShiftLeft
import Azurite.AzRat.Equiv.ToSci
import Mathlib.Data.Nat.Log

/-!
# Correctness of the `Float` conversions

Lean's `Float` is a structure around `Float.Model`, so `(Float.ofModel m).toModel = m` holds by
definition and everything reduces to the model's unpacked form `UnpackedFloat`, to which we give
a value `UnpackedFloat.toVal : UnpackedFloat → Option EReal`.

* `toVal_ofFloat64`: `ofFloat64` is exact.
* `unpack_pack`: the model's `pack` and `unpack` are inverse on the unpacked floats that binary64
  can hold (`UnpackedFloat.Binary64`), so `ofFloat64 (toFloat64 x mode) = ofUnpacked (toUnpacked
  x mode)` (`ofFloat64_toFloat64`) once `toUnpacked` is shown to produce such floats.
* `toVal_toUnpacked_normal`: in the normal range the result is the rounding of `x` to 53 bits;
  `toVal_toUnpacked_subnormal`: below it, the rounding of `x` to a multiple of `2^-1074`.
-/

namespace Azurite.AzFloat

open Float.Model (UnpackedFloat Format)
open Float.Model.UnpackedFloat (Sign)
open RoundingTarget

/-! ### Values of unpacked floats -/

/-- The value of an unpacked float (`none` for `NaN`). -/
noncomputable def _root_.Float.Model.UnpackedFloat.toVal : UnpackedFloat → Option EReal
  | .notANumber => none
  | .infinity s => some (if s = .positive then ⊤ else ⊥)
  | .zero _ => some 0
  | .finite s m e _ =>
    some ((((if s = .positive then 1 else -1) * (m : ℝ) * (2 : ℝ) ^ e : ℝ)) : EReal)

theorem toInt_azIntOfInt (i : ℤ) : (azIntOfInt i).toInt = i := by
  cases i with
  | ofNat n =>
    show ((AzNat.ofNat n).toAzInt).toInt = _
    rw [toInt_toAzInt, AzNat.toNat_ofNat]; rfl
  | negSucc n =>
    show (-(AzNat.ofNat (n + 1)).toAzInt).toInt = _
    rw [AzInt.toInt_neg, toInt_toAzInt, AzNat.toNat_ofNat, Int.negSucc_eq]
    push_cast
    ring

theorem ofNat_ne_zero_of_pos {m : ℕ} (hm : 0 < m) : AzNat.ofNat m ≠ 0 := by
  intro h
  have := congrArg AzNat.toNat h
  rw [AzNat.toNat_ofNat, AzNat.toNat_zero] at this
  omega

/-- `ofUnpacked` is exact. -/
theorem toVal_ofUnpacked (u : UnpackedFloat) : toVal (ofUnpacked u) = u.toVal := by
  cases u with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => rfl
  | finite s m e hm =>
    show toVal (mkFinite _ _ 53 (AzNat.ofNat m)) = _
    rw [toVal_mkFinite _ _ _ _ (ofNat_ne_zero_of_pos hm), finiteVal_sign, finiteVal_true_eq,
      AzInt.toInt_add, toInt_azIntOfInt, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat,
      add_sub_cancel_right]
    simp only [UnpackedFloat.toVal, Option.some.injEq, EReal.coe_eq_coe_iff]
    cases s <;> simp

/-- `ofFloat64` is exact: the value of the result is the value of the `Float`'s unpacked model. -/
theorem toVal_ofFloat64 (f : Float) : toVal (ofFloat64 f) = f.toModel.unpack.toVal :=
  toVal_ofUnpacked _

/-! ### Small values -/

theorem smallToNat_eq (n : AzNat) (h : n.toNat < 2 ^ 64) : smallToNat n = n.toNat := by
  have key : ∀ (a : Array UInt64), (a = #[] ∨ ∃ u, a = #[u]) →
      (a.getD 0 0).toNat = AzNat.toNatLimbsList a.toList := by
    rintro _ (rfl | ⟨u, rfl⟩)
    · rfl
    · show u.toNat = AzNat.toNatLimbsList [u]
      simp [AzNat.toNatLimbsList]
  rcases Nat.lt_or_ge n.limbs.size 2 with hs | hs
  · show (n.limbs.getD 0 0).toNat = AzNat.toNatLimbsList n.limbs.toList
    apply key
    interval_cases hsz : n.limbs.size
    · exact Or.inl (Array.eq_empty_of_size_eq_zero hsz)
    · obtain ⟨u, hu⟩ : ∃ u, n.limbs.toList = [u] :=
        List.length_eq_one_iff.mp (by rw [Array.length_toList]; exact hsz)
      exact Or.inr ⟨u, Array.toList_inj.mp (by rw [hu])⟩
  · exfalso
    have := AzNat.toNat_pos_of_size_pos n (by omega)
    have h2 : 2 ^ 64 ≤ 2 ^ (64 * (n.limbs.size - 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-! ### `pack` and `unpack` -/

theorem unpackSign_packComponents {spec : Format} {sign : Sign} {exponent mantissa} :
    UnpackedFloat.unpackSign (UnpackedFloat.packComponents spec sign exponent mantissa)
      = sign.toBitVec := by
  ext i hi
  simp only [UnpackedFloat.unpackSign, UnpackedFloat.packComponents, BitVec.getElem_extractLsb',
    BitVec.getLsbD_append]
  rw [ite_eq_right (by omega), ite_eq_right (by omega),
    show spec.mantissaBitsWithoutImplicit + spec.exponentBits + i - spec.mantissaBitsWithoutImplicit
      - spec.exponentBits = i by omega, BitVec.getLsbD_eq_getElem]

theorem _root_.Float.Model.UnpackedFloat.Sign.ofBitVec_toBitVec (s : Sign) :
    Sign.ofBitVec s.toBitVec = s := by
  cases s <;> decide

/-- The unpacked floats that binary64 encodes faithfully: normal (53-bit mantissa, exponent in
`[−1074, 971]`) or subnormal (smaller mantissa, exponent `−1074`); the special values always. -/
def _root_.Float.Model.UnpackedFloat.Binary64 : UnpackedFloat → Prop
  | .finite _ m e _ => (2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971) ∨ (m < 2 ^ 52 ∧ e = -1074)
  | _ => True

theorem log2_eq_52 {m : ℕ} (h1 : 2 ^ 52 ≤ m) (h2 : m < 2 ^ 53) : m.log2 = 52 := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow h1 h2

theorem log2_lt_52 {m : ℕ} (h0 : 0 < m) (h2 : m < 2 ^ 52) : m.log2 + 1 ≠ 53 := by
  intro h
  have := Nat.log2_self_le h0.ne'
  rw [show m.log2 = 52 by omega] at this
  omega

/-- The model's `unpack` undoes its `pack` on binary64-representable floats. -/
theorem unpack_pack (u : UnpackedFloat) (hu : u.Binary64) :
    UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 u) = u := by
  cases u with
  | notANumber =>
    unfold UnpackedFloat.pack UnpackedFloat.packedNaN UnpackedFloat.unpack
    simp +decide only [↓reduceIte]
  | infinity s =>
    unfold UnpackedFloat.pack UnpackedFloat.packedInfinity UnpackedFloat.unpack
    simp +decide only [UnpackedFloat.unpackMantissa_packComponents,
      UnpackedFloat.unpackExponent_packComponents, unpackSign_packComponents,
      Sign.ofBitVec_toBitVec, ↓reduceIte]
  | zero s =>
    unfold UnpackedFloat.pack UnpackedFloat.packedZero UnpackedFloat.unpack
    simp +decide only [UnpackedFloat.unpackMantissa_packComponents,
      UnpackedFloat.unpackExponent_packComponents, unpackSign_packComponents,
      Sign.ofBitVec_toBitVec, ↓reduceIte, ↓reduceDIte]
  | finite s m e hm =>
    simp only [UnpackedFloat.Binary64] at hu
    unfold UnpackedFloat.pack
    simp only
    rcases hu with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · -- normal
      have hlog := log2_eq_52 h1 h2
      have hbias : (e + (Format.binary64.exponentBias : ℤ)
          + (Format.binary64.mantissaBitsWithoutImplicit : ℤ)).toNat = (e + 1075).toNat := by
        show (e + ((2 ^ (11 - 1) - 1 : ℕ) : ℤ) + ((52 : ℕ) : ℤ)).toNat = _
        norm_num
        rw [show e + 1023 + 52 = e + 1075 by ring]
      have hb : ((e + 1075).toNat : ℤ) = e + 1075 := Int.toNat_of_nonneg (by omega)
      have hblt : (e + 1075).toNat < 2047 := by omega
      have hbpos : 0 < (e + 1075).toNat := by omega
      rw [hbias, ite_eq_right (by show ¬ 2 ^ 11 ≤ _; omega), ite_eq_left (by rw [hlog]; rfl)]
      unfold UnpackedFloat.unpack
      simp only [UnpackedFloat.unpackMantissa_packComponents,
        UnpackedFloat.unpackExponent_packComponents, unpackSign_packComponents,
        Sign.ofBitVec_toBitVec]
      have hne1 : BitVec.ofNat Format.binary64.exponentBits (e + 1075).toNat ≠ -1#_ := by
        rw [Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.neg_one_eq_allOnes,
          BitVec.toNat_allOnes]
        show ¬ (e + 1075).toNat % 2 ^ 11 = 2 ^ 11 - 1
        omega
      have hne0 : BitVec.ofNat Format.binary64.exponentBits (e + 1075).toNat ≠ 0#_ := by
        rw [Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_zero]
        show ¬ (e + 1075).toNat % 2 ^ 11 = 0
        omega
      rw [ite_eq_right hne1, ite_eq_right hne0]
      have hmant :
          (1#1 ++ BitVec.ofNat Format.binary64.mantissaBitsWithoutImplicit m).toNat = m := by
        rw [BitVec.toNat_append, BitVec.toNat_ofNat]
        show 1 <<< 52 ||| m % 2 ^ 52 = m
        have h := Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt m (by norm_num : 0 < 2 ^ 52)) 1
        rw [mul_one] at h
        rw [Nat.shiftLeft_eq, one_mul, ← h]
        omega
      have hexp : ((BitVec.ofNat Format.binary64.exponentBits (e + 1075).toNat).toNat : ℤ)
          - ((Format.binary64.exponentBias : ℤ) + (Format.binary64.mantissaBitsWithoutImplicit : ℤ))
          = e := by
        rw [BitVec.toNat_ofNat]
        show (((e + 1075).toNat % 2 ^ 11 : ℕ) : ℤ)
          - (((2 ^ (11 - 1) - 1 : ℕ) : ℤ) + ((52 : ℕ) : ℤ)) = e
        rw [Nat.mod_eq_of_lt (by omega)]
        norm_num
        omega
      simp only [hmant, hexp]
    · -- subnormal
      subst h2
      have hbias : ((-1074 : ℤ) + (Format.binary64.exponentBias : ℤ) +
          (Format.binary64.mantissaBitsWithoutImplicit : ℤ)).toNat = 1 := by
        show ((-1074 : ℤ) + ((2 ^ (11 - 1) - 1 : ℕ) : ℤ) + ((52 : ℕ) : ℤ)).toNat = 1
        norm_num
      rw [hbias, ite_eq_right (by show ¬ 2 ^ 11 ≤ 1 + 1; omega),
        ite_eq_right (by show ¬ (m.log2 + 1 = 53); exact log2_lt_52 hm h1)]
      unfold UnpackedFloat.unpack
      have hne0 : BitVec.ofNat 52 m ≠ 0#52 := by
        rw [Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt h1]
        omega
      have hmant : (BitVec.ofNat 52 m).toNat = m := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h1
      have hexp : (((0#11 : BitVec 11).toNat : ℤ) -
          ((Format.binary64.exponentBias : ℤ) + ((52 : ℕ) : ℤ))) + 1 = -1074 := by decide
      simp +decide only [UnpackedFloat.unpackMantissa_packComponents,
        UnpackedFloat.unpackExponent_packComponents, unpackSign_packComponents,
        Sign.ofBitVec_toBitVec, hne0, hmant, hexp, ↓reduceIte, ↓reduceDIte]

/-- The same at the level of `Float.Model`. -/
theorem model_unpack_pack (u : UnpackedFloat) (hu : u.Binary64) :
    (Float.Model.pack u).unpack = u := by
  show UnpackedFloat.unpack Format.binary64
    (UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 u)).toBitVec = u
  rw [UInt64.toBitVec_ofBitVec]
  exact unpack_pack u hu

/-! ### Rounded integers -/

theorem toInt_round_nonneg (mode : RoundingMode) (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ toInt (round intSet mode y) := by
  rcases AzRat.toInt_round_intSet_eq_floor_or_ceil mode y with h | h <;> rw [h]
  · exact Int.floor_nonneg.mpr hy
  · exact Int.ceil_nonneg hy

theorem toInt_round_nonpos (mode : RoundingMode) (y : ℝ) (hy : y ≤ 0) :
    toInt (round intSet mode y) ≤ 0 := by
  rcases AzRat.toInt_round_intSet_eq_floor_or_ceil mode y with h | h <;> rw [h]
  · exact Int.floor_nonpos hy
  · exact Int.ceil_nonpos.mpr hy

theorem abs_toInt_round_le (mode : RoundingMode) (y : ℝ) (B : ℤ) (hB : |y| ≤ B) :
    |toInt (round intSet mode y)| ≤ B := by
  obtain ⟨h1, h2⟩ := abs_le.mp hB
  rcases AzRat.toInt_round_intSet_eq_floor_or_ceil mode y with h | h <;> rw [h, abs_le]
  · exact ⟨Int.le_floor.mpr (by exact_mod_cast h1), Int.floor_le_iff.mpr (by linarith)⟩
  · exact ⟨Int.le_ceil_iff.mpr (by rw [Int.cast_neg]; linarith), Int.ceil_le.mpr h2⟩

theorem toInt_round_intCast (mode : RoundingMode) (z : ℤ) :
    toInt (round intSet mode (z : ℝ)) = z := by
  rcases AzRat.toInt_round_intSet_eq_floor_or_ceil mode (z : ℝ) with h | h <;> rw [h] <;> simp

/-! ### `finishUnpacked` -/

theorem AzInt.toInt_max (a b : AzInt) : (max a b).toInt = max a.toInt b.toInt := by
  show (if a ≤ b then b else a).toInt = _
  split_ifs with h
  · rw [max_eq_right ((AzInt.le_iff_toInt_le a b).mp h)]
  · rw [max_eq_left (le_of_not_ge (fun h' => h ((AzInt.le_iff_toInt_le a b).mpr h')))]

theorem AzInt.lt_iff_toInt_lt (a b : AzInt) : a < b ↔ a.toInt < b.toInt := by
  show AzInt.compare a b = .lt ↔ _
  rw [AzInt.compare_eq_compare_toInt, compare_lt_iff_lt]

theorem signOfBool_eq_positive (s : Bool) : (signOfBool s = .positive) ↔ s = true := by
  cases s <;> simp [signOfBool]

theorem size_eq_54_iff (n : AzNat) (hn : n.toNat ≤ 2 ^ 53) : n.size = 54 ↔ n.toNat = 2 ^ 53 := by
  rw [← AzNat.size_toNat]
  constructor
  · intro h
    have := Nat.lt_size.mp (show 53 < n.toNat.size by omega)
    omega
  · intro h
    rw [h, Nat.size_pow]

/-- Every result of `finishUnpacked` is representable, given `|r| ≤ 2^53`, `−1074 ≤ t`, and
`t = −1074` whenever `|r| < 2^52`. -/
theorem finishUnpacked_binary64 (s : Bool) (r t : AzInt) (mode : RoundingMode)
    (hr : r.abs.toNat ≤ 2 ^ 53) (ht : -1074 ≤ t.toInt)
    (hlow : r.abs.toNat < 2 ^ 52 → t.toInt = -1074) :
    (finishUnpacked s r t mode).Binary64 := by
  unfold finishUnpacked
  simp only []
  by_cases h0 : r.abs = 0
  · rw [ite_eq_left h0]; trivial
  · rw [ite_eq_right h0]
    have hpos : 0 < r.abs.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero h0)
    have hmax : (maxFinite64 (signOfBool s)).Binary64 := by
      unfold maxFinite64; show (_ ∨ _); left; norm_num
    have h1 : (1 : AzInt).toInt = 1 := rfl
    by_cases hc : r.abs.size = 54
    · have h53 : r.abs.toNat = 2 ^ 53 := (size_eq_54_iff r.abs hr).mp hc
      rw [ite_eq_left hc, ite_eq_left hc]
      by_cases hov : azIntOfInt 971 < t + 1
      · rw [ite_eq_left hov]; split_ifs <;> first | exact hmax | trivial
      · rw [ite_eq_right hov]
        rw [AzInt.lt_iff_toInt_lt, toInt_azIntOfInt, AzInt.toInt_add, h1] at hov
        have hM : smallToNat (r.abs.shiftRight 1) = 2 ^ 52 := by
          rw [smallToNat_eq _ (by rw [AzNat.toNat_shiftRight, h53]; norm_num),
            AzNat.toNat_shiftRight, h53]
          norm_num
        rw [dite_eq_left (by rw [hM]; norm_num)]
        show (_ ∨ _)
        rw [hM, AzInt.toInt_add, h1]
        left
        refine ⟨le_rfl, by norm_num, by omega, by omega⟩
    · have hne : r.abs.toNat ≠ 2 ^ 53 := fun h => hc ((size_eq_54_iff r.abs hr).mpr h)
      rw [ite_eq_right hc, ite_eq_right hc]
      by_cases hov : azIntOfInt 971 < t
      · rw [ite_eq_left hov]; split_ifs <;> first | exact hmax | trivial
      · rw [ite_eq_right hov]
        rw [AzInt.lt_iff_toInt_lt, toInt_azIntOfInt] at hov
        have hM : smallToNat r.abs = r.abs.toNat := smallToNat_eq _ (by omega)
        rw [dite_eq_left (by rw [hM]; exact hpos)]
        show (_ ∨ _)
        rw [hM]
        rcases Nat.lt_or_ge r.abs.toNat (2 ^ 52) with hlt | hge
        · right; exact ⟨hlt, hlow hlt⟩
        · left; exact ⟨hge, by omega, ht, by omega⟩

/-- The value of `finishUnpacked` when it does not overflow (`t ≤ 971`, or `t ≤ 970` with a
carry) and `r` has the sign `s`. -/
theorem toVal_finishUnpacked (s : Bool) (r t : AzInt) (mode : RoundingMode)
    (hr : r.abs.toNat ≤ 2 ^ 53) (hsign : r.toInt ≠ 0 → (0 < r.toInt ↔ s = true))
    (hno : t.toInt + (if r.abs.toNat = 2 ^ 53 then 1 else 0) ≤ 971) :
    (finishUnpacked s r t mode).toVal
      = some (((r.toInt : ℝ) * (2 : ℝ) ^ t.toInt : ℝ) : EReal) := by
  unfold finishUnpacked
  simp only []
  have habs : (r.abs.toNat : ℤ) = |r.toInt| := AzInt.abs_toNat_eq r
  have h1 : (1 : AzInt).toInt = 1 := rfl
  by_cases h0 : r.abs = 0
  · rw [ite_eq_left h0]
    have hr0 : r.toInt = 0 := by
      have := congrArg AzNat.toNat h0
      rw [AzNat.toNat_zero] at this
      rw [this] at habs
      exact abs_eq_zero.mp (by exact_mod_cast habs.symm)
    simp [UnpackedFloat.toVal, hr0]
  · rw [ite_eq_right h0]
    have hpos : 0 < r.abs.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero h0)
    have hr0 : r.toInt ≠ 0 := by
      intro h
      rw [h, abs_zero] at habs
      exact (toNat_ne_zero_of_ne_zero h0) (by exact_mod_cast habs)
    have hsgn := hsign hr0
    have habsR : (r.abs.toNat : ℝ) = |(r.toInt : ℝ)| := by
      rw [← Int.cast_abs, ← habs, Int.cast_natCast]
    have hsgn' : (if signOfBool s = Sign.positive then (1 : ℝ) else -1) = if s then 1 else -1 := by
      cases s <;> simp [signOfBool]
    have hsr : (if s then (1 : ℝ) else -1) * (r.abs.toNat : ℝ) = r.toInt := by
      rcases lt_or_gt_of_ne hr0 with hneg | hpos'
      · have hs : ¬ s = true := fun hs => absurd (hsgn.mpr hs) (not_lt.mpr hneg.le)
        rw [ite_eq_right hs, habsR, abs_of_neg (by exact_mod_cast hneg)]; ring
      · rw [ite_eq_left (hsgn.mp hpos'), habsR, abs_of_pos (by exact_mod_cast hpos')]; ring
    by_cases hc : r.abs.size = 54
    · have h53 : r.abs.toNat = 2 ^ 53 := (size_eq_54_iff r.abs hr).mp hc
      rw [ite_eq_left hc, ite_eq_left hc]
      rw [ite_eq_left h53] at hno
      have hnov : ¬ azIntOfInt 971 < t + 1 := by
        rw [AzInt.lt_iff_toInt_lt, toInt_azIntOfInt, AzInt.toInt_add, h1]; omega
      rw [ite_eq_right hnov]
      have hM : smallToNat (r.abs.shiftRight 1) = 2 ^ 52 := by
        rw [smallToNat_eq _ (by rw [AzNat.toNat_shiftRight, h53]; norm_num),
          AzNat.toNat_shiftRight, h53]
        norm_num
      rw [dite_eq_left (by rw [hM]; norm_num)]
      simp only [UnpackedFloat.toVal, Option.some.injEq, EReal.coe_eq_coe_iff]
      rw [hM, hsgn', AzInt.toInt_add, h1, zpow_add_one₀ (two_ne_zero : (2 : ℝ) ≠ 0), ← hsr, h53]
      push_cast
      ring
    · have hne : r.abs.toNat ≠ 2 ^ 53 := fun h => hc ((size_eq_54_iff r.abs hr).mpr h)
      rw [ite_eq_right hc, ite_eq_right hc]
      rw [ite_eq_right hne, add_zero] at hno
      have hnov : ¬ azIntOfInt 971 < t := by
        rw [AzInt.lt_iff_toInt_lt, toInt_azIntOfInt]; omega
      rw [ite_eq_right hnov]
      have hM : smallToNat r.abs = r.abs.toNat := smallToNat_eq _ (by omega)
      rw [dite_eq_left (by rw [hM]; exact hpos)]
      simp only [UnpackedFloat.toVal, Option.some.injEq, EReal.coe_eq_coe_iff]
      rw [hM, hsgn', ← hsr]

/-! ### `toUnpacked` -/

/-- The rounded integer of the shift step: `±n · 2^k` rounded to an integer in `mode`. -/
theorem round_shift_eq (s : Bool) (n : AzNat) (hn : n ≠ 0) (k : AzInt) (mode : RoundingMode) :
    (if k.sign then (AzInt.mkNorm s n).shiftLeft k.abs.toNat
        else (AzInt.shiftRightRound (AzInt.mkNorm s n) mode k.abs.toNat).1).toInt
      = toInt (round intSet mode ((if s then 1 else -1) * (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt)) := by
  have hz : ((AzInt.mkNorm s n).toInt : ℝ) = (if s then 1 else -1) * (n.toNat : ℝ) := by
    rcases Bool.eq_false_or_eq_true s with hs | hs <;>
      simp [hs, AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false n hn]
  have habs : (k.abs.toNat : ℤ) = |k.toInt| := AzInt.abs_toNat_eq k
  by_cases hsg : k.sign = true
  · have hk0 : 0 ≤ k.toInt := (AzInt.sign_eq_true_iff k).mp hsg
    rw [ite_eq_left hsg, AzInt.toInt_shiftLeft]
    have hk : ((k.abs.toNat : ℕ) : ℤ) = k.toInt := by rw [habs, abs_of_nonneg hk0]
    have : (if s then 1 else -1) * (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt
        = (((AzInt.mkNorm s n).toInt * 2 ^ k.abs.toNat : ℤ) : ℝ) := by
      push_cast
      rw [hz, ← zpow_natCast, hk]
    rw [this, toInt_round_intCast]
  · have hk0 : k.toInt < 0 := by
      have := (AzInt.sign_eq_true_iff k).not.mp hsg; push Not at this; exact this
    rw [ite_eq_right hsg]
    have h := AzInt.toInt_shiftRightRound (AzInt.mkNorm s n) mode k.abs.toNat
    have hk : ((k.abs.toNat : ℕ) : ℤ) = -k.toInt := by rw [habs, abs_of_neg hk0]
    have heq : ((AzInt.mkNorm s n).toInt : ℝ) / (2 : ℝ) ^ k.abs.toNat
        = (if s then 1 else -1) * (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt := by
      rw [hz, ← zpow_natCast, hk, zpow_neg, div_eq_mul_inv, inv_inv]
    rw [heq] at h
    exact (toInt_eq_of_val h).symm

/-- The finite case of `toUnpacked`, packaged: the result is `finishUnpacked` of an integer `r`
that rounds `x / 2^t`, where `t = max (e − 53) (−1074)` and `r` has the sign of `x`. -/
theorem toUnpacked_finite (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat} (hv : FiniteValid p m)
    (mode : RoundingMode) :
    ∃ r t : AzInt, toUnpacked (finite s e p m hv) mode = finishUnpacked s r t mode ∧
      t.toInt = max (e.toInt - 53) (-1074) ∧
      r.toInt = toInt (round intSet mode (finiteVal s e m / (2 : ℝ) ^ t.toInt)) ∧
      (r.toInt ≠ 0 → (0 < r.toInt ↔ s = true)) := by
  unfold toUnpacked
  simp only []
  set n := coreSignificand p m with hn
  have hn0 : n ≠ 0 := coreSignificand_ne_zero hv
  have hs : n.size = p := size_coreSignificand hv
  clear_value n
  set t : AzInt := max (e - (AzNat.ofNat 53).toAzInt) (azIntOfInt (-1074)) with ht_def
  have htI : t.toInt = max (e.toInt - 53) (-1074) := by
    rw [ht_def, AzInt.toInt_max, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat,
      toInt_azIntOfInt]
    push_cast
    rfl
  clear_value t
  set k : AzInt := e - (AzNat.ofNat p).toAzInt - t with hk_def
  have hkI : k.toInt = e.toInt - p - t.toInt := by
    rw [hk_def, AzInt.toInt_sub, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
  clear_value k
  refine ⟨_, t, rfl, htI, ?_, ?_⟩
  · rw [round_shift_eq s n hn0 k mode, finiteVal_eq_core s e hv, ← hn, finiteVal_sign,
      finiteVal_true_eq, hs, hkI]
    have key : (if s then (1 : ℝ) else -1) * (n.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - p - t.toInt)
        = (if s then 1 else -1) * ((n.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - p)) / 2 ^ t.toInt := by
      rw [zpow_sub₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; ring
    rw [key]
  · intro hr0
    rw [round_shift_eq s n hn0 k mode] at hr0 ⊢
    have hNpos : (0 : ℝ) < (n.toNat : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn0)
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k.toInt := zpow_pos (by norm_num) _
    cases s with
    | true =>
      simp only [↓reduceIte, one_mul, iff_true] at hr0 ⊢
      have := toInt_round_nonneg mode _ (mul_pos hNpos h2k).le
      omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul, iff_false, not_lt] at hr0 ⊢
      exact toInt_round_nonpos mode _ (by nlinarith)

/-- Every result of `toUnpacked` is representable in binary64. -/
theorem toUnpacked_binary64 (x : AzFloat) (mode : RoundingMode) :
    (toUnpacked x mode).Binary64 := by
  cases x with
  | nan => trivial
  | infinity s => trivial
  | zero => trivial
  | finite s e p m hv =>
    obtain ⟨r, t, hx, htI, hr, -⟩ := toUnpacked_finite s e hv mode
    rw [hx]
    have hv0 : finiteVal s e m ≠ 0 := by
      rw [finiteVal_eq_core s e hv]
      exact finiteVal_ne_zero' s e _ (coreSignificand_ne_zero hv)
    obtain ⟨hvlo, hvhi⟩ := abs_finiteVal_bounds s e hv
    have habs : (r.abs.toNat : ℤ) = |r.toInt| := AzInt.abs_toNat_eq r
    have h2t : (0 : ℝ) < (2 : ℝ) ^ t.toInt := zpow_pos (by norm_num) _
    rcases le_or_gt (-1021 : ℤ) e.toInt with hlo | hhi
    · -- normal range: `|x / 2^t| ∈ [2^52, 2^53)`
      have ht : t.toInt = e.toInt - 53 := by rw [htI]; exact max_eq_left (by omega)
      have hscale : precScale 2 53 (finiteVal s e m) = (2 : ℝ) ^ t.toInt := by
        rw [precScale_finiteVal s e hv 53, ht]; rfl
      obtain ⟨hlo', hhi'⟩ := abs_div_precScale_bounds (b := 2) (p := 53) (finiteVal s e m) hv0
      rw [hscale] at hlo' hhi'
      obtain ⟨hb1, hb2⟩ := abs_toInt_round_bounds 53 (by norm_num) mode _ (by simpa using hlo')
        (by simpa using hhi')
      rw [← hr] at hb1 hb2
      apply finishUnpacked_binary64 s r t mode
      · have : (r.abs.toNat : ℤ) ≤ ((2 ^ 53 : ℕ) : ℤ) := by rw [habs]; exact hb2
        exact_mod_cast this
      · omega
      · intro hlt
        exfalso
        have : ((2 ^ (53 - 1) : ℕ) : ℤ) ≤ (r.abs.toNat : ℤ) := by rw [habs]; exact hb1
        have : (2 ^ 52 : ℕ) ≤ r.abs.toNat := by exact_mod_cast this
        omega
    · -- subnormal range: `|x / 2^t| < 2^52`
      have ht : t.toInt = -1074 := by rw [htI]; exact max_eq_right (by omega)
      have hsmall : |finiteVal s e m / (2 : ℝ) ^ t.toInt| ≤ ((2 ^ 52 : ℤ) : ℝ) := by
        rw [show ((2 ^ 52 : ℤ) : ℝ) = (2 : ℝ) ^ (52 : ℤ) by norm_num]
        apply le_of_lt
        rw [abs_div, abs_of_pos h2t, div_lt_iff₀ h2t, ht]
        calc |finiteVal s e m| < (2 : ℝ) ^ e.toInt := hvhi
          _ ≤ (2 : ℝ) ^ (-1022 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = (2 : ℝ) ^ (52 : ℤ) * (2 : ℝ) ^ (-1074 : ℤ) := by
            rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; norm_num
      have hb := abs_toInt_round_le mode _ _ hsmall
      rw [← hr] at hb
      have hr52 : r.abs.toNat ≤ 2 ^ 52 := by
        have : (r.abs.toNat : ℤ) ≤ 2 ^ 52 := by rw [habs]; exact hb
        exact_mod_cast this
      exact finishUnpacked_binary64 s r t mode (by omega) (by omega) (fun _ => ht)

/-- In the normal range of binary64, `toUnpacked` is the rounding of `x` to 53 bits. -/
theorem toVal_toUnpacked_normal (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat}
    (hv : FiniteValid p m) (hlo : -1021 ≤ e.toInt) (hhi : e.toInt ≤ 1023) (mode : RoundingMode) :
    (toUnpacked (finite s e p m hv) mode).toVal
      = some (round (precisionSet 2 53) mode (finiteVal s e m)).val := by
  obtain ⟨r, t, hx, htI, hr, hsign⟩ := toUnpacked_finite s e hv mode
  rw [hx]
  have hv0 : finiteVal s e m ≠ 0 := by
    rw [finiteVal_eq_core s e hv]
    exact finiteVal_ne_zero' s e _ (coreSignificand_ne_zero hv)
  have habs : (r.abs.toNat : ℤ) = |r.toInt| := AzInt.abs_toNat_eq r
  have ht : t.toInt = e.toInt - 53 := by rw [htI]; exact max_eq_left (by omega)
  have hscale : precScale 2 53 (finiteVal s e m) = (2 : ℝ) ^ t.toInt := by
    rw [precScale_finiteVal s e hv 53, ht]; rfl
  obtain ⟨hlo', hhi'⟩ := abs_div_precScale_bounds (b := 2) (p := 53) (finiteVal s e m) hv0
  rw [hscale] at hlo' hhi'
  obtain ⟨hb1, hb2⟩ := abs_toInt_round_bounds 53 (by norm_num) mode _ (by simpa using hlo')
    (by simpa using hhi')
  rw [← hr] at hb1 hb2
  have hr53 : r.abs.toNat ≤ 2 ^ 53 := by
    have : (r.abs.toNat : ℤ) ≤ ((2 ^ 53 : ℕ) : ℤ) := by rw [habs]; exact hb2
    exact_mod_cast this
  rw [toVal_finishUnpacked s r t mode hr53 hsign (by rw [ht]; split_ifs <;> omega),
    val_round_precisionSet mode _ hv0, hscale, ← hr]

/-- Below the normal range, `toUnpacked` is the rounding of `x` to a multiple of `2^-1074`. -/
theorem toVal_toUnpacked_subnormal (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat}
    (hv : FiniteValid p m) (hhi : e.toInt ≤ -1022) (mode : RoundingMode) :
    (toUnpacked (finite s e p m hv) mode).toVal
      = some ((((toInt (round intSet mode (finiteVal s e m * (2 : ℝ) ^ (1074 : ℤ))) : ℝ)
          * (2 : ℝ) ^ (-1074 : ℤ) : ℝ)) : EReal) := by
  obtain ⟨r, t, hx, htI, hr, hsign⟩ := toUnpacked_finite s e hv mode
  rw [hx]
  obtain ⟨-, hvhi⟩ := abs_finiteVal_bounds s e hv
  have habs : (r.abs.toNat : ℤ) = |r.toInt| := AzInt.abs_toNat_eq r
  have ht : t.toInt = -1074 := by rw [htI]; exact max_eq_right (by omega)
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t.toInt := zpow_pos (by norm_num) _
  have hsmall : |finiteVal s e m / (2 : ℝ) ^ t.toInt| ≤ ((2 ^ 52 : ℤ) : ℝ) := by
    rw [show ((2 ^ 52 : ℤ) : ℝ) = (2 : ℝ) ^ (52 : ℤ) by norm_num]
    apply le_of_lt
    rw [abs_div, abs_of_pos h2t, div_lt_iff₀ h2t, ht]
    calc |finiteVal s e m| < (2 : ℝ) ^ e.toInt := hvhi
      _ ≤ (2 : ℝ) ^ (-1022 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = (2 : ℝ) ^ (52 : ℤ) * (2 : ℝ) ^ (-1074 : ℤ) := by
        rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; norm_num
  have hb := abs_toInt_round_le mode _ _ hsmall
  rw [← hr] at hb
  have hr52 : r.abs.toNat ≤ 2 ^ 52 := by
    have : (r.abs.toNat : ℤ) ≤ 2 ^ 52 := by rw [habs]; exact hb
    exact_mod_cast this
  have hdiv : finiteVal s e m / (2 : ℝ) ^ t.toInt = finiteVal s e m * (2 : ℝ) ^ (1074 : ℤ) := by
    rw [ht, div_eq_mul_inv, ← zpow_neg]; norm_num
  rw [toVal_finishUnpacked s r t mode (by omega) hsign (by rw [ht]; split_ifs <;> omega), hr, hdiv,
    ht]

/-! ### Through `Float` -/

/-- Converting to a `Float` and back is `ofUnpacked ∘ toUnpacked`: the model's `pack` and
`unpack` are inverse on every result of `toUnpacked`. -/
theorem ofFloat64_toFloat64 (x : AzFloat) (mode : RoundingMode) :
    ofFloat64 (toFloat64 x mode) = ofUnpacked (toUnpacked x mode) := by
  unfold ofFloat64 toFloat64
  rw [show (Float.ofModel (Float.Model.pack (toUnpacked x mode))).toModel
    = Float.Model.pack (toUnpacked x mode) from rfl,
    model_unpack_pack _ (toUnpacked_binary64 x mode)]

/-- The headline: in the normal range of binary64, converting a float to a `Float` in `mode` and
reading it back exactly gives the rounding of its value to 53 bits in `mode`. -/
theorem toVal_ofFloat64_toFloat64_normal (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat}
    (hv : FiniteValid p m) (hlo : -1021 ≤ e.toInt) (hhi : e.toInt ≤ 1023) (mode : RoundingMode) :
    toVal (ofFloat64 (toFloat64 (finite s e p m hv) mode))
      = some (round (precisionSet 2 53) mode (finiteVal s e m)).val := by
  rw [ofFloat64_toFloat64, toVal_ofUnpacked, toVal_toUnpacked_normal s e hv hlo hhi mode]

/-- Below the normal range, the same gives the rounding to a multiple of `2^-1074`. -/
theorem toVal_ofFloat64_toFloat64_subnormal (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat}
    (hv : FiniteValid p m) (hhi : e.toInt ≤ -1022) (mode : RoundingMode) :
    toVal (ofFloat64 (toFloat64 (finite s e p m hv) mode))
      = some ((((toInt (round intSet mode (finiteVal s e m * (2 : ℝ) ^ (1074 : ℤ))) : ℝ)
          * (2 : ℝ) ^ (-1074 : ℤ) : ℝ)) : EReal) := by
  rw [ofFloat64_toFloat64, toVal_ofUnpacked, toVal_toUnpacked_subnormal s e hv hhi mode]

end Azurite.AzFloat

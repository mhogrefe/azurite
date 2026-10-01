/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.SchonhageStrassen
import Azurite.AzFermat.Equiv.FFT
import Azurite.AzNat.Equiv.Mul.ToomEval
import Azurite.AzNat.Equiv.Mul.ToomUnbalanced
import Azurite.AzNat.Equiv.Pow2

/-!
# Correctness of `fftMulModWith` (MCA Theorem 2.3)

`fftMulModWith_toNat`: for `A, B < 2^n` (`n = 64 w · 2^(k+1)`), `fftMulModWith k w N _ _ A B`
is `A · B mod (2^n + 1)`.  The proof follows the stages of the implementation:

* `toNat_eq_sum_blocks`: `A = ∑_j a_j 2^{jM}` with `a_j` the limb-block digits (the Toom
  framework's `sliceVal_eq_polyEval_blocks`);
* `toZModFun_ssWeighted`: the weighted array is `extendZero (weight θ a)` over `ZMod (2^N+1)`;
* `toZMod_backwardFFT_ssProducts`: after the two forward transforms, the pointwise products and
  the backward transform, entry `j` is `K θ^j c_j` (`BZ.backwardFFT_forwardFFT_weight_mul`);
* `toInt_ssCoefficients_getElem`: dividing by `K θ^j` (a unit) and recovering from the window
  (`BZ.negacyclicConv_bounds`, `BZ.int_recover_of_mem_window`) gives the integer `c_j`;
* `ssSweep_spec` and `toZMod_ssAssemble`: the digit sweeps and their combination in
  `AzFermat n` give `∑_j c_j 2^{jM}` modulo `2^n + 1`;
* finally `BZ.sum_weight_mul_sum_weight` at `θ = 2^M` in `ZMod (2^n + 1)` identifies
  `∑_j c_j 2^{jM}` with `A · B` modulo `2^n + 1`.
-/

namespace Azurite.AzNat

open AzFermat BZ Finset

/-! ### Sums, digits and the assembled value -/

theorem polyEvalInt_range_map (c : Int) (g : Nat → Int) : ∀ K : Nat,
    polyEvalInt c ((List.range K).map g) = ∑ j ∈ range K, g j * c ^ j
  | 0 => by simp [polyEvalInt]
  | K + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyEvalInt_cons,
      polyEvalInt_range_map c (g ∘ Nat.succ) K, Finset.sum_range_succ', Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Function.comp, pow_succ, mul_assoc]
    · rw [pow_zero, mul_one]

theorem polyEvalNat_ofFn (c : Nat) : ∀ {K : Nat} (g : Fin K → Nat),
    polyEvalNat c (List.ofFn g) = ∑ j : Fin K, g j * c ^ j.val
  | 0, g => by simp [polyEvalNat]
  | K + 1, g => by
    rw [List.ofFn_succ, polyEvalNat_cons, polyEvalNat_ofFn c (fun i => g i.succ),
      Fin.sum_univ_succ, Finset.sum_mul, add_comm]
    congr 1
    · rw [Fin.val_zero, pow_zero, mul_one]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ, mul_assoc]

/-- The value of a signed coefficient. -/
def SSCoeff.toInt (c : SSCoeff) : Int := if c.neg then -(c.mag.toNat : Int) else c.mag.toNat

/-- **The digit sweep**: on input coefficients `cs`, an incoming carry and an accumulator of
`acc.size` limbs, `ssSweep` appends `w · |cs|` limbs and returns the carry out, with
`low + carry_out · 2^{64 (acc.size + w |cs|)} = acc + 2^{64 acc.size} (carry_in + ∑_j cs_j 2^{64 w j})`. -/
theorem ssSweep_spec (w : Nat) : ∀ (cs : List AzNat) (carry : AzNat) (acc : Array UInt64),
    (ssSweep w cs carry acc).1.size = acc.size + w * cs.length ∧
    toNatLimbsList (ssSweep w cs carry acc).1.toList
        + (ssSweep w cs carry acc).2.toNat * 2 ^ (64 * (acc.size + w * cs.length))
      = toNatLimbsList acc.toList
        + 2 ^ (64 * acc.size) * (carry.toNat + polyEvalNat (2 ^ (64 * w)) (cs.map AzNat.toNat))
  | [], carry, acc => by
    simp [ssSweep, polyEvalNat, Nat.mul_comm]
  | c :: cs, carry, acc => by
    have ih := ssSweep_spec w cs ((c + carry) >>> (64 * w))
      (acc ++ truncatePad ((c + carry).modPow2 (64 * w)).limbs w)
    simp only [ssSweep]
    have hdig : toNatLimbsList ((c + carry).modPow2 (64 * w)).limbs.toList < 2 ^ (64 * w) := by
      change AzNat.toNat _ < _
      rw [AzNat.toNat_modPow2]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    refine ⟨?_, ?_⟩
    · rw [ih.1, Array.size_append, truncatePad_size, List.length_cons]
      ring
    · have hl : acc.toList.length = acc.size := Array.length_toList
      rw [Array.size_append, truncatePad_size, Array.toList_append, toNatLimbsList_append, hl,
        truncatePad_toNat _ _ hdig] at ih
      rw [show 64 * (acc.size + w * (c :: cs).length) = 64 * (acc.size + w + w * cs.length) by
          rw [List.length_cons]; ring, ih.2, List.map_cons, polyEvalNat_cons]
      change AzNat.toNat ((c + carry).modPow2 (64 * w)) * 2 ^ (64 * acc.size) + toNatLimbsList acc.toList
          + 2 ^ (64 * (acc.size + w)) * (((c + carry) >>> (64 * w)).toNat
            + polyEvalNat (2 ^ (64 * w)) (cs.map AzNat.toNat)) = _
      rw [AzNat.toNat_modPow2, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow, AzNat.toNat_add]
      have hdiv := Nat.div_add_mod (c.toNat + carry.toNat) (2 ^ (64 * w))
      rw [show 64 * (acc.size + w) = 64 * acc.size + 64 * w by ring, pow_add]
      generalize (c.toNat + carry.toNat) / 2 ^ (64 * w) = q at hdiv ⊢
      generalize (c.toNat + carry.toNat) % 2 ^ (64 * w) = r at hdiv ⊢
      generalize (2 : ℕ) ^ (64 * w) = B at hdiv ⊢
      generalize (2 : ℕ) ^ (64 * acc.size) = A
      generalize polyEvalNat B (cs.map AzNat.toNat) = P
      have key : A * (carry.toNat + (P * B + c.toNat)) = A * (B * q + r + P * B) := by
        rw [hdiv]; ring
      rw [key]
      ring

/-- **The assembled value**: `∑_j c_j (2^{64 w})^j` modulo `2^n + 1`, `n = 64 w · 2^(k+1)`. -/
theorem toZMod_ssAssemble (k w : Nat) (hw0 : 0 < w) (f : Fin (2 ^ (k + 1)) → SSCoeff) :
    toZMod (ssAssemble k w hw0 (Array.ofFn f))
      = ∑ j : Fin (2 ^ (k + 1)), ((f j).toInt : ZMod (2 ^ (64 * w * 2 ^ (k + 1)) + 1))
          * ((2 : ZMod (2 ^ (64 * w * 2 ^ (k + 1)) + 1)) ^ (64 * w)) ^ j.val := by
  have : NeZero (64 * w * 2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩
  set n := 64 * w * 2 ^ (k + 1) with hn
  unfold ssAssemble
  dsimp only
  rw [Array.toList_ofFn, List.map_ofFn, List.map_ofFn]
  set pos := ssSweep w (List.ofFn ((fun c : SSCoeff => if c.neg then 0 else c.mag) ∘ f)) 0 #[]
    with hpos
  set neg := ssSweep w (List.ofFn ((fun c : SSCoeff => if c.neg then c.mag else 0) ∘ f)) 0 #[]
    with hneg
  have hP := (ssSweep_spec w (List.ofFn ((fun c : SSCoeff => if c.neg then 0 else c.mag) ∘ f)) 0 #[]).2
  have hQ := (ssSweep_spec w (List.ofFn ((fun c : SSCoeff => if c.neg then c.mag else 0) ∘ f)) 0 #[]).2
  rw [← hpos] at hP
  rw [← hneg] at hQ
  simp only [Array.size_empty, List.length_ofFn, Nat.zero_add, Nat.mul_zero, pow_zero, one_mul,
    AzNat.toNat_zero] at hP hQ
  rw [show 64 * (w * 2 ^ (k + 1)) = n by rw [hn]; ring] at hP hQ
  rw [List.map_ofFn, polyEvalNat_ofFn] at hP hQ
  have hPz := congrArg (fun m : ℕ => (m : ZMod (2 ^ n + 1))) hP
  have hQz := congrArg (fun m : ℕ => (m : ZMod (2 ^ n + 1))) hQ
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum,
    two_pow_eq_neg_one] at hPz hQz
  have htoNat : ∀ c : SSCoeff, ((c.toInt : Int) : ZMod (2 ^ n + 1))
      = ((if c.neg then 0 else c.mag).toNat : ZMod (2 ^ n + 1))
        - ((if c.neg then c.mag else 0).toNat : ZMod (2 ^ n + 1)) := by
    intro c
    unfold SSCoeff.toInt
    split_ifs <;> simp
  rw [toZMod_sub', toZMod_add', toZMod_add', toZMod_ofAzNat, toZMod_ofAzNat, toZMod_ofAzNat,
    toZMod_ofAzNat, toNat_ofLimbs, toNat_ofLimbs]
  simp only [Function.comp_apply] at hPz hQz
  simp only [htoNat, sub_mul, Finset.sum_sub_distrib]
  linear_combination hPz - hQz

/-- `A < 2^{64 w K}` has at most `w K` limbs. -/
theorem limbs_size_le_of_toNat_lt (A : AzNat) (L : Nat) (hA : A.toNat < 2 ^ (64 * L)) :
    A.limbs.size ≤ L := by
  rcases Nat.eq_zero_or_pos A.limbs.size with h0 | hpos
  · omega
  · have h := toNat_pos_of_size_pos A hpos
    have : 64 * (A.limbs.size - 1) < 64 * L :=
      (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h hA)
    omega

/-- **Digit decomposition**: `A = ∑_{j<K} a_j (2^{64 w})^j` with `a_j` the `j`-th block of `w`
limbs, for `A < 2^{64 w K}`. -/
theorem toNat_eq_sum_blocks (A : AzNat) (w K : Nat) (hA : A.toNat < 2 ^ (64 * w * K)) :
    (A.toNat : Int)
      = ∑ j : Fin K, ((block A.limbs 0 A.limbs.size w j.val).toNat : Int) * (2 ^ (64 * w)) ^ j.val := by
  have hsz : A.limbs.size ≤ K * w := by
    have := limbs_size_le_of_toNat_lt A (w * K) (by rwa [← Nat.mul_assoc])
    rwa [Nat.mul_comm] at this
  have h1 : A.toNat = sliceVal A.limbs 0 A.limbs.size := (sliceVal_self A.limbs _ rfl).symm
  rw [h1, sliceVal_eq_polyEval_blocks A.limbs 0 A.limbs.size w K hsz (by simp), blocks,
    List.map_map, polyEvalInt_range_map, Fin.sum_univ_eq_sum_range
      (fun j => ((block A.limbs 0 A.limbs.size w j).toNat : Int) * (2 ^ (64 * w)) ^ j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Function.comp, Azurite.AzNat.toInt_toAzInt]

/-- The integer negacyclic convolution, cast into a ring. -/
theorem negacyclicConv_intCast {R : Type*} [CommRing R] {K : Nat} [NeZero K] (a b : Fin K → Int)
    (i : Fin K) :
    ((negacyclicConv a b i : Int) : R)
      = negacyclicConv (fun j => (a j : R)) (fun j => (b j : R)) i := by
  unfold negacyclicConv
  push_cast
  rfl

/-! ### The stages of the algorithm over `ZMod (2^N + 1)` -/

variable {N : Nat} [NeZero N]

/-- The digits of `A` as residues, as a `Fin`-vector over `ZMod (2^N + 1)`. -/
def ssDigitsZ (N w : Nat) (K : Nat) (A : AzNat) : Fin K → ZMod (2 ^ N + 1) :=
  fun j => ((block A.limbs 0 A.limbs.size w j.val).toNat : ZMod (2 ^ N + 1))

theorem toZModFun_ssWeighted (k w : Nat) (eθ : Nat) (A : AzNat) :
    toZModFun (ssWeighted k w N eθ A)
      = extendZero (weight ((2 : ZMod (2 ^ N + 1)) ^ eθ) (ssDigitsZ N w (2 ^ (k + 1)) A)) := by
  funext i
  by_cases hi : i < 2 ^ (k + 1)
  · rw [toZModFun_of_lt _ (by rw [ssWeighted_size]; exact hi), extendZero, dite_eq_left hi]
    unfold ssWeighted
    rw [Array.getElem_ofFn, toZMod_mulPow2, ssDigit, toZMod_ofAzNat, weight, ssDigitsZ, ← pow_mul,
      mul_comm]
  · rw [toZModFun_of_le _ (by rw [ssWeighted_size]; omega), extendZero,
      dite_eq_right (Nat.not_lt.mpr (Nat.not_lt.mp hi))]

theorem toZMod_ssProducts_getElem (k : Nat) (eθ : Nat) (mulFn : AzNat → AzNat → AzNat)
    (hmul : ∀ x y : AzNat, (mulFn x y).toNat = x.toNat * y.toNat) (a b : Array (AzFermat N))
    (ha : a.size = 2 ^ (k + 1)) (hb : b.size = 2 ^ (k + 1)) (r : Nat) (hr : r < 2 ^ (k + 1)) :
    toZMod ((ssProducts k N eθ mulFn a b ha hb)[r]'(by rw [ssProducts_size]; exact hr))
      = BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * eθ)) (k + 1) (toZModFun a) r
        * BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * eθ)) (k + 1) (toZModFun b) r := by
  unfold ssProducts
  simp only [Array.getElem_ofFn]
  rw [toZMod_mulWith _ _ _ (hmul _ _), toZMod_forwardFFT _ _ _ _ r hr,
    toZMod_forwardFFT _ _ _ _ r hr]

theorem toZMod_ssSquares_getElem (k : Nat) (eθ : Nat) (sqFn : AzNat → AzNat)
    (hsq : ∀ x : AzNat, (sqFn x).toNat = x.toNat * x.toNat) (a : Array (AzFermat N))
    (ha : a.size = 2 ^ (k + 1)) (r : Nat) (hr : r < 2 ^ (k + 1)) :
    toZMod ((ssSquares k N eθ sqFn a ha)[r]'(by rw [ssSquares_size]; exact hr))
      = BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * eθ)) (k + 1) (toZModFun a) r
        * BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * eθ)) (k + 1) (toZModFun a) r := by
  unfold ssSquares
  simp only [Array.getElem_ofFn]
  rw [toZMod_reduceAny, hsq, Nat.cast_mul, ← toZMod_forwardFFT _ _ _ _ r hr]
  rfl

/-- Entry `j` of the backward transform of any array of pointwise products of the transforms of
the weighted digits is `K θ^j c_j`. -/
theorem toZMod_backwardFFT_of_products (k w : Nat) (eθ : Nat)
    (hθ : ((2 : ZMod (2 ^ N + 1)) ^ eθ) ^ 2 ^ (k + 1) = -1) (A B : AzNat)
    (c : Array (AzFermat N)) (hc : c.size = 2 ^ (k + 1))
    (hcr : ∀ (r : Nat) (hr : r < 2 ^ (k + 1)), toZMod (c[r]'(by rw [hc]; exact hr))
      = BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * eθ)) (k + 1)
          (toZModFun (ssWeighted k w N eθ A)) r
        * BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * eθ)) (k + 1)
          (toZModFun (ssWeighted k w N eθ B)) r)
    (j : Nat) (hj : j < 2 ^ (k + 1)) :
    haveI : NeZero (2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)⟩
    toZMod ((backwardFFT (2 * eθ) (k + 1) c hc)[j]'(by rw [backwardFFT_size]; exact hj))
      = ((2 ^ (k + 1) : ℕ) : ZMod (2 ^ N + 1))
        * (((2 : ZMod (2 ^ N + 1)) ^ eθ) ^ j
          * negacyclicConv (ssDigitsZ N w (2 ^ (k + 1)) A) (ssDigitsZ N w (2 ^ (k + 1)) B) ⟨j, hj⟩) := by
  have : NeZero (2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)⟩
  rw [toZMod_backwardFFT _ _ _ _ j hj]
  have hω : (2 : ZMod (2 ^ N + 1)) ^ (2 * eθ) = ((2 : ZMod (2 ^ N + 1)) ^ eθ) ^ 2 := by
    rw [← pow_mul, mul_comm]
  rw [hω, BZ.backwardFFT_congr (k + 1) _ _
      (fun r => BZ.forwardFFT (((2 : ZMod (2 ^ N + 1)) ^ eθ) ^ 2) (k + 1)
          (extendZero (weight ((2 : ZMod (2 ^ N + 1)) ^ eθ) (ssDigitsZ N w (2 ^ (k + 1)) A))) r
        * BZ.forwardFFT (((2 : ZMod (2 ^ N + 1)) ^ eθ) ^ 2) (k + 1)
          (extendZero (weight ((2 : ZMod (2 ^ N + 1)) ^ eθ) (ssDigitsZ N w (2 ^ (k + 1)) B))) r)
      j hj ?_]
  · exact BZ.backwardFFT_forwardFFT_weight_mul k hθ _ _ ⟨j, hj⟩
  · intro r hr
    rw [toZModFun_of_lt _ (by rw [hc]; exact hr), hcr r hr, toZModFun_ssWeighted,
      toZModFun_ssWeighted, hω]

/-- `2` is a unit modulo `2^N + 1`. -/
theorem isUnit_two : IsUnit (2 : ZMod (2 ^ N + 1)) := by
  have h : (2 : ZMod (2 ^ N + 1)) * 2 ^ (2 * N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (by have := NeZero.pos N; omega), two_pow_two_mul_eq_one]
  exact ⟨⟨2, 2 ^ (2 * N - 1), h, by rw [mul_comm]; exact h⟩, rfl⟩

omit [NeZero N] in
/-- **Recovery**: if `toZMod d` is the residue of an integer `c` in the window
`[(j+1) 2^{2M} − (2^N + 1), (j+1) 2^{2M})`, `ssRecover` returns `c`. -/
theorem toInt_ssRecover (M j : Nat) (d : AzFermat N) (c : Int)
    (hc : (c : ZMod (2 ^ N + 1)) = toZMod d)
    (hlo : ((j + 1 : ℕ) : ℤ) * 2 ^ (2 * M) - (2 ^ N + 1) ≤ c)
    (hhi : c < ((j + 1 : ℕ) : ℤ) * 2 ^ (2 * M)) (hU : (j + 1) * 2 ^ (2 * M) ≤ 2 ^ N + 1) :
    (ssRecover N (AzNat.ofNat (j + 1) <<< (2 * M)) d).toInt = c := by
  have hd := d.isLe
  -- the residue of `c` is `d.val.toNat`
  have hres : c % ((2 ^ N + 1 : ℕ) : ℤ) = (d.val.toNat : ℤ) := by
    have h := (ZMod.intCast_eq_intCast_iff' c (d.val.toNat : ℤ) (2 ^ N + 1)).mp
      (by rw [hc, toZMod, Int.cast_natCast])
    rw [h, Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_succ_of_le hd))]
  have hU' : ((j + 1 : ℕ) : ℤ) * 2 ^ (2 * M) ≤ ((2 ^ N + 1 : ℕ) : ℤ) := by
    have h := hU
    exact_mod_cast h
  have hwin := BZ.int_recover_of_mem_window (N := ((2 ^ N + 1 : ℕ) : ℤ)) (by positivity) hU' hlo hhi
  rw [hres] at hwin
  have hUval : (AzNat.ofNat (j + 1) <<< (2 * M)).toNat = (j + 1) * 2 ^ (2 * M) := by
    rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_ofNat]
  unfold ssRecover
  split_ifs with h
  · have h' : (j + 1) * 2 ^ (2 * M) ≤ d.val.toNat := by
      have := (AzNat.le_iff_toNat_le _ _).mp h
      rwa [hUval] at this
    have h'' : ((j + 1 : ℕ) : ℤ) * 2 ^ (2 * M) ≤ (d.val.toNat : ℤ) := by exact_mod_cast h'
    rw [SSCoeff.toInt, ite_eq_left rfl, AzNat.toNat_sub, toNat_modulus, hwin, ite_eq_left h'',
      Nat.cast_sub (by omega)]
    push_cast
    ring
  · have h' : d.val.toNat < (j + 1) * 2 ^ (2 * M) := by
      have := Nat.not_le.mp (fun hle => h ((AzNat.le_iff_toNat_le _ _).mpr (by rwa [hUval])))
      exact this
    have h'' : (d.val.toNat : ℤ) < ((j + 1 : ℕ) : ℤ) * 2 ^ (2 * M) := by exact_mod_cast h'
    rw [SSCoeff.toInt, ite_eq_right Bool.false_ne_true, hwin, ite_eq_right (not_le.mpr h'')]

/-- **The recovered coefficients are the negacyclic convolution of the digits**, for any array
`c` of pointwise products of the transforms of the weighted digits. -/
theorem toInt_ssCoefficients_getElem (k w : Nat) (hN : 2 * (64 * w) + (k + 1) ≤ N)
    (hK : 2 ^ (k + 1) ∣ N) (A B : AzNat) (c : Array (AzFermat N)) (hc : c.size = 2 ^ (k + 1))
    (hcr : ∀ (r : Nat) (hr : r < 2 ^ (k + 1)), toZMod (c[r]'(by rw [hc]; exact hr))
      = BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * (N / 2 ^ (k + 1)))) (k + 1)
          (toZModFun (ssWeighted k w N (N / 2 ^ (k + 1)) A)) r
        * BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * (N / 2 ^ (k + 1)))) (k + 1)
          (toZModFun (ssWeighted k w N (N / 2 ^ (k + 1)) B)) r)
    (j : Nat) (hj : j < 2 ^ (k + 1)) :
    haveI : NeZero (2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)⟩
    ((ssCoefficients k w N (N / 2 ^ (k + 1))
        (backwardFFT (2 * (N / 2 ^ (k + 1))) (k + 1) c hc)
        (backwardFFT_size _ _ _ _))[j]'(by rw [ssCoefficients, Array.size_ofFn]; exact hj)).toInt
      = negacyclicConv
          (fun i : Fin (2 ^ (k + 1)) => ((block A.limbs 0 A.limbs.size w i.val).toNat : Int))
          (fun i : Fin (2 ^ (k + 1)) => ((block B.limbs 0 B.limbs.size w i.val).toNat : Int))
          ⟨j, hj⟩ := by
  have : NeZero (2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)⟩
  set eθ := N / 2 ^ (k + 1) with heθ
  have hNe : N = eθ * 2 ^ (k + 1) := (Nat.div_mul_cancel hK).symm
  have hθ : ((2 : ZMod (2 ^ N + 1)) ^ eθ) ^ 2 ^ (k + 1) = -1 := by
    rw [← pow_mul, ← hNe]; exact two_pow_eq_neg_one
  set cZ := negacyclicConv
    (fun i : Fin (2 ^ (k + 1)) => ((block A.limbs 0 A.limbs.size w i.val).toNat : Int))
    (fun i : Fin (2 ^ (k + 1)) => ((block B.limbs 0 B.limbs.size w i.val).toNat : Int)) ⟨j, hj⟩
    with hcZ
  unfold ssCoefficients
  rw [Array.getElem_ofFn]
  -- the window
  have hbounds := BZ.negacyclicConv_bounds (K := 2 ^ (k + 1)) ((2 : Int) ^ (64 * w)) (by positivity)
    (fun i => ((block A.limbs 0 A.limbs.size w i.val).toNat : Int))
    (fun i => ((block B.limbs 0 B.limbs.size w i.val).toNat : Int))
    (fun i => ⟨by positivity, by exact_mod_cast toNat_block_lt _ _ _ _ _⟩)
    (fun i => ⟨by positivity, by exact_mod_cast toNat_block_lt _ _ _ _ _⟩) ⟨j, hj⟩
  rw [← hcZ] at hbounds
  have hpow : ((2 : Int) ^ (64 * w)) ^ 2 = 2 ^ (2 * (64 * w)) := by rw [← pow_mul, mul_comm]
  rw [hpow] at hbounds
  have hKfit : (2 ^ (k + 1) : Int) * 2 ^ (2 * (64 * w)) ≤ 2 ^ N := by
    rw [← pow_add]
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega : k + 1 + 2 * (64 * w) ≤ N)
  have hentry := toZMod_backwardFFT_of_products k w eθ hθ A B c hc hcr j hj
  refine toInt_ssRecover (64 * w) j _ cZ ?_ ?_ hbounds.2 ?_
  · -- the residue is `c_j`: divide `K θ^j c_j` by the unit `K θ^j`
    have hu : IsUnit ((2 : ZMod (2 ^ N + 1)) ^ (k + 1 + eθ * j)) := isUnit_two.pow _
    apply hu.mul_left_cancel
    rw [mul_comm _ (toZMod _), toZMod_divPow2_mul_two_pow, hentry, hcZ, negacyclicConv_intCast,
      pow_add, pow_mul]
    unfold ssDigitsZ
    push_cast
    ring
  · have h1 : (((2 ^ (k + 1) - 1 - j : ℕ) : ℤ)) = (2 ^ (k + 1) : Int) - 1 - j := by
      have hj' : j + 1 ≤ 2 ^ (k + 1) := hj
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h1] at hbounds
    push_cast
    nlinarith [hbounds.1, hKfit]
  · calc (j + 1) * 2 ^ (2 * (64 * w)) ≤ 2 ^ (k + 1) * 2 ^ (2 * (64 * w)) :=
          Nat.mul_le_mul_right _ hj
      _ ≤ 2 ^ N + 1 := by
          have : 2 ^ (k + 1) * 2 ^ (2 * (64 * w)) ≤ 2 ^ N := by
            rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
          omega

/-! ### The main theorem -/

/-- **MCA Theorem 2.3, from the pointwise products**: for `A, B < 2^n` (`n = 64 w · 2^(k+1)`) and
any array `c` of pointwise products of the transforms of the weighted digits,
`ssFinish k w N _ eθ c hc = A · B mod (2^n + 1)`. -/
theorem ssFinish_toNat (k w : Nat) (hw0 : 0 < w) (hN : 2 * (64 * w) + (k + 1) ≤ N)
    (hK : 2 ^ (k + 1) ∣ N) (A B : AzNat) (hA : A.toNat < 2 ^ (64 * w * 2 ^ (k + 1)))
    (hB : B.toNat < 2 ^ (64 * w * 2 ^ (k + 1))) (c : Array (AzFermat N))
    (hc : c.size = 2 ^ (k + 1))
    (hcr : ∀ (r : Nat) (hr : r < 2 ^ (k + 1)), toZMod (c[r]'(by rw [hc]; exact hr))
      = BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * (N / 2 ^ (k + 1)))) (k + 1)
          (toZModFun (ssWeighted k w N (N / 2 ^ (k + 1)) A)) r
        * BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * (N / 2 ^ (k + 1)))) (k + 1)
          (toZModFun (ssWeighted k w N (N / 2 ^ (k + 1)) B)) r) :
    (ssFinish k w N hw0 (N / 2 ^ (k + 1)) c hc).toNat
      = (A.toNat * B.toNat) % (2 ^ (64 * w * 2 ^ (k + 1)) + 1) := by
  have : NeZero (2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)⟩
  set n := 64 * w * 2 ^ (k + 1) with hn
  set dA : Fin (2 ^ (k + 1)) → Int := fun i => ((block A.limbs 0 A.limbs.size w i.val).toNat : Int)
    with hdA
  set dB : Fin (2 ^ (k + 1)) → Int := fun i => ((block B.limbs 0 B.limbs.size w i.val).toNat : Int)
    with hdB
  -- the assembled value is `∑ c_j 2^{jM}`
  have hS : toZMod (ssAssemble k w hw0 (ssCoefficients k w N (N / 2 ^ (k + 1))
        (backwardFFT (2 * (N / 2 ^ (k + 1))) (k + 1) c hc) (backwardFFT_size _ _ _ _)))
      = ∑ j : Fin (2 ^ (k + 1)),
          ((negacyclicConv dA dB j : Int) : ZMod (2 ^ n + 1)) * ((2 : ZMod (2 ^ n + 1)) ^ (64 * w)) ^ j.val := by
    unfold ssCoefficients
    rw [toZMod_ssAssemble]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := toInt_ssCoefficients_getElem k w hN hK A B c hc hcr j.val j.isLt
    unfold ssCoefficients at this
    rw [Array.getElem_ofFn] at this
    rw [this]
  -- the value modulo `2^n + 1`, in `ZMod (2^n + 1)`
  have hAB : (∑ j : Fin (2 ^ (k + 1)),
      ((negacyclicConv dA dB j : Int) : ZMod (2 ^ n + 1)) * ((2 : ZMod (2 ^ n + 1)) ^ (64 * w)) ^ j.val)
      = ((A.toNat * B.toNat : ℕ) : ZMod (2 ^ n + 1)) := by
    have hθ : ((2 : ZMod (2 ^ n + 1)) ^ (64 * w)) ^ 2 ^ (k + 1) = -1 := by
      rw [← pow_mul, ← hn]; exact BZ.two_pow_eq_neg_one_zmod n
    have hA' : ((A.toNat : ℕ) : ZMod (2 ^ n + 1))
        = ∑ ℓ : Fin (2 ^ (k + 1)), ((2 : ZMod (2 ^ n + 1)) ^ (64 * w)) ^ ℓ.val * (dA ℓ : ZMod (2 ^ n + 1)) := by
      have h := toNat_eq_sum_blocks A w (2 ^ (k + 1)) hA
      have h' := congrArg (fun z : Int => (z : ZMod (2 ^ n + 1))) h
      simp only [Int.cast_natCast] at h'
      rw [h']
      push_cast
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [hdA]
      push_cast
      ring
    have hB' : ((B.toNat : ℕ) : ZMod (2 ^ n + 1))
        = ∑ ℓ : Fin (2 ^ (k + 1)), ((2 : ZMod (2 ^ n + 1)) ^ (64 * w)) ^ ℓ.val * (dB ℓ : ZMod (2 ^ n + 1)) := by
      have h := toNat_eq_sum_blocks B w (2 ^ (k + 1)) hB
      have h' := congrArg (fun z : Int => (z : ZMod (2 ^ n + 1))) h
      simp only [Int.cast_natCast] at h'
      rw [h']
      push_cast
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [hdB]
      push_cast
      ring
    rw [Nat.cast_mul, hA', hB', BZ.sum_weight_mul_sum_weight hθ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [negacyclicConv_intCast, mul_comm]
  -- assemble
  unfold ssFinish
  dsimp only
  rw [← toZMod_val, hS, hAB, ZMod.val_natCast]

/-- **MCA Theorem 2.3**: `fftMulModWith k w N _ _ mulFn A B = A · B mod (2^n + 1)` for
`A, B < 2^n`, `n = 64 w · 2^(k+1)`, and any correct `mulFn`. -/
theorem fftMulModWith_toNat (k w N : Nat) (hw0 : 0 < w) (hN : 2 * (64 * w) + (k + 1) ≤ N)
    (hK : 2 ^ (k + 1) ∣ N) (mulFn : AzNat → AzNat → AzNat)
    (hmul : ∀ x y : AzNat, (mulFn x y).toNat = x.toNat * y.toNat) (A B : AzNat)
    (hA : A.toNat < 2 ^ (64 * w * 2 ^ (k + 1))) (hB : B.toNat < 2 ^ (64 * w * 2 ^ (k + 1))) :
    (fftMulModWith k w N hw0 hN hK mulFn A B).toNat
      = (A.toNat * B.toNat) % (2 ^ (64 * w * 2 ^ (k + 1)) + 1) := by
  have : NeZero N := ⟨by omega⟩
  exact ssFinish_toNat k w hw0 hN hK A B hA hB _ _
    (fun r hr => toZMod_ssProducts_getElem k _ mulFn hmul _ _ _ _ r hr)

/-- The squaring version of Theorem 2.3. -/
theorem fftSquareModWith_toNat (k w N : Nat) (hw0 : 0 < w) (hN : 2 * (64 * w) + (k + 1) ≤ N)
    (hK : 2 ^ (k + 1) ∣ N) (sqFn : AzNat → AzNat)
    (hsq : ∀ x : AzNat, (sqFn x).toNat = x.toNat * x.toNat) (A : AzNat)
    (hA : A.toNat < 2 ^ (64 * w * 2 ^ (k + 1))) :
    (fftSquareModWith k w N hw0 hN hK sqFn A).toNat
      = (A.toNat * A.toNat) % (2 ^ (64 * w * 2 ^ (k + 1)) + 1) := by
  have : NeZero N := ⟨by omega⟩
  exact ssFinish_toNat k w hw0 hN hK A A hA hA _ _
    (fun r hr => toZMod_ssSquares_getElem k _ sqFn hsq _ _ r hr)

theorem fftMulMod_toNat (k w : Nat) (hw0 : 0 < w) (mulFn : AzNat → AzNat → AzNat)
    (hmul : ∀ x y : AzNat, (mulFn x y).toNat = x.toNat * y.toNat) (A B : AzNat)
    (hA : A.toNat < 2 ^ (64 * w * 2 ^ (k + 1))) (hB : B.toNat < 2 ^ (64 * w * 2 ^ (k + 1))) :
    (fftMulMod k w hw0 mulFn A B).toNat
      = (A.toNat * B.toNat) % (2 ^ (64 * w * 2 ^ (k + 1)) + 1) :=
  fftMulModWith_toNat k w _ hw0 _ _ mulFn hmul A B hA hB

theorem fftSquareMod_toNat (k w : Nat) (hw0 : 0 < w) (sqFn : AzNat → AzNat)
    (hsq : ∀ x : AzNat, (sqFn x).toNat = x.toNat * x.toNat) (A : AzNat)
    (hA : A.toNat < 2 ^ (64 * w * 2 ^ (k + 1))) :
    (fftSquareMod k w hw0 sqFn A).toNat
      = (A.toNat * A.toNat) % (2 ^ (64 * w * 2 ^ (k + 1)) + 1) :=
  fftSquareModWith_toNat k w _ hw0 _ _ sqFn hsq A hA

/-! ### Integer multiplication -/

/-- `2^(64 · size) ≤ 2^n` for the parameters chosen by `ssParamsWith`. -/
theorem two_pow_le_of_ssParamsWith (kAdj L : Nat) :
    2 ^ (64 * L) ≤ 2 ^ (64 * (ssParamsWith kAdj L).2 * 2 ^ ((ssParamsWith kAdj L).1 + 1)) :=
  Nat.pow_le_pow_right (by norm_num) (by
    have := ssParamsWith_le kAdj L
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 64 this)

/-- **`fftMulWith` is multiplication**, for any digit-count adjustment. -/
theorem toNat_fftMulWith (kAdj : Nat) (mulFn : AzNat → AzNat → AzNat)
    (hmul : ∀ x y : AzNat, (mulFn x y).toNat = x.toNat * y.toNat) (A B : AzNat) :
    (fftMulWith kAdj mulFn A B).toNat = A.toNat * B.toNat := by
  unfold fftMulWith
  have hL := two_pow_le_of_ssParamsWith kAdj (A.limbs.size + B.limbs.size)
  have hA := toNat_lt_pow A
  have hB := toNat_lt_pow B
  have hprod : A.toNat * B.toNat < 2 ^ (64 * (A.limbs.size + B.limbs.size)) := by
    rw [Nat.mul_add, pow_add]
    exact Nat.mul_lt_mul'' hA hB
  rw [fftMulMod_toNat _ _ _ mulFn hmul A B
    (Nat.lt_of_lt_of_le hA (Nat.le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hL))
    (Nat.lt_of_lt_of_le hB (Nat.le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hL))]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hprod hL) (Nat.le_succ _))

/-- **`fftMul` is multiplication.** -/
theorem toNat_fftMul (mulFn : AzNat → AzNat → AzNat)
    (hmul : ∀ x y : AzNat, (mulFn x y).toNat = x.toNat * y.toNat) (A B : AzNat) :
    (fftMul mulFn A B).toNat = A.toNat * B.toNat :=
  toNat_fftMulWith _ mulFn hmul A B

/-- **`fftSquareWith` is squaring**, for any digit-count adjustment. -/
theorem toNat_fftSquareWith (kAdj : Nat) (sqFn : AzNat → AzNat)
    (hsq : ∀ x : AzNat, (sqFn x).toNat = x.toNat * x.toNat) (A : AzNat) :
    (fftSquareWith kAdj sqFn A).toNat = A.toNat * A.toNat := by
  unfold fftSquareWith
  have hL := two_pow_le_of_ssParamsWith kAdj (2 * A.limbs.size)
  have hA := toNat_lt_pow A
  have hprod : A.toNat * A.toNat < 2 ^ (64 * (2 * A.limbs.size)) := by
    rw [show 64 * (2 * A.limbs.size) = 64 * A.limbs.size + 64 * A.limbs.size by ring, pow_add]
    exact Nat.mul_lt_mul'' hA hA
  rw [fftSquareMod_toNat _ _ _ sqFn hsq A
    (Nat.lt_of_lt_of_le hA (Nat.le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hL))]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hprod hL) (Nat.le_succ _))

/-- **`fftSquare` is squaring.** -/
theorem toNat_fftSquare (sqFn : AzNat → AzNat)
    (hsq : ∀ x : AzNat, (sqFn x).toNat = x.toNat * x.toNat) (A : AzNat) :
    (fftSquare sqFn A).toNat = A.toNat * A.toNat :=
  toNat_fftSquareWith _ sqFn hsq A

/-- `fftMulLimbs` multiplies two slices. -/
theorem fftMulLimbs_toNat (mulFn : AzNat → AzNat → AzNat)
    (hmul : ∀ x y : AzNat, (mulFn x y).toNat = x.toNat * y.toNat) (a b : Array UInt64)
    (loA loB len : Nat) (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    toNatLimbsList (fftMulLimbs mulFn a b loA loB len hA hB).toList
      = sliceVal a loA len * sliceVal b loB len := by
  unfold fftMulLimbs
  have hv : (fftMul mulFn (ofLimbs (a.extract loA (loA + len)))
      (ofLimbs (b.extract loB (loB + len)))).toNat = sliceVal a loA len * sliceVal b loB len := by
    rw [toNat_fftMul mulFn hmul, toNat_ofLimbs, toNat_ofLimbs, toNatLimbsList_extract,
      toNatLimbsList_extract]
  rw [truncatePad_toNat]
  · exact hv
  · change AzNat.toNat _ < _
    rw [hv, show 64 * (2 * len) = 64 * len + 64 * len by ring, pow_add]
    exact Nat.mul_lt_mul'' (sliceVal_lt_pow _ _ _) (sliceVal_lt_pow _ _ _)

/-- `fftSquareLimbs` squares a slice. -/
theorem fftSquareLimbs_toNat (sqFn : AzNat → AzNat)
    (hsq : ∀ x : AzNat, (sqFn x).toNat = x.toNat * x.toNat) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) :
    toNatLimbsList (fftSquareLimbs sqFn a lo len hA).toList = sliceVal a lo len * sliceVal a lo len := by
  unfold fftSquareLimbs
  have hv : (fftSquare sqFn (ofLimbs (a.extract lo (lo + len)))).toNat
      = sliceVal a lo len * sliceVal a lo len := by
    rw [toNat_fftSquare sqFn hsq, toNat_ofLimbs, toNatLimbsList_extract]
  rw [truncatePad_toNat]
  · exact hv
  · change AzNat.toNat _ < _
    rw [hv, show 64 * (2 * len) = 64 * len + 64 * len by ring, pow_add]
    exact Nat.mul_lt_mul'' (sliceVal_lt_pow _ _ _) (sliceVal_lt_pow _ _ _)

end Azurite.AzNat

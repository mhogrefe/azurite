/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFermat.FFT
import Azurite.AzNat.Mul.ToomEval

/-!
# Schönhage–Strassen multiplication modulo `2^n + 1` (MCA Algorithm 2.4)

`fftMulModWith k w N A B` computes `A · B mod (2^n + 1)` for `A, B < 2^n`, where the operands are
cut into `K = 2^(k+1)` digits of `w` limbs (`M = 64 w` bits, `n = M K`) and the coefficient ring
is `ℤ/(2^N + 1)` with `2M + k + 1 ≤ N` (so that the coefficients of the product polynomial fit)
and `K ∣ N` (so that `θ = 2^{N/K}` has `θ^K = 2^N = −1`).  The steps are those of
Brent–Zimmermann §2.3.3:

1. digits `a_j = block j` of `A` (limb slices), as residues; weighted by `θ^j` (`mulPow2`);
2. `forwardFFT` of both operands at `ω = θ²`, in bit-reversed order;
3. pointwise products (the `AzFermat` product: the production multiplication ladder, reduced);
4. `backwardFFT`, natural order;
5. division by `K θ^j` (`divPow2`), then recovery of the signed coefficient `c_j` from its
   residue: `c_j ≥ (j+1) 2^{2M}` means the true value is negative (steps 12–13 of MCA); the
   coefficient is produced directly as a residue modulo `2^n + 1` (`AzFermat n`);
6. `∑ c_j 2^{jM}` by Horner's rule in `AzFermat n`, whose canonical representative is the
   result.

`fftMulMod k w` picks the smallest admissible `N` (`ssFermatExponent`); `fftMul` chooses `k` and
`w` from the operand sizes (`ssParams`) so that the product is below `2^n` and the residue is the
product itself; `fftMulLimbs` is the slice-level shape used by the balanced ladder of
`AzNat/Mul.lean`, and `fftSquare*` are the squaring versions (one transform saved).  Correctness
is in `Equiv/Mul/SchonhageStrassen.lean` (`fftMulModWith_toNat`, `toNat_fftMul`, …).
-/

namespace Azurite.AzNat

open AzFermat

/-- Digit `j` of `A` (the `j`-th slice of `w` limbs) as a residue modulo `2^N + 1`.  The
digit is below `2^{64 w} ≤ 2^N`, so `ofAzNat` is one comparison and no arithmetic. -/
def ssDigit (N w : Nat) [NeZero N] (A : AzNat) (j : Nat) : AzFermat N :=
  ofAzNat N (block A.limbs 0 A.limbs.size w j)

/-- The signed coefficient from its residue `r` modulo `2^N + 1` (MCA steps 12–13): `r` itself
unless `r ≥ U = (j+1) 2^{2M}`, in which case `r − (2^N + 1)`; delivered as a residue modulo
`2^n + 1`. -/
def ssRecover (N n : Nat) [NeZero n] (U : AzNat) (r : AzFermat N) : AzFermat n :=
  if U ≤ r.val then AzFermat.neg (reduceAny (modulus N - r.val)) else reduceAny r.val

/-- Step 1 and step 5 of Algorithm 2.4: the `K = 2^(k+1)` digits of `A`, weighted by
`θ^j = 2^{eθ·j}`. -/
def ssWeighted (k w N : Nat) [NeZero N] (eθ : Nat) (A : AzNat) : Array (AzFermat N) :=
  Array.ofFn fun j : Fin (2 ^ (k + 1)) => mulPow2 (eθ * j.val) (ssDigit N w A j.val)

theorem ssWeighted_size (k w N : Nat) [NeZero N] (eθ : Nat) (A : AzNat) :
    (ssWeighted k w N eθ A).size = 2 ^ (k + 1) := Array.size_ofFn

/-- Steps 6–8: the forward transforms at `ω = 2^{2 eθ}` and their pointwise products, the
`AzNat` products taken by `mulFn` (the Toom ladder, or a recursive FFT multiplication). -/
def ssProducts (k N : Nat) [NeZero N] (eθ : Nat) (mulFn : AzNat → AzNat → AzNat)
    (a b : Array (AzFermat N)) (ha : a.size = 2 ^ (k + 1)) (hb : b.size = 2 ^ (k + 1)) :
    Array (AzFermat N) :=
  let fa := forwardFFT (2 * eθ) (k + 1) a ha
  let fb := forwardFFT (2 * eθ) (k + 1) b hb
  Array.ofFn fun r : Fin (2 ^ (k + 1)) =>
    mulWith mulFn (fa[r.val]'(by rw [forwardFFT_size]; exact r.isLt))
      (fb[r.val]'(by rw [forwardFFT_size]; exact r.isLt))

theorem ssProducts_size (k N : Nat) [NeZero N] (eθ : Nat) (mulFn : AzNat → AzNat → AzNat)
    (a b : Array (AzFermat N)) (ha : a.size = 2 ^ (k + 1)) (hb : b.size = 2 ^ (k + 1)) :
    (ssProducts k N eθ mulFn a b ha hb).size = 2 ^ (k + 1) := Array.size_ofFn

/-- Steps 6–8 for squaring: one forward transform, pointwise squares by `sqFn`. -/
def ssSquares (k N : Nat) [NeZero N] (eθ : Nat) (sqFn : AzNat → AzNat) (a : Array (AzFermat N))
    (ha : a.size = 2 ^ (k + 1)) : Array (AzFermat N) :=
  let fa := forwardFFT (2 * eθ) (k + 1) a ha
  Array.ofFn fun r : Fin (2 ^ (k + 1)) =>
    reduceAny (sqFn (fa[r.val]'(by rw [forwardFFT_size]; exact r.isLt)).val)

theorem ssSquares_size (k N : Nat) [NeZero N] (eθ : Nat) (sqFn : AzNat → AzNat)
    (a : Array (AzFermat N)) (ha : a.size = 2 ^ (k + 1)) :
    (ssSquares k N eθ sqFn a ha).size = 2 ^ (k + 1) := Array.size_ofFn

/-- Steps 10–13: divide the `j`-th entry of the backward transform by `K θ^j` and recover the
signed coefficient, as a residue modulo `2^n + 1`. -/
def ssCoefficients (k w N : Nat) [NeZero N] (n : Nat) [NeZero n] (eθ : Nat)
    (bc : Array (AzFermat N)) (hbc : bc.size = 2 ^ (k + 1)) : Array (AzFermat n) :=
  Array.ofFn fun j : Fin (2 ^ (k + 1)) =>
    ssRecover N n (AzNat.ofNat (j.val + 1) <<< (2 * (64 * w)))
      (divPow2 (k + 1 + eθ * j.val) (bc[j.val]'(by rw [hbc]; exact j.isLt)))

/-- Step 14: `∑_j c_j 2^{jM}` by Horner's rule modulo `2^n + 1` (`M ≤ n`). -/
def ssAssemble (M n : Nat) (hM : M ≤ n) (coeffs : Array (AzFermat n)) : AzFermat n :=
  coeffs.toList.foldr (fun c acc => AzFermat.add c (mulPow2Le M hM acc)) 0

/-- Steps 9–14 from the array of pointwise products: backward transform, coefficients, assembly
modulo `2^n + 1`. -/
def ssFinish (k w N : Nat) [NeZero N] (hw0 : 0 < w) (eθ : Nat) (c : Array (AzFermat N))
    (hc : c.size = 2 ^ (k + 1)) : AzNat :=
  haveI : NeZero (64 * w * 2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩
  let bc := backwardFFT (2 * eθ) (k + 1) c hc
  (ssAssemble (64 * w) (64 * w * 2 ^ (k + 1)) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    (ssCoefficients k w N (64 * w * 2 ^ (k + 1)) eθ bc (backwardFFT_size _ _ _ _))).val

/-- Algorithm 2.4 with explicit parameters (see the module docstring); `mulFn` multiplies the
pointwise products. -/
def fftMulModWith (k w N : Nat) (hw0 : 0 < w) (hN : 2 * (64 * w) + (k + 1) ≤ N)
    (_hK : 2 ^ (k + 1) ∣ N) (mulFn : AzNat → AzNat → AzNat) (A B : AzNat) : AzNat :=
  haveI : NeZero N := ⟨by omega⟩
  let eθ := N / 2 ^ (k + 1)
  ssFinish k w N hw0 eθ (ssProducts k N eθ mulFn (ssWeighted k w N eθ A) (ssWeighted k w N eθ B)
    (ssWeighted_size k w N eθ A) (ssWeighted_size k w N eθ B)) (ssProducts_size k N eθ _ _ _ _ _)

/-- Algorithm 2.4 for squaring: one weighting and one forward transform, pointwise squares by
`sqFn`. -/
def fftSquareModWith (k w N : Nat) (hw0 : 0 < w) (hN : 2 * (64 * w) + (k + 1) ≤ N)
    (_hK : 2 ^ (k + 1) ∣ N) (sqFn : AzNat → AzNat) (A : AzNat) : AzNat :=
  haveI : NeZero N := ⟨by omega⟩
  let eθ := N / 2 ^ (k + 1)
  ssFinish k w N hw0 eθ (ssSquares k N eθ sqFn (ssWeighted k w N eθ A) (ssWeighted_size k w N eθ A))
    (ssSquares_size k N eθ _ _ _)

/-- The smallest admissible Fermat exponent: `2M + k + 1` rounded up to a multiple of
`max K 64` (a multiple of `K` and of `64`). -/
def ssFermatExponent (k w : Nat) : Nat :=
  (2 * (64 * w) + (k + 1) + max (2 ^ (k + 1)) 64 - 1) / max (2 ^ (k + 1)) 64
    * max (2 ^ (k + 1)) 64

theorem ssFermatExponent_ge (k w : Nat) : 2 * (64 * w) + (k + 1) ≤ ssFermatExponent k w := by
  unfold ssFermatExponent
  have hg : 0 < max (2 ^ (k + 1)) 64 := by omega
  have h := Nat.lt_div_mul_add (a := 2 * (64 * w) + (k + 1) + max (2 ^ (k + 1)) 64 - 1) hg
  generalize (2 * (64 * w) + (k + 1) + max (2 ^ (k + 1)) 64 - 1) / max (2 ^ (k + 1)) 64
    * max (2 ^ (k + 1)) 64 = Q at h ⊢
  omega

theorem two_pow_dvd_ssFermatExponent (k w : Nat) : 2 ^ (k + 1) ∣ ssFermatExponent k w := by
  unfold ssFermatExponent
  apply Dvd.dvd.mul_left
  rcases Nat.lt_or_ge (2 ^ (k + 1)) 64 with h | h
  · rw [Nat.max_eq_right (le_of_lt h)]
    have hk : k + 1 ≤ 6 := by
      rcases Nat.lt_or_ge (k + 1) 7 with hk | hk
      · omega
      · exact absurd h (Nat.not_lt.mpr (Nat.le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)))
    exact Nat.pow_dvd_pow 2 hk
  · rw [Nat.max_eq_left h]

/-- Algorithm 2.4 with the smallest admissible Fermat exponent: `A · B mod (2^n + 1)` for
`A, B < 2^n`, `n = 64 w · 2^(k+1)`. -/
def fftMulMod (k w : Nat) (hw0 : 0 < w) (mulFn : AzNat → AzNat → AzNat) (A B : AzNat) : AzNat :=
  fftMulModWith k w (ssFermatExponent k w) hw0 (ssFermatExponent_ge k w)
    (two_pow_dvd_ssFermatExponent k w) mulFn A B

/-- The squaring version of `fftMulMod`. -/
def fftSquareMod (k w : Nat) (hw0 : 0 < w) (sqFn : AzNat → AzNat) (A : AzNat) : AzNat :=
  fftSquareModWith k w (ssFermatExponent k w) hw0 (ssFermatExponent_ge k w)
    (two_pow_dvd_ssFermatExponent k w) sqFn A

/-! ### Integer multiplication -/

/-- Parameters for a product of at most `L` limbs: `K = 2^(k+1)` digits with
`k = ⌊lg L⌋ / 2 + kAdj` (so `K ≈ 2^(kAdj+1) √L`; more digits mean smaller pointwise products
and a bigger transform), and `w = ⌈L / K⌉` limbs per digit, so that `n = 64 w K ≥ 64 L` bits. -/
def ssParamsWith (kAdj L : Nat) : Nat × Nat :=
  let k := Nat.log2 L / 2 + kAdj
  (k, max 1 ((L + 2 ^ (k + 1) - 1) / 2 ^ (k + 1)))

theorem ssParamsWith_pos (kAdj L : Nat) : 0 < (ssParamsWith kAdj L).2 := by
  unfold ssParamsWith
  dsimp only
  omega

theorem ssParamsWith_le (kAdj L : Nat) :
    L ≤ (ssParamsWith kAdj L).2 * 2 ^ ((ssParamsWith kAdj L).1 + 1) := by
  unfold ssParamsWith
  dsimp only
  generalize Nat.log2 L / 2 + kAdj = k
  have hK : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
  have h := Nat.lt_div_mul_add (a := L + 2 ^ (k + 1) - 1) hK
  generalize (L + 2 ^ (k + 1) - 1) / 2 ^ (k + 1) = q at h ⊢
  generalize 2 ^ (k + 1) = K at h hK ⊢
  rcases Nat.lt_or_ge q 1 with hq | hq
  · obtain rfl : q = 0 := by omega
    rw [Nat.max_eq_left (Nat.zero_le _)]
    omega
  · rw [Nat.max_eq_right hq]
    omega

/-- The digit-count adjustment used by `fftMul` and `fftSquare` (`ssParamsWith`); tuned by
`az_nat_fft_profile`. -/
def ssKAdjust : Nat := 0

/-- The default parameters: `ssParamsWith ssKAdjust`. -/
def ssParams (L : Nat) : Nat × Nat := ssParamsWith ssKAdjust L

theorem ssParams_pos (L : Nat) : 0 < (ssParams L).2 := ssParamsWith_pos _ L

theorem ssParams_le (L : Nat) : L ≤ (ssParams L).2 * 2 ^ ((ssParams L).1 + 1) :=
  ssParamsWith_le _ L

/-- Schönhage–Strassen integer multiplication with an explicit digit-count adjustment. -/
def fftMulWith (kAdj : Nat) (mulFn : AzNat → AzNat → AzNat) (A B : AzNat) : AzNat :=
  fftMulMod (ssParamsWith kAdj (A.limbs.size + B.limbs.size)).1
    (ssParamsWith kAdj (A.limbs.size + B.limbs.size)).2 (ssParamsWith_pos _ _) mulFn A B

/-- **Schönhage–Strassen integer multiplication**: `A · B`, exactly, with `mulFn` for the
pointwise products. -/
def fftMul (mulFn : AzNat → AzNat → AzNat) (A B : AzNat) : AzNat :=
  fftMulWith ssKAdjust mulFn A B

/-- Schönhage–Strassen squaring with an explicit digit-count adjustment. -/
def fftSquareWith (kAdj : Nat) (sqFn : AzNat → AzNat) (A : AzNat) : AzNat :=
  fftSquareMod (ssParamsWith kAdj (2 * A.limbs.size)).1 (ssParamsWith kAdj (2 * A.limbs.size)).2
    (ssParamsWith_pos _ _) sqFn A

/-- **Schönhage–Strassen squaring**: `A · A`, exactly, with `sqFn` for the pointwise squares. -/
def fftSquare (sqFn : AzNat → AzNat) (A : AzNat) : AzNat :=
  fftSquareWith ssKAdjust sqFn A

/-- `fftMul` on two `len`-limb slices, in `2·len` limbs (the shape of the balanced ladder). -/
def fftMulLimbs (mulFn : AzNat → AzNat → AzNat) (a b : Array UInt64) (loA loB len : Nat)
    (_hA : loA + len ≤ a.size) (_hB : loB + len ≤ b.size) : Array UInt64 :=
  truncatePad (fftMul mulFn (ofLimbs (a.extract loA (loA + len)))
    (ofLimbs (b.extract loB (loB + len)))).limbs (2 * len)

theorem fftMulLimbs_size (mulFn : AzNat → AzNat → AzNat) (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (fftMulLimbs mulFn a b loA loB len hA hB).size = 2 * len := truncatePad_size _ _

/-- `fftSquare` on a `len`-limb slice, in `2·len` limbs. -/
def fftSquareLimbs (sqFn : AzNat → AzNat) (a : Array UInt64) (lo len : Nat)
    (_hA : lo + len ≤ a.size) : Array UInt64 :=
  truncatePad (fftSquare sqFn (ofLimbs (a.extract lo (lo + len)))).limbs (2 * len)

theorem fftSquareLimbs_size (sqFn : AzNat → AzNat) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : (fftSquareLimbs sqFn a lo len hA).size = 2 * len :=
  truncatePad_size _ _

end Azurite.AzNat

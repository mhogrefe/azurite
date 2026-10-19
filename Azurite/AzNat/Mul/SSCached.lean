/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.SchonhageStrassen

/-!
# Schönhage–Strassen with a cached forward transform

A fixed operand that is multiplied many times (Barrett's reciprocal and divisor, MCA §2.4.1:
"if the forward transforms of `I` and `B` are stored, the cost decreases to `M(n)`") has its
weighting and forward transform computed once (`ssTransform`); each product then costs one
forward and one backward transform plus the pointwise products (`ssProductsCached`,
`fftMulModCachedF`).  The result is kept in the Fermat ring `ℤ/(2^(64 w K) + 1)` (`ssFinishF`),
so that a difference modulo `2^n + 1` — the wrap-around trick of MCA §3.4.1 — needs no second
reduction.  `SSPlan L` packages the parameters for residues of at least `L` limbs.

Everything here is definitionally a rearrangement of `fftMulModWith`, so its correctness
(`Equiv/Mul/SSCached.lean`) is that of `fftMulModWith_toNat`.
-/

namespace Azurite.AzNat

open AzFermat

/-- Steps 1–6 of Algorithm 2.4 for one operand: its weighted digits, transformed. -/
def ssTransform (k w N : Nat) [NeZero N] (eθ : Nat) (A : AzNat) : Array (AzFermat N) :=
  forwardFFT (2 * eθ) (k + 1) (ssWeighted k w N eθ A) (ssWeighted_size k w N eθ A)

theorem ssTransform_size (k w N : Nat) [NeZero N] (eθ : Nat) (A : AzNat) :
    (ssTransform k w N eθ A).size = 2 ^ (k + 1) := forwardFFT_size _ _ _ _

/-- Steps 6–8 with the first operand's transform `fa` already computed. -/
def ssProductsCached (k N : Nat) [NeZero N] (eθ : Nat) (mulFn : AzNat → AzNat → AzNat)
    (fa : Array (AzFermat N)) (hfa : fa.size = 2 ^ (k + 1)) (b : Array (AzFermat N))
    (hb : b.size = 2 ^ (k + 1)) : Array (AzFermat N) :=
  let fb := forwardFFT (2 * eθ) (k + 1) b hb
  Array.ofFn fun r : Fin (2 ^ (k + 1)) =>
    mulWith mulFn (fa[r.val]'(by rw [hfa]; exact r.isLt))
      (fb[r.val]'(by rw [forwardFFT_size]; exact r.isLt))

theorem ssProductsCached_size (k N : Nat) [NeZero N] (eθ : Nat) (mulFn : AzNat → AzNat → AzNat)
    (fa : Array (AzFermat N)) (hfa : fa.size = 2 ^ (k + 1)) (b : Array (AzFermat N))
    (hb : b.size = 2 ^ (k + 1)) :
    (ssProductsCached k N eθ mulFn fa hfa b hb).size = 2 ^ (k + 1) := Array.size_ofFn

/-- With the transform of `a`, the cached products are the products. -/
theorem ssProductsCached_forwardFFT (k N : Nat) [NeZero N] (eθ : Nat)
    (mulFn : AzNat → AzNat → AzNat) (a b : Array (AzFermat N)) (ha : a.size = 2 ^ (k + 1))
    (hb : b.size = 2 ^ (k + 1)) :
    ssProductsCached k N eθ mulFn (forwardFFT (2 * eθ) (k + 1) a ha) (forwardFFT_size _ _ _ _) b hb
      = ssProducts k N eθ mulFn a b ha hb := rfl

/-- Steps 9–14, with the result in the Fermat ring `ℤ/(2^(64 w K) + 1)`. -/
def ssFinishF (k w N : Nat) [NeZero N] (hw0 : 0 < w) (eθ : Nat) (c : Array (AzFermat N))
    (hc : c.size = 2 ^ (k + 1)) : AzFermat (64 * w * 2 ^ (k + 1)) :=
  ssAssemble k w hw0 (ssCoefficients k w N eθ (backwardFFT (2 * eθ) (k + 1) c hc)
    (backwardFFT_size _ _ _ _))

theorem ssFinishF_val (k w N : Nat) [NeZero N] (hw0 : 0 < w) (eθ : Nat) (c : Array (AzFermat N))
    (hc : c.size = 2 ^ (k + 1)) :
    (ssFinishF k w N hw0 eθ c hc).val = ssFinish k w N hw0 eθ c hc := rfl

/-- Algorithm 2.4 with the first operand's transform cached, in the Fermat ring. -/
def fftMulModCachedF (k w N : Nat) (hw0 : 0 < w) (hN : 2 * (64 * w) + (k + 1) ≤ N)
    (_hK : 2 ^ (k + 1) ∣ N) (mulFn : AzNat → AzNat → AzNat) (fa : Array (AzFermat N))
    (hfa : fa.size = 2 ^ (k + 1)) (B : AzNat) : AzFermat (64 * w * 2 ^ (k + 1)) :=
  haveI : NeZero N := ⟨by omega⟩
  let eθ := N / 2 ^ (k + 1)
  ssFinishF k w N hw0 eθ (ssProductsCached k N eθ mulFn fa hfa (ssWeighted k w N eθ B)
    (ssWeighted_size k w N eθ B)) (ssProductsCached_size k N eθ mulFn fa hfa _ _)

/-- With the transform of `A`, the cached product is `fftMulModWith`. -/
theorem fftMulModCachedF_ssTransform (k w N : Nat) [NeZero N] (hw0 : 0 < w)
    (hN : 2 * (64 * w) + (k + 1) ≤ N) (hK : 2 ^ (k + 1) ∣ N) (mulFn : AzNat → AzNat → AzNat)
    (A B : AzNat) :
    (fftMulModCachedF k w N hw0 hN hK mulFn (ssTransform k w N (N / 2 ^ (k + 1)) A)
        (ssTransform_size _ _ _ _ _) B).val
      = fftMulModWith k w N hw0 hN hK mulFn A B := rfl

/-! ### Plans -/

/-- The parameters of a Fermat ring `ℤ/(2^(64 w K) + 1)`, `K = 2^(k+1)`. -/
structure SSPlan where
  /-- `K = 2^(k+1)` digits. -/
  k : Nat
  /-- Limbs per digit. -/
  w : Nat
  hw0 : 0 < w

namespace SSPlan

/-- The plan for residues of at least `L` limbs (`64 L ≤ bits`). -/
def ofLimbs (L : Nat) : SSPlan := ⟨(ssParams L).1, (ssParams L).2, ssParams_pos L⟩

/-- The coefficient-ring exponent. -/
def N (p : SSPlan) : Nat := ssFermatExponent p.k p.w

/-- The residue size: `n = 64 w K` bits. -/
def bits (p : SSPlan) : Nat := 64 * p.w * 2 ^ (p.k + 1)

theorem N_pos (p : SSPlan) : 0 < p.N := by
  have := ssFermatExponent_ge p.k p.w
  unfold N; omega

instance (p : SSPlan) : NeZero p.N := ⟨(N_pos p).ne'⟩

theorem bits_pos (p : SSPlan) : 0 < p.bits := by
  unfold bits; have := p.hw0; positivity

instance (p : SSPlan) : NeZero p.bits := ⟨(bits_pos p).ne'⟩

/-- `θ`'s exponent, `N/K`. -/
def eθ (p : SSPlan) : Nat := p.N / 2 ^ (p.k + 1)

/-- The cached transform of an operand. -/
def transform (p : SSPlan) (A : AzNat) : Array (AzFermat p.N) :=
  ssTransform p.k p.w p.N p.eθ A

theorem transform_size (p : SSPlan) (A : AzNat) : (p.transform A).size = 2 ^ (p.k + 1) :=
  ssTransform_size _ _ _ _ _

/-- `A · B mod (2^bits + 1)` in the Fermat ring, from the transform `fa` of `A`. -/
def mulModF (p : SSPlan) (mulFn : AzNat → AzNat → AzNat) (fa : Array (AzFermat p.N))
    (hfa : fa.size = 2 ^ (p.k + 1)) (B : AzNat) : AzFermat p.bits :=
  fftMulModCachedF p.k p.w p.N p.hw0 (ssFermatExponent_ge p.k p.w)
    (two_pow_dvd_ssFermatExponent p.k p.w) mulFn fa hfa B

/-- `A · B mod (2^bits + 1)` in the Fermat ring (transforming `A` now). -/
def mulModF' (p : SSPlan) (mulFn : AzNat → AzNat → AzNat) (A B : AzNat) : AzFermat p.bits :=
  p.mulModF mulFn (p.transform A) (p.transform_size A) B

theorem mulModF'_val (p : SSPlan) (mulFn : AzNat → AzNat → AzNat) (A B : AzNat) :
    (p.mulModF' mulFn A B).val
      = fftMulModWith p.k p.w p.N p.hw0 (ssFermatExponent_ge p.k p.w)
          (two_pow_dvd_ssFermatExponent p.k p.w) mulFn A B := rfl

end SSPlan

end Azurite.AzNat

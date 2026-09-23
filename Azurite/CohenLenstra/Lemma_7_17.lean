/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra Lemma (7.17): roots of unity are separated by the
  ideal `𝔯 = rB + 𝔫`.**

  If `ζ ∈ U_{p^k}` satisfies `ζ ≡ 1 (mod 𝔯)`, then `ζ = 1`.  The
  paper's proof: `∏_{ζ' ≠ 1} (1 − ζ') = p^k`, so if some nontrivial
  root were `≡ 1`, then `p^k ∈ 𝔯 = rB + 𝔫`, say `p^k = rx + y`;
  multiplying by `n/r` gives `p^k·(n/r) ∈ 𝔫`, hence `n ∣ p^k·(n/r)`
  by (7.7), i.e. `r ∣ p^k` — impossible for a prime `r` dividing `n`
  when `p ∤ n`.

  We state it for a primitive `M`-th root of unity (`M = p^k` in the
  application) in a domain `R`, an ideal `I` (the `𝔫`) with `n ∈ I`
  and `I ∩ ℤ ⊆ nℤ` (the halves of (7.7) that the argument uses; the
  `σ_n`-stability half is consumed elsewhere), and any divisor
  `r ∣ n` with `¬ r ∣ M` — for the application, `r` is a prime
  divisor of `n` and `p ∤ n` forces `r ≠ p`, hence `¬ r ∣ p^k`.
-/
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.Ideal.Operations

namespace Azurite

namespace CL

open Finset

/-- **Cohen–Lenstra Lemma (7.17)**: a power of a primitive `M`-th
root of unity congruent to `1` modulo `I ⊔ (r)` equals `1`, provided
`n ∈ I`, integers in `I` are multiples of `n`, `r ∣ n`, and
`¬ r ∣ M`. -/
theorem lemma_7_17 {R : Type _} [CommRing R] [IsDomain R] {M n r : ℕ}
    {ζ : R} (hζ : IsPrimitiveRoot ζ M) (hM : M ≠ 0) (hn0 : n ≠ 0)
    {I : Ideal R} (hnI : (n : R) ∈ I)
    (hIZ : ∀ a : ℕ, (a : R) ∈ I → n ∣ a)
    (hrn : r ∣ n) (hrM : ¬ r ∣ M)
    {e : ℕ} (he : ζ ^ e - 1 ∈ I ⊔ Ideal.span {(r : R)}) :
    ζ ^ e = 1 := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  -- reduce the exponent modulo the order
  have hmod : ζ ^ e = ζ ^ (e % (M' + 1)) := by
    conv_lhs => rw [← Nat.div_add_mod e (M' + 1), pow_add, pow_mul,
      hζ.pow_eq_one, one_pow, one_mul]
  rcases Nat.eq_zero_or_pos (e % (M' + 1)) with h0 | hpos
  · rw [hmod, h0, pow_zero]
  exfalso
  -- the nontrivial factor `1 − ζ^(e mod M)` lies in the ideal
  have hfac_mem : (1 : R) - ζ ^ (e % (M' + 1))
      ∈ I ⊔ Ideal.span {(r : R)} := by
    have := (I ⊔ Ideal.span {(r : R)}).neg_mem (hmod ▸ he)
    rwa [neg_sub] at this
  -- and it divides `M` in `R`
  have hfac_dvd : ((1 : R) - ζ ^ (e % (M' + 1))) ∣ ((M' + 1 : ℕ) : R) := by
    rw [show (((M' + 1 : ℕ)) : R) = (M' : R) + 1 by push_cast; ring,
      ← hζ.prod_one_sub_pow_eq_order]
    obtain ⟨d, hd⟩ : ∃ d, e % (M' + 1) = d + 1 :=
      ⟨e % (M' + 1) - 1, by omega⟩
    rw [hd]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by
      have : e % (M' + 1) < M' + 1 := Nat.mod_lt _ (by omega)
      omega))
  -- hence `M ∈ I ⊔ (r)`
  have hM_mem : (((M' + 1 : ℕ)) : R) ∈ I ⊔ Ideal.span {(r : R)} := by
    obtain ⟨c, hc⟩ := hfac_dvd
    rw [hc]
    exact Ideal.mul_mem_right _ _ hfac_mem
  -- decompose and multiply by `n/r`
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hM_mem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz
  have hkey : (((M' + 1) * (n / r) : ℕ) : R) ∈ I := by
    have hrn' : ((r : ℕ) : R) * ((n / r : ℕ) : R) = (n : R) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hrn]
    have hy' : y = (((M' + 1 : ℕ)) : R) - c * ((r : ℕ) : R) := by
      rw [← hyz, ← hc]; ring
    have hexp : (((M' + 1) * (n / r) : ℕ) : R)
        = y * ((n / r : ℕ) : R) + c * (n : R) := by
      rw [hy', ← hrn', Nat.cast_mul]
      ring
    rw [hexp]
    exact Ideal.add_mem I (Ideal.mul_mem_right _ I hy)
      (Ideal.mul_mem_left I c hnI)
  -- `(7.7)`: so `n ∣ M·(n/r)`, i.e. `r ∣ M`
  have hdvd : n ∣ (M' + 1) * (n / r) := hIZ _ hkey
  have hnr : n = r * (n / r) := (Nat.mul_div_cancel' hrn).symm
  have hnr0 : n / r ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnr
    exact hn0 hnr
  refine hrM ?_
  have : r * (n / r) ∣ (M' + 1) * (n / r) := hnr ▸ hdvd
  exact (Nat.mul_dvd_mul_iff_right (Nat.pos_of_ne_zero hnr0)).mp this

end CL

end Azurite

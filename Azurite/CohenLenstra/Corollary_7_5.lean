/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra Corollary (7.5): the Gauss-sum congruence raised to
  a group-ring exponent.**

  The paper raises Lemma (7.3) to an arbitrary power
  `β = Σ_x n_x·σ_x ∈ ℤ[G]` and weakens the modulus to any ideal `𝔫`
  of `B` containing `n`:

    `τ(χ)^((n−σ_n)β) ≡ χ(n)^(−nβ)  (mod 𝔫)`.

  In our Galois-free framework, `σ_x` acts on Gauss-sum congruences
  by replacing `χ` with `χ^x` (Lemma (7.3) holds for every character,
  so its `σ_x`-twist is just its instance at `χ^x`), and raising to
  `β` is taking the product over `x` with multiplicities `n_x`.  We
  state the corollary for a nonnegative exponent `β = Σ_{x ∈ S} ν(x)
  σ_x` — a general `β` splits as `β⁺ − β⁻`, and the congruence with
  the `β⁻`-parts cleared to the other side is the product of the two
  nonnegative instances, so no generality is lost where congruences
  (rather than unit identities) are consumed.  The ideal weakening is
  the separate statement `corollary_7_5_mem`.

  Of the paper's side conditions, (7.6) (`ζ_p^β ≠ 1`, equivalently
  `Σ_x n_x·x ≢ 0 mod p`) and (7.7) (`𝔫 ∩ ℤ = nℤ`, `σ_n[𝔫] = 𝔫`) are
  consumed by the converse results later (the paper investigates
  (7.7) in its §10); we defer them to their points of use.  Note that
  on `p^k`-th roots of unity the `β`-action is plain exponentiation
  by the integer `Σ_x n_x·x`, so (7.6) will materialize as a
  coprimality condition.
-/
import Azurite.CohenLenstra.Lemma_7_3
import Mathlib.Algebra.Ring.GeomSum

namespace Azurite

namespace CL

open Finset

/-- Congruences multiply: a common divisor of the differences
`f i − g i` divides the difference of the products. -/
theorem dvd_prod_sub_prod {ι R : Type _} [CommRing R] {c : R}
    {f g : ι → R} : ∀ {S : Finset ι}, (∀ i ∈ S, c ∣ f i - g i) →
      c ∣ ∏ i ∈ S, f i - ∏ i ∈ S, g i := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | insert a S haS ih =>
    intro h
    rw [Finset.prod_insert haS, Finset.prod_insert haS]
    have h1 : c ∣ f a - g a := h a (Finset.mem_insert_self a S)
    have h2 : c ∣ ∏ i ∈ S, f i - ∏ i ∈ S, g i :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hsplit : f a * ∏ i ∈ S, f i - g a * ∏ i ∈ S, g i
        = f a * (∏ i ∈ S, f i - ∏ i ∈ S, g i)
          + (f a - g a) * ∏ i ∈ S, g i := by
      ring
    rw [hsplit]
    exact dvd_add (Dvd.dvd.mul_left h2 _) (Dvd.dvd.mul_right h1 _)

/-- **Cohen–Lenstra Corollary (7.5)**, unit-free form: Lemma (7.3)
raised to the group-ring exponent `β = Σ_{x ∈ S} ν(x)·σ_x`.  For a
prime `n` not divisible by `q`,

`∏_x (χ^x(n)^n · τ(χ^x,ψ)^n)^ν(x) ≡ ∏_x τ((χ^x)^n, ψ)^ν(x)
  (mod nR)`.

The indices `x` need not be coprime to the order of `χ`. -/
theorem corollary_7_5 {R : Type _} [CommRing R] {q n : ℕ}
    [Fact q.Prime] (hn : n.Prime) (hqn : ¬ q ∣ n)
    (χ : MulChar (ZMod q) R) (ψ : AddChar (ZMod q) R)
    (S : Finset ℕ) (ν : ℕ → ℕ) :
    (n : R) ∣
      ∏ x ∈ S, ((χ ^ x) (n : ZMod q) ^ n * gaussSum (χ ^ x) ψ ^ n) ^ ν x
        - ∏ x ∈ S, gaussSum ((χ ^ x) ^ n) ψ ^ ν x :=
  dvd_prod_sub_prod fun x _ =>
    dvd_trans (lemma_7_3 hn hqn (χ ^ x) ψ)
      (sub_dvd_pow_sub_pow _ _ (ν x))

/-- **Corollary (7.5) modulo an ideal**: the same congruence holds in
any ideal of `R` containing `n` — the paper's "any ideal `𝔫` of `B`
with `n ∈ 𝔫`". -/
theorem corollary_7_5_mem {R : Type _} [CommRing R] {q n : ℕ}
    [Fact q.Prime] (hn : n.Prime) (hqn : ¬ q ∣ n)
    (χ : MulChar (ZMod q) R) (ψ : AddChar (ZMod q) R)
    (S : Finset ℕ) (ν : ℕ → ℕ) {I : Ideal R} (hnI : (n : R) ∈ I) :
    ∏ x ∈ S, ((χ ^ x) (n : ZMod q) ^ n * gaussSum (χ ^ x) ψ ^ n) ^ ν x
      - ∏ x ∈ S, gaussSum ((χ ^ x) ^ n) ψ ^ ν x ∈ I := by
  obtain ⟨d, hd⟩ := corollary_7_5 hn hqn χ ψ S ν
  rw [hd]
  exact I.mul_mem_right d hnI

end CL

end Azurite

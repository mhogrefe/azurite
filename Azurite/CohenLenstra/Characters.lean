/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra §6 (Characters): separation (6.1) and the generating
  set `Y_q` of (6.2).**

  A character mod a prime `q` is a homomorphism `(ℤ/q)^* → ℂ^*`,
  extended by zero — Mathlib's `MulChar (ZMod q) ℂ`.  The characters
  form a group `X_q` isomorphic (via evaluation at a chosen generator
  of the cyclic group `(ℤ/q)^*`) to the `(q−1)`-st roots of unity;
  the paper records two easy consequences:

  * **(6.1)** characters separate points: if `χ(x) = χ(y)` for every
    character `χ` mod `q`, then `x = y` in `(ℤ/q)^*`;
  * **(6.2)** writing `q − 1 = ∏ p^(k(p))`, any set `Y_q` containing,
    for each prime `p ∣ q − 1`, a character `χ_{p,q}` of order
    `p^(k(p))`, generates the whole group `X_q`.

  We prove (6.1) from Mathlib's multiplicative-character duality
  (`MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`), compute
  `|X_q| = q − 1` from the duality cardinality theorem, and derive the
  generation statement from a general fact valid in any finite group:
  a subset containing, for each prime `p`, an element of order
  `p^(v_p(|G|))` generates `G` (each such element forces
  `p^(v_p(|G|))` to divide the order of the generated subgroup, so
  Lagrange pins the subgroup to the whole group).  The characters
  `χ_{p,q}` themselves are the `MulChar.ofRootOfUnity` construction
  whose order lemmas are already in the Crandall–Pomerance §4.4
  development; here we add the existence statement over `ℂ` at the
  exact order `p^(v_p(q−1))`.
-/
import Azurite.CrandallPomerance.Chapter4.GaussSums
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Azurite

namespace CL

open Finset

/-! ### A generation criterion in finite groups -/

/-- If a subset of a finite group `G` contains, for each prime `p`
dividing `|G|`, an element of order `p^(v_p(|G|))`, then it generates
`G`: each such element forces `p^(v_p(|G|))` to divide the order of
the generated subgroup, so `|G|` divides it, and Lagrange finishes. -/
theorem closure_eq_top_of_forall_exists_orderOf {G : Type _} [Group G]
    [Finite G] {s : Set G}
    (h : ∀ p ∈ (Nat.card G).primeFactors,
      ∃ x ∈ s, orderOf x = p ^ (Nat.card G).factorization p) :
    Subgroup.closure s = ⊤ := by
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hH : Nat.card (Subgroup.closure s) ≠ 0 := Nat.card_pos.ne'
  refine Subgroup.eq_top_of_card_eq _ (Nat.dvd_antisymm
    (Subgroup.card_subgroup_dvd_card _) ?_)
  rw [← Nat.factorization_le_iff_dvd hG hH]
  refine (Finsupp.le_iff _ _).mpr fun p hp => ?_
  rw [Nat.support_factorization] at hp
  obtain ⟨x, hxs, hx⟩ := h p hp
  have hdvd : p ^ (Nat.card G).factorization p
      ∣ Nat.card (Subgroup.closure s) := by
    rw [← hx, ← Subgroup.orderOf_mk x (Subgroup.subset_closure hxs)]
    exact orderOf_dvd_natCard _
  exact (Nat.Prime.pow_dvd_iff_le_factorization
    (Nat.prime_of_mem_primeFactors hp) hH).mp hdvd

/-! ### The character group `X_q` -/

/-- `|X_q| = q − 1`: the group of characters mod `q` has the same
order as `(ℤ/q)^*`, by finite-abelian duality. -/
theorem card_mulChar_eq {q : ℕ} [Fact q.Prime] :
    Nat.card (MulChar (ZMod q) ℂ) = q - 1 := by
  rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity (ZMod q) ℂ,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime Fact.out]

/-! ### (6.1): characters separate points -/

/-- **Cohen–Lenstra (6.1)**: if `χ(x) = χ(y)` for every character `χ`
mod `q`, then `x = y` in `(ℤ/q)^*`. -/
theorem eq_6_1 {q : ℕ} [Fact q.Prime] {x y : (ZMod q)ˣ}
    (h : ∀ χ : MulChar (ZMod q) ℂ, χ x = χ y) : x = y := by
  by_contra hne
  have hxy : ((x * y⁻¹ : (ZMod q)ˣ) : ZMod q) ≠ 1 := fun h1 =>
    hne (mul_inv_eq_one.mp (Units.val_eq_one.mp h1))
  obtain ⟨χ, hχ⟩ :=
    MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod q) ℂ hxy
  apply hχ
  have hy : χ ↑y ≠ 0 := by
    rw [← MulChar.coe_equivToUnitHom]
    exact Units.ne_zero _
  have hval : ((x * y⁻¹ : (ZMod q)ˣ) : ZMod q) * ↑y = ↑x := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  have hmul : χ ↑(x * y⁻¹) * χ ↑y = χ ↑y := by
    rw [← map_mul χ, hval, h χ]
  calc χ ↑(x * y⁻¹) = χ ↑(x * y⁻¹) * χ ↑y * (χ ↑y)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hy, mul_one]
    _ = 1 := by rw [hmul, mul_inv_cancel₀ hy]

/-! ### (6.2): the set `Y_q` generates `X_q` -/

/-- **Existence of the `χ_{p,q}` over `ℂ`**: for each prime
`p ∣ q − 1` there is a character mod `q` of order exactly
`p^(v_p(q−1))` — send a generator of `(ℤ/q)^*` to a primitive
`p^(v_p(q−1))`-th root of unity. -/
theorem exists_mulChar_orderOf_eq {q p : ℕ} [Fact q.Prime]
    (hp : p ∈ (q - 1).primeFactors) :
    ∃ χ : MulChar (ZMod q) ℂ,
      orderOf χ = p ^ (q - 1).factorization p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  have hpk : (0 : ℕ) < p ^ (q - 1).factorization p :=
    pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have : NeZero ((p ^ (q - 1).factorization p : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr hpk.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ
    (p ^ (q - 1).factorization p)
  have hζu : IsPrimitiveRoot ((hζ₀.isUnit hpk.ne').unit)
      (p ^ (q - 1).factorization p) := hζ₀.isUnit_unit hpk.ne'
  have hmem : (hζ₀.isUnit hpk.ne').unit
      ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) ℂ :=
    CP.mem_rootsOfUnity_card_units_of_dvd hζu.pow_eq_one
      (Nat.ordProj_dvd _ _)
  exact ⟨MulChar.ofRootOfUnity hmem hg,
    CP.orderOf_ofRootOfUnity_eq hζu hmem hg⟩

/-- **Cohen–Lenstra (6.2)**: any set `Y_q` of characters mod `q`
containing, for each prime `p ∣ q − 1`, a character of order
`p^(v_p(q−1))` — such as the chosen `χ_{p,q}` of
`exists_mulChar_orderOf_eq` — generates the full character group
`X_q`. -/
theorem closure_eq_top_of_forall_orderOf {q : ℕ} [Fact q.Prime]
    {Y : Set (MulChar (ZMod q) ℂ)}
    (hY : ∀ p ∈ (q - 1).primeFactors,
      ∃ χ ∈ Y, orderOf χ = p ^ (q - 1).factorization p) :
    Subgroup.closure Y = ⊤ :=
  closure_eq_top_of_forall_exists_orderOf (by rwa [card_mulChar_eq])

end CL

end Azurite

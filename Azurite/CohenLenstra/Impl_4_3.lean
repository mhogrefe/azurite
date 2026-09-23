/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Implementation paper, Test (4.3): the `n + 1` side of the
  Lucas–Lehmer stage.**

  For `p ∣ n + 1` (not necessarily prime) the computations live in
  the quadratic ring `A = (ℤ/nℤ)[T]/(T² − uT − a)` (`QuadRing`
  below), elements written `x₀ + x₁α` with `α = T mod (T² − uT − a)`;
  `u, a` are fixed in (4.4) and the arithmetic of `A` is the
  subject of Remark (4.9).

  The test: find `x ∈ A` of *norm one* — `N(x₀ + x₁α) = x₀² + u
  x₀x₁ − a x₁²` (`quadNorm`; the product with the conjugate
  `x₀ + x₁(u − α)`, `mul_conj_eq_quadNorm`) — with
  `x^((n+1)/p) ≠ 1` (fifty trials, else the test *fails*; how to
  find such `x` is Remark (4.10)); verify `x^(n+1) = 1` (else `n`
  is composite); write `x^((n+1)/p) − 1 = x₀ + x₁α`, pick a
  coordinate `x_i ≠ 0` (one exists, since the element is nonzero),
  and accumulate `prod ← prod·x_i`; `prod = 0` convicts `n` as in
  (4.2) (`zmod_mul_ne_zero_of_prime`).

  The `n + 1` analogue of Fermat, proved here
  (`pow_card_succ_eq_quadNorm` / `quadNorm_one_pow_eq_one`): for
  *prime* `n` and a nonsquare discriminant `u² + 4a` (which the
  Jacobi symbol `((u² + 4a)/n) = −1` guarantees, `not_isSquare_disc`;
  the lemmas take `u, a ∈ ℤ/nℤ` so the computable rail applies them
  directly), `T² − uT − a` is irreducible `T² − uT − a` is
  irreducible (`quad_irreducible`) and `A = 𝔽_(n²)`; the Frobenius
  sends `α` to the other root `u − α` (`root_pow_card_eq_conj` —
  the `a = 1` argument of `xi_pow_eq_neg_one_of_prime`, which this
  generalizes: it cannot fix `α`, else `X^n − X` would have
  `n + 1` roots), hence `x^n = x̄` and `x^(n+1) = x·x̄ = N(x)`.
  So a norm-one `x` with `x^(n+1) ≠ 1` proves `n` composite.

  Deferred to (5.2): the *confinement* content of a passed test —
  that a unit coordinate `x_i` keeps `x^((n+1)/p) − 1` nonzero in
  `A ⊗ ℤ/r` for every prime `r ∣ n` (coordinate faithfulness over
  the field `ℤ/r`), giving `x` order divisible by the `p`-part of
  `n + 1` there and confining `r` modulo it.
-/
import Azurite.CohenLenstra.Impl_4_2
import Azurite.CohenLenstra.Procedure_11_5

namespace Azurite

namespace CL

open Polynomial

/-- **The quadratic ring of Test (4.3)**: `A = R[T]/(T² − uT − a)`. -/
abbrev QuadRing (R : Type _) [CommRing R] (u a : R) : Type _ :=
  AdjoinRoot (X ^ 2 - C u * X - C a : Polynomial R)

/-- **The norm form** `N(x₀ + x₁α) = x₀² + u·x₀x₁ − a·x₁²`. -/
def quadNorm {R : Type _} [CommRing R] (u a x₀ x₁ : R) : R :=
  x₀ ^ 2 + u * x₀ * x₁ - a * x₁ ^ 2

/-- The defining relation `α² = uα + a` in `QuadRing R u a`. -/
theorem quadRing_root_sq {R : Type _} [CommRing R] (u a : R) :
    (AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)) ^ 2
      = algebraMap R (QuadRing R u a) u
          * AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)
        + algebraMap R (QuadRing R u a) a := by
  have h0 : aeval (AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R))
      (X ^ 2 - C u * X - C a : Polynomial R) = 0 := by
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self
  simp only [map_sub, map_pow, map_mul, aeval_X, aeval_C] at h0
  linear_combination h0

/-- **Norm = product with the conjugate**: with `ᾱ = u − α`,
`(x₀ + x₁α)(x₀ + x₁ᾱ) = N(x₀ + x₁α)`. -/
theorem mul_conj_eq_quadNorm {R : Type _} [CommRing R] (u a x₀ x₁ : R) :
    (algebraMap R (QuadRing R u a) x₀
        + algebraMap R (QuadRing R u a) x₁
          * AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R))
      * (algebraMap R (QuadRing R u a) x₀
        + algebraMap R (QuadRing R u a) x₁
          * (algebraMap R (QuadRing R u a) u
            - AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial R)))
      = algebraMap R (QuadRing R u a) (quadNorm u a x₀ x₁) := by
  have hrel := quadRing_root_sq u a
  rw [quadNorm]
  simp only [map_sub, map_add, map_mul, map_pow]
  linear_combination (-(algebraMap R (QuadRing R u a) x₁) ^ 2) * hrel

/-- **The Jacobi-symbol form of the hypothesis**: `((u² + 4a)/n) = −1`
for prime `n` makes the discriminant a nonsquare mod `n`. -/
theorem not_isSquare_disc {n : ℕ} (hn : n.Prime) {u a : ℤ}
    (hJ : jacobiSym (u ^ 2 + 4 * a) n = -1) :
    ¬ IsSquare ((u : ZMod n) ^ 2 + 4 * (a : ZMod n)) := by
  have : Fact n.Prime := ⟨hn⟩
  have hleg : legendreSym n (u ^ 2 + 4 * a) = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    exact hJ
  have hnsq := (legendreSym.eq_neg_one_iff (p := n)).mp hleg
  have hcast : (((u ^ 2 + 4 * a : ℤ)) : ZMod n)
      = (u : ZMod n) ^ 2 + 4 * (a : ZMod n) := by
    push_cast
    rfl
  rwa [hcast] at hnsq

/-- **Irreducibility of `T² − uT − a` over `𝔽_n`** for a nonsquare
discriminant `u² + 4a` (the Jacobi-symbol form `((u² + 4a)/n) = −1`
gives this via `not_isSquare_disc`): there is no root, and a rootless
quadratic is irreducible. -/
theorem quad_irreducible {n : ℕ} (hn : n.Prime) {u a : ZMod n}
    (hns : ¬ IsSquare (u ^ 2 + 4 * a)) :
    Irreducible (X ^ 2 - C u * X - C a : Polynomial (ZMod n)) := by
  have : Fact n.Prime := ⟨hn⟩
  set f : Polynomial (ZMod n) := X ^ 2 - C u * X - C a with hf
  have hnoroot : ∀ c : ZMod n, ¬ (c ^ 2 - u * c - a = 0) := by
    intro c hc
    apply hns
    refine ⟨2 * c - u, ?_⟩
    linear_combination (-4 : ZMod n) * hc
  have hfrw : f = X ^ 2 - (C u * X + C a) := by
    rw [hf]
    ring
  have hfmonic : f.Monic := by
    rw [hfrw]
    have hlt : (1 : WithBot ℕ) < ((2 : ℕ) : WithBot ℕ) := by
      exact_mod_cast (by norm_num : (1 : ℕ) < 2)
    exact monic_X_pow_sub (lt_of_le_of_lt degree_linear_le hlt)
  have hfdeg : f.natDegree = 2 := by
    rw [hfrw, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt natDegree_linear_le (by norm_num)
  have hroots0 : f.roots = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro c hc
    rw [Polynomial.mem_roots hfmonic.ne_zero] at hc
    apply hnoroot c
    have he := hc
    rw [Polynomial.IsRoot, hf] at he
    simpa using he
  exact (hfmonic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by omega) (by omega)).mpr hroots0

/-- **The Frobenius swaps the roots**: for prime `n` and
a nonsquare discriminant, `α^n = u − α` in `A = 𝔽_(n²)`.  (The `a = 1`
case is the engine of `xi_pow_eq_neg_one_of_prime`.) -/
theorem root_pow_card_eq_conj {n : ℕ} (hn : n.Prime) {u a : ZMod n}
    (hns : ¬ IsSquare (u ^ 2 + 4 * a)) :
    (AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial (ZMod n))) ^ n
      = algebraMap (ZMod n) (QuadRing (ZMod n) u a) u
        - AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial (ZMod n)) := by
  have : Fact n.Prime := ⟨hn⟩
  have hn1 : 1 < n := hn.one_lt
  set f : Polynomial (ZMod n) := X ^ 2 - C u * X - C a with hf
  have hirr : Irreducible f := quad_irreducible hn hns
  have : Fact (Irreducible f) := ⟨hirr⟩
  have : CharP (AdjoinRoot f) n :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod n) (AdjoinRoot f)).injective n
  have hnoroot : ∀ c : ZMod n, ¬ (c ^ 2 - u * c - a = 0) := by
    intro c hc
    apply hns
    refine ⟨2 * c - u, ?_⟩
    linear_combination (-4 : ZMod n) * hc
  set ξ : AdjoinRoot f := AdjoinRoot.root f with hξ
  set uK : AdjoinRoot f := algebraMap (ZMod n) (AdjoinRoot f) u with huK
  set aK : AdjoinRoot f := algebraMap (ZMod n) (AdjoinRoot f) a with haK
  have hzero : ξ ^ 2 - uK * ξ - aK = 0 := by
    have h := quadRing_root_sq u a
    rw [← hξ, ← huK, ← haK] at h
    linear_combination h
  have hfrobfix : ∀ c : ZMod n,
      (algebraMap (ZMod n) (AdjoinRoot f) c) ^ n
        = algebraMap (ZMod n) (AdjoinRoot f) c := by
    intro c
    rw [← map_pow, ZMod.pow_card]
  have hξn : (ξ ^ n) ^ 2 - uK * ξ ^ n - aK = 0 := by
    have hφ := congrArg (frobenius (AdjoinRoot f) n) hzero
    rw [map_zero, map_sub, map_sub, map_mul] at hφ
    simp only [frobenius_def] at hφ
    rw [← pow_mul, mul_comm 2 n, pow_mul] at hφ
    have hUK : uK ^ n = uK := hfrobfix u
    have hAK : aK ^ n = aK := hfrobfix a
    rwa [hUK, hAK] at hφ
  have hswap : ξ ^ n = ξ ∨ ξ ^ n = uK - ξ := by
    have hfact : (ξ ^ n - ξ) * (ξ ^ n - (uK - ξ)) = 0 := by
      linear_combination hξn - hzero
    rcases mul_eq_zero.mp hfact with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hinj : Function.Injective (algebraMap (ZMod n) (AdjoinRoot f)) :=
    (algebraMap (ZMod n) (AdjoinRoot f)).injective
  have hnotfix : ξ ^ n ≠ ξ := by
    intro hfix
    have hgmonic : (X ^ n - X : Polynomial (AdjoinRoot f)).Monic := by
      refine monic_X_pow_sub ?_
      calc degree (X : Polynomial (AdjoinRoot f)) = 1 := degree_X
        _ < ((n : ℕ) : WithBot ℕ) := by
            exact_mod_cast (by omega : (1 : ℕ) < n)
    have hgdeg : (X ^ n - X : Polynomial (AdjoinRoot f)).natDegree
        = n := by
      rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
      rw [natDegree_X, natDegree_X_pow]
      omega
    have hξnotmem : ξ ∉ (Finset.univ : Finset (ZMod n)).image
        (algebraMap (ZMod n) (AdjoinRoot f)) := by
      intro hmem
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hmem
      apply hnoroot c
      have h1 : algebraMap (ZMod n) (AdjoinRoot f)
          (c ^ 2 - u * c - a) = 0 := by
        rw [map_sub, map_sub, map_pow, map_mul, hc, ← huK, ← haK]
        linear_combination hzero
      exact hinj (h1.trans (map_zero _).symm)
    have hcardS : (insert ξ ((Finset.univ : Finset (ZMod n)).image
        (algebraMap (ZMod n) (AdjoinRoot f)))).card = n + 1 := by
      rw [Finset.card_insert_of_notMem hξnotmem,
        Finset.card_image_of_injective _ hinj, Finset.card_univ,
        ZMod.card]
    have hsub : (insert ξ ((Finset.univ : Finset (ZMod n)).image
        (algebraMap (ZMod n) (AdjoinRoot f))))
        ⊆ (X ^ n - X : Polynomial (AdjoinRoot f)).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset,
        Polynomial.mem_roots hgmonic.ne_zero]
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, hfix, sub_self]
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
        rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, hfrobfix c, sub_self]
    have hle := Finset.card_le_card hsub
    have hle2 : (X ^ n - X : Polynomial (AdjoinRoot f)).roots.toFinset.card
        ≤ Multiset.card (X ^ n - X : Polynomial (AdjoinRoot f)).roots :=
      Multiset.toFinset_card_le _
    have hle3 := Polynomial.card_roots'
      (X ^ n - X : Polynomial (AdjoinRoot f))
    omega
  exact hswap.resolve_left hnotfix

/-- **The `n + 1` Fermat analogue of Test (4.3)**: for prime `n`
and a nonsquare discriminant, every `x = x₀ + x₁α ∈ A` satisfies
`x^(n+1) = N(x)` — Frobenius gives `x^n = x̄`, and `x·x̄ = N(x)`. -/
theorem pow_card_succ_eq_quadNorm {n : ℕ} (hn : n.Prime) {u a : ZMod n}
    (hns : ¬ IsSquare (u ^ 2 + 4 * a)) (x₀ x₁ : ZMod n) :
    (algebraMap (ZMod n) (QuadRing (ZMod n) u a) x₀
        + algebraMap (ZMod n) (QuadRing (ZMod n) u a) x₁
          * AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial (ZMod n))) ^ (n + 1)
      = algebraMap (ZMod n) (QuadRing (ZMod n) u a) (quadNorm u a x₀ x₁) := by
  have : Fact n.Prime := ⟨hn⟩
  set f : Polynomial (ZMod n) := X ^ 2 - C u * X - C a with hf
  have hirr : Irreducible f := quad_irreducible hn hns
  have : Fact (Irreducible f) := ⟨hirr⟩
  have : CharP (AdjoinRoot f) n :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod n) (AdjoinRoot f)).injective n
  set ξ : AdjoinRoot f := AdjoinRoot.root f with hξ
  have hconj : ξ ^ n = algebraMap (ZMod n) (AdjoinRoot f) u - ξ :=
    root_pow_card_eq_conj hn hns
  have hfrobfix : ∀ c : ZMod n,
      (algebraMap (ZMod n) (AdjoinRoot f) c) ^ n
        = algebraMap (ZMod n) (AdjoinRoot f) c := by
    intro c
    rw [← map_pow, ZMod.pow_card]
  have hxn : (algebraMap (ZMod n) (AdjoinRoot f) x₀
      + algebraMap (ZMod n) (AdjoinRoot f) x₁ * ξ) ^ n
      = algebraMap (ZMod n) (AdjoinRoot f) x₀
        + algebraMap (ZMod n) (AdjoinRoot f) x₁
          * (algebraMap (ZMod n) (AdjoinRoot f) u - ξ) := by
    rw [add_pow_char, mul_pow, hfrobfix, hfrobfix, hconj]
  rw [pow_succ, hxn, mul_comm]
  exact mul_conj_eq_quadNorm u a x₀ x₁

/-- **The (4.3) composite verdict**: for prime `n` and
a nonsquare discriminant, a norm-one `x ∈ A` has `x^(n+1) = 1`.
Contrapositive: a norm-one `x` with `x^(n+1) ≠ 1` proves `n`
composite. -/
theorem quadNorm_one_pow_eq_one {n : ℕ} (hn : n.Prime) {u a : ZMod n}
    (hns : ¬ IsSquare (u ^ 2 + 4 * a)) {x₀ x₁ : ZMod n}
    (hN : quadNorm u a x₀ x₁ = 1) :
    (algebraMap (ZMod n) (QuadRing (ZMod n) u a) x₀
        + algebraMap (ZMod n) (QuadRing (ZMod n) u a) x₁
          * AdjoinRoot.root (X ^ 2 - C u * X - C a : Polynomial (ZMod n))) ^ (n + 1)
      = 1 := by
  rw [pow_card_succ_eq_quadNorm hn hns, hN, map_one]

end CL

end Azurite

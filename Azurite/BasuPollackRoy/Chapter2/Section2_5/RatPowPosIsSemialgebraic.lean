/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.EvenRootIsSemialgebraic

/-! # Rational powers are semialgebraic on `(0, ∞)`

(Not in BPR.) For *any* rational `q` (possibly negative), the power function `x ↦ x^q` is
semialgebraic on `(0, ∞)`. Writing `q.num = a⁺ - a⁻` with `a⁺ = q.num.toNat` and
`a⁻ = (-q.num).toNat` (so `x^{q.num} = x^{a⁺}/x^{a⁻}` for `x > 0`), `x^q` is the unique
nonnegative `q.den`-th root of `x^{a⁺}/x^{a⁻}`, and its graph relation `y^b = x^{a⁺}/x^{a⁻}`
becomes the *polynomial* equation `y^b · x^{a⁻} = x^{a⁺}`. So the graph is semialgebraic.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- `x^q` for `x > 0` and rational `q` (any sign): the nonnegative `q.den`-th root of
`x^{q.num} = x^{a⁺}/x^{a⁻}`, valued in `Fin 1 → R`. -/
noncomputable def ratPowPos (q : ℚ) : (Fin 1 → R) → (Fin 1 → R) :=
  fun x _ => (exists_root_total q.den_pos.ne'
    ((x 0) ^ q.num.toNat / (x 0) ^ (-q.num).toNat)).choose

/-- Defining property of `ratPowPos`: for `x > 0`, `ratPowPos q x 0` is nonnegative and its
`q.den`-th power is `x^{a⁺}/x^{a⁻}`. -/
theorem ratPowPos_spec (q : ℚ) (x : Fin 1 → R) (hx : 0 < x 0) :
    0 ≤ ratPowPos q x 0 ∧
      (ratPowPos q x 0) ^ q.den = (x 0) ^ q.num.toNat / (x 0) ^ (-q.num).toNat :=
  (exists_root_total q.den_pos.ne' _).choose_spec
    (le_of_lt (div_pos (pow_pos hx _) (pow_pos hx _)))

/-- **The rational power `x ↦ x^q` (any rational `q`) is semialgebraic on `(0, ∞)`.** Its
graph is the intersection of `{x > 0}`, `{y ≥ 0}`, and the zero set of
`X_2^{q.den} · X_1^{a⁻} - X_1^{a⁺}`. -/
theorem ratPowPos_isSemialgebraicFunction (q : ℚ) :
    IsSemialgebraicFunction {x : Fin 1 → R | 0 < x 0} (ratPowPos (R := R) q) := by
  have hcidx : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hnidx : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  have hgraph : funGraph {x : Fin 1 → R | 0 < x 0} (ratPowPos q)
      = {z : Fin 2 → R | 0 < z 0 ∧ 0 ≤ z 1 ∧
          z 1 ^ q.den * z 0 ^ (-q.num).toNat = z 0 ^ q.num.toNat} := by
    ext z
    rw [mem_funGraph]
    constructor
    · rintro ⟨ha, hb⟩
      have ha0 : (0 : R) < z 0 := by
        have h : (0 : R) < (z ∘ Fin.castAdd 1) 0 := ha
        rwa [Function.comp_apply, hcidx] at h
      have hne : z 0 ^ (-q.num).toNat ≠ 0 := (pow_pos ha0 _).ne'
      have hspec := ratPowPos_spec q (z ∘ Fin.castAdd 1) (by rw [Function.comp_apply, hcidx]; exact ha0)
      rw [Function.comp_apply, hcidx] at hspec
      have hb0 : z 1 = ratPowPos q (z ∘ Fin.castAdd 1) 0 := by
        have h := congrFun hb 0
        rwa [Function.comp_apply, hnidx] at h
      have hz1d : z 1 ^ q.den = z 0 ^ q.num.toNat / z 0 ^ (-q.num).toNat := by
        rw [hb0]; exact hspec.2
      exact ⟨ha0, by rw [hb0]; exact hspec.1, (eq_div_iff hne).mp hz1d⟩
    · rintro ⟨hz0, hz1, hrel⟩
      have hne : z 0 ^ (-q.num).toNat ≠ 0 := (pow_pos hz0 _).ne'
      have hspec := ratPowPos_spec q (z ∘ Fin.castAdd 1) (by rw [Function.comp_apply, hcidx]; exact hz0)
      rw [Function.comp_apply, hcidx] at hspec
      have hz1d : z 1 ^ q.den = z 0 ^ q.num.toNat / z 0 ^ (-q.num).toNat :=
        (eq_div_iff hne).mpr hrel
      refine ⟨?_, ?_⟩
      · show (0 : R) < (z ∘ Fin.castAdd 1) 0
        rwa [Function.comp_apply, hcidx]
      · funext i; rw [Subsingleton.elim i 0]
        show (z ∘ Fin.natAdd 1) 0 = ratPowPos q (z ∘ Fin.castAdd 1) 0
        rw [Function.comp_apply, hnidx]
        exact (pow_left_inj₀ hz1 hspec.1 q.den_pos.ne').mp (by rw [hz1d, hspec.2])
  have hsemialg : IsSemialgebraicSet
      {z : Fin 2 → R | 0 < z 0 ∧ 0 ≤ z 1 ∧
        z 1 ^ q.den * z 0 ^ (-q.num).toNat = z 0 ^ q.num.toNat} := by
    have heq : {z : Fin 2 → R | 0 < z 0 ∧ 0 ≤ z 1 ∧
          z 1 ^ q.den * z 0 ^ (-q.num).toNat = z 0 ^ q.num.toNat}
        = {z | MvPolynomial.eval z (X 0) > 0} ∩ ({z | MvPolynomial.eval z (X 1) ≥ 0} ∩
            {z | MvPolynomial.eval z (X 1 ^ q.den * X 0 ^ (-q.num).toNat - X 0 ^ q.num.toNat)
              = 0}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, MvPolynomial.eval_X, map_sub, map_mul,
        MvPolynomial.eval_pow, sub_eq_zero, gt_iff_lt, ge_iff_le]
    rw [heq]
    exact (IsSemialgebraicSet.gtZero _).inter
      ((IsSemialgebraicSet.geZero _).inter (IsSemialgebraicSet.eqZero _))
  show IsSemialgebraicSet (funGraph {x : Fin 1 → R | 0 < x 0} (ratPowPos q))
  rw [hgraph]; exact hsemialg

end Azurite.BPR

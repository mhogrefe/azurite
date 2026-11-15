/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/Catalan/Energy/BarrierRationalSumNumerator.lean`),
licensed under the Apache License, Version 2.0.

     Copyright © 2026 OpenAI

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial

def barrierFractionProduct (fs : List (ℚ[X] × ℚ[X])) : ℚ[X] :=
  (fs.map Prod.snd).prod

def barrierFractionNumerator : List (ℚ[X] × ℚ[X]) → ℚ[X]
  | [] => 0
  | aq :: fs => aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs

def barrierFractionSum (fs : List (ℚ[X] × ℚ[X])) (x : ℝ) : ℝ :=
  (fs.map (fun aq : ℚ[X] × ℚ[X] =>
    aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x)).sum

theorem barrierFractionNumerator_eval (fs : List (ℚ[X] × ℚ[X])) (x : ℝ)
    (hprod : (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0) :
    (barrierFractionNumerator fs).eval₂ (Rat.castHom ℝ) x =
      (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x * barrierFractionSum fs x := by
  revert hprod
  induction fs with
  | nil =>
      intro _
      simp [barrierFractionNumerator, barrierFractionProduct, barrierFractionSum]
  | cons aq fs ih =>
      intro hprod
      have hh : aq.2.eval₂ (Rat.castHom ℝ) x *
          (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0 := by
        simpa only [barrierFractionProduct, List.map_cons, List.prod_cons, eval₂_mul]
          using hprod
      have hq : aq.2.eval₂ (Rat.castHom ℝ) x ≠ 0 := (mul_ne_zero_iff.mp hh).1
      have ht : (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0 :=
        (mul_ne_zero_iff.mp hh).2
      have hrec := ih ht
      change
        (aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs).eval₂
          (Rat.castHom ℝ) x =
        (aq.2 * barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x *
          (aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x +
            barrierFractionSum fs x)
      rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, hrec]
      field_simp [hq]

end InternalCatalan

end

end OAI

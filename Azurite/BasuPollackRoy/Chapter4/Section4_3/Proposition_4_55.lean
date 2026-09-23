/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_3.QuotientAlgebra
import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_50
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Trace.Basic

/-!
# BPR Proposition 4.55: the trace of the multiplication map as a sum over roots

For `P : K[X]` monic and `g : K[X]`, let `A = K[X]/(P)` (`AdjoinRoot P`) and let
`L_{mk g} : A → A` be multiplication by the class of `g`. Then, over an algebraically
closed `K`-algebra `C`,
`Tr(L_{mk g}) = ∑_{x ∈ aroots P (C)} g(x)`,
the sum being taken over the roots of `P` in `C` counted with multiplicity.

The proof reduces, by `K`-linearity, to the monomial case `g = X^j`, where the trace of
`(root P)^j` is the `j`-th Newton sum of `P` (Definition 4.7). That power-sum identity is
exactly `newtonSum_charpoly_eq_trace` (Proposition 4.50) applied to the companion-style
matrix `M = leftMulMatrix (powerBasis) (root P)`, whose characteristic polynomial is the
minimal polynomial of `root P`, namely `P` (since `P` is monic).
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial
open scoped Matrix

section

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **Part A (monomial case).** The trace of the `j`-th power of `root P` in `A = K[X]/(P)`
equals the `j`-th Newton sum of `P` (the sum of `j`-th powers of the roots of `P` in an
algebraically closed extension `C`). -/
theorem trace_gen_pow_eq_newtonSum (P : K[X]) (hP : P.Monic) (j : ℕ) :
    algebraMap K C (Algebra.trace K (AdjoinRoot P) (AdjoinRoot.root P ^ j))
      = newtonSum (C := C) P j := by
  classical
  have hP0 : P ≠ 0 := hP.ne_zero
  set pb := AdjoinRoot.powerBasis hP0 with hpb
  have : Module.Finite K (AdjoinRoot P) := pb.finite
  have : Module.Free K (AdjoinRoot P) := Module.Free.of_basis pb.basis
  set M := Algebra.leftMulMatrix pb.basis (AdjoinRoot.root P) with hM
  -- The charpoly of `M` is `P`.
  have hgen : pb.gen = AdjoinRoot.root P := AdjoinRoot.powerBasis_gen hP0
  have hcp : M.charpoly = P := by
    rw [hM, ← hgen, charpoly_leftMulMatrix pb, AdjoinRoot.minpoly_powerBasis_gen_of_monic hP]
  -- Trace of the `j`-th power equals trace of `M^j`.
  have htr : Algebra.trace K (AdjoinRoot P) (AdjoinRoot.root P ^ j)
      = Matrix.trace (M ^ j) := by
    rw [Algebra.trace_eq_matrix_trace pb.basis, map_pow, hM]
  rw [htr]
  -- Newton sum of `M.charpoly = P` is `algebraMap (trace (M^j))`.
  have hns := newtonSum_charpoly_eq_trace (C := C) M j
  rw [hcp] at hns
  rw [← hns]

/-- **Proposition 4.55.** For `P : K[X]` monic and `g : K[X]`, the trace of multiplication by
the class of `g` in `A = K[X]/(P)` equals the sum, over the roots `x` of `P` in an
algebraically closed extension `C` (counted with multiplicity), of the values `g(x)`. -/
theorem proposition_4_55 (P : K[X]) (hP : P.Monic) (g : K[X]) :
    algebraMap K C (Algebra.trace K (AdjoinRoot P) (AdjoinRoot.mk P g))
      = ((P.aroots C).map (fun x => Polynomial.aeval x g)).sum := by
  classical
  -- Both sides equal `∑ j ∈ range (g.natDegree+1), algebraMap (g.coeff j) * newtonSum P j`.
  -- LHS.
  have hlhs : algebraMap K C (Algebra.trace K (AdjoinRoot P) (AdjoinRoot.mk P g))
      = ∑ j ∈ Finset.range (g.natDegree + 1),
          algebraMap K C (g.coeff j) * newtonSum (C := C) P j := by
    rw [← AdjoinRoot.aeval_eq g, Polynomial.aeval_eq_sum_range (R := K)
      (AdjoinRoot.root P) (p := g)]
    rw [map_sum]
    simp_rw [map_smul]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_eq_mul, map_mul, trace_gen_pow_eq_newtonSum P hP j]
  -- RHS.
  have hrhs : ((P.aroots C).map (fun x => Polynomial.aeval x g)).sum
      = ∑ j ∈ Finset.range (g.natDegree + 1),
          algebraMap K C (g.coeff j) * newtonSum (C := C) P j := by
    have hpt : ∀ x : C, Polynomial.aeval x g
        = ∑ j ∈ Finset.range (g.natDegree + 1), algebraMap K C (g.coeff j) * x ^ j := by
      intro x
      rw [Polynomial.aeval_eq_sum_range (R := K) x (p := g)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Algebra.smul_def]
    simp_rw [hpt]
    rw [Multiset.sum_map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Multiset.sum_map_mul_left]
    rfl
  rw [hlhs, hrhs]

/-- **Proposition 4.55, stated via the trace `Tr` of the multiplication map `Lmul`.**
`Tr(L_{mk g}) = ∑_{x ∈ aroots P (C)} g(x)`. -/
theorem proposition_4_55_Tr_Lmul (P : K[X]) (hP : P.Monic) (g : K[X]) :
    algebraMap K C (Tr P (Lmul P (AdjoinRoot.mk P g)))
      = ((P.aroots C).map (fun x => Polynomial.aeval x g)).sum := by
  rw [← proposition_4_55 (C := C) P hP g, Algebra.trace_apply]
  rfl

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Trace

/-!
# BPR §4.3.2: the quotient algebra `A = K[X]/(P)` and the trace `Tr`

For `P ∈ K[X]` of degree `p`, the quotient ring `A = K[X]/(P)` (Mathlib's `AdjoinRoot P`)
is a `K`-vector space of dimension `p` with basis `1, X, …, X^{p-1}`: every `f ∈ K[X]` has
the representative `f %ₘ P` (its remainder in euclidean division by `P`) of degree `< p`,
and `f, g` are equal modulo `P` exactly when `P ∣ f - g`, so the remainder is well defined.
The power basis `1, X, …, X^{p-1}` is `AdjoinRoot.powerBasis`.

`Tr` denotes the usual trace of a `K`-linear endomorphism of `A` — the sum of the diagonal
entries of its matrix in any basis. This is Mathlib's `LinearMap.trace`, which is
basis-independent by construction.
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial

section QuotientAlgebra

variable {K : Type*} [Field K]

/-- **`A = K[X]/(P)` is a `K`-vector space of dimension `p = deg P`** (for `P ≠ 0`), with the
power basis `1, X, …, X^{p-1}` (`AdjoinRoot.powerBasis`). -/
theorem finrank_adjoinRoot (P : K[X]) (hP : P ≠ 0) :
    Module.finrank K (AdjoinRoot P) = P.natDegree :=
  (AdjoinRoot.powerBasis hP).finrank.trans (AdjoinRoot.powerBasis_dim hP)

/-- The `i`-th element of the power basis of `A = K[X]/(P)` is `X^i` (the class of `Xⁱ`),
`0 ≤ i < p`: the basis is `1, X, …, X^{p-1}`. -/
theorem adjoinRoot_powerBasis_apply (P : K[X]) (hP : P ≠ 0)
    (i : Fin (AdjoinRoot.powerBasis hP).dim) :
    (AdjoinRoot.powerBasis hP).basis i = AdjoinRoot.root P ^ (i : ℕ) := by
  rw [(AdjoinRoot.powerBasis hP).basis_eq_pow, AdjoinRoot.powerBasis_gen]

/-- **The remainder is a representative.** The class of `f` in `A = K[X]/(P)` equals the class
of its remainder `f %ₘ P` in euclidean division by `P` (a representative of degree `< p`). -/
theorem mk_modByMonic (P f : K[X]) :
    AdjoinRoot.mk P (f %ₘ P) = AdjoinRoot.mk P f := by
  rw [AdjoinRoot.mk_eq_mk]
  exact ⟨-(f /ₘ P), by linear_combination Polynomial.modByMonic_add_div f P⟩

/-- **Two polynomials are equal modulo `P` exactly when `P` divides their difference**; hence
if `f` and `g` are equal modulo `P` their remainders in euclidean division by `P` coincide,
so the representative above is well defined. -/
theorem mk_eq_mk_iff (P f g : K[X]) :
    AdjoinRoot.mk P f = AdjoinRoot.mk P g ↔ P ∣ f - g :=
  AdjoinRoot.mk_eq_mk

/-- **The trace `Tr` on `A = K[X]/(P)`**: the trace of a `K`-linear endomorphism of `A`, i.e.
the sum of the diagonal entries of its matrix in any basis. This is Mathlib's
`LinearMap.trace`, which is basis-independent by construction. -/
noncomputable abbrev Tr (P : K[X]) :
    (AdjoinRoot P →ₗ[K] AdjoinRoot P) →ₗ[K] K :=
  LinearMap.trace K (AdjoinRoot P)

/-- `Tr f` is the sum of the diagonal entries of the matrix of `f` in **any** basis of `A`
(basis-independence of the trace). -/
theorem Tr_eq_matrix_trace {ι : Type*} [DecidableEq ι] [Fintype ι] (P : K[X])
    (b : Module.Basis ι K (AdjoinRoot P)) (f : AdjoinRoot P →ₗ[K] AdjoinRoot P) :
    Tr P f = ((LinearMap.toMatrix b b) f).trace :=
  LinearMap.trace_eq_matrix_trace K b f

/-- **Notation 4.53 (multiplication map).** For `f ∈ A`, `Lmul P f : A → A` is the `K`-linear
map of multiplication by `f`, sending `g ∈ A` to `f g` — i.e. to the remainder of `f g` in
the euclidean division by `P` (Mathlib's `LinearMap.mulLeft`). -/
noncomputable def Lmul (P : K[X]) (f : AdjoinRoot P) : AdjoinRoot P →ₗ[K] AdjoinRoot P :=
  LinearMap.mulLeft K f

@[simp] theorem Lmul_apply (P : K[X]) (f g : AdjoinRoot P) : Lmul P f g = f * g :=
  LinearMap.mulLeft_apply K f g

/-- `L_f` sends the class of `b` to the class of the remainder of `a · b` in the euclidean
division by `P`, where `a` represents `f`. -/
theorem Lmul_mk (P a b : K[X]) :
    Lmul P (AdjoinRoot.mk P a) (AdjoinRoot.mk P b) = AdjoinRoot.mk P ((a * b) %ₘ P) := by
  rw [Lmul_apply, ← map_mul]
  exact (mk_modByMonic P (a * b)).symm

end QuotientAlgebra

end Azurite.BPR.Chapter4

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_5.TangentSpace

/-! # BPR §3.5 — the derivative of an `𝒮^∞` map between submanifolds

**Let `f : M → N` be an `𝒮^∞` map between submanifolds (`M ⊆ R^m` of dimension `m′`,
`N ⊆ R^n` of dimension `n′`), `x ∈ M`, with charts `ϕ` at `x` and `ψ` at `f(x)`. The
derivative of `f` at `x` is the map `df(x) : T_x(M) → T_{f(x)}(N)` defined by**
\[
  df(x)(v) = f(x) + dψ(0)\bigl(d(ψ^{-1} ∘ f ∘ ϕ)(0)\bigl(dϕ^{-1}(x)(v − x)\bigr)\bigr).
\]

In coordinates this is `f(x) + dψ · (dcomp · (dϕinv · (v − x)))` with the three Jacobian
matrices `dϕinv = dϕ⁻¹(x)`, `dcomp = d(ψ⁻¹ ∘ f ∘ ϕ)(0)`, `dψ = dψ(0)` (`mapDeriv`). BPR's
"clearly" remarks — that `ψ⁻¹ ∘ f ∘ ϕ` restricted to `R^{m′} × {0}` is an `𝒮^∞` map into
`R^{n′} × {0}`, and hence its derivative carries `R^{m′} × {0}` into `R^{n′} × {0}` —
are exactly what makes `df(x)` land in `T_{f(x)}(N)`; `mapDeriv_mem_tangentSpace` records
this, with those structural facts as hypotheses. -/

namespace Azurite.BPR

open MvPolynomial

variable {m n m' n' : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- **BPR definition (derivative of an `𝒮^∞` map).** The derivative `df(x)` as a map
`T_x(M) → T_{f(x)}(N)`, in coordinates:
`df(x)(v) = f(x) + dψ(0)(d(ψ⁻¹∘f∘ϕ)(0)(dϕ⁻¹(x)(v − x)))`. -/
def mapDeriv (x : Fin m → R) (fx : Fin n → R)
    (dϕinv : Matrix (Fin m) (Fin m) R) (dcomp : Matrix (Fin n) (Fin m) R)
    (dψ : Matrix (Fin n) (Fin n) R) (v : Fin m → R) : Fin n → R :=
  fx + dψ.mulVec (dcomp.mulVec (dϕinv.mulVec (v - x)))

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem mapDeriv_apply (x : Fin m → R) (fx : Fin n → R)
    (dϕinv : Matrix (Fin m) (Fin m) R) (dcomp : Matrix (Fin n) (Fin m) R)
    (dψ : Matrix (Fin n) (Fin n) R) (v : Fin m → R) :
    mapDeriv x fx dϕinv dcomp dψ v
      = fx + dψ.mulVec (dcomp.mulVec (dϕinv.mulVec (v - x))) := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **The derivative maps `T_x(M)` into `T_{f(x)}(N)`.** Given BPR's "clearly" facts —
`dϕ⁻¹(x)` carries the tangent direction `dϕ(0)(R^{m′} × {0})` into `R^{m′} × {0}`, and the
derivative `d(ψ⁻¹∘f∘ϕ)(0)` carries `R^{m′} × {0}` into `R^{n′} × {0}` — the derivative
`df(x)` (with `dψ = dψ(0)`) sends `T_x(M)` into `T_{f(x)}(N)`. -/
theorem mapDeriv_mem_tangentSpace {x : Fin m → R} {fx : Fin n → R}
    {dϕinv : Matrix (Fin m) (Fin m) R} {dcomp : Matrix (Fin n) (Fin m) R}
    {gϕ : Fin m → Fin m → (Fin m → R) → R} {gψ : Fin n → Fin n → (Fin n → R) → R}
    (hA : ∀ w ∈ tangentSpaceDir gϕ m', dϕinv.mulVec w ∈ coordSubmodule m m')
    (hB : ∀ w ∈ coordSubmodule m m', dcomp.mulVec w ∈ coordSubmodule n n')
    {v : Fin m → R} (hv : v ∈ tangentSpace x gϕ m') :
    mapDeriv x fx dϕinv dcomp (jacobianMatrix gψ 0) v ∈ tangentSpace fx gψ n' := by
  rw [mem_tangentSpace_iff] at hv
  rw [mem_tangentSpace_iff, mapDeriv_apply, add_sub_cancel_left, tangentSpaceDir]
  exact Submodule.mem_map.mpr
    ⟨_, hB _ (hA _ hv), by rw [Matrix.mulVecLin_apply]⟩

end Azurite.BPR

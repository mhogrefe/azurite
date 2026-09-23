/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_3.Proposition_4_46

/-!
# BPR Proposition 4.47: `Newt_k(M) = A_k A_kᵀ`

Let `M` be a symmetric `p × p` matrix. The matrix `A_k` is the `(p−k) × p(p+1)/2`
matrix whose `(i, (j,ℓ))`-entry is the `(j,ℓ)`-component of `M^{i-1}` in the orthonormal
basis `E` of `Sym(p)` (Proposition 4.46) — equivalently `⟨M^{i-1}, E_{j,ℓ}⟩`. Then the
trace–Hankel matrix factors as `Newt_k(M) = A_k A_kᵀ`, because the `(i,j)`-entry of the
product is the scalar product of `M^{i-1}` and `M^{j-1}` computed in the orthonormal
basis `E`, which equals `Tr(M^{i-1} M^{j-1}) = Tr(M^{i+j-2})`.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open Matrix

section

variable {p : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- The matrix `A_k`: rows indexed by `i` (the power `M^i`, 0-indexed), columns indexed
by the basis `E`. Its `(i, q)`-entry is the component of `M^i` along `E_q` in the
orthonormal basis `E`, i.e. `⟨M^i, E_q⟩ = Tr(M^i · E_q)`. -/
noncomputable def Ak (k : ℕ) (M : Matrix (Fin p) (Fin p) R) :
    Matrix (Fin (p - k)) (STri p) R :=
  Matrix.of fun i q => traceBilin (M ^ (i : ℕ)) (E q : Matrix (Fin p) (Fin p) R)

/-- Coordinate = inner product: the `q`-th coordinate of a symmetric matrix `S` in the
orthonormal basis `B` equals `⟨S, E q⟩`. -/
private lemma traceBilin_eq_repr
    (B : Module.Basis (STri p) R (symmMatrices (p := p) (R := R)))
    (hBE : ∀ a, ((B a : Matrix (Fin p) (Fin p) R)) = (E a : Matrix (Fin p) (Fin p) R))
    (horth : ∀ a b : STri p,
      traceBilin (E a : Matrix (Fin p) (Fin p) R) (E b : Matrix (Fin p) (Fin p) R)
        = if a = b then 1 else 0)
    (S : Matrix (Fin p) (Fin p) R) (hS : S.IsSymm) (q : STri p) :
    traceBilin S (E q : Matrix (Fin p) (Fin p) R) = B.repr ⟨S, hS⟩ q := by
  classical
  set c : STri p → R := fun r => B.repr ⟨S, hS⟩ r with hc
  -- `S = ∑ r, c r • E r`
  have hSsum : S = ∑ r, c r • (E r : Matrix (Fin p) (Fin p) R) := by
    have hrepr := B.sum_repr ⟨S, hS⟩
    have h2 := congrArg (Submodule.subtype _) hrepr
    rw [map_sum] at h2
    simp only [map_smul, Submodule.subtype_apply] at h2
    refine h2.symm.trans ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hBE r, hc]
  conv_lhs => rw [hSsum]
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, horth, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ q c, ite_eq_left (Finset.mem_univ q)]

/-- Parseval's identity: the inner product of two symmetric matrices equals the sum of
products of their coordinates in the orthonormal basis `E`. -/
private lemma parseval
    (B : Module.Basis (STri p) R (symmMatrices (p := p) (R := R)))
    (hBE : ∀ a, ((B a : Matrix (Fin p) (Fin p) R)) = (E a : Matrix (Fin p) (Fin p) R))
    (horth : ∀ a b : STri p,
      traceBilin (E a : Matrix (Fin p) (Fin p) R) (E b : Matrix (Fin p) (Fin p) R)
        = if a = b then 1 else 0)
    (S T : Matrix (Fin p) (Fin p) R) (hS : S.IsSymm) (_hT : T.IsSymm) :
    ∑ q, traceBilin S (E q : Matrix (Fin p) (Fin p) R)
        * traceBilin T (E q : Matrix (Fin p) (Fin p) R)
      = traceBilin S T := by
  classical
  set c : STri p → R := fun r => B.repr ⟨S, hS⟩ r with hc
  have hSsum : S = ∑ r, c r • (E r : Matrix (Fin p) (Fin p) R) := by
    have hrepr := B.sum_repr ⟨S, hS⟩
    have h2 := congrArg (Submodule.subtype _) hrepr
    rw [map_sum] at h2
    simp only [map_smul, Submodule.subtype_apply] at h2
    refine h2.symm.trans ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hBE r, hc]
  -- `⟨S, T⟩ = ∑ r, c r * ⟨E r, T⟩`
  have hST : traceBilin S T = ∑ r, c r * traceBilin (E r : Matrix (Fin p) (Fin p) R) T := by
    conv_lhs => rw [hSsum]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hST]
  refine Finset.sum_congr rfl fun r _ => ?_
  -- `c r = ⟨S, E r⟩` and `⟨E r, T⟩ = ⟨T, E r⟩`
  have hcr : c r = traceBilin S (E r : Matrix (Fin p) (Fin p) R) :=
    (traceBilin_eq_repr B hBE horth S hS r).symm
  rw [hcr, traceBilin_apply (E r), traceBilin_apply T, Matrix.trace_mul_comm]

/-- **Proposition 4.47.** The trace–Hankel matrix is the Gram matrix `A_k A_kᵀ`. -/
theorem proposition_4_47 (k : ℕ) (M : Matrix (Fin p) (Fin p) R) (hM : M.IsSymm) :
    traceNewtMatrix k M = Ak k M * (Ak k M)ᵀ := by
  classical
  obtain ⟨_, _, horth, B, hBE⟩ := (proposition_4_46 (p := p) (R := R))
  ext i i'
  rw [Matrix.mul_apply]
  simp only [Ak, Matrix.of_apply, Matrix.transpose_apply]
  rw [parseval B hBE horth (M ^ (i : ℕ)) (M ^ (i' : ℕ))
    (Matrix.IsSymm.pow hM _) (Matrix.IsSymm.pow hM _)]
  rw [traceBilin_apply, ← pow_add, traceNewtMatrix, Matrix.of_apply]

end

end Azurite.BPR.Chapter4

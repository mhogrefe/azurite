import Azurite.BasuPollackRoy.Chapter2.Section2_6.RiDecomp

/-!
# BPR §4.7: realification `Cᵏ ≅ R^{2k}`

Let `R` be a real closed field and `C = R[i] = Ri R`. To speak of semialgebraic subsets of `Cᵏ` we
identify `Cᵏ = (Fin k → C)` with `R^{2k} = (Fin (k + k) → R)` by recording the real parts in the
first `k` coordinates and the imaginary parts in the last `k`:
`z ↦ (Re z₀, …, Re z_{k-1}, Im z₀, …, Im z_{k-1})`. This `realEquiv` is the basis of the
semialgebraic-over-`C` framework: a subset of `Cᵏ` is semialgebraic when its image in `R^{2k}` is.

The re-block / im-block layout matches the `Fin.castAdd` / `Fin.natAdd` convention already used by the
semialgebraic-function graph machinery (`funGraph`).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- **Realification `Cᵏ ≅ R^{2k}`.** A complex tuple `z : Fin k → C` is sent to the real tuple whose
first `k` entries are the real parts `Re zⱼ` and whose last `k` entries are the imaginary parts
`Im zⱼ`. -/
noncomputable def realEquiv : (Fin k → Ri R) ≃ (Fin (k + k) → R) where
  toFun z := Fin.append (fun j => Ri.reL (z j)) (fun j => Ri.imL (z j))
  invFun w := fun j =>
    AdjoinRoot.of (X ^ 2 + 1 : R[X]) (w (Fin.castAdd k j))
      + AdjoinRoot.of (X ^ 2 + 1 : R[X]) (w (Fin.natAdd k j)) * Ri.i R
  left_inv z := by
    funext j
    simp only [Fin.append_left, Fin.append_right]
    exact Ri.of_reL_add_of_imL_mul_i (z j)
  right_inv w := by
    funext m
    refine Fin.addCases (fun j => ?_) (fun j => ?_) m
    · simp only [Fin.append_left, Ri.reL_lin]
    · simp only [Fin.append_right, Ri.imL_lin]

set_option linter.unusedSectionVars false in
/-- The real part of coordinate `j` sits in the `castAdd` (first) block. -/
@[simp] theorem realEquiv_apply_castAdd (z : Fin k → Ri R) (j : Fin k) :
    realEquiv z (Fin.castAdd k j) = Ri.reL (z j) := by
  simp only [realEquiv, Equiv.coe_fn_mk, Fin.append_left]

set_option linter.unusedSectionVars false in
/-- The imaginary part of coordinate `j` sits in the `natAdd` (last) block. -/
@[simp] theorem realEquiv_apply_natAdd (z : Fin k → Ri R) (j : Fin k) :
    realEquiv z (Fin.natAdd k j) = Ri.imL (z j) := by
  simp only [realEquiv, Equiv.coe_fn_mk, Fin.append_right]

set_option linter.unusedSectionVars false in
/-- The inverse reconstructs each complex coordinate from its real/imaginary parts. -/
theorem realEquiv_symm_apply (w : Fin (k + k) → R) (j : Fin k) :
    (realEquiv.symm w) j =
      AdjoinRoot.of (X ^ 2 + 1 : R[X]) (w (Fin.castAdd k j))
        + AdjoinRoot.of (X ^ 2 + 1 : R[X]) (w (Fin.natAdd k j)) * Ri.i R :=
  rfl

end Azurite.BPR.Chapter4

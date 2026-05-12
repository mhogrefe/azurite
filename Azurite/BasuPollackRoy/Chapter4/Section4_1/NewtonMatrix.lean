import Azurite.BasuPollackRoy.Chapter4.Section4_1.Definition_4_7
import Mathlib.Data.Matrix.Basic

/-!
# BPR Newton matrix

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

For a polynomial `P : K[X]` and `k : ℕ`, the **`(p-k)`-Newton matrix** of `P`
is the `k × k` matrix `Newt_{p-k}(P)` with entry `N_{i + j}` in row `i` and
column `j` (0-indexed), where `N_l = newtonSum P l` is the `l`-th Newton
sum. This is a Hankel matrix: entries are constant on each anti-diagonal.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **BPR Newton matrix** (unnumbered definition, §4.1). For `P : K[X]`
    and `k : ℕ`, `newtMat P k : Matrix (Fin k) (Fin k) C` is the `k × k`
    Hankel matrix with entry `N_{i + j} = newtonSum P (i + j)` at row `i`,
    column `j`. In BPR's notation this is `Newt_{p-k}(P)` (with subscript
    `p - k`, where `p` is the degree of `P`). -/
noncomputable def newtMat (P : K[X]) (k : ℕ) : Matrix (Fin k) (Fin k) C :=
  Matrix.of fun i j => newtonSum P (i.val + j.val)

end Azurite.BPR.Chapter4

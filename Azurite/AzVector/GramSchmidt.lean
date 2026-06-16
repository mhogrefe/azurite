import Azurite.AzVector.Dot
import Azurite.AzVector.Operations
import Azurite.AzVector.Parse
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement
import Mathlib.Algebra.Field.Basic

/-!
# Gram–Schmidt orthogonalization of a list of `AzVector`s

A computable Gram–Schmidt over a field `R` (intended `R = AzRat`, an ordered
field). Given a list of vectors `v₁, …, v_k`, it returns `w₁, …, w_k` where each
`wᵢ = vᵢ − ∑_{j<i} (vᵢ · wⱼ)/‖wⱼ‖² · wⱼ` — the projections onto the already
orthogonalized `wⱼ` subtracted off. The vectors are processed left to right with
a `List.foldl` accumulating the running orthogonal family.

Over an ordered field with linearly independent input, the output is a list of
linearly independent, pairwise orthogonal vectors (the computational counterpart
of BPR Proposition 4.41).
-/

namespace Azurite

variable {R : Type*} [Field R] {n : Nat}

/-- **Gram–Schmidt orthogonalization** of a list of `AzVector`s over a field.
Each input vector `v` is replaced by `v − ∑ⱼ (v · wⱼ)/‖wⱼ‖² · wⱼ`, the sum over
the already-orthogonalized vectors `wⱼ` accumulated so far. -/
def AzVector.gramSchmidt (vs : List (AzVector R n)) : List (AzVector R n) :=
  vs.foldl
    (fun acc v => acc ++ [acc.foldl (fun u w => u - ((v.dot w / w.normSq : R) • w)) v])
    []

/-! ### Sanity checks (over `AzRat`), via `parseStr`/`toString` -/

-- Parsing round-trips through `toString`.
#guard (AzVector.parseStr (R := AzRat) (n := 2) "[1, 1]").map toString = some "[1, 1]"

-- Gram–Schmidt of `(1, 1)` and `(2, 0)` yields the orthogonal `(1, 1)`, `(1, -1)`.
#guard
  (do
    let v₀ ← AzVector.parseStr (R := AzRat) (n := 2) "[1, 1]"
    let v₁ ← AzVector.parseStr (R := AzRat) (n := 2) "[2, 0]"
    pure ((AzVector.gramSchmidt [v₀, v₁]).map toString)) = some ["[1, 1]", "[1, -1]"]

-- A 3-vector example exercising the rational arithmetic.
#guard
  (do
    let v₀ ← AzVector.parseStr (R := AzRat) (n := 3) "[1, 1, 0]"
    let v₁ ← AzVector.parseStr (R := AzRat) (n := 3) "[1, 0, 1]"
    let v₂ ← AzVector.parseStr (R := AzRat) (n := 3) "[0, 1, 1]"
    pure ((AzVector.gramSchmidt [v₀, v₁, v₂]).map toString)) =
      some ["[1, 1, 0]", "[1/2, -1/2, 1]", "[-2/3, 2/3, 2/3]"]

end Azurite

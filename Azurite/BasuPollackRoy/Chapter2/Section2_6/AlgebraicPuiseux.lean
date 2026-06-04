import Azurite.BasuPollackRoy.Chapter2.Section2_6.RatFuncEmbedding
import Mathlib.FieldTheory.AlgebraicClosure

/-! # BPR §2.6 — algebraic Puiseux series `K⟨ε⟩`

For a field `K`, the rational function field `K(ε) = RatFunc K` embeds into the Puiseux series
`K⟨⟨ε⟩⟩ = PuiseuxSeries K` (`ratFuncToPuiseuxHom`). The *algebraic Puiseux series* `K⟨ε⟩` is the
subfield of `K⟨⟨ε⟩⟩` of those elements that are algebraic over `K(ε)` — i.e. that satisfy a
polynomial equation with coefficients in `K(ε)`. It is the relative algebraic closure of `K(ε)`
inside `K⟨⟨ε⟩⟩`. -/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- `K(ε) = RatFunc K` acts on `K⟨⟨ε⟩⟩ = PuiseuxSeries K` via the Laurent-expansion embedding
`ratFuncToPuiseuxHom`. -/
noncomputable instance ratFuncPuiseuxAlgebra : Algebra (RatFunc K) (PuiseuxSeries K) :=
  (ratFuncToPuiseuxHom K).toAlgebra

/-- **The algebraic Puiseux series `K⟨ε⟩`.** The subfield of `K⟨⟨ε⟩⟩` of elements algebraic over
`K(ε)`: the relative algebraic closure of `K(ε) = RatFunc K` inside `K⟨⟨ε⟩⟩ = PuiseuxSeries K`. -/
noncomputable def algebraicPuiseux (K : Type*) [Field K] : Subfield (PuiseuxSeries K) :=
  (algebraicClosure (RatFunc K) (PuiseuxSeries K)).toSubfield

/-- An element is an algebraic Puiseux series exactly when it is algebraic over `K(ε)`. -/
@[simp] theorem mem_algebraicPuiseux {x : PuiseuxSeries K} :
    x ∈ algebraicPuiseux K ↔ IsAlgebraic (RatFunc K) x := by
  rw [algebraicPuiseux, IntermediateField.mem_toSubfield, mem_algebraicClosure_iff]

end Azurite.BPR

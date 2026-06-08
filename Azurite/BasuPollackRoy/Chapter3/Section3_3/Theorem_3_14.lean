import Azurite.BasuPollackRoy.Chapter3.Section3_3.Proposition_3_13
import Azurite.BasuPollackRoy.Chapter2.Section2_6.PuiseuxLimit

/-! # BPR §3.3 — Theorem 3.14: the germ field is `R⟨ε⟩`

The real closed field of germs of semialgebraic continuous functions at the right of the origin is
isomorphic, as an `R(ε)`-algebra, to the field of algebraic Puiseux series `R⟨ε⟩ = algebraicPuiseux R`.

Both are real closures of `R(ε)`: the germ field by Proposition 3.13, and `R⟨ε⟩` by Corollary 2.98
(real closed) together with its definition (algebraic over `R(ε)`) and the order-compatibility of the
Laurent-expansion embedding (`ratFuncToPuiseux_strictMono`). Uniqueness of the real closure then
gives the isomorphism. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **The order of `R(ε)` extends to `R⟨ε⟩`.** Every nonnegative element of `R(ε)` maps to a square
in the real closed field `R⟨ε⟩`, since the Laurent-expansion embedding is order-preserving. -/
theorem algebraicPuiseux_isSquare_of_nonneg (p : RatFunc R) (hp : 0 ≤ p) :
    IsSquare (algebraMap (RatFunc R) (algebraicPuiseux R) p) := by
  apply IsRealClosed.nonneg_iff_isSquare.mp
  rw [← Subtype.coe_le_coe]
  have hcoe : ((algebraMap (RatFunc R) (algebraicPuiseux R) p : algebraicPuiseux R) :
      PuiseuxSeries R) = ratFuncToPuiseux p := by
    show algebraMap (RatFunc R) (PuiseuxSeries R) p = ratFuncToPuiseux p
    rw [RingHom.algebraMap_toAlgebra, ratFuncToPuiseuxHom_apply]
  rw [ZeroMemClass.coe_zero, hcoe]
  calc (0 : PuiseuxSeries R) = ratFuncToPuiseux 0 := ratFuncToPuiseux_zero.symm
    _ ≤ ratFuncToPuiseux p := ratFuncToPuiseux_strictMono.monotone hp

/-- **BPR Theorem 3.14.** The real closed field of germs of semialgebraic continuous functions at the
right of the origin is `R(ε)`-isomorphic to the field of algebraic Puiseux series `R⟨ε⟩`.

`R⟨ε⟩` is real closed (Corollary 2.98), is algebraic over `R(ε)` (by definition, as the relative
algebraic closure of `R(ε)` in the Puiseux series), and its order extends that of `R(ε)`
(`algebraicPuiseux_isSquare_of_nonneg`); hence by Proposition 3.13 it is `R(ε)`-isomorphic to the
germ field. -/
theorem theorem_3_14 : Nonempty (SemialgGerm R ≃ₐ[RatFunc R] algebraicPuiseux R) := by
  haveI : Algebra.IsAlgebraic (RatFunc R) (algebraicPuiseux R) :=
    inferInstanceAs (Algebra.IsAlgebraic (RatFunc R)
      (algebraicClosure (RatFunc R) (PuiseuxSeries R)))
  exact proposition_3_13 inferInstance algebraicPuiseux_isSquare_of_nonneg

end Azurite.BPR

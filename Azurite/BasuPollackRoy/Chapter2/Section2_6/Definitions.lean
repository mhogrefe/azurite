import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.LaurentSeries

/-! # BPR §2.6 — Puiseux series: formal power series and Laurent series

BPR introduce, for a field `K` and a variable `ε`:

* the ring of **formal power series** `K[[ε]]` of series `∑_{i ≥ 0} aᵢ εⁱ` (`i ∈ ℕ`); and
* its field of quotients, the field of **formal Laurent series** `K((ε))` of series
  `∑_{i ≥ k} aᵢ εⁱ` (`k ∈ ℤ`).

Both are already in Mathlib. This file records the correspondence and the
field-of-fractions relationship so they can be referenced from the blueprint.

* `K[[ε]] = PowerSeries K` (Mathlib notation `K⟦X⟧`); the `i`-th coefficient `aᵢ` is
  `PowerSeries.coeff K i a`.
* `K((ε)) = LaurentSeries K` (Mathlib notation `K⸨X⸩`), implemented as `HahnSeries ℤ K`.
* `K((ε))` is the field of fractions of `K[[ε]]`: the Mathlib instance
  `IsFractionRing (PowerSeries K) (LaurentSeries K)`.
-/

namespace Azurite.BPR

/-- **BPR Exercise 2.18 (part 1).** `K((ε)) = LaurentSeries K` is a field. (It is the field of
fractions of the integral domain `K[[ε]]`; Mathlib provides the `Field` structure directly via
`HahnSeries`.) -/
theorem laurentSeries_isField (K : Type*) [Field K] : IsField (LaurentSeries K) :=
  Field.toIsField (LaurentSeries K)

/-- **BPR Exercise 2.18 (part 2).** The field of formal Laurent series `K((ε)) = LaurentSeries K`
is the field of quotients of the ring of formal power series `K[[ε]] = PowerSeries K`. -/
theorem laurentSeries_isFractionRing (K : Type*) [Field K] :
    IsFractionRing (PowerSeries K) (LaurentSeries K) :=
  inferInstance

end Azurite.BPR

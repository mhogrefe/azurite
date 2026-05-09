import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Ordering.Basic
import Mathlib.Tactic.Positivity

/-! # BPR Section 2.1 — Cones, proper cones, and the positive cone

**Definition (BPR p.36).** A *cone* of a field `F` is a subset `C ⊆ F`
satisfying:
1. `x ∈ C, y ∈ C ⇒ x + y ∈ C`
2. `x ∈ C, y ∈ C ⇒ x · y ∈ C`
3. `x ∈ F ⇒ x² ∈ C`

The cone `C` is *proper* if in addition `−1 ∉ C`.

**Mathlib correspondence.**
- BPR's "cone" is a `Subsemiring` that contains all squares.
  We define `IsCone` below as this predicate on a `Subsemiring`.
- BPR's "proper cone" is exactly Mathlib's `RingPreordering`
  (from `Mathlib.Algebra.Order.Ring.Ordering.Basic`):
  a `Subsemiring` containing all squares with `−1 ∉ C`.
- Mathlib's `RingCone` is *stronger* than a proper cone: it
  additionally requires `a ∈ C ∧ −a ∈ C → a = 0`, which
  corresponds to the cone inducing a *total* order.
- The *positive cone* `{x ∈ F | x ≥ 0}` of an ordered field is
  `RingCone.nonneg` from `Mathlib.Algebra.Order.Ring.Cone`.
-/

namespace Azurite.BPR

variable {F : Type*} [CommRing F]

/-- **BPR Definition (Cone).** A *cone* of a commutative ring `F` is a
    `Subsemiring` that contains all squares.
    This is weaker than Mathlib's `RingPreordering`, which additionally
    requires `−1 ∉ C`. -/
def IsCone (C : Subsemiring F) : Prop :=
  ∀ x : F, x ^ 2 ∈ C

/-- A cone is *proper* iff `−1 ∉ C`. A proper `IsCone` is exactly a
    `RingPreordering`. -/
def IsProperCone (C : Subsemiring F) : Prop :=
  IsCone C ∧ (-1 : F) ∉ C

/-- Every `RingPreordering` is a proper cone. -/
lemma RingPreordering.isProperCone (P : RingPreordering F) :
    IsProperCone P.toSubsemiring :=
  ⟨fun x => by
    have : IsSquare (x ^ 2) := ⟨x, sq x⟩
    exact P.mem_of_isSquare this,
   P.neg_one_notMem⟩

/-- A proper cone gives rise to a `RingPreordering`. -/
def IsProperCone.toRingPreordering {C : Subsemiring F} (hC : IsProperCone C) :
    RingPreordering F :=
  RingPreordering.mk' (↑C)
    (fun hx hy => C.add_mem hx hy)
    (fun hx hy => C.mul_mem hx hy)
    (fun x => by have := hC.1 x; rwa [sq] at this)
    hC.2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **BPR Remark.** The positive cone `{x ∈ F | x ≥ 0}` of an ordered field
    is a cone. This is `Subsemiring.nonneg` in Mathlib. -/
lemma isCone_nonneg : IsCone (Subsemiring.nonneg F) :=
  fun x => by simp [Subsemiring.mem_nonneg]; positivity

/-- The positive cone of an ordered field is proper. -/
lemma isProperCone_nonneg : IsProperCone (Subsemiring.nonneg F) :=
  ⟨isCone_nonneg, by simp [Subsemiring.mem_nonneg]⟩

end Azurite.BPR

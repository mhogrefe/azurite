import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# BPR §4.5: local rings

A *local ring* `B` is a (nontrivial) ring such that for every `a ∈ B`, either `a` is invertible
or `1 + a` is invertible. A field is always a local ring.

This is Mathlib's `IsLocalRing`, whose built-in characterization uses `1 - a`; the `1 + a` form of
BPR is recorded here (`isUnit_or_isUnit_one_add_self` and `isLocalRing_of_isUnit_or_isUnit_one_add_self`,
equivalent via `a ↦ -a`). That a field is a local ring is a Mathlib instance
(`field_isLocalRing`).
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [CommRing R]

/-- **BPR local-ring property (forward).** In a local ring, for every `a` either `a` or `1 + a`
is invertible. -/
theorem isUnit_or_isUnit_one_add_self [IsLocalRing R] (a : R) :
    IsUnit a ∨ IsUnit (1 + a) := by
  have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (-a)
  rwa [IsUnit.neg_iff, sub_neg_eq_add] at h

/-- **BPR Definition (local ring).** A nontrivial ring in which, for every `a`, either `a` or
`1 + a` is invertible, is a local ring. -/
theorem isLocalRing_of_isUnit_or_isUnit_one_add_self [Nontrivial R]
    (h : ∀ a : R, IsUnit a ∨ IsUnit (1 + a)) : IsLocalRing R :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    have h' := h (-a)
    rwa [IsUnit.neg_iff, ← sub_eq_add_neg] at h'

/-- **A field is always a local ring.** -/
theorem field_isLocalRing (K : Type*) [Field K] : IsLocalRing K := inferInstance

/-- **BPR Exercise 4.2.** A ring `B` is local if and only if it has a unique maximal (proper) ideal,
which is then the set of non-invertible elements. -/
theorem exercise_4_2 :
    IsLocalRing R ↔ ∃ I : Ideal R, I.IsMaximal ∧ (∀ J : Ideal R, J.IsMaximal → J = I)
      ∧ (↑I : Set R) = nonunits R := by
  constructor
  · intro _
    refine ⟨IsLocalRing.maximalIdeal R, IsLocalRing.maximalIdeal.isMaximal R,
      fun J hJ => IsLocalRing.eq_maximalIdeal hJ, ?_⟩
    ext x
    rw [SetLike.mem_coe]
    exact IsLocalRing.mem_maximalIdeal x
  · rintro ⟨I, hImax, huniq, -⟩
    exact IsLocalRing.of_unique_max_ideal ⟨I, hImax, huniq⟩

end Azurite.BPR.Chapter4

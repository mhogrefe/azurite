import Azurite.AzNat.Basic

namespace Azurite.AzNat

/-- Strip trailing zero limbs from an array. The resulting array's `back?`
    is `none` or `some v` for `v ≠ 0`. -/
def trimTrailingZeros (a : Array UInt64) : Array UInt64 :=
  if h : a.size = 0 then a
  else
    have h_idx : a.size - 1 < a.size :=
      Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one
    if a[a.size - 1] = 0 then
      trimTrailingZeros a.pop
    else
      a
  termination_by a.size
  decreasing_by simp [Array.size_pop]; omega

/-- `trimTrailingZeros` produces an array satisfying the `AzNat` invariant. -/
theorem back?_trimTrailingZeros (a : Array UInt64) :
    (trimTrailingZeros a).back? ≠ some 0 := by
  rw [trimTrailingZeros]
  by_cases h : a.size = 0
  · simp only [h, ↓reduceDIte]
    have h_nil : a.toList = [] := by
      have : a.toList.length = 0 := h
      exact List.length_eq_zero_iff.mp this
    rw [Array.back?_eq_none_iff.mpr (by cases a; simpa using h_nil)]
    simp
  · simp only [h, ↓reduceDIte]
    have h_idx : a.size - 1 < a.size :=
      Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one
    by_cases h_last : a[a.size - 1] = 0
    · rw [ite_eq_left h_last]
      exact back?_trimTrailingZeros a.pop
    · rw [ite_eq_right h_last]
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem h_idx]
      intro heq
      exact h_last (Option.some.inj heq)
  termination_by a.size
  decreasing_by simp [Array.size_pop]; omega

/-- Build an `AzNat` from an arbitrary array of limbs by stripping trailing
    zeros. -/
def ofLimbs (a : Array UInt64) : AzNat where
  limbs := trimTrailingZeros a
  last_ne_zero := back?_trimTrailingZeros a

end Azurite.AzNat

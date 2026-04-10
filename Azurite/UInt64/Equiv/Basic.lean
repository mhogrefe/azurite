import Mathlib.Data.UInt

/-- `UInt64` values are equal iff their `toNat` images are equal. -/
lemma UInt64.eq_of_toNat_eq {x y : UInt64} (h : x.toNat = y.toNat) : x = y := by
  have h2 : x.toBitVec = y.toBitVec := BitVec.eq_of_toNat_eq h
  cases x; cases y; simp at h2; subst h2; rfl

import Mathlib.Algebra.Polynomial.Basic
import Azurite.DensePoly.Basic
open Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

lemma toList_popWhile_eq_dropTrailingZeros (a : Array R) :
  (a.popWhile (· = 0)).toList = dropTrailingZeros a.toList := by
  dsimp [dropTrailingZeros]
  have h := List.popWhile_toArray (· = 0) a.toList
  have ht : a.toList.toArray = a := by simp
  rw [ht] at h
  rw [h]
  simp

def normalize_native (a : Array R) : Azurite.DensePoly R :=
  let orig := dropTrailingZeros a.toList
  let arr := a.popWhile (· = 0)
  ⟨arr, by
    intro h
    have h1 : arr.toList = orig := toList_popWhile_eq_dropTrailingZeros a
    have h2 : arr.toList.getLast? = arr.back? := by simp
    rw [← h2] at h
    rw [h1] at h
    have ht := dropTrailingZeros_last a.toList
    change orig = [] ∨ orig.getLast? ≠ some 0 at ht
    rcases ht with h_empty | h_not_zero
    · rw [h_empty] at h
      simp at h
    · exact h_not_zero h
  ⟩

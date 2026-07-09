/-
  FINITE exhaustive generators over the fixed-width unsigned integers
  `UInt8`, `UInt16`, `UInt32`, `UInt64` (Malachite's `exhaustive_unsigneds`).

  Each generator produces `0, 1, …, 2^width − 1` and then STOPS: positions at
  or beyond the cardinality yield `none`. This is the payoff of the
  `Option`-valued `ExhaustiveGenerator` design — a finite type is enumerated by
  a generator that eventually runs out, and `firstN` recovers the whole (finite)
  enumeration. The finite proof is factored once through
  `ExhaustiveGenerator.ofBoundedBij` with `f = UIntXX.ofNat` and
  `card = 2^width`.
-/
import Azurite.ExhaustiveGenerator.Basic

namespace Azurite

/-- Generic builder for the positive elements of a bounded unsigned type, in the
order `1, 2, …, MAX`. `bound = 2^w`, card `= bound - 1`, value `ofNat (n+1)`. -/
@[reducible] def positiveUnsignedGen {T : Type*} [Zero T] [LT T]
    (toNat : T → ℕ) (ofNat : ℕ → T) (bound : ℕ)
    (canon : ∀ n : ℕ, n < bound → toNat (ofNat n) = n)
    (ofNat_toNat : ∀ x : T, ofNat (toNat x) = x)
    (toNat_lt : ∀ x : T, toNat x < bound)
    (lt_iff : ∀ x y : T, x < y ↔ toNat x < toNat y)
    (zero_toNat : toNat (0 : T) = 0) :
    ExhaustiveGenerator {x : T // 0 < x} :=
  ExhaustiveGenerator.ofBoundedBijOn (bound - 1)
    (fun n h => ⟨ofNat (n + 1), by
      rw [lt_iff, zero_toNat, canon (n + 1) (by omega)]; omega⟩)
    (fun i j hi hj h => by
      have hv : ofNat (i + 1) = ofNat (j + 1) := congrArg Subtype.val h
      have h2 := congrArg toNat hv
      rw [canon (i + 1) (by omega), canon (j + 1) (by omega)] at h2
      omega)
    (fun t => by
      have h1 : 0 < toNat t.val := by have := t.2; rw [lt_iff, zero_toNat] at this; exact this
      have h2 : toNat t.val < bound := toNat_lt t.val
      refine ⟨toNat t.val - 1, by omega, ?_⟩
      apply Subtype.ext
      show ofNat (toNat t.val - 1 + 1) = t.val
      rw [show toNat t.val - 1 + 1 = toNat t.val from by omega, ofNat_toNat])

/-- Finite exhaustive generator for `UInt8`: `0, 1, …, 255`, then `none`. -/
instance uint8Gen : ExhaustiveGenerator UInt8 :=
  ExhaustiveGenerator.ofBoundedBij (2 ^ 8) UInt8.ofNat
    (fun i j hi hj h => by
      have := congrArg UInt8.toNat h
      rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at this
      omega)
    (fun t => ⟨t.toNat, UInt8.toNat_lt t, UInt8.ofNat_toNat⟩)

/-- Finite exhaustive generator for `UInt16`: `0, 1, …, 2^16 − 1`, then `none`. -/
instance uint16Gen : ExhaustiveGenerator UInt16 :=
  ExhaustiveGenerator.ofBoundedBij (2 ^ 16) UInt16.ofNat
    (fun i j hi hj h => by
      have := congrArg UInt16.toNat h
      rw [UInt16.toNat_ofNat', UInt16.toNat_ofNat'] at this
      omega)
    (fun t => ⟨t.toNat, UInt16.toNat_lt t, UInt16.ofNat_toNat⟩)

/-- Finite exhaustive generator for `UInt32`: `0, 1, …, 2^32 − 1`, then `none`. -/
instance uint32Gen : ExhaustiveGenerator UInt32 :=
  ExhaustiveGenerator.ofBoundedBij (2 ^ 32) UInt32.ofNat
    (fun i j hi hj h => by
      have := congrArg UInt32.toNat h
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat'] at this
      omega)
    (fun t => ⟨t.toNat, UInt32.toNat_lt t, UInt32.ofNat_toNat⟩)

/-- Finite exhaustive generator for `UInt64`: `0, 1, …, 2^64 − 1`, then `none`. -/
instance uint64Gen : ExhaustiveGenerator UInt64 :=
  ExhaustiveGenerator.ofBoundedBij (2 ^ 64) UInt64.ofNat
    (fun i j hi hj h => by
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat'] at this
      omega)
    (fun t => ⟨t.toNat, UInt64.toNat_lt t, UInt64.ofNat_toNat⟩)

instance : Contiguous UInt8 := ExhaustiveGenerator.contiguous_of_boundedBij uint8Gen rfl
instance : Contiguous UInt16 := ExhaustiveGenerator.contiguous_of_boundedBij uint16Gen rfl
instance : Contiguous UInt32 := ExhaustiveGenerator.contiguous_of_boundedBij uint32Gen rfl
instance : Contiguous UInt64 := ExhaustiveGenerator.contiguous_of_boundedBij uint64Gen rfl

-- The unsigned generators start `0, 1, 2, …`.
#guard ((ExhaustiveGenerator.firstN UInt8 10).map (·.toNat)) == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
#guard ((ExhaustiveGenerator.firstN UInt16 10).map (·.toNat)) == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
#guard ((ExhaustiveGenerator.firstN UInt32 10).map (·.toNat)) == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
#guard ((ExhaustiveGenerator.firstN UInt64 10).map (·.toNat)) == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

-- Finiteness: `UInt8` stops at its cardinality `256`, not at the requested `300`.
#guard (ExhaustiveGenerator.firstN UInt8 300).length == 256

/-! ### Positive unsigneds `1, 2, …, MAX` -/

instance positiveUInt8Gen : ExhaustiveGenerator {x : UInt8 // 0 < x} :=
  positiveUnsignedGen UInt8.toNat UInt8.ofNat (2 ^ 8)
    (fun _ h => by rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt8.ofNat_toNat) UInt8.toNat_lt (fun _ _ => UInt8.lt_iff_toNat_lt) rfl

instance positiveUInt16Gen : ExhaustiveGenerator {x : UInt16 // 0 < x} :=
  positiveUnsignedGen UInt16.toNat UInt16.ofNat (2 ^ 16)
    (fun _ h => by rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt16.ofNat_toNat) UInt16.toNat_lt (fun _ _ => UInt16.lt_iff_toNat_lt) rfl

instance positiveUInt32Gen : ExhaustiveGenerator {x : UInt32 // 0 < x} :=
  positiveUnsignedGen UInt32.toNat UInt32.ofNat (2 ^ 32)
    (fun _ h => by rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt32.ofNat_toNat) UInt32.toNat_lt (fun _ _ => UInt32.lt_iff_toNat_lt) rfl

instance positiveUInt64Gen : ExhaustiveGenerator {x : UInt64 // 0 < x} :=
  positiveUnsignedGen UInt64.toNat UInt64.ofNat (2 ^ 64)
    (fun _ h => by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt64.ofNat_toNat) UInt64.toNat_lt (fun _ _ => UInt64.lt_iff_toNat_lt) rfl

instance : Contiguous {x : UInt8 // 0 < x} :=
  ExhaustiveGenerator.contiguous_of_boundedBijOn positiveUInt8Gen rfl
instance : Contiguous {x : UInt16 // 0 < x} :=
  ExhaustiveGenerator.contiguous_of_boundedBijOn positiveUInt16Gen rfl
instance : Contiguous {x : UInt32 // 0 < x} :=
  ExhaustiveGenerator.contiguous_of_boundedBijOn positiveUInt32Gen rfl
instance : Contiguous {x : UInt64 // 0 < x} :=
  ExhaustiveGenerator.contiguous_of_boundedBijOn positiveUInt64Gen rfl

-- Positive unsigneds start `1, 2, …`; and stop at cardinality `2^w - 1`.
#guard ((ExhaustiveGenerator.firstN {x : UInt8 // 0 < x} 10).map (·.val.toNat)) ==
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#guard (ExhaustiveGenerator.firstN {x : UInt8 // 0 < x} 300).length == 255

end Azurite

/-
  Parametrized FINITE range generators over the fixed-width integers
  (Malachite `primitive_int_increasing_range` /
  `primitive_int_increasing_inclusive_range`).

  Given runtime bounds `a b`, each generator ascends `a, a+1, …` over the range
  subtype (`{x // a ≤ x ∧ x < b}` exclusive, `{x // a ≤ x ∧ x ≤ b}` inclusive)
  and STOPS. Card is `b − a` (`+1` inclusive). The EMPTY range `a ≥ b` needs no
  special case: card `= 0`, `gen ≡ none`, and surjectivity is vacuous (the
  subtype is empty — any inhabitant would force `a < b`).

  Four generic builders (signed via `toInt`, unsigned via `toNat`, ×
  exclusive/inclusive) do the proof once over an abstract `T`; each width is a
  one-line application, mirroring the Group-1 monotone builders in `Signeds.lean`.
-/
import Azurite.ExhaustiveGenerator.Count
import Mathlib.Data.List.Sort

namespace Azurite.ExhaustiveGenerator

variable {T : Type*}

/-- The list `[gen 0, …, gen (bound-1)]` (dropping `none`s) is duplicate-free:
distinct positions cannot generate the same value (`occurs_exactly_once`). -/
theorem nodup_range_filterMap_gen [ExhaustiveGenerator T] (bound : ℕ) :
    ((List.range bound).filterMap (gen (T := T))).Nodup :=
  List.Nodup.filterMap (fun _ _ t h1 h2 =>
    (occurs_exactly_once t).unique (Option.mem_def.mp h1) (Option.mem_def.mp h2)) List.nodup_range

/-- If the generator is exhausted by `bound` (`hnone`), that list contains every
value: each `t` is produced at its unique index, which is `< bound`. -/
theorem mem_range_filterMap_gen [ExhaustiveGenerator T] (bound : ℕ)
    (hnone : ∀ n, bound ≤ n → gen (T := T) n = none) (t : T) :
    t ∈ (List.range bound).filterMap (gen (T := T)) := by
  obtain ⟨n, hn, _⟩ := occurs_exactly_once t
  have hlt : n < bound := by
    by_contra h
    rw [hnone n (Nat.not_lt.mp h)] at hn
    exact absurd hn (by simp)
  exact List.mem_filterMap.mpr ⟨n, List.mem_range.mpr hlt, hn⟩

end Azurite.ExhaustiveGenerator

namespace Azurite

open ExhaustiveGenerator

/-! ### Generic builders -/

/-- Signed exclusive range `[a, b)`, ascending. Card `(toInt b - toInt a).toNat`,
value at `n` is `ofInt (toInt a + n)`. -/
@[reducible] def increasingRangeSignedGen {T : Type*} [LE T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (lt_iff : ∀ x y : T, x < y ↔ toInt x < toInt y)
    (le_iff : ∀ x y : T, x ≤ y ↔ toInt x ≤ toInt y)
    (a b : T) : ExhaustiveGenerator {x : T // a ≤ x ∧ x < b} :=
  ExhaustiveGenerator.ofBoundedBijOn (toInt b - toInt a).toNat
    (fun n h => ⟨ofInt (toInt a + (n : ℤ)), by
      have hb := toInt_lt b; have ha := le_toInt a
      have hc : toInt (ofInt (toInt a + (n : ℤ))) = toInt a + n := canon _ (by omega) (by omega)
      exact ⟨by rw [le_iff, hc]; omega, by rw [lt_iff, hc]; omega⟩⟩)
    (fun i j hi hj h => by
      have hv : ofInt (toInt a + (i : ℤ)) = ofInt (toInt a + (j : ℤ)) := congrArg Subtype.val h
      have h2 := congrArg toInt hv
      have hb := toInt_lt b; have ha := le_toInt a
      rw [canon _ (by omega) (by omega), canon _ (by omega) (by omega)] at h2; omega)
    (fun t => by
      have hla : toInt a ≤ toInt t.val := (le_iff a t.val).mp t.2.1
      have hlt : toInt t.val < toInt b := (lt_iff t.val b).mp t.2.2
      refine ⟨(toInt t.val - toInt a).toNat, by omega, ?_⟩
      apply Subtype.ext
      show ofInt (toInt a + ((toInt t.val - toInt a).toNat : ℤ)) = t.val
      rw [show toInt a + ((toInt t.val - toInt a).toNat : ℤ) = toInt t.val from by omega, ofInt_toInt])

/-- Signed inclusive range `[a, b]`, ascending. Card `(toInt b - toInt a + 1).toNat`. -/
@[reducible] def increasingInclusiveRangeSignedGen {T : Type*} [LE T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (le_iff : ∀ x y : T, x ≤ y ↔ toInt x ≤ toInt y)
    (a b : T) : ExhaustiveGenerator {x : T // a ≤ x ∧ x ≤ b} :=
  ExhaustiveGenerator.ofBoundedBijOn (toInt b - toInt a + 1).toNat
    (fun n h => ⟨ofInt (toInt a + (n : ℤ)), by
      have hb := toInt_lt b; have ha := le_toInt a
      have hc : toInt (ofInt (toInt a + (n : ℤ))) = toInt a + n := canon _ (by omega) (by omega)
      exact ⟨by rw [le_iff, hc]; omega, by rw [le_iff, hc]; omega⟩⟩)
    (fun i j hi hj h => by
      have hv : ofInt (toInt a + (i : ℤ)) = ofInt (toInt a + (j : ℤ)) := congrArg Subtype.val h
      have h2 := congrArg toInt hv
      have hb := toInt_lt b; have ha := le_toInt a
      rw [canon _ (by omega) (by omega), canon _ (by omega) (by omega)] at h2; omega)
    (fun t => by
      have hla : toInt a ≤ toInt t.val := (le_iff a t.val).mp t.2.1
      have hlb : toInt t.val ≤ toInt b := (le_iff t.val b).mp t.2.2
      refine ⟨(toInt t.val - toInt a).toNat, by omega, ?_⟩
      apply Subtype.ext
      show ofInt (toInt a + ((toInt t.val - toInt a).toNat : ℤ)) = t.val
      rw [show toInt a + ((toInt t.val - toInt a).toNat : ℤ) = toInt t.val from by omega, ofInt_toInt])

/-- Unsigned exclusive range `[a, b)`, ascending. Card `toNat b - toNat a`. -/
@[reducible] def increasingRangeUnsignedGen {T : Type*} [LE T] [LT T]
    (toNat : T → ℕ) (ofNat : ℕ → T) (bound : ℕ)
    (canon : ∀ n : ℕ, n < bound → toNat (ofNat n) = n)
    (ofNat_toNat : ∀ x : T, ofNat (toNat x) = x)
    (toNat_lt : ∀ x : T, toNat x < bound)
    (lt_iff : ∀ x y : T, x < y ↔ toNat x < toNat y)
    (le_iff : ∀ x y : T, x ≤ y ↔ toNat x ≤ toNat y)
    (a b : T) : ExhaustiveGenerator {x : T // a ≤ x ∧ x < b} :=
  ExhaustiveGenerator.ofBoundedBijOn (toNat b - toNat a)
    (fun n h => ⟨ofNat (toNat a + n), by
      have hb := toNat_lt b
      have hc : toNat (ofNat (toNat a + n)) = toNat a + n := canon _ (by omega)
      exact ⟨by rw [le_iff, hc]; omega, by rw [lt_iff, hc]; omega⟩⟩)
    (fun i j hi hj h => by
      have hv : ofNat (toNat a + i) = ofNat (toNat a + j) := congrArg Subtype.val h
      have h2 := congrArg toNat hv
      have hb := toNat_lt b
      rw [canon _ (by omega), canon _ (by omega)] at h2; omega)
    (fun t => by
      have hla : toNat a ≤ toNat t.val := (le_iff a t.val).mp t.2.1
      have hlt : toNat t.val < toNat b := (lt_iff t.val b).mp t.2.2
      refine ⟨toNat t.val - toNat a, by omega, ?_⟩
      apply Subtype.ext
      show ofNat (toNat a + (toNat t.val - toNat a)) = t.val
      rw [show toNat a + (toNat t.val - toNat a) = toNat t.val from by omega, ofNat_toNat])

/-- Unsigned inclusive range `[a, b]`, ascending. Card `toNat b + 1 - toNat a`
(the `+1` is applied BEFORE the `ℕ` subtraction so a reversed `a > b` range
correctly gives `0`, not `1`). -/
@[reducible] def increasingInclusiveRangeUnsignedGen {T : Type*} [LE T]
    (toNat : T → ℕ) (ofNat : ℕ → T) (bound : ℕ)
    (canon : ∀ n : ℕ, n < bound → toNat (ofNat n) = n)
    (ofNat_toNat : ∀ x : T, ofNat (toNat x) = x)
    (toNat_lt : ∀ x : T, toNat x < bound)
    (le_iff : ∀ x y : T, x ≤ y ↔ toNat x ≤ toNat y)
    (a b : T) : ExhaustiveGenerator {x : T // a ≤ x ∧ x ≤ b} :=
  ExhaustiveGenerator.ofBoundedBijOn (toNat b + 1 - toNat a)
    (fun n h => ⟨ofNat (toNat a + n), by
      have hb := toNat_lt b
      have hc : toNat (ofNat (toNat a + n)) = toNat a + n := canon _ (by omega)
      exact ⟨by rw [le_iff, hc]; omega, by rw [le_iff, hc]; omega⟩⟩)
    (fun i j hi hj h => by
      have hv : ofNat (toNat a + i) = ofNat (toNat a + j) := congrArg Subtype.val h
      have h2 := congrArg toNat hv
      have hb := toNat_lt b
      rw [canon _ (by omega), canon _ (by omega)] at h2; omega)
    (fun t => by
      have hla : toNat a ≤ toNat t.val := (le_iff a t.val).mp t.2.1
      have hlb : toNat t.val ≤ toNat b := (le_iff t.val b).mp t.2.2
      refine ⟨toNat t.val - toNat a, by omega, ?_⟩
      apply Subtype.ext
      show ofNat (toNat a + (toNat t.val - toNat a)) = t.val
      rw [show toNat a + (toNat t.val - toNat a) = toNat t.val from by omega, ofNat_toNat])

/-! ### Per-type wrappers, `Fintype` instances, and counts -/

@[reducible] def int8RangeGen (a b : Int8) :
    ExhaustiveGenerator ({x : Int8 // a ≤ x ∧ x < b}) :=
  increasingRangeSignedGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt
    (fun _ _ => Int8.lt_iff_toInt_lt) (fun _ _ => Int8.le_iff_toInt_le) a b

noncomputable instance instFintypeInt8Range (a b : Int8) : Fintype ({x : Int8 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (int8RangeGen a b) ((b.toInt - a.toInt).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int8RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `int8RangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem int8RangeGen_card (a b : Int8) :
    Fintype.card ({x : Int8 // a ≤ x ∧ x < b}) = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (int8RangeGen a b) _ ((b.toInt - a.toInt).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int8RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def int16RangeGen (a b : Int16) :
    ExhaustiveGenerator ({x : Int16 // a ≤ x ∧ x < b}) :=
  increasingRangeSignedGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt
    (fun _ _ => Int16.lt_iff_toInt_lt) (fun _ _ => Int16.le_iff_toInt_le) a b

noncomputable instance instFintypeInt16Range (a b : Int16) : Fintype ({x : Int16 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (int16RangeGen a b) ((b.toInt - a.toInt).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int16RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `int16RangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem int16RangeGen_card (a b : Int16) :
    Fintype.card ({x : Int16 // a ≤ x ∧ x < b}) = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (int16RangeGen a b) _ ((b.toInt - a.toInt).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int16RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def int32RangeGen (a b : Int32) :
    ExhaustiveGenerator ({x : Int32 // a ≤ x ∧ x < b}) :=
  increasingRangeSignedGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt
    (fun _ _ => Int32.lt_iff_toInt_lt) (fun _ _ => Int32.le_iff_toInt_le) a b

noncomputable instance instFintypeInt32Range (a b : Int32) : Fintype ({x : Int32 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (int32RangeGen a b) ((b.toInt - a.toInt).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int32RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `int32RangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem int32RangeGen_card (a b : Int32) :
    Fintype.card ({x : Int32 // a ≤ x ∧ x < b}) = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (int32RangeGen a b) _ ((b.toInt - a.toInt).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int32RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def int64RangeGen (a b : Int64) :
    ExhaustiveGenerator ({x : Int64 // a ≤ x ∧ x < b}) :=
  increasingRangeSignedGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt
    (fun _ _ => Int64.lt_iff_toInt_lt) (fun _ _ => Int64.le_iff_toInt_le) a b

noncomputable instance instFintypeInt64Range (a b : Int64) : Fintype ({x : Int64 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (int64RangeGen a b) ((b.toInt - a.toInt).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int64RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `int64RangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem int64RangeGen_card (a b : Int64) :
    Fintype.card ({x : Int64 // a ≤ x ∧ x < b}) = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (int64RangeGen a b) _ ((b.toInt - a.toInt).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int64RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def int8RangeInclusiveGen (a b : Int8) :
    ExhaustiveGenerator ({x : Int8 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeSignedGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt (fun _ _ => Int8.le_iff_toInt_le) a b

noncomputable instance instFintypeInt8RangeInclusive (a b : Int8) : Fintype ({x : Int8 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (int8RangeInclusiveGen a b) ((b.toInt - a.toInt + 1).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int8RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `int8RangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem int8RangeInclusiveGen_card (a b : Int8) :
    Fintype.card ({x : Int8 // a ≤ x ∧ x ≤ b}) = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (int8RangeInclusiveGen a b) _ ((b.toInt - a.toInt + 1).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int8RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def int16RangeInclusiveGen (a b : Int16) :
    ExhaustiveGenerator ({x : Int16 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeSignedGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt (fun _ _ => Int16.le_iff_toInt_le) a b

noncomputable instance instFintypeInt16RangeInclusive (a b : Int16) : Fintype ({x : Int16 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (int16RangeInclusiveGen a b) ((b.toInt - a.toInt + 1).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int16RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `int16RangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem int16RangeInclusiveGen_card (a b : Int16) :
    Fintype.card ({x : Int16 // a ≤ x ∧ x ≤ b}) = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (int16RangeInclusiveGen a b) _ ((b.toInt - a.toInt + 1).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int16RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def int32RangeInclusiveGen (a b : Int32) :
    ExhaustiveGenerator ({x : Int32 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeSignedGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt (fun _ _ => Int32.le_iff_toInt_le) a b

noncomputable instance instFintypeInt32RangeInclusive (a b : Int32) : Fintype ({x : Int32 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (int32RangeInclusiveGen a b) ((b.toInt - a.toInt + 1).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int32RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `int32RangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem int32RangeInclusiveGen_card (a b : Int32) :
    Fintype.card ({x : Int32 // a ≤ x ∧ x ≤ b}) = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (int32RangeInclusiveGen a b) _ ((b.toInt - a.toInt + 1).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int32RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def int64RangeInclusiveGen (a b : Int64) :
    ExhaustiveGenerator ({x : Int64 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeSignedGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt (fun _ _ => Int64.le_iff_toInt_le) a b

noncomputable instance instFintypeInt64RangeInclusive (a b : Int64) : Fintype ({x : Int64 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (int64RangeInclusiveGen a b) ((b.toInt - a.toInt + 1).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int64RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `int64RangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem int64RangeInclusiveGen_card (a b : Int64) :
    Fintype.card ({x : Int64 // a ≤ x ∧ x ≤ b}) = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (int64RangeInclusiveGen a b) _ ((b.toInt - a.toInt + 1).toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (int64RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def uint8RangeGen (a b : UInt8) :
    ExhaustiveGenerator ({x : UInt8 // a ≤ x ∧ x < b}) :=
  increasingRangeUnsignedGen UInt8.toNat UInt8.ofNat (2 ^ 8)
    (fun _ h => by rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt8.ofNat_toNat) UInt8.toNat_lt
    (fun _ _ => UInt8.lt_iff_toNat_lt) (fun _ _ => UInt8.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt8Range (a b : UInt8) : Fintype ({x : UInt8 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (uint8RangeGen a b) (b.toNat - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint8RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint8RangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem uint8RangeGen_card (a b : UInt8) :
    Fintype.card ({x : UInt8 // a ≤ x ∧ x < b}) = b.toNat - a.toNat :=
  @fintypeCard_eq _ (uint8RangeGen a b) _ (b.toNat - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint8RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def uint16RangeGen (a b : UInt16) :
    ExhaustiveGenerator ({x : UInt16 // a ≤ x ∧ x < b}) :=
  increasingRangeUnsignedGen UInt16.toNat UInt16.ofNat (2 ^ 16)
    (fun _ h => by rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt16.ofNat_toNat) UInt16.toNat_lt
    (fun _ _ => UInt16.lt_iff_toNat_lt) (fun _ _ => UInt16.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt16Range (a b : UInt16) : Fintype ({x : UInt16 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (uint16RangeGen a b) (b.toNat - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint16RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint16RangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem uint16RangeGen_card (a b : UInt16) :
    Fintype.card ({x : UInt16 // a ≤ x ∧ x < b}) = b.toNat - a.toNat :=
  @fintypeCard_eq _ (uint16RangeGen a b) _ (b.toNat - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint16RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def uint32RangeGen (a b : UInt32) :
    ExhaustiveGenerator ({x : UInt32 // a ≤ x ∧ x < b}) :=
  increasingRangeUnsignedGen UInt32.toNat UInt32.ofNat (2 ^ 32)
    (fun _ h => by rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt32.ofNat_toNat) UInt32.toNat_lt
    (fun _ _ => UInt32.lt_iff_toNat_lt) (fun _ _ => UInt32.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt32Range (a b : UInt32) : Fintype ({x : UInt32 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (uint32RangeGen a b) (b.toNat - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint32RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint32RangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem uint32RangeGen_card (a b : UInt32) :
    Fintype.card ({x : UInt32 // a ≤ x ∧ x < b}) = b.toNat - a.toNat :=
  @fintypeCard_eq _ (uint32RangeGen a b) _ (b.toNat - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint32RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def uint64RangeGen (a b : UInt64) :
    ExhaustiveGenerator ({x : UInt64 // a ≤ x ∧ x < b}) :=
  increasingRangeUnsignedGen UInt64.toNat UInt64.ofNat (2 ^ 64)
    (fun _ h => by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt64.ofNat_toNat) UInt64.toNat_lt
    (fun _ _ => UInt64.lt_iff_toNat_lt) (fun _ _ => UInt64.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt64Range (a b : UInt64) : Fintype ({x : UInt64 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (uint64RangeGen a b) (b.toNat - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint64RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint64RangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem uint64RangeGen_card (a b : UInt64) :
    Fintype.card ({x : UInt64 // a ≤ x ∧ x < b}) = b.toNat - a.toNat :=
  @fintypeCard_eq _ (uint64RangeGen a b) _ (b.toNat - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint64RangeGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def uint8RangeInclusiveGen (a b : UInt8) :
    ExhaustiveGenerator ({x : UInt8 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeUnsignedGen UInt8.toNat UInt8.ofNat (2 ^ 8)
    (fun _ h => by rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt8.ofNat_toNat) UInt8.toNat_lt (fun _ _ => UInt8.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt8RangeInclusive (a b : UInt8) : Fintype ({x : UInt8 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (uint8RangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint8RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint8RangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem uint8RangeInclusiveGen_card (a b : UInt8) :
    Fintype.card ({x : UInt8 // a ≤ x ∧ x ≤ b}) = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (uint8RangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint8RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def uint16RangeInclusiveGen (a b : UInt16) :
    ExhaustiveGenerator ({x : UInt16 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeUnsignedGen UInt16.toNat UInt16.ofNat (2 ^ 16)
    (fun _ h => by rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt16.ofNat_toNat) UInt16.toNat_lt (fun _ _ => UInt16.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt16RangeInclusive (a b : UInt16) : Fintype ({x : UInt16 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (uint16RangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint16RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint16RangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem uint16RangeInclusiveGen_card (a b : UInt16) :
    Fintype.card ({x : UInt16 // a ≤ x ∧ x ≤ b}) = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (uint16RangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint16RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def uint32RangeInclusiveGen (a b : UInt32) :
    ExhaustiveGenerator ({x : UInt32 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeUnsignedGen UInt32.toNat UInt32.ofNat (2 ^ 32)
    (fun _ h => by rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt32.ofNat_toNat) UInt32.toNat_lt (fun _ _ => UInt32.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt32RangeInclusive (a b : UInt32) : Fintype ({x : UInt32 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (uint32RangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint32RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint32RangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem uint32RangeInclusiveGen_card (a b : UInt32) :
    Fintype.card ({x : UInt32 // a ≤ x ∧ x ≤ b}) = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (uint32RangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint32RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

@[reducible] def uint64RangeInclusiveGen (a b : UInt64) :
    ExhaustiveGenerator ({x : UInt64 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeUnsignedGen UInt64.toNat UInt64.ofNat (2 ^ 64)
    (fun _ h => by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt64.ofNat_toNat) UInt64.toNat_lt (fun _ _ => UInt64.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt64RangeInclusive (a b : UInt64) : Fintype ({x : UInt64 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (uint64RangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint64RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-- `uint64RangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem uint64RangeInclusiveGen_card (a b : UInt64) :
    Fintype.card ({x : UInt64 // a ≤ x ∧ x ≤ b}) = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (uint64RangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (fun _ _ => dif_neg (by omega))
    (fun _ h => by rw [show @gen _ (uint64RangeInclusiveGen a b) _ = some _ from dif_pos (by omega)]; exact Option.some_ne_none _)

/-! ### Magnitude-ordered signed ranges

Malachite `exhaustive_signed_range` / `exhaustive_signed_inclusive_range`:
the SAME set as the ascending range, but enumerated by magnitude — sorted by the
key `(|x|, positive-first)` (`|x|` ascending; for equal `|x|`, the positive
value first). We realize this by `List.mergeSort`ing the ascending range list
by that key, then feeding it to `ofListNodup`; `Nodup`/completeness transfer
from the ascending list through `List.mergeSort_perm`. -/

/-- Magnitude-ordered signed exclusive range `[a, b)`. -/
@[reducible] def exhaustiveSignedRangeGen {T : Type*} [LE T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (lt_iff : ∀ x y : T, x < y ↔ toInt x < toInt y)
    (le_iff : ∀ x y : T, x ≤ y ↔ toInt x ≤ toInt y)
    (a b : T) : ExhaustiveGenerator {x : T // a ≤ x ∧ x < b} :=
  let base := increasingRangeSignedGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff a b
  let l := (List.range (toInt b - toInt a).toNat).filterMap (@gen _ base)
  let keyNat := fun (x : {v : T // a ≤ v ∧ v < b}) =>
    (toInt x.val).natAbs * 2 + (if 0 < toInt x.val then 0 else 1)
  ExhaustiveGenerator.ofListNodup (l.mergeSort (fun p q => decide (keyNat p ≤ keyNat q)))
    ((List.mergeSort_perm l _).nodup_iff.mpr (@nodup_range_filterMap_gen _ base (toInt b - toInt a).toNat))
    (fun t => (List.mergeSort_perm l _).mem_iff.mpr
      (@mem_range_filterMap_gen _ base (toInt b - toInt a).toNat (fun _ _ => dif_neg (by omega)) t))

/-- Magnitude-ordered signed inclusive range `[a, b]`. -/
@[reducible] def exhaustiveSignedRangeInclusiveGen {T : Type*} [LE T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (le_iff : ∀ x y : T, x ≤ y ↔ toInt x ≤ toInt y)
    (a b : T) : ExhaustiveGenerator {x : T // a ≤ x ∧ x ≤ b} :=
  let base := increasingInclusiveRangeSignedGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt le_iff a b
  let l := (List.range (toInt b - toInt a + 1).toNat).filterMap (@gen _ base)
  let keyNat := fun (x : {v : T // a ≤ v ∧ v ≤ b}) =>
    (toInt x.val).natAbs * 2 + (if 0 < toInt x.val then 0 else 1)
  ExhaustiveGenerator.ofListNodup (l.mergeSort (fun p q => decide (keyNat p ≤ keyNat q)))
    ((List.mergeSort_perm l _).nodup_iff.mpr (@nodup_range_filterMap_gen _ base (toInt b - toInt a + 1).toNat))
    (fun t => (List.mergeSort_perm l _).mem_iff.mpr
      (@mem_range_filterMap_gen _ base (toInt b - toInt a + 1).toNat (fun _ _ => dif_neg (by omega)) t))



@[reducible] def int8SignedRangeGen (a b : Int8) :
    ExhaustiveGenerator {x : Int8 // a ≤ x ∧ x < b} :=
  exhaustiveSignedRangeGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt
    (fun _ _ => Int8.lt_iff_toInt_lt) (fun _ _ => Int8.le_iff_toInt_le) a b

/-- `int8SignedRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements (same
set as the ascending `int8RangeGen`, so the count is reused). -/
theorem int8SignedRangeGen_card (a b : Int8) :
    Fintype.card {x : Int8 // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  int8RangeGen_card a b

@[reducible] def int16SignedRangeGen (a b : Int16) :
    ExhaustiveGenerator {x : Int16 // a ≤ x ∧ x < b} :=
  exhaustiveSignedRangeGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt
    (fun _ _ => Int16.lt_iff_toInt_lt) (fun _ _ => Int16.le_iff_toInt_le) a b

/-- `int16SignedRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements (same
set as the ascending `int16RangeGen`, so the count is reused). -/
theorem int16SignedRangeGen_card (a b : Int16) :
    Fintype.card {x : Int16 // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  int16RangeGen_card a b

@[reducible] def int32SignedRangeGen (a b : Int32) :
    ExhaustiveGenerator {x : Int32 // a ≤ x ∧ x < b} :=
  exhaustiveSignedRangeGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt
    (fun _ _ => Int32.lt_iff_toInt_lt) (fun _ _ => Int32.le_iff_toInt_le) a b

/-- `int32SignedRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements (same
set as the ascending `int32RangeGen`, so the count is reused). -/
theorem int32SignedRangeGen_card (a b : Int32) :
    Fintype.card {x : Int32 // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  int32RangeGen_card a b

@[reducible] def int64SignedRangeGen (a b : Int64) :
    ExhaustiveGenerator {x : Int64 // a ≤ x ∧ x < b} :=
  exhaustiveSignedRangeGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt
    (fun _ _ => Int64.lt_iff_toInt_lt) (fun _ _ => Int64.le_iff_toInt_le) a b

/-- `int64SignedRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements (same
set as the ascending `int64RangeGen`, so the count is reused). -/
theorem int64SignedRangeGen_card (a b : Int64) :
    Fintype.card {x : Int64 // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  int64RangeGen_card a b

@[reducible] def int8SignedRangeInclusiveGen (a b : Int8) :
    ExhaustiveGenerator {x : Int8 // a ≤ x ∧ x ≤ b} :=
  exhaustiveSignedRangeInclusiveGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt (fun _ _ => Int8.le_iff_toInt_le) a b

/-- `int8SignedRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat`
elements (count reused from the ascending `int8RangeInclusiveGen`). -/
theorem int8SignedRangeInclusiveGen_card (a b : Int8) :
    Fintype.card {x : Int8 // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  int8RangeInclusiveGen_card a b

@[reducible] def int16SignedRangeInclusiveGen (a b : Int16) :
    ExhaustiveGenerator {x : Int16 // a ≤ x ∧ x ≤ b} :=
  exhaustiveSignedRangeInclusiveGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt (fun _ _ => Int16.le_iff_toInt_le) a b

/-- `int16SignedRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat`
elements (count reused from the ascending `int16RangeInclusiveGen`). -/
theorem int16SignedRangeInclusiveGen_card (a b : Int16) :
    Fintype.card {x : Int16 // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  int16RangeInclusiveGen_card a b

@[reducible] def int32SignedRangeInclusiveGen (a b : Int32) :
    ExhaustiveGenerator {x : Int32 // a ≤ x ∧ x ≤ b} :=
  exhaustiveSignedRangeInclusiveGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt (fun _ _ => Int32.le_iff_toInt_le) a b

/-- `int32SignedRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat`
elements (count reused from the ascending `int32RangeInclusiveGen`). -/
theorem int32SignedRangeInclusiveGen_card (a b : Int32) :
    Fintype.card {x : Int32 // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  int32RangeInclusiveGen_card a b

@[reducible] def int64SignedRangeInclusiveGen (a b : Int64) :
    ExhaustiveGenerator {x : Int64 // a ≤ x ∧ x ≤ b} :=
  exhaustiveSignedRangeInclusiveGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt (fun _ _ => Int64.le_iff_toInt_le) a b

/-- `int64SignedRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat`
elements (count reused from the ascending `int64RangeInclusiveGen`). -/
theorem int64SignedRangeInclusiveGen_card (a b : Int64) :
    Fintype.card {x : Int64 // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  int64RangeInclusiveGen_card a b

/-! ### Guards -/

-- Concrete ranges (Malachite doctests).
#guard (@firstN _ (int8RangeGen (-2) 3) 10).map (·.val.toInt) = [-2, -1, 0, 1, 2]
#guard (@firstN _ (int8RangeInclusiveGen (-2) 3) 10).map (·.val.toInt) = [-2, -1, 0, 1, 2, 3]
#guard (@firstN _ (uint8RangeGen 3 7) 10).map (·.val.toNat) = [3, 4, 5, 6]
#guard (@firstN _ (uint8RangeInclusiveGen 3 7) 10).map (·.val.toNat) = [3, 4, 5, 6, 7]
-- Empty ranges: `a = b`, reversed `a > b`.
#guard (@firstN _ (int8RangeGen 5 5) 10).map (·.val.toInt) = []
#guard (@firstN _ (int8RangeGen 5 2) 10).map (·.val.toInt) = []
example : Fintype.card {x : Int8 // (5 : Int8) ≤ x ∧ x < 5} = 0 := by rw [int8RangeGen_card]; decide
example : Fintype.card {x : Int8 // (5 : Int8) ≤ x ∧ x < 2} = 0 := by rw [int8RangeGen_card]; decide

-- Magnitude-ordered ranges (Malachite doctests): key `(|x|, positive-first)`.
#guard (@firstN _ (int8SignedRangeGen (-5) 5) 20).map (·.val.toInt) =
  [0, 1, -1, 2, -2, 3, -3, 4, -4, -5]
#guard (@firstN _ (int8SignedRangeInclusiveGen (-5) 5) 20).map (·.val.toInt) =
  [0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5]
-- All-positive range stays ascending (all in the `NonNegative` case).
#guard (@firstN _ (int8SignedRangeGen 2 6) 20).map (·.val.toInt) = [2, 3, 4, 5]
-- All-negative range `[-6, -2)` = {-6,-5,-4,-3}: closest-to-0 first.
#guard (@firstN _ (int8SignedRangeGen (-6) (-2)) 20).map (·.val.toInt) = [-3, -4, -5, -6]
-- Empty range.
#guard (@firstN _ (int8SignedRangeGen 3 3) 20).map (·.val.toInt) = []

end Azurite

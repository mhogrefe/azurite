/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

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

  The magnitude-ordered signed ranges (bottom half of the file) use a CLOSED-FORM
  index formula (`magF`), so `gen n` is O(1) with no per-call materialization —
  see the `magF` doc comment for the phased shape. (An earlier version built the
  whole ascending list and `mergeSort`ed it by the magnitude key; that made
  `gen 0` Θ(N log N) and unusable on wide ranges.)

  Deviation from Malachite: where Malachite's range constructors `assert!(a <= b)`
  (and PANIC on a reversed range), every Azurite range generator is a TOTAL
  function — a reversed or degenerate range (`a ≥ b`) is simply the empty
  generator (card `0`, `gen ≡ none`), needing no precondition.
-/
import Azurite.ExhaustiveGenerator.Count

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

/-- Positions at or past the card `(toInt b - toInt a).toNat` are `none`. Exported
so callers (and the `Fintype`/`_card` layer below) reuse it rather than re-derive. -/
theorem increasingRangeSignedGen_gen_none {T : Type*} [LE T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff) (a b : T) (n : ℕ)
    (h : (toInt b - toInt a).toNat ≤ n) :
    @gen _ (increasingRangeSignedGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff a b) n = none :=
  dite_eq_right (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem increasingRangeSignedGen_gen_some {T : Type*} [LE T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff) (a b : T) (n : ℕ)
    (h : n < (toInt b - toInt a).toNat) :
    @gen _ (increasingRangeSignedGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff a b) n ≠ none := by
  rw [show @gen _ (increasingRangeSignedGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff a b) n = some _ from dite_eq_left (by omega)]
  exact Option.some_ne_none _

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

/-- Positions at or past the card `(toInt b - toInt a + 1).toNat` are `none`. -/
theorem increasingInclusiveRangeSignedGen_gen_none {T : Type*} [LE T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon ofInt_toInt toInt_lt le_toInt le_iff) (a b : T) (n : ℕ)
    (h : (toInt b - toInt a + 1).toNat ≤ n) :
    @gen _ (increasingInclusiveRangeSignedGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt le_iff a b) n = none :=
  dite_eq_right (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem increasingInclusiveRangeSignedGen_gen_some {T : Type*} [LE T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon ofInt_toInt toInt_lt le_toInt le_iff) (a b : T) (n : ℕ)
    (h : n < (toInt b - toInt a + 1).toNat) :
    @gen _ (increasingInclusiveRangeSignedGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt le_iff a b) n ≠ none := by
  rw [show @gen _ (increasingInclusiveRangeSignedGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt le_iff a b) n = some _ from dite_eq_left (by omega)]
  exact Option.some_ne_none _

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

/-- Positions at or past the card `toNat b - toNat a` are `none`. -/
theorem increasingRangeUnsignedGen_gen_none {T : Type*} [LE T] [LT T]
    (toNat : T → ℕ) (ofNat : ℕ → T) (bound : ℕ)
    (canon ofNat_toNat toNat_lt lt_iff le_iff) (a b : T) (n : ℕ)
    (h : toNat b - toNat a ≤ n) :
    @gen _ (increasingRangeUnsignedGen toNat ofNat bound canon ofNat_toNat toNat_lt lt_iff le_iff a b) n = none :=
  dite_eq_right (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem increasingRangeUnsignedGen_gen_some {T : Type*} [LE T] [LT T]
    (toNat : T → ℕ) (ofNat : ℕ → T) (bound : ℕ)
    (canon ofNat_toNat toNat_lt lt_iff le_iff) (a b : T) (n : ℕ)
    (h : n < toNat b - toNat a) :
    @gen _ (increasingRangeUnsignedGen toNat ofNat bound canon ofNat_toNat toNat_lt lt_iff le_iff a b) n ≠ none := by
  rw [show @gen _ (increasingRangeUnsignedGen toNat ofNat bound canon ofNat_toNat toNat_lt lt_iff le_iff a b) n = some _ from dite_eq_left (by omega)]
  exact Option.some_ne_none _

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

/-- Positions at or past the card `toNat b + 1 - toNat a` are `none`. -/
theorem increasingInclusiveRangeUnsignedGen_gen_none {T : Type*} [LE T]
    (toNat : T → ℕ) (ofNat : ℕ → T) (bound : ℕ)
    (canon ofNat_toNat toNat_lt le_iff) (a b : T) (n : ℕ)
    (h : toNat b + 1 - toNat a ≤ n) :
    @gen _ (increasingInclusiveRangeUnsignedGen toNat ofNat bound canon ofNat_toNat toNat_lt le_iff a b) n = none :=
  dite_eq_right (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem increasingInclusiveRangeUnsignedGen_gen_some {T : Type*} [LE T]
    (toNat : T → ℕ) (ofNat : ℕ → T) (bound : ℕ)
    (canon ofNat_toNat toNat_lt le_iff) (a b : T) (n : ℕ)
    (h : n < toNat b + 1 - toNat a) :
    @gen _ (increasingInclusiveRangeUnsignedGen toNat ofNat bound canon ofNat_toNat toNat_lt le_iff a b) n ≠ none := by
  rw [show @gen _ (increasingInclusiveRangeUnsignedGen toNat ofNat bound canon ofNat_toNat toNat_lt le_iff a b) n = some _ from dite_eq_left (by omega)]
  exact Option.some_ne_none _

/-! ### Per-type wrappers, `Fintype` instances, and counts -/

@[reducible] def int8RangeGen (a b : Int8) :
    ExhaustiveGenerator ({x : Int8 // a ≤ x ∧ x < b}) :=
  increasingRangeSignedGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt
    (fun _ _ => Int8.lt_iff_toInt_lt) (fun _ _ => Int8.le_iff_toInt_le) a b

noncomputable instance instFintypeInt8Range (a b : Int8) : Fintype ({x : Int8 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (int8RangeGen a b) ((b.toInt - a.toInt).toNat)
    (fun n hn => increasingRangeSignedGen_gen_none _ _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeSignedGen_gen_some _ _ _ _ _ _ _ _ _ a b n hn)

/-- `int8RangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem int8RangeGen_card (a b : Int8) :
    Fintype.card ({x : Int8 // a ≤ x ∧ x < b}) = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (int8RangeGen a b) _ ((b.toInt - a.toInt).toNat)
    (fun n hn => increasingRangeSignedGen_gen_none _ _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeSignedGen_gen_some _ _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def int16RangeGen (a b : Int16) :
    ExhaustiveGenerator ({x : Int16 // a ≤ x ∧ x < b}) :=
  increasingRangeSignedGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt
    (fun _ _ => Int16.lt_iff_toInt_lt) (fun _ _ => Int16.le_iff_toInt_le) a b

noncomputable instance instFintypeInt16Range (a b : Int16) : Fintype ({x : Int16 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (int16RangeGen a b) ((b.toInt - a.toInt).toNat)
    (fun n hn => increasingRangeSignedGen_gen_none _ _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeSignedGen_gen_some _ _ _ _ _ _ _ _ _ a b n hn)

/-- `int16RangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem int16RangeGen_card (a b : Int16) :
    Fintype.card ({x : Int16 // a ≤ x ∧ x < b}) = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (int16RangeGen a b) _ ((b.toInt - a.toInt).toNat)
    (fun n hn => increasingRangeSignedGen_gen_none _ _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeSignedGen_gen_some _ _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def int32RangeGen (a b : Int32) :
    ExhaustiveGenerator ({x : Int32 // a ≤ x ∧ x < b}) :=
  increasingRangeSignedGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt
    (fun _ _ => Int32.lt_iff_toInt_lt) (fun _ _ => Int32.le_iff_toInt_le) a b

noncomputable instance instFintypeInt32Range (a b : Int32) : Fintype ({x : Int32 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (int32RangeGen a b) ((b.toInt - a.toInt).toNat)
    (fun n hn => increasingRangeSignedGen_gen_none _ _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeSignedGen_gen_some _ _ _ _ _ _ _ _ _ a b n hn)

/-- `int32RangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem int32RangeGen_card (a b : Int32) :
    Fintype.card ({x : Int32 // a ≤ x ∧ x < b}) = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (int32RangeGen a b) _ ((b.toInt - a.toInt).toNat)
    (fun n hn => increasingRangeSignedGen_gen_none _ _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeSignedGen_gen_some _ _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def int64RangeGen (a b : Int64) :
    ExhaustiveGenerator ({x : Int64 // a ≤ x ∧ x < b}) :=
  increasingRangeSignedGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt
    (fun _ _ => Int64.lt_iff_toInt_lt) (fun _ _ => Int64.le_iff_toInt_le) a b

noncomputable instance instFintypeInt64Range (a b : Int64) : Fintype ({x : Int64 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (int64RangeGen a b) ((b.toInt - a.toInt).toNat)
    (fun n hn => increasingRangeSignedGen_gen_none _ _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeSignedGen_gen_some _ _ _ _ _ _ _ _ _ a b n hn)

/-- `int64RangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem int64RangeGen_card (a b : Int64) :
    Fintype.card ({x : Int64 // a ≤ x ∧ x < b}) = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (int64RangeGen a b) _ ((b.toInt - a.toInt).toNat)
    (fun n hn => increasingRangeSignedGen_gen_none _ _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeSignedGen_gen_some _ _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def int8RangeInclusiveGen (a b : Int8) :
    ExhaustiveGenerator ({x : Int8 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeSignedGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt (fun _ _ => Int8.le_iff_toInt_le) a b

noncomputable instance instFintypeInt8RangeInclusive (a b : Int8) : Fintype ({x : Int8 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (int8RangeInclusiveGen a b) ((b.toInt - a.toInt + 1).toNat)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

/-- `int8RangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem int8RangeInclusiveGen_card (a b : Int8) :
    Fintype.card ({x : Int8 // a ≤ x ∧ x ≤ b}) = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (int8RangeInclusiveGen a b) _ ((b.toInt - a.toInt + 1).toNat)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def int16RangeInclusiveGen (a b : Int16) :
    ExhaustiveGenerator ({x : Int16 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeSignedGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt (fun _ _ => Int16.le_iff_toInt_le) a b

noncomputable instance instFintypeInt16RangeInclusive (a b : Int16) : Fintype ({x : Int16 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (int16RangeInclusiveGen a b) ((b.toInt - a.toInt + 1).toNat)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

/-- `int16RangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem int16RangeInclusiveGen_card (a b : Int16) :
    Fintype.card ({x : Int16 // a ≤ x ∧ x ≤ b}) = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (int16RangeInclusiveGen a b) _ ((b.toInt - a.toInt + 1).toNat)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def int32RangeInclusiveGen (a b : Int32) :
    ExhaustiveGenerator ({x : Int32 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeSignedGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt (fun _ _ => Int32.le_iff_toInt_le) a b

noncomputable instance instFintypeInt32RangeInclusive (a b : Int32) : Fintype ({x : Int32 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (int32RangeInclusiveGen a b) ((b.toInt - a.toInt + 1).toNat)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

/-- `int32RangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem int32RangeInclusiveGen_card (a b : Int32) :
    Fintype.card ({x : Int32 // a ≤ x ∧ x ≤ b}) = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (int32RangeInclusiveGen a b) _ ((b.toInt - a.toInt + 1).toNat)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def int64RangeInclusiveGen (a b : Int64) :
    ExhaustiveGenerator ({x : Int64 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeSignedGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt (fun _ _ => Int64.le_iff_toInt_le) a b

noncomputable instance instFintypeInt64RangeInclusive (a b : Int64) : Fintype ({x : Int64 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (int64RangeInclusiveGen a b) ((b.toInt - a.toInt + 1).toNat)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

/-- `int64RangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem int64RangeInclusiveGen_card (a b : Int64) :
    Fintype.card ({x : Int64 // a ≤ x ∧ x ≤ b}) = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (int64RangeInclusiveGen a b) _ ((b.toInt - a.toInt + 1).toNat)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeSignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def uint8RangeGen (a b : UInt8) :
    ExhaustiveGenerator ({x : UInt8 // a ≤ x ∧ x < b}) :=
  increasingRangeUnsignedGen UInt8.toNat UInt8.ofNat (2 ^ 8)
    (fun _ h => by rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt8.ofNat_toNat) UInt8.toNat_lt
    (fun _ _ => UInt8.lt_iff_toNat_lt) (fun _ _ => UInt8.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt8Range (a b : UInt8) : Fintype ({x : UInt8 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (uint8RangeGen a b) (b.toNat - a.toNat)
    (fun n hn => increasingRangeUnsignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeUnsignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

/-- `uint8RangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem uint8RangeGen_card (a b : UInt8) :
    Fintype.card ({x : UInt8 // a ≤ x ∧ x < b}) = b.toNat - a.toNat :=
  @fintypeCard_eq _ (uint8RangeGen a b) _ (b.toNat - a.toNat)
    (fun n hn => increasingRangeUnsignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeUnsignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def uint16RangeGen (a b : UInt16) :
    ExhaustiveGenerator ({x : UInt16 // a ≤ x ∧ x < b}) :=
  increasingRangeUnsignedGen UInt16.toNat UInt16.ofNat (2 ^ 16)
    (fun _ h => by rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt16.ofNat_toNat) UInt16.toNat_lt
    (fun _ _ => UInt16.lt_iff_toNat_lt) (fun _ _ => UInt16.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt16Range (a b : UInt16) : Fintype ({x : UInt16 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (uint16RangeGen a b) (b.toNat - a.toNat)
    (fun n hn => increasingRangeUnsignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeUnsignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

/-- `uint16RangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem uint16RangeGen_card (a b : UInt16) :
    Fintype.card ({x : UInt16 // a ≤ x ∧ x < b}) = b.toNat - a.toNat :=
  @fintypeCard_eq _ (uint16RangeGen a b) _ (b.toNat - a.toNat)
    (fun n hn => increasingRangeUnsignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeUnsignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def uint32RangeGen (a b : UInt32) :
    ExhaustiveGenerator ({x : UInt32 // a ≤ x ∧ x < b}) :=
  increasingRangeUnsignedGen UInt32.toNat UInt32.ofNat (2 ^ 32)
    (fun _ h => by rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt32.ofNat_toNat) UInt32.toNat_lt
    (fun _ _ => UInt32.lt_iff_toNat_lt) (fun _ _ => UInt32.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt32Range (a b : UInt32) : Fintype ({x : UInt32 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (uint32RangeGen a b) (b.toNat - a.toNat)
    (fun n hn => increasingRangeUnsignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeUnsignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

/-- `uint32RangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem uint32RangeGen_card (a b : UInt32) :
    Fintype.card ({x : UInt32 // a ≤ x ∧ x < b}) = b.toNat - a.toNat :=
  @fintypeCard_eq _ (uint32RangeGen a b) _ (b.toNat - a.toNat)
    (fun n hn => increasingRangeUnsignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeUnsignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def uint64RangeGen (a b : UInt64) :
    ExhaustiveGenerator ({x : UInt64 // a ≤ x ∧ x < b}) :=
  increasingRangeUnsignedGen UInt64.toNat UInt64.ofNat (2 ^ 64)
    (fun _ h => by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt64.ofNat_toNat) UInt64.toNat_lt
    (fun _ _ => UInt64.lt_iff_toNat_lt) (fun _ _ => UInt64.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt64Range (a b : UInt64) : Fintype ({x : UInt64 // a ≤ x ∧ x < b}) :=
  @fintypeOfBounded _ (uint64RangeGen a b) (b.toNat - a.toNat)
    (fun n hn => increasingRangeUnsignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeUnsignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

/-- `uint64RangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem uint64RangeGen_card (a b : UInt64) :
    Fintype.card ({x : UInt64 // a ≤ x ∧ x < b}) = b.toNat - a.toNat :=
  @fintypeCard_eq _ (uint64RangeGen a b) _ (b.toNat - a.toNat)
    (fun n hn => increasingRangeUnsignedGen_gen_none _ _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingRangeUnsignedGen_gen_some _ _ _ _ _ _ _ _ a b n hn)

@[reducible] def uint8RangeInclusiveGen (a b : UInt8) :
    ExhaustiveGenerator ({x : UInt8 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeUnsignedGen UInt8.toNat UInt8.ofNat (2 ^ 8)
    (fun _ h => by rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt8.ofNat_toNat) UInt8.toNat_lt (fun _ _ => UInt8.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt8RangeInclusive (a b : UInt8) : Fintype ({x : UInt8 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (uint8RangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_none _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_some _ _ _ _ _ _ _ a b n hn)

/-- `uint8RangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem uint8RangeInclusiveGen_card (a b : UInt8) :
    Fintype.card ({x : UInt8 // a ≤ x ∧ x ≤ b}) = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (uint8RangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_none _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_some _ _ _ _ _ _ _ a b n hn)

@[reducible] def uint16RangeInclusiveGen (a b : UInt16) :
    ExhaustiveGenerator ({x : UInt16 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeUnsignedGen UInt16.toNat UInt16.ofNat (2 ^ 16)
    (fun _ h => by rw [UInt16.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt16.ofNat_toNat) UInt16.toNat_lt (fun _ _ => UInt16.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt16RangeInclusive (a b : UInt16) : Fintype ({x : UInt16 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (uint16RangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_none _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_some _ _ _ _ _ _ _ a b n hn)

/-- `uint16RangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem uint16RangeInclusiveGen_card (a b : UInt16) :
    Fintype.card ({x : UInt16 // a ≤ x ∧ x ≤ b}) = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (uint16RangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_none _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_some _ _ _ _ _ _ _ a b n hn)

@[reducible] def uint32RangeInclusiveGen (a b : UInt32) :
    ExhaustiveGenerator ({x : UInt32 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeUnsignedGen UInt32.toNat UInt32.ofNat (2 ^ 32)
    (fun _ h => by rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt32.ofNat_toNat) UInt32.toNat_lt (fun _ _ => UInt32.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt32RangeInclusive (a b : UInt32) : Fintype ({x : UInt32 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (uint32RangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_none _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_some _ _ _ _ _ _ _ a b n hn)

/-- `uint32RangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem uint32RangeInclusiveGen_card (a b : UInt32) :
    Fintype.card ({x : UInt32 // a ≤ x ∧ x ≤ b}) = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (uint32RangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_none _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_some _ _ _ _ _ _ _ a b n hn)

@[reducible] def uint64RangeInclusiveGen (a b : UInt64) :
    ExhaustiveGenerator ({x : UInt64 // a ≤ x ∧ x ≤ b}) :=
  increasingInclusiveRangeUnsignedGen UInt64.toNat UInt64.ofNat (2 ^ 64)
    (fun _ h => by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
    (fun _ => UInt64.ofNat_toNat) UInt64.toNat_lt (fun _ _ => UInt64.le_iff_toNat_le) a b

noncomputable instance instFintypeUInt64RangeInclusive (a b : UInt64) : Fintype ({x : UInt64 // a ≤ x ∧ x ≤ b}) :=
  @fintypeOfBounded _ (uint64RangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_none _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_some _ _ _ _ _ _ _ a b n hn)

/-- `uint64RangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem uint64RangeInclusiveGen_card (a b : UInt64) :
    Fintype.card ({x : UInt64 // a ≤ x ∧ x ≤ b}) = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (uint64RangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_none _ _ _ _ _ _ _ a b n hn)
    (fun n hn => increasingInclusiveRangeUnsignedGen_gen_some _ _ _ _ _ _ _ a b n hn)

/-! ### Magnitude-ordered signed ranges

Malachite `exhaustive_signed_range` / `exhaustive_signed_inclusive_range`:
the SAME set as the ascending range, but enumerated by magnitude — ordered by the
key `(|x|, positive-first)` (`|x|` ascending; for equal `|x|`, the positive value
first). Rather than materialize and sort the whole range (Θ(N log N) at `gen 0`,
O(n) per later query), we use the CLOSED-FORM index formula `magF` below, so
`gen n` is O(1). It is the finite two-sided analogue of the infinite-ray `toInfF`
in `AzRanges.lean`; the injectivity/surjectivity proofs share `toInfF`'s
phase/parity `split_ifs <;> omega` shape. -/

/-- Magnitude-order value formula for the finite integer range `[a, b)`
(`ℤ`-valued; use `b + 1` for the inclusive variant). By phase:

* `0 ≤ a` (all-nonneg): plain ascending `a, a+1, …`;
* `b ≤ 0` (all-nonpos): descending toward `a` — `b-1, b-2, …, a` (closest to `0`
  first);
* straddling `a < 0 < b`: the leading `0`, then interleaved `+1, -1, +2, -2, …`
  up to `m := min (b-1) (-a)` pairs, then the LONGER side continues linearly
  (positives `k - m` if `b-1 > -a`, else negatives `-(k - m)`).

`magF_mem` bounds it in `[a, b)`, and `magF_inj`/`magF_surj` make `n ↦ magF a b n`
a bijection of `{0, …, (b-a).toNat - 1}` onto `[a, b) ∩ ℤ`. -/
def magF (a b : ℤ) (n : ℕ) : ℤ :=
  if 0 ≤ a then a + (n : ℤ)
  else if b ≤ 0 then (b - 1) - (n : ℤ)
  else if n = 0 then 0
    else if (n : ℤ) ≤ 2 * min (b - 1) (-a) then
      (if n % 2 = 1 then ((n : ℤ) + 1) / 2 else -((n : ℤ) / 2))
    else if (b - 1) > (-a) then (n : ℤ) - min (b - 1) (-a)
    else -((n : ℤ) - min (b - 1) (-a))

/-- Every emitted value lies in `[a, b)` (for `n` below the card `b - a`). -/
theorem magF_mem {a b : ℤ} {n : ℕ} (h : (n : ℤ) < b - a) :
    a ≤ magF a b n ∧ magF a b n < b := by
  unfold magF; split_ifs <;> omega

/-- The formula is injective: distinct indices land on distinct values (phase and
parity are disjoint across the branches). -/
theorem magF_inj {a b : ℤ} {i j : ℕ} (h : magF a b i = magF a b j) : i = j := by
  unfold magF at h; split_ifs at h <;> omega

/-- Every target `x ∈ [a, b)` is hit at an explicit in-range index (mirrors
`toInfF_surj`: `x` in the interleave uses `2x-1`/`-2x`, in the tail `x ± m`). -/
theorem magF_surj {a b : ℤ} {x : ℤ} (hax : a ≤ x) (hxb : x < b) :
    ∃ n : ℕ, (n : ℤ) < b - a ∧ magF a b n = x := by
  by_cases ha : 0 ≤ a
  · exact ⟨(x - a).toNat, by omega, by unfold magF; rw [ite_eq_left ha]; omega⟩
  · by_cases hb : b ≤ 0
    · exact ⟨(b - 1 - x).toNat, by omega, by unfold magF; rw [ite_eq_right ha, ite_eq_left hb]; omega⟩
    · rcases lt_trichotomy x 0 with hneg | hzero | hpos
      · by_cases hle : -x ≤ min (b - 1) (-a)
        · exact ⟨(-2 * x).toNat, by omega, by
            unfold magF; rw [ite_eq_right ha, ite_eq_right hb]; split_ifs <;> omega⟩
        · exact ⟨(-x + min (b - 1) (-a)).toNat, by omega, by
            unfold magF; rw [ite_eq_right ha, ite_eq_right hb]; split_ifs <;> omega⟩
      · exact ⟨0, by omega, by unfold magF; rw [ite_eq_right ha, ite_eq_right hb]; simp [hzero]⟩
      · by_cases hle : x ≤ min (b - 1) (-a)
        · exact ⟨(2 * x - 1).toNat, by omega, by
            unfold magF; rw [ite_eq_right ha, ite_eq_right hb]; split_ifs <;> omega⟩
        · exact ⟨(x + min (b - 1) (-a)).toNat, by omega, by
            unfold magF; rw [ite_eq_right ha, ite_eq_right hb]; split_ifs <;> omega⟩

/-- Magnitude-ordered signed exclusive range `[a, b)`, closed-form: `gen n =
some ⟨ofInt (magF (toInt a) (toInt b) n), _⟩` (O(1) per index, no sort). -/
@[reducible] def exhaustiveSignedRangeGen {T : Type*} [LE T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (lt_iff : ∀ x y : T, x < y ↔ toInt x < toInt y)
    (le_iff : ∀ x y : T, x ≤ y ↔ toInt x ≤ toInt y)
    (a b : T) : ExhaustiveGenerator {x : T // a ≤ x ∧ x < b} :=
  ExhaustiveGenerator.ofBoundedBijOn (toInt b - toInt a).toNat
    (fun n h => ⟨ofInt (magF (toInt a) (toInt b) n), by
      have hb := toInt_lt b; have ha := le_toInt a
      obtain ⟨hm1, hm2⟩ := magF_mem (a := toInt a) (b := toInt b) (n := n) (by omega)
      have hc : toInt (ofInt (magF (toInt a) (toInt b) n)) = magF (toInt a) (toInt b) n :=
        canon _ (by omega) (by omega)
      exact ⟨by rw [le_iff, hc]; omega, by rw [lt_iff, hc]; omega⟩⟩)
    (fun i j hi hj h => by
      have hv : ofInt (magF (toInt a) (toInt b) i) = ofInt (magF (toInt a) (toInt b) j) :=
        congrArg Subtype.val h
      have h2 := congrArg toInt hv
      have hb := toInt_lt b; have ha := le_toInt a
      obtain ⟨_, _⟩ := magF_mem (a := toInt a) (b := toInt b) (n := i) (by omega)
      obtain ⟨_, _⟩ := magF_mem (a := toInt a) (b := toInt b) (n := j) (by omega)
      rw [canon _ (by omega) (by omega), canon _ (by omega) (by omega)] at h2
      exact magF_inj h2)
    (fun t => by
      have hla : toInt a ≤ toInt t.val := (le_iff a t.val).mp t.2.1
      have hlt : toInt t.val < toInt b := (lt_iff t.val b).mp t.2.2
      obtain ⟨n, hn, hval⟩ := magF_surj (a := toInt a) (b := toInt b) (x := toInt t.val) hla hlt
      refine ⟨n, by omega, ?_⟩
      apply Subtype.ext
      show ofInt (magF (toInt a) (toInt b) n) = t.val
      rw [hval, ofInt_toInt])

/-- Positions at or past the card `(toInt b - toInt a).toNat` are `none`. -/
theorem exhaustiveSignedRangeGen_gen_none {T : Type*} [LE T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff) (a b : T) (n : ℕ)
    (h : (toInt b - toInt a).toNat ≤ n) :
    @gen _ (exhaustiveSignedRangeGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff a b) n = none :=
  dite_eq_right (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem exhaustiveSignedRangeGen_gen_some {T : Type*} [LE T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff) (a b : T) (n : ℕ)
    (h : n < (toInt b - toInt a).toNat) :
    @gen _ (exhaustiveSignedRangeGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff a b) n ≠ none := by
  rw [show @gen _ (exhaustiveSignedRangeGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt lt_iff le_iff a b) n = some _ from dite_eq_left (by omega)]
  exact Option.some_ne_none _

/-- Magnitude-ordered signed inclusive range `[a, b]`, closed-form (uses
`magF (toInt a) (toInt b + 1)`; card `(toInt b - toInt a + 1).toNat`). -/
@[reducible] def exhaustiveSignedRangeInclusiveGen {T : Type*} [LE T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (le_iff : ∀ x y : T, x ≤ y ↔ toInt x ≤ toInt y)
    (a b : T) : ExhaustiveGenerator {x : T // a ≤ x ∧ x ≤ b} :=
  ExhaustiveGenerator.ofBoundedBijOn (toInt b - toInt a + 1).toNat
    (fun n h => ⟨ofInt (magF (toInt a) (toInt b + 1) n), by
      have hb := toInt_lt b; have ha := le_toInt a
      obtain ⟨hm1, hm2⟩ := magF_mem (a := toInt a) (b := toInt b + 1) (n := n) (by omega)
      have hc : toInt (ofInt (magF (toInt a) (toInt b + 1) n)) = magF (toInt a) (toInt b + 1) n :=
        canon _ (by omega) (by omega)
      exact ⟨by rw [le_iff, hc]; omega, by rw [le_iff, hc]; omega⟩⟩)
    (fun i j hi hj h => by
      have hv : ofInt (magF (toInt a) (toInt b + 1) i) = ofInt (magF (toInt a) (toInt b + 1) j) :=
        congrArg Subtype.val h
      have h2 := congrArg toInt hv
      have hb := toInt_lt b; have ha := le_toInt a
      obtain ⟨_, _⟩ := magF_mem (a := toInt a) (b := toInt b + 1) (n := i) (by omega)
      obtain ⟨_, _⟩ := magF_mem (a := toInt a) (b := toInt b + 1) (n := j) (by omega)
      rw [canon _ (by omega) (by omega), canon _ (by omega) (by omega)] at h2
      exact magF_inj h2)
    (fun t => by
      have hla : toInt a ≤ toInt t.val := (le_iff a t.val).mp t.2.1
      have hlb : toInt t.val ≤ toInt b := (le_iff t.val b).mp t.2.2
      obtain ⟨n, hn, hval⟩ := magF_surj (a := toInt a) (b := toInt b + 1) (x := toInt t.val) hla (by omega)
      refine ⟨n, by omega, ?_⟩
      apply Subtype.ext
      show ofInt (magF (toInt a) (toInt b + 1) n) = t.val
      rw [hval, ofInt_toInt])

/-- Positions at or past the card `(toInt b - toInt a + 1).toNat` are `none`. -/
theorem exhaustiveSignedRangeInclusiveGen_gen_none {T : Type*} [LE T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon ofInt_toInt toInt_lt le_toInt le_iff) (a b : T) (n : ℕ)
    (h : (toInt b - toInt a + 1).toNat ≤ n) :
    @gen _ (exhaustiveSignedRangeInclusiveGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt le_iff a b) n = none :=
  dite_eq_right (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem exhaustiveSignedRangeInclusiveGen_gen_some {T : Type*} [LE T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon ofInt_toInt toInt_lt le_toInt le_iff) (a b : T) (n : ℕ)
    (h : n < (toInt b - toInt a + 1).toNat) :
    @gen _ (exhaustiveSignedRangeInclusiveGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt le_iff a b) n ≠ none := by
  rw [show @gen _ (exhaustiveSignedRangeInclusiveGen toInt ofInt bound canon ofInt_toInt toInt_lt le_toInt le_iff a b) n = some _ from dite_eq_left (by omega)]
  exact Option.some_ne_none _


@[reducible] def int8SignedRangeGen (a b : Int8) :
    ExhaustiveGenerator {x : Int8 // a ≤ x ∧ x < b} :=
  exhaustiveSignedRangeGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt
    (fun _ _ => Int8.lt_iff_toInt_lt) (fun _ _ => Int8.le_iff_toInt_le) a b

/-- `int8SignedRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements.
`Fintype.card` is a fact about the *subtype* `{x // a ≤ x ∧ x < b}`, independent
of which generator enumerates it or in what order — so the magnitude-ordered
count is literally the ascending `int8RangeGen_card` restated; the proof never
touches the magnitude generator. -/
theorem int8SignedRangeGen_card (a b : Int8) :
    Fintype.card {x : Int8 // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  int8RangeGen_card a b

@[reducible] def int16SignedRangeGen (a b : Int16) :
    ExhaustiveGenerator {x : Int16 // a ≤ x ∧ x < b} :=
  exhaustiveSignedRangeGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt
    (fun _ _ => Int16.lt_iff_toInt_lt) (fun _ _ => Int16.le_iff_toInt_le) a b

/-- `int16SignedRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements.
`Fintype.card` is a fact about the *subtype* `{x // a ≤ x ∧ x < b}`, independent
of which generator enumerates it or in what order — so the magnitude-ordered
count is literally the ascending `int16RangeGen_card` restated; the proof never
touches the magnitude generator. -/
theorem int16SignedRangeGen_card (a b : Int16) :
    Fintype.card {x : Int16 // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  int16RangeGen_card a b

@[reducible] def int32SignedRangeGen (a b : Int32) :
    ExhaustiveGenerator {x : Int32 // a ≤ x ∧ x < b} :=
  exhaustiveSignedRangeGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt
    (fun _ _ => Int32.lt_iff_toInt_lt) (fun _ _ => Int32.le_iff_toInt_le) a b

/-- `int32SignedRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements.
`Fintype.card` is a fact about the *subtype* `{x // a ≤ x ∧ x < b}`, independent
of which generator enumerates it or in what order — so the magnitude-ordered
count is literally the ascending `int32RangeGen_card` restated; the proof never
touches the magnitude generator. -/
theorem int32SignedRangeGen_card (a b : Int32) :
    Fintype.card {x : Int32 // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  int32RangeGen_card a b

@[reducible] def int64SignedRangeGen (a b : Int64) :
    ExhaustiveGenerator {x : Int64 // a ≤ x ∧ x < b} :=
  exhaustiveSignedRangeGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt
    (fun _ _ => Int64.lt_iff_toInt_lt) (fun _ _ => Int64.le_iff_toInt_le) a b

/-- `int64SignedRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements.
`Fintype.card` is a fact about the *subtype* `{x // a ≤ x ∧ x < b}`, independent
of which generator enumerates it or in what order — so the magnitude-ordered
count is literally the ascending `int64RangeGen_card` restated; the proof never
touches the magnitude generator. -/
theorem int64SignedRangeGen_card (a b : Int64) :
    Fintype.card {x : Int64 // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  int64RangeGen_card a b

@[reducible] def int8SignedRangeInclusiveGen (a b : Int8) :
    ExhaustiveGenerator {x : Int8 // a ≤ x ∧ x ≤ b} :=
  exhaustiveSignedRangeInclusiveGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt (fun _ _ => Int8.le_iff_toInt_le) a b

/-- `int8SignedRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat`
elements. `Fintype.card` is a fact about the *subtype* `{x // a ≤ x ∧ x ≤ b}`,
independent of which generator enumerates it or in what order — so the
magnitude-ordered count is literally the ascending `int8RangeInclusiveGen_card`
restated; the proof never touches the magnitude generator. -/
theorem int8SignedRangeInclusiveGen_card (a b : Int8) :
    Fintype.card {x : Int8 // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  int8RangeInclusiveGen_card a b

@[reducible] def int16SignedRangeInclusiveGen (a b : Int16) :
    ExhaustiveGenerator {x : Int16 // a ≤ x ∧ x ≤ b} :=
  exhaustiveSignedRangeInclusiveGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt (fun _ _ => Int16.le_iff_toInt_le) a b

/-- `int16SignedRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat`
elements. `Fintype.card` is a fact about the *subtype* `{x // a ≤ x ∧ x ≤ b}`,
independent of which generator enumerates it or in what order — so the
magnitude-ordered count is literally the ascending `int16RangeInclusiveGen_card`
restated; the proof never touches the magnitude generator. -/
theorem int16SignedRangeInclusiveGen_card (a b : Int16) :
    Fintype.card {x : Int16 // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  int16RangeInclusiveGen_card a b

@[reducible] def int32SignedRangeInclusiveGen (a b : Int32) :
    ExhaustiveGenerator {x : Int32 // a ≤ x ∧ x ≤ b} :=
  exhaustiveSignedRangeInclusiveGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt (fun _ _ => Int32.le_iff_toInt_le) a b

/-- `int32SignedRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat`
elements. `Fintype.card` is a fact about the *subtype* `{x // a ≤ x ∧ x ≤ b}`,
independent of which generator enumerates it or in what order — so the
magnitude-ordered count is literally the ascending `int32RangeInclusiveGen_card`
restated; the proof never touches the magnitude generator. -/
theorem int32SignedRangeInclusiveGen_card (a b : Int32) :
    Fintype.card {x : Int32 // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  int32RangeInclusiveGen_card a b

@[reducible] def int64SignedRangeInclusiveGen (a b : Int64) :
    ExhaustiveGenerator {x : Int64 // a ≤ x ∧ x ≤ b} :=
  exhaustiveSignedRangeInclusiveGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt (fun _ _ => Int64.le_iff_toInt_le) a b

/-- `int64SignedRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat`
elements. `Fintype.card` is a fact about the *subtype* `{x // a ≤ x ∧ x ≤ b}`,
independent of which generator enumerates it or in what order — so the
magnitude-ordered count is literally the ascending `int64RangeInclusiveGen_card`
restated; the proof never touches the magnitude generator. -/
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
-- Wide `Int64` magnitude range: the closed form yields the leading interleave
-- instantly — the old materialize-and-sort would have built a 10^12-element list.
#guard (@firstN _ (int64SignedRangeGen (-(10 ^ 12)) (10 ^ 12)) 7).map (·.val.toInt) =
  [0, 1, -1, 2, -2, 3, -3]
-- A deep index is O(1): position 2·10^9 in the interleave is `-(10^9)`.
#guard (@gen _ (int64SignedRangeGen (-(10 ^ 12)) (10 ^ 12)) (2 * 10 ^ 9)).map (·.val.toInt) =
  some (-(10 ^ 9))

end Azurite

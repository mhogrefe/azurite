/-
  FINITE monotone exhaustive generators over the fixed-width signed integers
  `Int8`, `Int16`, `Int32`, `Int64` (Malachite's `exhaustive_natural_signeds`,
  `exhaustive_negative_signeds`, `exhaustive_positive_signeds`).

  Each width has three monotone half-line generators onto an order subtype:
    * nonnegative `{x // 0 ≤ x}` : `0, 1, …, MAX`   (card `2^(w-1)`)
    * negative    `{x // x < 0}` : `-1, -2, …, MIN`  (card `2^(w-1)`)
    * positive    `{x // 0 < x}` : `1, 2, …, MAX`    (card `2^(w-1) - 1`)

  All are finite, so each is built with `ExhaustiveGenerator.ofBoundedBijOn`.
  To avoid twelve copy-pasted proofs, three GENERIC builders
  (`positiveSignedGen`, `nonnegativeSignedGen`, `negativeSignedGen`) do the
  proof once over an abstract type `T` with its `toInt`/`ofInt`, its
  in-range round-trip (`canon`), range bounds, and the order↔`toInt` bridge;
  each width is then a one-line application supplying its core lemmas.
-/
import Azurite.ExhaustiveGenerator.Basic

namespace Azurite

/-! ### Generic finite-signed builders -/

/-- Generic builder for the positive elements of a bounded signed type, in the
order `1, 2, …, MAX`. `bound = 2^(w-1)`, card `= bound - 1`, value `ofInt (n+1)`. -/
@[reducible] def positiveSignedGen {T : Type*} [Zero T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (lt_iff : ∀ x y : T, x < y ↔ toInt x < toInt y)
    (zero_toInt : toInt (0 : T) = 0) :
    ExhaustiveGenerator {x : T // 0 < x} :=
  ExhaustiveGenerator.ofBoundedBijOn (bound - 1)
    (fun n h => ⟨ofInt ((n : ℤ) + 1), by
      rw [lt_iff, zero_toInt, canon ((n : ℤ) + 1) (by omega) (by omega)]; omega⟩)
    (fun i j hi hj h => by
      have hv : ofInt ((i : ℤ) + 1) = ofInt ((j : ℤ) + 1) := congrArg Subtype.val h
      have h2 := congrArg toInt hv
      rw [canon ((i : ℤ) + 1) (by omega) (by omega),
        canon ((j : ℤ) + 1) (by omega) (by omega)] at h2
      omega)
    (fun t => by
      have h1 : 0 < toInt t.val := by have := t.2; rw [lt_iff, zero_toInt] at this; exact this
      have h2 : toInt t.val < (bound : ℤ) := toInt_lt t.val
      refine ⟨(toInt t.val - 1).toNat, by omega, ?_⟩
      apply Subtype.ext
      show ofInt (((toInt t.val - 1).toNat : ℤ) + 1) = t.val
      rw [show ((toInt t.val - 1).toNat : ℤ) + 1 = toInt t.val from by omega, ofInt_toInt])

/-- Generic builder for the nonnegative elements of a bounded signed type, in the
order `0, 1, …, MAX`. `bound = 2^(w-1)`, card `= bound`, value `ofInt n`. -/
@[reducible] def nonnegativeSignedGen {T : Type*} [Zero T] [LE T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_iff : ∀ x y : T, x ≤ y ↔ toInt x ≤ toInt y)
    (zero_toInt : toInt (0 : T) = 0) :
    ExhaustiveGenerator {x : T // 0 ≤ x} :=
  ExhaustiveGenerator.ofBoundedBijOn bound
    (fun n h => ⟨ofInt (n : ℤ), by
      rw [le_iff, zero_toInt, canon (n : ℤ) (by omega) (by omega)]; omega⟩)
    (fun i j hi hj h => by
      have hv : ofInt (i : ℤ) = ofInt (j : ℤ) := congrArg Subtype.val h
      have h2 := congrArg toInt hv
      rw [canon (i : ℤ) (by omega) (by omega), canon (j : ℤ) (by omega) (by omega)] at h2
      omega)
    (fun t => by
      have h1 : 0 ≤ toInt t.val := by have := t.2; rw [le_iff, zero_toInt] at this; exact this
      have h2 : toInt t.val < (bound : ℤ) := toInt_lt t.val
      refine ⟨(toInt t.val).toNat, by omega, ?_⟩
      apply Subtype.ext
      show ofInt ((toInt t.val).toNat : ℤ) = t.val
      rw [show ((toInt t.val).toNat : ℤ) = toInt t.val from by omega, ofInt_toInt])

/-- Generic builder for the negative elements of a bounded signed type, in the
order `-1, -2, …, MIN`. `bound = 2^(w-1)`, card `= bound`, value `ofInt (-(n+1))`. -/
@[reducible] def negativeSignedGen {T : Type*} [Zero T] [LT T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (bound : ℕ)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (lt_iff : ∀ x y : T, x < y ↔ toInt x < toInt y)
    (zero_toInt : toInt (0 : T) = 0) :
    ExhaustiveGenerator {x : T // x < 0} :=
  ExhaustiveGenerator.ofBoundedBijOn bound
    (fun n h => ⟨ofInt (-((n : ℤ) + 1)), by
      rw [lt_iff, zero_toInt, canon (-((n : ℤ) + 1)) (by omega) (by omega)]; omega⟩)
    (fun i j hi hj h => by
      have hv : ofInt (-((i : ℤ) + 1)) = ofInt (-((j : ℤ) + 1)) := congrArg Subtype.val h
      have h2 := congrArg toInt hv
      rw [canon (-((i : ℤ) + 1)) (by omega) (by omega),
        canon (-((j : ℤ) + 1)) (by omega) (by omega)] at h2
      omega)
    (fun t => by
      have h1 : toInt t.val < 0 := by have := t.2; rw [lt_iff, zero_toInt] at this; exact this
      have h2 : -(bound : ℤ) ≤ toInt t.val := le_toInt t.val
      refine ⟨(-toInt t.val - 1).toNat, by omega, ?_⟩
      apply Subtype.ext
      show ofInt (-(((-toInt t.val - 1).toNat : ℤ) + 1)) = t.val
      rw [show -(((-toInt t.val - 1).toNat : ℤ) + 1) = toInt t.val from by omega, ofInt_toInt])

/-! ### Per-width instances

The `canon` argument reduces the core `IntX.toInt_ofInt` (a balanced-mod
`bmod`) to the identity on the in-range interval via `Int.bmod_eq_of_le`. -/

/-! #### Nonnegative signeds `0, 1, …, MAX` -/

instance nonnegativeInt8Gen : ExhaustiveGenerator {x : Int8 // 0 ≤ x} :=
  nonnegativeSignedGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt (fun _ _ => Int8.le_iff_toInt_le) rfl

instance nonnegativeInt16Gen : ExhaustiveGenerator {x : Int16 // 0 ≤ x} :=
  nonnegativeSignedGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt (fun _ _ => Int16.le_iff_toInt_le) rfl

instance nonnegativeInt32Gen : ExhaustiveGenerator {x : Int32 // 0 ≤ x} :=
  nonnegativeSignedGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt (fun _ _ => Int32.le_iff_toInt_le) rfl

instance nonnegativeInt64Gen : ExhaustiveGenerator {x : Int64 // 0 ≤ x} :=
  nonnegativeSignedGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt (fun _ _ => Int64.le_iff_toInt_le) rfl

/-! #### Negative signeds `-1, -2, …, MIN` -/

instance negativeInt8Gen : ExhaustiveGenerator {x : Int8 // x < 0} :=
  negativeSignedGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.le_toInt (fun _ _ => Int8.lt_iff_toInt_lt) rfl

instance negativeInt16Gen : ExhaustiveGenerator {x : Int16 // x < 0} :=
  negativeSignedGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.le_toInt (fun _ _ => Int16.lt_iff_toInt_lt) rfl

instance negativeInt32Gen : ExhaustiveGenerator {x : Int32 // x < 0} :=
  negativeSignedGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.le_toInt (fun _ _ => Int32.lt_iff_toInt_lt) rfl

instance negativeInt64Gen : ExhaustiveGenerator {x : Int64 // x < 0} :=
  negativeSignedGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.le_toInt (fun _ _ => Int64.lt_iff_toInt_lt) rfl

/-! #### Positive signeds `1, 2, …, MAX` -/

instance positiveInt8Gen : ExhaustiveGenerator {x : Int8 // 0 < x} :=
  positiveSignedGen Int8.toInt Int8.ofInt (2 ^ 7)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt (fun _ _ => Int8.lt_iff_toInt_lt) rfl

instance positiveInt16Gen : ExhaustiveGenerator {x : Int16 // 0 < x} :=
  positiveSignedGen Int16.toInt Int16.ofInt (2 ^ 15)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt (fun _ _ => Int16.lt_iff_toInt_lt) rfl

instance positiveInt32Gen : ExhaustiveGenerator {x : Int32 // 0 < x} :=
  positiveSignedGen Int32.toInt Int32.ofInt (2 ^ 31)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt (fun _ _ => Int32.lt_iff_toInt_lt) rfl

instance positiveInt64Gen : ExhaustiveGenerator {x : Int64 // 0 < x} :=
  positiveSignedGen Int64.toInt Int64.ofInt (2 ^ 63)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt (fun _ _ => Int64.lt_iff_toInt_lt) rfl

/-! ### Generic finite zig-zag signed builders

The finite signed range `[MIN, MAX] = [-2^(w-1), 2^(w-1)-1]` has ONE extra
negative (`MIN = -2^(w-1)`), so the symmetric zig-zag `0,1,-1,…,MAX,-MAX`
covers `[-MAX, MAX]` and `MIN` lands ALONE at the final index. With
`bound = 2^(w-1)` we have `MAX = bound - 1`, `MIN = -bound`. -/

/-- Generic builder for the FULL signed type in zig-zag order
`0, 1, -1, 2, -2, …, MAX, -MAX, MIN`. Card `= 2·bound = 2^w`; the last index
`2·bound - 1` maps to `minValue`, all earlier indices run the symmetric
zig-zag onto `[-MAX, MAX]`. -/
@[reducible] def zigZagSignedGen {T : Type*}
    (toInt : T → ℤ) (ofInt : ℤ → T) (minValue : T) (bound : ℕ) (hbound : 0 < bound)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (toInt_minValue : toInt minValue = -(bound : ℤ)) :
    ExhaustiveGenerator T := by
  have tinj : ∀ a b : T, toInt a = toInt b → a = b :=
    fun a b hab => by rw [← ofInt_toInt a, ← ofInt_toInt b, hab]
  -- Bridge: the `toInt` of the (finite) zig-zag value, for indices in range.
  have key : ∀ m, m < 2 * bound →
      toInt (if m = 2 * bound - 1 then minValue
             else ofInt (if m % 2 = 0 then -(m / 2 : ℤ) else (m / 2 : ℤ) + 1))
      = (if m = 2 * bound - 1 then -(bound : ℤ)
         else (if m % 2 = 0 then -(m / 2 : ℤ) else (m / 2 : ℤ) + 1)) := by
    intro m hm
    split_ifs with h1 h2
    · exact toInt_minValue
    · apply canon <;> omega
    · apply canon <;> omega
  refine ExhaustiveGenerator.ofBoundedBij (2 * bound)
    (fun n => if n = 2 * bound - 1 then minValue
              else ofInt (if n % 2 = 0 then -(n / 2 : ℤ) else (n / 2 : ℤ) + 1)) ?_ ?_
  · -- injective: reduce to `ℤ` via `key`, then parity/`MIN` disjointness by `omega`
    intro i j hi hj h
    have h2 := congrArg toInt h
    rw [key i hi, key j hj] at h2
    split_ifs at h2 <;> omega
  · -- surjective: `MIN` at the last index, `t.toInt ≥ 1` at `2·t.toInt - 1`,
    -- `t.toInt ≤ 0` (and `≠ MIN`) at `2·(-t.toInt)`
    intro t
    by_cases hmin : toInt t = -(bound : ℤ)
    · exact ⟨2 * bound - 1, by omega, by
        apply tinj; rw [key (2 * bound - 1) (by omega)]; split_ifs <;> omega⟩
    · by_cases hpos : 1 ≤ toInt t
      · exact ⟨(2 * toInt t - 1).toNat, by have := toInt_lt t; omega, by
          apply tinj; rw [key _ (by have := toInt_lt t; omega)]
          have := toInt_lt t; split_ifs <;> omega⟩
      · exact ⟨(2 * (-toInt t)).toNat, by have := le_toInt t; omega, by
          apply tinj; rw [key _ (by have := le_toInt t; omega)]
          have := le_toInt t; split_ifs <;> omega⟩

/-- Generic builder for the NONZERO signed subtype in zig-zag order
`1, -1, 2, -2, …, MAX, -MAX, MIN`. Card `= 2·bound - 1`; the last index
`2·bound - 2` maps to `minValue`, all earlier indices run the nonzero zig-zag
onto `[-MAX, MAX] \ {0}`. Uses `ofBoundedBijOn` because each value must carry
its `≠ 0` proof (valid only in range). -/
@[reducible] def zigZagNonzeroSignedGen {T : Type*} [Zero T]
    (toInt : T → ℤ) (ofInt : ℤ → T) (minValue : T) (bound : ℕ) (hbound : 0 < bound)
    (canon : ∀ n : ℤ, -(bound : ℤ) ≤ n → n < (bound : ℤ) → toInt (ofInt n) = n)
    (ofInt_toInt : ∀ x : T, ofInt (toInt x) = x)
    (toInt_lt : ∀ x : T, toInt x < (bound : ℤ))
    (le_toInt : ∀ x : T, -(bound : ℤ) ≤ toInt x)
    (toInt_minValue : toInt minValue = -(bound : ℤ))
    (zero_toInt : toInt (0 : T) = 0) :
    ExhaustiveGenerator {x : T // x ≠ 0} := by
  have tinj : ∀ a b : T, toInt a = toInt b → a = b :=
    fun a b hab => by rw [← ofInt_toInt a, ← ofInt_toInt b, hab]
  let g : ℕ → T := fun m => if m = 2 * bound - 2 then minValue
                            else ofInt (if m % 2 = 0 then (m / 2 : ℤ) + 1 else -((m / 2 : ℤ) + 1))
  have key : ∀ m, m < 2 * bound - 1 → toInt (g m)
      = (if m = 2 * bound - 2 then -(bound : ℤ)
         else (if m % 2 = 0 then (m / 2 : ℤ) + 1 else -((m / 2 : ℤ) + 1))) := by
    intro m hm
    show toInt (if m = 2 * bound - 2 then minValue
                else ofInt (if m % 2 = 0 then (m / 2 : ℤ) + 1 else -((m / 2 : ℤ) + 1))) = _
    split_ifs with h1 h2
    · exact toInt_minValue
    · apply canon <;> omega
    · apply canon <;> omega
  -- every produced value is nonzero (`MIN ≠ 0`, zig-zag values are `≥1` or `≤-1`)
  have gne : ∀ m, m < 2 * bound - 1 → g m ≠ 0 := by
    intro m hm hz
    have hk := key m hm
    rw [hz, zero_toInt] at hk
    split_ifs at hk <;> omega
  refine ExhaustiveGenerator.ofBoundedBijOn (2 * bound - 1) (fun m h => ⟨g m, gne m h⟩) ?_ ?_
  · intro i j hi hj h
    have h2 := congrArg toInt (congrArg Subtype.val h)
    rw [key i hi, key j hj] at h2
    split_ifs at h2 <;> omega
  · intro t
    have hz0 : toInt t.val ≠ 0 := fun h0 => t.2 (tinj t.val 0 (by rw [h0, zero_toInt]))
    by_cases hmin : toInt t.val = -(bound : ℤ)
    · refine ⟨2 * bound - 2, by omega, ?_⟩
      apply Subtype.ext
      show g (2 * bound - 2) = t.val
      apply tinj; rw [key (2 * bound - 2) (by omega)]; split_ifs <;> omega
    · by_cases hpos : 1 ≤ toInt t.val
      · refine ⟨(2 * (toInt t.val - 1)).toNat, by have := toInt_lt t.val; omega, ?_⟩
        apply Subtype.ext
        show g ((2 * (toInt t.val - 1)).toNat) = t.val
        apply tinj; rw [key _ (by have := toInt_lt t.val; omega)]
        have := toInt_lt t.val; split_ifs <;> omega
      · refine ⟨(-2 * toInt t.val - 1).toNat, by have := le_toInt t.val; omega, ?_⟩
        apply Subtype.ext
        show g ((-2 * toInt t.val - 1).toNat) = t.val
        apply tinj; rw [key _ (by have := le_toInt t.val; omega)]
        have := le_toInt t.val; split_ifs <;> omega

/-! #### Zig-zag signeds (full type) `0, 1, -1, 2, -2, …, MAX, -MAX, MIN` -/

instance int8Gen : ExhaustiveGenerator Int8 :=
  zigZagSignedGen Int8.toInt Int8.ofInt Int8.minValue (2 ^ 7) (by norm_num)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt Int8.toInt_minValue

instance int16Gen : ExhaustiveGenerator Int16 :=
  zigZagSignedGen Int16.toInt Int16.ofInt Int16.minValue (2 ^ 15) (by norm_num)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt Int16.toInt_minValue

instance int32Gen : ExhaustiveGenerator Int32 :=
  zigZagSignedGen Int32.toInt Int32.ofInt Int32.minValue (2 ^ 31) (by norm_num)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt Int32.toInt_minValue

instance int64Gen : ExhaustiveGenerator Int64 :=
  zigZagSignedGen Int64.toInt Int64.ofInt Int64.minValue (2 ^ 63) (by norm_num)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt Int64.toInt_minValue

/-! #### Nonzero zig-zag signeds `1, -1, 2, -2, …, MAX, -MAX, MIN` -/

instance nonzeroInt8Gen : ExhaustiveGenerator {x : Int8 // x ≠ 0} :=
  zigZagNonzeroSignedGen Int8.toInt Int8.ofInt Int8.minValue (2 ^ 7) (by norm_num)
    (fun _ _ _ => by rw [Int8.toInt_ofInt, Int8.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int8.ofInt_toInt Int8.toInt_lt Int8.le_toInt Int8.toInt_minValue rfl

instance nonzeroInt16Gen : ExhaustiveGenerator {x : Int16 // x ≠ 0} :=
  zigZagNonzeroSignedGen Int16.toInt Int16.ofInt Int16.minValue (2 ^ 15) (by norm_num)
    (fun _ _ _ => by rw [Int16.toInt_ofInt, Int16.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int16.ofInt_toInt Int16.toInt_lt Int16.le_toInt Int16.toInt_minValue rfl

instance nonzeroInt32Gen : ExhaustiveGenerator {x : Int32 // x ≠ 0} :=
  zigZagNonzeroSignedGen Int32.toInt Int32.ofInt Int32.minValue (2 ^ 31) (by norm_num)
    (fun _ _ _ => by rw [Int32.toInt_ofInt, Int32.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int32.ofInt_toInt Int32.toInt_lt Int32.le_toInt Int32.toInt_minValue rfl

instance nonzeroInt64Gen : ExhaustiveGenerator {x : Int64 // x ≠ 0} :=
  zigZagNonzeroSignedGen Int64.toInt Int64.ofInt Int64.minValue (2 ^ 63) (by norm_num)
    (fun _ _ _ => by rw [Int64.toInt_ofInt, Int64.size]; exact Int.bmod_eq_of_le (by omega) (by omega))
    Int64.ofInt_toInt Int64.toInt_lt Int64.le_toInt Int64.toInt_minValue rfl

-- First-10 of one of each shape (Malachite doctests) + finiteness.
#guard ((ExhaustiveGenerator.firstN {x : Int8 // 0 ≤ x} 10).map (·.val.toInt)) ==
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
#guard ((ExhaustiveGenerator.firstN {x : Int8 // x < 0} 10).map (·.val.toInt)) ==
  [-1, -2, -3, -4, -5, -6, -7, -8, -9, -10]
#guard ((ExhaustiveGenerator.firstN {x : Int8 // 0 < x} 10).map (·.val.toInt)) ==
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
-- Finiteness: nonnegative `Int8` stops at its cardinality `128`, not at `300`.
#guard (ExhaustiveGenerator.firstN {x : Int8 // 0 ≤ x} 300).length == 128

-- Zig-zag signeds (Malachite doctests) + the MIN-tail / finiteness edge.
#guard ((ExhaustiveGenerator.firstN Int8 10).map (·.toInt)) ==
  [0, 1, -1, 2, -2, 3, -3, 4, -4, 5]
#guard ((ExhaustiveGenerator.firstN {x : Int8 // x ≠ 0} 10).map (·.val.toInt)) ==
  [1, -1, 2, -2, 3, -3, 4, -4, 5, -5]
-- Full `Int8` enumeration ends at `MIN = -128` (the lone last index) and has `256` elements.
#guard ((ExhaustiveGenerator.firstN Int8 256).getLast?.map (·.toInt)) == some (-128)
#guard (ExhaustiveGenerator.firstN Int8 300).length == 256
-- Nonzero `Int8` stops at cardinality `255`, also ending at `MIN = -128`.
#guard (ExhaustiveGenerator.firstN {x : Int8 // x ≠ 0} 300).length == 255
#guard ((ExhaustiveGenerator.firstN {x : Int8 // x ≠ 0} 255).getLast?.map (·.val.toInt)) ==
  some (-128)

end Azurite

/-
  Ascending range generators over the arbitrary-precision `AzNat` / `AzInt`
  (Malachite `exhaustive_natural_range`/`_inclusive_range`/`_range_to_infinity`
  and `integer_increasing_range`/`_inclusive_range`/`_range_to_infinity`/
  `decreasing_range_to_negative_infinity`).

  These are SIMPLER than the fixed-width ranges: `AzNat`/`AzInt` are unbounded,
  so `ofNat`/`ofInt` round-trips UNCONDITIONALLY (no `MAX` bound, no `bmod`) —
  the proofs are just the order↔`toNat`/`toInt` bridges plus `omega`. Bounded
  ranges use `ofBoundedBijOn` (empty `a ≥ b` ⟹ card `0` ⟹ `gen ≡ none`, no
  special case); the `[a, ∞)` / `(-∞, b]` families are infinite, via
  `ofBijective`.

  The bounded `AzInt` magnitude-ordered ranges use the CLOSED-FORM `magF` index
  formula from `Ranges.lean` (the finite two-sided analogue of the infinite-ray
  `toInfF` below), so `gen n` is O(1) — no per-call list materialization. An
  earlier version built the ascending list and `mergeSort`ed it, making `gen 0`
  Θ(N log N) and `azIntRangeGen` over a wide range (e.g. ±10^12) unusable.

  Deviation from Malachite: where Malachite's range constructors `assert!(a <= b)`
  (and PANIC on a reversed range), every Azurite range generator here is a TOTAL
  function — a reversed or degenerate range (`a ≥ b`) is simply the empty
  generator (card `0`, `gen ≡ none`), needing no precondition.
-/
import Azurite.ExhaustiveGenerator.Count
import Azurite.ExhaustiveGenerator.Ranges
import Azurite.AzNat.Equiv.Compare
import Azurite.AzInt.Equiv.Compare

namespace Azurite

open ExhaustiveGenerator

/-! ### `AzNat` bounded ascending ranges -/

/-- `AzNat` ascending range `[a, b)`: `a, a+1, …, b-1`. -/
@[reducible] def azNatRangeGen (a b : AzNat) : ExhaustiveGenerator {x : AzNat // a ≤ x ∧ x < b} :=
  ExhaustiveGenerator.ofBoundedBijOn (b.toNat - a.toNat)
    (fun n h => ⟨AzNat.ofNat (a.toNat + n), by
      refine ⟨?_, ?_⟩
      · rw [AzNat.le_iff_toNat_le, AzNat.toNat_ofNat]; omega
      · rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_ofNat]; omega⟩)
    (fun i j hi hj h => by
      have h2 := congrArg AzNat.toNat (congrArg Subtype.val h)
      rw [AzNat.toNat_ofNat, AzNat.toNat_ofNat] at h2; omega)
    (fun t => by
      have hla : a.toNat ≤ t.val.toNat := (AzNat.le_iff_toNat_le a t.val).mp t.2.1
      have hlt : t.val.toNat < b.toNat := (AzNat.lt_iff_toNat_lt t.val b).mp t.2.2
      refine ⟨t.val.toNat - a.toNat, by omega, ?_⟩
      apply Subtype.ext
      show AzNat.ofNat (a.toNat + (t.val.toNat - a.toNat)) = t.val
      rw [show a.toNat + (t.val.toNat - a.toNat) = t.val.toNat from by omega, AzNat.ofNat_toNat])

/-- Positions at or past the card `b.toNat - a.toNat` are `none`. -/
theorem azNatRangeGen_gen_none (a b : AzNat) (n : ℕ) (h : b.toNat - a.toNat ≤ n) :
    @gen _ (azNatRangeGen a b) n = none :=
  dif_neg (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem azNatRangeGen_gen_some (a b : AzNat) (n : ℕ) (h : n < b.toNat - a.toNat) :
    @gen _ (azNatRangeGen a b) n ≠ none := by
  rw [show @gen _ (azNatRangeGen a b) n = some _ from dif_pos (by omega)]
  exact Option.some_ne_none _

noncomputable instance instFintypeAzNatRange (a b : AzNat) :
    Fintype {x : AzNat // a ≤ x ∧ x < b} :=
  @fintypeOfBounded _ (azNatRangeGen a b) (b.toNat - a.toNat)
    (azNatRangeGen_gen_none a b) (azNatRangeGen_gen_some a b)

/-- `azNatRangeGen a b` produces `b.toNat - a.toNat` elements. -/
theorem azNatRangeGen_card (a b : AzNat) :
    Fintype.card {x : AzNat // a ≤ x ∧ x < b} = b.toNat - a.toNat :=
  @fintypeCard_eq _ (azNatRangeGen a b) _ (b.toNat - a.toNat)
    (azNatRangeGen_gen_none a b) (azNatRangeGen_gen_some a b)

/-- `AzNat` ascending inclusive range `[a, b]`. Card `b.toNat + 1 - a.toNat` (the
`+1` before the `ℕ` subtraction, so reversed `a > b` gives `0`). -/
@[reducible] def azNatRangeInclusiveGen (a b : AzNat) :
    ExhaustiveGenerator {x : AzNat // a ≤ x ∧ x ≤ b} :=
  ExhaustiveGenerator.ofBoundedBijOn (b.toNat + 1 - a.toNat)
    (fun n h => ⟨AzNat.ofNat (a.toNat + n), by
      refine ⟨?_, ?_⟩
      · rw [AzNat.le_iff_toNat_le, AzNat.toNat_ofNat]; omega
      · rw [AzNat.le_iff_toNat_le, AzNat.toNat_ofNat]; omega⟩)
    (fun i j hi hj h => by
      have h2 := congrArg AzNat.toNat (congrArg Subtype.val h)
      rw [AzNat.toNat_ofNat, AzNat.toNat_ofNat] at h2; omega)
    (fun t => by
      have hla : a.toNat ≤ t.val.toNat := (AzNat.le_iff_toNat_le a t.val).mp t.2.1
      have hlb : t.val.toNat ≤ b.toNat := (AzNat.le_iff_toNat_le t.val b).mp t.2.2
      refine ⟨t.val.toNat - a.toNat, by omega, ?_⟩
      apply Subtype.ext
      show AzNat.ofNat (a.toNat + (t.val.toNat - a.toNat)) = t.val
      rw [show a.toNat + (t.val.toNat - a.toNat) = t.val.toNat from by omega, AzNat.ofNat_toNat])

/-- Positions at or past the card `b.toNat + 1 - a.toNat` are `none`. -/
theorem azNatRangeInclusiveGen_gen_none (a b : AzNat) (n : ℕ) (h : b.toNat + 1 - a.toNat ≤ n) :
    @gen _ (azNatRangeInclusiveGen a b) n = none :=
  dif_neg (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem azNatRangeInclusiveGen_gen_some (a b : AzNat) (n : ℕ) (h : n < b.toNat + 1 - a.toNat) :
    @gen _ (azNatRangeInclusiveGen a b) n ≠ none := by
  rw [show @gen _ (azNatRangeInclusiveGen a b) n = some _ from dif_pos (by omega)]
  exact Option.some_ne_none _

noncomputable instance instFintypeAzNatRangeInclusive (a b : AzNat) :
    Fintype {x : AzNat // a ≤ x ∧ x ≤ b} :=
  @fintypeOfBounded _ (azNatRangeInclusiveGen a b) (b.toNat + 1 - a.toNat)
    (azNatRangeInclusiveGen_gen_none a b) (azNatRangeInclusiveGen_gen_some a b)

/-- `azNatRangeInclusiveGen a b` produces `b.toNat + 1 - a.toNat` elements. -/
theorem azNatRangeInclusiveGen_card (a b : AzNat) :
    Fintype.card {x : AzNat // a ≤ x ∧ x ≤ b} = b.toNat + 1 - a.toNat :=
  @fintypeCard_eq _ (azNatRangeInclusiveGen a b) _ (b.toNat + 1 - a.toNat)
    (azNatRangeInclusiveGen_gen_none a b) (azNatRangeInclusiveGen_gen_some a b)

/-! ### `AzInt` bounded ascending ranges -/

/-- `AzInt` ascending range `[a, b)`: `a, a+1, …, b-1`. -/
@[reducible] def azIntIncreasingRangeGen (a b : AzInt) :
    ExhaustiveGenerator {x : AzInt // a ≤ x ∧ x < b} :=
  ExhaustiveGenerator.ofBoundedBijOn (b.toInt - a.toInt).toNat
    (fun n h => ⟨AzInt.ofInt (a.toInt + (n : ℤ)), by
      refine ⟨?_, ?_⟩
      · rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; omega
      · rw [AzInt.lt_iff_toInt_lt, AzInt.toInt_ofInt]; omega⟩)
    (fun i j hi hj h => by
      have h2 := congrArg AzInt.toInt (congrArg Subtype.val h)
      rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at h2; omega)
    (fun t => by
      have hla : a.toInt ≤ t.val.toInt := (AzInt.le_iff_toInt_le a t.val).mp t.2.1
      have hlt : t.val.toInt < b.toInt := (AzInt.lt_iff_toInt_lt t.val b).mp t.2.2
      refine ⟨(t.val.toInt - a.toInt).toNat, by omega, ?_⟩
      apply Subtype.ext
      show AzInt.ofInt (a.toInt + ((t.val.toInt - a.toInt).toNat : ℤ)) = t.val
      rw [show a.toInt + ((t.val.toInt - a.toInt).toNat : ℤ) = t.val.toInt from by omega, AzInt.ofInt_toInt])

/-- Positions at or past the card `(b.toInt - a.toInt).toNat` are `none`. -/
theorem azIntIncreasingRangeGen_gen_none (a b : AzInt) (n : ℕ) (h : (b.toInt - a.toInt).toNat ≤ n) :
    @gen _ (azIntIncreasingRangeGen a b) n = none :=
  dif_neg (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem azIntIncreasingRangeGen_gen_some (a b : AzInt) (n : ℕ) (h : n < (b.toInt - a.toInt).toNat) :
    @gen _ (azIntIncreasingRangeGen a b) n ≠ none := by
  rw [show @gen _ (azIntIncreasingRangeGen a b) n = some _ from dif_pos (by omega)]
  exact Option.some_ne_none _

noncomputable instance instFintypeAzIntIncreasingRange (a b : AzInt) :
    Fintype {x : AzInt // a ≤ x ∧ x < b} :=
  @fintypeOfBounded _ (azIntIncreasingRangeGen a b) (b.toInt - a.toInt).toNat
    (azIntIncreasingRangeGen_gen_none a b) (azIntIncreasingRangeGen_gen_some a b)

/-- `azIntIncreasingRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements. -/
theorem azIntIncreasingRangeGen_card (a b : AzInt) :
    Fintype.card {x : AzInt // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  @fintypeCard_eq _ (azIntIncreasingRangeGen a b) _ (b.toInt - a.toInt).toNat
    (azIntIncreasingRangeGen_gen_none a b) (azIntIncreasingRangeGen_gen_some a b)

/-- `AzInt` ascending inclusive range `[a, b]`. Card `(b.toInt - a.toInt + 1).toNat`. -/
@[reducible] def azIntIncreasingRangeInclusiveGen (a b : AzInt) :
    ExhaustiveGenerator {x : AzInt // a ≤ x ∧ x ≤ b} :=
  ExhaustiveGenerator.ofBoundedBijOn (b.toInt - a.toInt + 1).toNat
    (fun n h => ⟨AzInt.ofInt (a.toInt + (n : ℤ)), by
      refine ⟨?_, ?_⟩
      · rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; omega
      · rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; omega⟩)
    (fun i j hi hj h => by
      have h2 := congrArg AzInt.toInt (congrArg Subtype.val h)
      rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at h2; omega)
    (fun t => by
      have hla : a.toInt ≤ t.val.toInt := (AzInt.le_iff_toInt_le a t.val).mp t.2.1
      have hlb : t.val.toInt ≤ b.toInt := (AzInt.le_iff_toInt_le t.val b).mp t.2.2
      refine ⟨(t.val.toInt - a.toInt).toNat, by omega, ?_⟩
      apply Subtype.ext
      show AzInt.ofInt (a.toInt + ((t.val.toInt - a.toInt).toNat : ℤ)) = t.val
      rw [show a.toInt + ((t.val.toInt - a.toInt).toNat : ℤ) = t.val.toInt from by omega, AzInt.ofInt_toInt])

/-- Positions at or past the card `(b.toInt - a.toInt + 1).toNat` are `none`. -/
theorem azIntIncreasingRangeInclusiveGen_gen_none (a b : AzInt) (n : ℕ)
    (h : (b.toInt - a.toInt + 1).toNat ≤ n) :
    @gen _ (azIntIncreasingRangeInclusiveGen a b) n = none :=
  dif_neg (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem azIntIncreasingRangeInclusiveGen_gen_some (a b : AzInt) (n : ℕ)
    (h : n < (b.toInt - a.toInt + 1).toNat) :
    @gen _ (azIntIncreasingRangeInclusiveGen a b) n ≠ none := by
  rw [show @gen _ (azIntIncreasingRangeInclusiveGen a b) n = some _ from dif_pos (by omega)]
  exact Option.some_ne_none _

noncomputable instance instFintypeAzIntIncreasingRangeInclusive (a b : AzInt) :
    Fintype {x : AzInt // a ≤ x ∧ x ≤ b} :=
  @fintypeOfBounded _ (azIntIncreasingRangeInclusiveGen a b) (b.toInt - a.toInt + 1).toNat
    (azIntIncreasingRangeInclusiveGen_gen_none a b) (azIntIncreasingRangeInclusiveGen_gen_some a b)

/-- `azIntIncreasingRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements. -/
theorem azIntIncreasingRangeInclusiveGen_card (a b : AzInt) :
    Fintype.card {x : AzInt // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  @fintypeCard_eq _ (azIntIncreasingRangeInclusiveGen a b) _ (b.toInt - a.toInt + 1).toNat
    (azIntIncreasingRangeInclusiveGen_gen_none a b) (azIntIncreasingRangeInclusiveGen_gen_some a b)

/-! ### Infinite: rays to `+∞` / `-∞` -/

/-- `[a, ∞)` over `AzNat`, ascending: `f n = ⟨ofNat (a.toNat + n), _⟩`. -/
def azNatRangeToInfinityFun (a : AzNat) : ℕ → {x : AzNat // a ≤ x} :=
  fun n => ⟨AzNat.ofNat (a.toNat + n), by rw [AzNat.le_iff_toNat_le, AzNat.toNat_ofNat]; omega⟩

theorem azNatRangeToInfinityFun_bijective (a : AzNat) :
    Function.Bijective (azNatRangeToInfinityFun a) := by
  constructor
  · intro i j h
    have h2 := congrArg AzNat.toNat (congrArg Subtype.val h)
    rw [azNatRangeToInfinityFun, azNatRangeToInfinityFun] at h2
    simp only [AzNat.toNat_ofNat] at h2; omega
  · rintro ⟨x, hx⟩
    have hla : a.toNat ≤ x.toNat := (AzNat.le_iff_toNat_le a x).mp hx
    refine ⟨x.toNat - a.toNat, ?_⟩
    apply Subtype.ext
    show AzNat.ofNat (a.toNat + (x.toNat - a.toNat)) = x
    rw [show a.toNat + (x.toNat - a.toNat) = x.toNat from by omega, AzNat.ofNat_toNat]

/-- `[a, ∞)` over `AzNat`, ascending (generalizes `naturalsGen` at `a = 0`). -/
@[reducible] def azNatRangeToInfinityGen (a : AzNat) : ExhaustiveGenerator {x : AzNat // a ≤ x} :=
  ExhaustiveGenerator.ofBijective (azNatRangeToInfinityFun a) (azNatRangeToInfinityFun_bijective a)

theorem azNatRangeToInfinityGen_infinite (a : AzNat) : Infinite {x : AzNat // a ≤ x} :=
  infinite_of_bijective (azNatRangeToInfinityFun a) (azNatRangeToInfinityFun_bijective a)

/-- `[a, ∞)` over `AzInt`, ascending: `f n = ⟨ofInt (a.toInt + n), _⟩`. -/
def azIntIncreasingRangeToInfinityFun (a : AzInt) : ℕ → {x : AzInt // a ≤ x} :=
  fun n => ⟨AzInt.ofInt (a.toInt + (n : ℤ)), by rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; omega⟩

theorem azIntIncreasingRangeToInfinityFun_bijective (a : AzInt) :
    Function.Bijective (azIntIncreasingRangeToInfinityFun a) := by
  constructor
  · intro i j h
    have h2 := congrArg AzInt.toInt (congrArg Subtype.val h)
    rw [azIntIncreasingRangeToInfinityFun, azIntIncreasingRangeToInfinityFun] at h2
    simp only [AzInt.toInt_ofInt] at h2; omega
  · rintro ⟨x, hx⟩
    have hla : a.toInt ≤ x.toInt := (AzInt.le_iff_toInt_le a x).mp hx
    refine ⟨(x.toInt - a.toInt).toNat, ?_⟩
    apply Subtype.ext
    show AzInt.ofInt (a.toInt + ((x.toInt - a.toInt).toNat : ℤ)) = x
    rw [show a.toInt + ((x.toInt - a.toInt).toNat : ℤ) = x.toInt from by omega, AzInt.ofInt_toInt]

/-- `[a, ∞)` over `AzInt`, ascending. -/
@[reducible] def azIntIncreasingRangeToInfinityGen (a : AzInt) : ExhaustiveGenerator {x : AzInt // a ≤ x} :=
  ExhaustiveGenerator.ofBijective (azIntIncreasingRangeToInfinityFun a) (azIntIncreasingRangeToInfinityFun_bijective a)

theorem azIntIncreasingRangeToInfinityGen_infinite (a : AzInt) : Infinite {x : AzInt // a ≤ x} :=
  infinite_of_bijective (azIntIncreasingRangeToInfinityFun a) (azIntIncreasingRangeToInfinityFun_bijective a)

/-- `(-∞, b]` over `AzInt`, DESCENDING: `f n = ⟨ofInt (b.toInt - n), _⟩` yields
`b, b-1, b-2, …` (Malachite `integer_decreasing_range_to_negative_infinity`). -/
def azIntDecreasingRangeToNegativeInfinityFun (b : AzInt) : ℕ → {x : AzInt // x ≤ b} :=
  fun n => ⟨AzInt.ofInt (b.toInt - (n : ℤ)), by rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; omega⟩

theorem azIntDecreasingRangeToNegativeInfinityFun_bijective (b : AzInt) :
    Function.Bijective (azIntDecreasingRangeToNegativeInfinityFun b) := by
  constructor
  · intro i j h
    have h2 := congrArg AzInt.toInt (congrArg Subtype.val h)
    rw [azIntDecreasingRangeToNegativeInfinityFun, azIntDecreasingRangeToNegativeInfinityFun] at h2
    simp only [AzInt.toInt_ofInt] at h2; omega
  · rintro ⟨x, hx⟩
    have hlb : x.toInt ≤ b.toInt := (AzInt.le_iff_toInt_le x b).mp hx
    refine ⟨(b.toInt - x.toInt).toNat, ?_⟩
    apply Subtype.ext
    show AzInt.ofInt (b.toInt - ((b.toInt - x.toInt).toNat : ℤ)) = x
    rw [show b.toInt - ((b.toInt - x.toInt).toNat : ℤ) = x.toInt from by omega, AzInt.ofInt_toInt]

/-- `(-∞, b]` over `AzInt`, descending. -/
@[reducible] def azIntDecreasingRangeToNegativeInfinityGen (b : AzInt) : ExhaustiveGenerator {x : AzInt // x ≤ b} :=
  ExhaustiveGenerator.ofBijective (azIntDecreasingRangeToNegativeInfinityFun b)
    (azIntDecreasingRangeToNegativeInfinityFun_bijective b)

theorem azIntDecreasingRangeToNegativeInfinityGen_infinite (b : AzInt) :
    Infinite {x : AzInt // x ≤ b} :=
  infinite_of_bijective (azIntDecreasingRangeToNegativeInfinityFun b)
    (azIntDecreasingRangeToNegativeInfinityFun_bijective b)

/-! ### `AzInt` bounded magnitude-ordered ranges

Malachite `exhaustive_integer_range`/`_inclusive_range`: the same SET as the
ascending range, ordered by the key `(|x|, positive-first)`. Realized by the
CLOSED-FORM `magF` index formula from `Ranges.lean` (`gen n` O(1), no sort),
exactly like the fixed-width `exhaustiveSignedRangeGen`; the counts are reused
from the ascending versions (they are order-independent). `AzInt`'s `ofInt`/
`toInt` round-trip unconditionally, so — unlike the fixed-width builder — no
`bmod`/`canon` bound is needed. -/

/-- `AzInt` magnitude-ordered range `[a, b)`, closed-form. -/
@[reducible] def azIntRangeGen (a b : AzInt) : ExhaustiveGenerator {x : AzInt // a ≤ x ∧ x < b} :=
  ExhaustiveGenerator.ofBoundedBijOn (b.toInt - a.toInt).toNat
    (fun n h => ⟨AzInt.ofInt (magF a.toInt b.toInt n), by
      obtain ⟨hm1, hm2⟩ := magF_mem (a := a.toInt) (b := b.toInt) (n := n) (by omega)
      refine ⟨?_, ?_⟩
      · rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; omega
      · rw [AzInt.lt_iff_toInt_lt, AzInt.toInt_ofInt]; omega⟩)
    (fun i j hi hj h => by
      have h2 := congrArg AzInt.toInt (congrArg Subtype.val h)
      rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at h2
      exact magF_inj h2)
    (fun t => by
      have hla : a.toInt ≤ t.val.toInt := (AzInt.le_iff_toInt_le a t.val).mp t.2.1
      have hlt : t.val.toInt < b.toInt := (AzInt.lt_iff_toInt_lt t.val b).mp t.2.2
      obtain ⟨n, hn, hval⟩ := magF_surj (a := a.toInt) (b := b.toInt) (x := t.val.toInt) hla hlt
      refine ⟨n, by omega, ?_⟩
      apply Subtype.ext
      show AzInt.ofInt (magF a.toInt b.toInt n) = t.val
      rw [hval, AzInt.ofInt_toInt])

/-- Positions at or past the card `(b.toInt - a.toInt).toNat` are `none`. -/
theorem azIntRangeGen_gen_none (a b : AzInt) (n : ℕ) (h : (b.toInt - a.toInt).toNat ≤ n) :
    @gen _ (azIntRangeGen a b) n = none :=
  dif_neg (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem azIntRangeGen_gen_some (a b : AzInt) (n : ℕ) (h : n < (b.toInt - a.toInt).toNat) :
    @gen _ (azIntRangeGen a b) n ≠ none := by
  rw [show @gen _ (azIntRangeGen a b) n = some _ from dif_pos (by omega)]
  exact Option.some_ne_none _

/-- `azIntRangeGen a b` produces `(b.toInt - a.toInt).toNat` elements (count reused
from the ascending `azIntIncreasingRangeGen`). -/
theorem azIntRangeGen_card (a b : AzInt) :
    Fintype.card {x : AzInt // a ≤ x ∧ x < b} = (b.toInt - a.toInt).toNat :=
  azIntIncreasingRangeGen_card a b

/-- `AzInt` magnitude-ordered inclusive range `[a, b]`, closed-form (uses
`magF a.toInt (b.toInt + 1)`). -/
@[reducible] def azIntRangeInclusiveGen (a b : AzInt) :
    ExhaustiveGenerator {x : AzInt // a ≤ x ∧ x ≤ b} :=
  ExhaustiveGenerator.ofBoundedBijOn (b.toInt - a.toInt + 1).toNat
    (fun n h => ⟨AzInt.ofInt (magF a.toInt (b.toInt + 1) n), by
      obtain ⟨hm1, hm2⟩ := magF_mem (a := a.toInt) (b := b.toInt + 1) (n := n) (by omega)
      refine ⟨?_, ?_⟩
      · rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; omega
      · rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; omega⟩)
    (fun i j hi hj h => by
      have h2 := congrArg AzInt.toInt (congrArg Subtype.val h)
      rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at h2
      exact magF_inj h2)
    (fun t => by
      have hla : a.toInt ≤ t.val.toInt := (AzInt.le_iff_toInt_le a t.val).mp t.2.1
      have hlb : t.val.toInt ≤ b.toInt := (AzInt.le_iff_toInt_le t.val b).mp t.2.2
      obtain ⟨n, hn, hval⟩ := magF_surj (a := a.toInt) (b := b.toInt + 1) (x := t.val.toInt) hla (by omega)
      refine ⟨n, by omega, ?_⟩
      apply Subtype.ext
      show AzInt.ofInt (magF a.toInt (b.toInt + 1) n) = t.val
      rw [hval, AzInt.ofInt_toInt])

/-- Positions at or past the card `(b.toInt - a.toInt + 1).toNat` are `none`. -/
theorem azIntRangeInclusiveGen_gen_none (a b : AzInt) (n : ℕ)
    (h : (b.toInt - a.toInt + 1).toNat ≤ n) :
    @gen _ (azIntRangeInclusiveGen a b) n = none :=
  dif_neg (by omega)

/-- Positions below the card produce a value (`≠ none`). -/
theorem azIntRangeInclusiveGen_gen_some (a b : AzInt) (n : ℕ)
    (h : n < (b.toInt - a.toInt + 1).toNat) :
    @gen _ (azIntRangeInclusiveGen a b) n ≠ none := by
  rw [show @gen _ (azIntRangeInclusiveGen a b) n = some _ from dif_pos (by omega)]
  exact Option.some_ne_none _

/-- `azIntRangeInclusiveGen a b` produces `(b.toInt - a.toInt + 1).toNat` elements
(count reused from the ascending `azIntIncreasingRangeInclusiveGen`). -/
theorem azIntRangeInclusiveGen_card (a b : AzInt) :
    Fintype.card {x : AzInt // a ≤ x ∧ x ≤ b} = (b.toInt - a.toInt + 1).toNat :=
  azIntIncreasingRangeInclusiveGen_card a b

/-! ### `AzInt` infinite magnitude-ordered rays

Malachite `exhaustive_integer_range_to_infinity` / `_range_to_negative_infinity`.
The value function dispatches on the bound's sign: when the ray already lies on
one side of `0` it is monotone (ascending/descending); otherwise it INTERLEAVES
`0, +1, -1, +2, -2, …` up to the finite side, then continues linearly on the
infinite side. Bijectivity is proved by phase/parity case analysis
(`split_ifs <;> omega`) on the `ℤ`-valued formula. -/

/-- Value formula for `[a, ∞)` in magnitude order. -/
def toInfF (a : AzInt) (n : ℕ) : ℤ :=
  if 0 ≤ a.toInt then a.toInt + (n : ℤ)
  else if n = 0 then 0
    else if (n : ℤ) ≤ 2 * (-a.toInt) then (if n % 2 = 1 then ((n : ℤ) + 1) / 2 else -((n : ℤ) / 2))
    else (n : ℤ) + a.toInt

theorem toInfF_ge (a : AzInt) (n : ℕ) : a.toInt ≤ toInfF a n := by
  unfold toInfF; split_ifs <;> omega

theorem toInfF_inj (a : AzInt) {i j : ℕ} (h : toInfF a i = toInfF a j) : i = j := by
  unfold toInfF at h; split_ifs at h <;> omega

theorem toInfF_surj (a : AzInt) (x : ℤ) (hx : a.toInt ≤ x) : ∃ n, toInfF a n = x := by
  by_cases hsign : 0 ≤ a.toInt
  · exact ⟨(x - a.toInt).toNat, by unfold toInfF; rw [if_pos hsign]; omega⟩
  · rcases lt_trichotomy x 0 with hneg | hzero | hpos
    · exact ⟨(2 * (-x)).toNat, by unfold toInfF; rw [if_neg hsign]; split_ifs <;> omega⟩
    · exact ⟨0, by unfold toInfF; rw [if_neg hsign]; simp [hzero]⟩
    · by_cases hle : x ≤ -a.toInt
      · exact ⟨(2 * x - 1).toNat, by unfold toInfF; rw [if_neg hsign]; split_ifs <;> omega⟩
      · exact ⟨(x - a.toInt).toNat, by unfold toInfF; rw [if_neg hsign]; split_ifs <;> omega⟩

/-- `[a, ∞)` over `AzInt` in magnitude order (`|x|` ascending, positive first). -/
def azIntRangeToInfinityFun (a : AzInt) : ℕ → {x : AzInt // a ≤ x} :=
  fun n => ⟨AzInt.ofInt (toInfF a n), by rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; exact toInfF_ge a n⟩

theorem azIntRangeToInfinityFun_bijective (a : AzInt) :
    Function.Bijective (azIntRangeToInfinityFun a) := by
  constructor
  · intro i j h
    have h2 := congrArg AzInt.toInt (congrArg Subtype.val h)
    rw [azIntRangeToInfinityFun, azIntRangeToInfinityFun] at h2
    simp only [AzInt.toInt_ofInt] at h2
    exact toInfF_inj a h2
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := toInfF_surj a x.toInt ((AzInt.le_iff_toInt_le a x).mp hx)
    refine ⟨n, ?_⟩
    apply Subtype.ext
    show AzInt.ofInt (toInfF a n) = x
    rw [hn, AzInt.ofInt_toInt]

/-- `[a, ∞)` over `AzInt`, magnitude order. -/
@[reducible] def azIntRangeToInfinityGen (a : AzInt) : ExhaustiveGenerator {x : AzInt // a ≤ x} :=
  ExhaustiveGenerator.ofBijective (azIntRangeToInfinityFun a) (azIntRangeToInfinityFun_bijective a)

theorem azIntRangeToInfinityGen_infinite (a : AzInt) : Infinite {x : AzInt // a ≤ x} :=
  infinite_of_bijective (azIntRangeToInfinityFun a) (azIntRangeToInfinityFun_bijective a)

/-- Value formula for `(-∞, b]` in magnitude order. -/
def toNegInfF (b : AzInt) (n : ℕ) : ℤ :=
  if b.toInt ≤ 0 then b.toInt - (n : ℤ)
  else if n = 0 then 0
    else if (n : ℤ) ≤ 2 * b.toInt then (if n % 2 = 1 then ((n : ℤ) + 1) / 2 else -((n : ℤ) / 2))
    else b.toInt - (n : ℤ)

theorem toNegInfF_le (b : AzInt) (n : ℕ) : toNegInfF b n ≤ b.toInt := by
  unfold toNegInfF; split_ifs <;> omega

theorem toNegInfF_inj (b : AzInt) {i j : ℕ} (h : toNegInfF b i = toNegInfF b j) : i = j := by
  unfold toNegInfF at h; split_ifs at h <;> omega

theorem toNegInfF_surj (b : AzInt) (x : ℤ) (hx : x ≤ b.toInt) : ∃ n, toNegInfF b n = x := by
  by_cases hsign : b.toInt ≤ 0
  · exact ⟨(b.toInt - x).toNat, by unfold toNegInfF; rw [if_pos hsign]; omega⟩
  · rcases lt_trichotomy x 0 with hneg | hzero | hpos
    · by_cases hge : -b.toInt ≤ x
      · exact ⟨(2 * (-x)).toNat, by unfold toNegInfF; rw [if_neg hsign]; split_ifs <;> omega⟩
      · exact ⟨(b.toInt - x).toNat, by unfold toNegInfF; rw [if_neg hsign]; split_ifs <;> omega⟩
    · exact ⟨0, by unfold toNegInfF; rw [if_neg hsign]; simp [hzero]⟩
    · exact ⟨(2 * x - 1).toNat, by unfold toNegInfF; rw [if_neg hsign]; split_ifs <;> omega⟩

/-- `(-∞, b]` over `AzInt` in magnitude order (`|x|` ascending, positive first). -/
def azIntRangeToNegativeInfinityFun (b : AzInt) : ℕ → {x : AzInt // x ≤ b} :=
  fun n => ⟨AzInt.ofInt (toNegInfF b n), by rw [AzInt.le_iff_toInt_le, AzInt.toInt_ofInt]; exact toNegInfF_le b n⟩

theorem azIntRangeToNegativeInfinityFun_bijective (b : AzInt) :
    Function.Bijective (azIntRangeToNegativeInfinityFun b) := by
  constructor
  · intro i j h
    have h2 := congrArg AzInt.toInt (congrArg Subtype.val h)
    rw [azIntRangeToNegativeInfinityFun, azIntRangeToNegativeInfinityFun] at h2
    simp only [AzInt.toInt_ofInt] at h2
    exact toNegInfF_inj b h2
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := toNegInfF_surj b x.toInt ((AzInt.le_iff_toInt_le x b).mp hx)
    refine ⟨n, ?_⟩
    apply Subtype.ext
    show AzInt.ofInt (toNegInfF b n) = x
    rw [hn, AzInt.ofInt_toInt]

/-- `(-∞, b]` over `AzInt`, magnitude order. -/
@[reducible] def azIntRangeToNegativeInfinityGen (b : AzInt) : ExhaustiveGenerator {x : AzInt // x ≤ b} :=
  ExhaustiveGenerator.ofBijective (azIntRangeToNegativeInfinityFun b) (azIntRangeToNegativeInfinityFun_bijective b)

theorem azIntRangeToNegativeInfinityGen_infinite (b : AzInt) : Infinite {x : AzInt // x ≤ b} :=
  infinite_of_bijective (azIntRangeToNegativeInfinityFun b) (azIntRangeToNegativeInfinityFun_bijective b)

/-! ### Guards -/

#guard (@firstN _ (azNatRangeGen (AzNat.ofNat 3) (AzNat.ofNat 7)) 10).map (·.val.toNat) = [3, 4, 5, 6]
#guard (@firstN _ (azNatRangeInclusiveGen (AzNat.ofNat 3) (AzNat.ofNat 7)) 10).map (·.val.toNat) = [3, 4, 5, 6, 7]
#guard (@firstN _ (azIntIncreasingRangeGen (AzInt.ofInt (-2)) (AzInt.ofInt 3)) 10).map (·.val.toInt) = [-2, -1, 0, 1, 2]
#guard (@firstN _ (azNatRangeToInfinityGen (AzNat.ofNat 5)) 10).map (·.val.toNat) = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
#guard (@firstN _ (azIntIncreasingRangeToInfinityGen (AzInt.ofInt (-3))) 10).map (·.val.toInt) = [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6]
#guard (@firstN _ (azIntDecreasingRangeToNegativeInfinityGen (AzInt.ofInt 3)) 10).map (·.val.toInt) = [3, 2, 1, 0, -1, -2, -3, -4, -5, -6]
-- Magnitude-ordered `AzInt` ranges (Malachite doctests).
#guard (@firstN _ (azIntRangeGen (AzInt.ofInt (-5)) (AzInt.ofInt 5)) 20).map (·.val.toInt) =
  [0, 1, -1, 2, -2, 3, -3, 4, -4, -5]
#guard (@firstN _ (azIntRangeInclusiveGen (AzInt.ofInt (-5)) (AzInt.ofInt 5)) 20).map (·.val.toInt) =
  [0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5]
#guard (@firstN _ (azIntRangeGen (AzInt.ofInt 3) (AzInt.ofInt 3)) 20).map (·.val.toInt) = []
-- Wide `AzInt` magnitude range: the closed form yields the leading interleave
-- instantly (the old materialize-and-sort would build a 2·10^12-element list).
#guard (@firstN _ (azIntRangeGen (AzInt.ofInt (-(10 ^ 12))) (AzInt.ofInt (10 ^ 12))) 7).map (·.val.toInt) =
  [0, 1, -1, 2, -2, 3, -3]
-- A deep index is O(1): position 2·10^9 in the interleave is `-(10^9)`.
#guard (@gen _ (azIntRangeGen (AzInt.ofInt (-(10 ^ 12))) (AzInt.ofInt (10 ^ 12))) (2 * 10 ^ 9)).map (·.val.toInt) =
  some (-(10 ^ 9))
-- Magnitude-ordered infinite rays (Malachite doctests).
#guard (@firstN _ (azIntRangeToInfinityGen (AzInt.ofInt (-2))) 10).map (·.val.toInt) =
  [0, 1, -1, 2, -2, 3, 4, 5, 6, 7]
#guard (@firstN _ (azIntRangeToInfinityGen (AzInt.ofInt 3)) 10).map (·.val.toInt) =
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
#guard (@firstN _ (azIntRangeToNegativeInfinityGen (AzInt.ofInt 2)) 10).map (·.val.toInt) =
  [0, 1, -1, 2, -2, -3, -4, -5, -6, -7]
-- Empty range.
#guard (@firstN _ (azNatRangeGen (AzNat.ofNat 5) (AzNat.ofNat 5)) 10).map (·.val.toNat) = []
example : Fintype.card {x : AzNat // AzNat.ofNat 5 ≤ x ∧ x < AzNat.ofNat 5} = 0 := by
  rw [azNatRangeGen_card]; simp [AzNat.toNat_ofNat]

end Azurite

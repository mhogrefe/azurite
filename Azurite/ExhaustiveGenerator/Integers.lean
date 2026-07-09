/-
  Exhaustive generators over `AzInt` (Malachite's `exhaustive_positive_integers`,
  `exhaustive_nonnegative_integers`, `exhaustive_negative_integers`).

  Each generator enumerates a half-line of the integers:
    * `positiveIntegers`    : `1, 2, 3, …`   (values `> 0`)
    * `nonnegativeIntegers` : `0, 1, 2, …`   (values `≥ 0`)
    * `negativeIntegers`    : `-1, -2, -3, …` (values `< 0`)

  As with `positiveNaturals`, a generator that skips part of `AzInt` is not an
  `ExhaustiveGenerator AzInt`; the honest fit is the corresponding order
  subtype (`{z // 0 < z}`, `{z // 0 ≤ z}`, `{z // z < 0}`), for which the
  generator is a genuine bijection with `ℕ`.
-/
import Azurite.ExhaustiveGenerator.Basic
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Equiv.Compare

namespace Azurite

/-- `toInt` is injective: `a = ofInt a.toInt = ofInt b.toInt = b`. A local
self-contained restatement (the `AzInt` core lemma of the same name is
`private`), used to reduce `AzInt` equalities to their `ℤ` images. -/
private theorem toInt_inj {a b : AzInt} (h : a.toInt = b.toInt) : a = b := by
  rw [← AzInt.ofInt_toInt a, ← AzInt.ofInt_toInt b, h]

/-! ### Positive integers `1, 2, 3, …` -/

/-- The positive-integers generator: `positiveIntegers k = AzInt.ofInt (k + 1)`,
producing `1, 2, 3, …`. -/
def positiveIntegers : ℕ → AzInt := fun k => AzInt.ofInt ((k : ℤ) + 1)

/-- `positiveIntegers k` is positive: its `toInt` is `k + 1 > 0`. -/
theorem positiveIntegers_pos (k : ℕ) : 0 < positiveIntegers k := by
  rw [AzInt.lt_iff_toInt_lt, AzInt.toInt_zero]
  simp only [positiveIntegers, AzInt.toInt_ofInt]
  omega

/-- `positiveIntegers` packaged as a map into the subtype `{z // 0 < z}`. -/
def positiveIntegersFun : ℕ → {z : AzInt // 0 < z} :=
  fun k => ⟨positiveIntegers k, positiveIntegers_pos k⟩

/-- `positiveIntegersFun` is a bijection onto the positive `AzInt`s. -/
theorem positiveIntegersFun_bijective : Function.Bijective positiveIntegersFun := by
  constructor
  · -- injective: `ofInt (k+1) = ofInt (j+1) → k+1 = j+1 → k = j`
    intro k j h
    have hv : positiveIntegers k = positiveIntegers j := congrArg Subtype.val h
    simp only [positiveIntegers] at hv
    have := congrArg AzInt.toInt hv
    rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at this
    omega
  · -- surjective: a positive `z` (`z.toInt ≥ 1`) is hit at `(z.toInt - 1).toNat`
    rintro ⟨z, hz⟩
    refine ⟨(z.toInt - 1).toNat, ?_⟩
    apply Subtype.ext
    simp only [positiveIntegersFun, positiveIntegers]
    rw [AzInt.lt_iff_toInt_lt, AzInt.toInt_zero] at hz
    have hcast : ((z.toInt - 1).toNat : ℤ) + 1 = z.toInt := by omega
    rw [hcast, AzInt.ofInt_toInt]

/-- Exhaustive generator for the positive `AzInt`s, `1, 2, 3, …`. -/
instance positiveIntegersGen : ExhaustiveGenerator {z : AzInt // 0 < z} :=
  ExhaustiveGenerator.ofBijective positiveIntegersFun positiveIntegersFun_bijective

instance : Contiguous {z : AzInt // 0 < z} :=
  ExhaustiveGenerator.contiguous_of_gen_some positiveIntegersGen rfl

/-! ### Nonnegative integers `0, 1, 2, …` -/

/-- The nonnegative-integers generator: `nonnegativeIntegers k = AzInt.ofInt k`,
producing `0, 1, 2, …`. -/
def nonnegativeIntegers : ℕ → AzInt := fun k => AzInt.ofInt (k : ℤ)

/-- `nonnegativeIntegers k` is nonnegative: its `toInt` is `k ≥ 0`. -/
theorem nonnegativeIntegers_nonneg (k : ℕ) : 0 ≤ nonnegativeIntegers k := by
  rw [AzInt.le_iff_toInt_le, AzInt.toInt_zero]
  simp only [nonnegativeIntegers, AzInt.toInt_ofInt]
  omega

/-- `nonnegativeIntegers` packaged as a map into the subtype `{z // 0 ≤ z}`. -/
def nonnegativeIntegersFun : ℕ → {z : AzInt // 0 ≤ z} :=
  fun k => ⟨nonnegativeIntegers k, nonnegativeIntegers_nonneg k⟩

/-- `nonnegativeIntegersFun` is a bijection onto the nonnegative `AzInt`s. -/
theorem nonnegativeIntegersFun_bijective :
    Function.Bijective nonnegativeIntegersFun := by
  constructor
  · -- injective: `ofInt k = ofInt j → k = j`
    intro k j h
    have hv : nonnegativeIntegers k = nonnegativeIntegers j := congrArg Subtype.val h
    simp only [nonnegativeIntegers] at hv
    have := congrArg AzInt.toInt hv
    rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at this
    omega
  · -- surjective: a nonnegative `z` (`z.toInt ≥ 0`) is hit at `z.toInt.toNat`
    rintro ⟨z, hz⟩
    refine ⟨z.toInt.toNat, ?_⟩
    apply Subtype.ext
    simp only [nonnegativeIntegersFun, nonnegativeIntegers]
    rw [AzInt.le_iff_toInt_le, AzInt.toInt_zero] at hz
    have hcast : (z.toInt.toNat : ℤ) = z.toInt := by omega
    rw [hcast, AzInt.ofInt_toInt]

/-- Exhaustive generator for the nonnegative `AzInt`s, `0, 1, 2, …`. -/
instance nonnegativeIntegersGen : ExhaustiveGenerator {z : AzInt // 0 ≤ z} :=
  ExhaustiveGenerator.ofBijective nonnegativeIntegersFun nonnegativeIntegersFun_bijective

instance : Contiguous {z : AzInt // 0 ≤ z} :=
  ExhaustiveGenerator.contiguous_of_gen_some nonnegativeIntegersGen rfl

/-! ### Negative integers `-1, -2, -3, …` -/

/-- The negative-integers generator: `negativeIntegers k = AzInt.ofInt (-(k + 1))`,
producing `-1, -2, -3, …`. -/
def negativeIntegers : ℕ → AzInt := fun k => AzInt.ofInt (-((k : ℤ) + 1))

/-- `negativeIntegers k` is negative: its `toInt` is `-(k + 1) < 0`. -/
theorem negativeIntegers_neg (k : ℕ) : negativeIntegers k < 0 := by
  rw [AzInt.lt_iff_toInt_lt, AzInt.toInt_zero]
  simp only [negativeIntegers, AzInt.toInt_ofInt]
  omega

/-- `negativeIntegers` packaged as a map into the subtype `{z // z < 0}`. -/
def negativeIntegersFun : ℕ → {z : AzInt // z < 0} :=
  fun k => ⟨negativeIntegers k, negativeIntegers_neg k⟩

/-- `negativeIntegersFun` is a bijection onto the negative `AzInt`s. -/
theorem negativeIntegersFun_bijective : Function.Bijective negativeIntegersFun := by
  constructor
  · -- injective: `ofInt (-(k+1)) = ofInt (-(j+1)) → k+1 = j+1 → k = j`
    intro k j h
    have hv : negativeIntegers k = negativeIntegers j := congrArg Subtype.val h
    simp only [negativeIntegers] at hv
    have := congrArg AzInt.toInt hv
    rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at this
    omega
  · -- surjective: a negative `z` (`z.toInt ≤ -1`) is hit at `(-z.toInt - 1).toNat`
    rintro ⟨z, hz⟩
    refine ⟨(-z.toInt - 1).toNat, ?_⟩
    apply Subtype.ext
    simp only [negativeIntegersFun, negativeIntegers]
    rw [AzInt.lt_iff_toInt_lt, AzInt.toInt_zero] at hz
    have hcast : -(((-z.toInt - 1).toNat : ℤ) + 1) = z.toInt := by omega
    rw [hcast, AzInt.ofInt_toInt]

/-- Exhaustive generator for the negative `AzInt`s, `-1, -2, -3, …`. -/
instance negativeIntegersGen : ExhaustiveGenerator {z : AzInt // z < 0} :=
  ExhaustiveGenerator.ofBijective negativeIntegersFun negativeIntegersFun_bijective

instance : Contiguous {z : AzInt // z < 0} :=
  ExhaustiveGenerator.contiguous_of_gen_some negativeIntegersGen rfl

/-! ### All integers `0, 1, -1, 2, -2, 3, -3, …` (zig-zag) -/

/-- The all-integers generator, zig-zagging outward from `0`:
`0, 1, -1, 2, -2, 3, -3, …`. Even indices go to `0, -1, -2, …`, odd indices to
`1, 2, 3, …`, so every integer (including `0`) is covered exactly once — hence
this is a genuine `ExhaustiveGenerator AzInt` on the full type. -/
def integers : ℕ → AzInt :=
  fun n => AzInt.ofInt (if n % 2 = 0 then -(n / 2 : ℤ) else ((n / 2 : ℤ) + 1))

/-- `integers` is a bijection `ℕ ≃ AzInt`: same-parity indices collide only when
equal, cross-parity indices land on disjoint half-lines, and every integer is
reached (`z ≤ 0` at `2·(-z)`, `z ≥ 1` at `2·z - 1`). -/
theorem integers_bijective : Function.Bijective integers := by
  constructor
  · -- injective: same-parity forces equality, cross-parity can't collide
    intro a b h
    simp only [integers] at h
    have h2 := congrArg AzInt.toInt h
    rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at h2
    split_ifs at h2 <;> omega
  · -- surjective: `z ≤ 0` hit at `2·(-z)`, `z ≥ 1` hit at `2·z - 1`
    intro z
    by_cases hz : z.toInt ≤ 0
    · exact ⟨(2 * (-z.toInt)).toNat, by
        apply toInt_inj
        simp only [integers, AzInt.toInt_ofInt]
        split_ifs <;> omega⟩
    · exact ⟨(2 * z.toInt - 1).toNat, by
        apply toInt_inj
        simp only [integers, AzInt.toInt_ofInt]
        split_ifs <;> omega⟩

/-- Exhaustive generator for all of `AzInt`, `0, 1, -1, 2, -2, …`. -/
instance integersGen : ExhaustiveGenerator AzInt :=
  ExhaustiveGenerator.ofBijective integers integers_bijective

instance : Contiguous AzInt := ExhaustiveGenerator.contiguous_of_gen_some integersGen rfl

/-! ### Nonzero integers `1, -1, 2, -2, 3, -3, …` (zig-zag) -/

/-- The nonzero-integers generator, zig-zagging outward from `1`/`-1`:
`1, -1, 2, -2, 3, -3, …`. Even indices go to `1, 2, 3, …`, odd indices to
`-1, -2, -3, …`, so `0` is never produced and every nonzero integer is covered
exactly once — the honest fit is the subtype `{z // z ≠ 0}`. -/
def nonzeroIntegers : ℕ → AzInt :=
  fun n => AzInt.ofInt (if n % 2 = 0 then ((n / 2 : ℤ) + 1) else -((n / 2 : ℤ) + 1))

/-- `nonzeroIntegers n` is never zero: even indices give `≥ 1`, odd give `≤ -1`. -/
theorem nonzeroIntegers_ne_zero (n : ℕ) : nonzeroIntegers n ≠ 0 := by
  simp only [nonzeroIntegers]
  intro h
  have h2 := congrArg AzInt.toInt h
  rw [AzInt.toInt_ofInt, AzInt.toInt_zero] at h2
  split_ifs at h2 <;> omega

/-- `nonzeroIntegers` packaged as a map into the subtype `{z // z ≠ 0}`. -/
def nonzeroIntegersFun : ℕ → {z : AzInt // z ≠ 0} :=
  fun n => ⟨nonzeroIntegers n, nonzeroIntegers_ne_zero n⟩

/-- `nonzeroIntegersFun` is a bijection onto the nonzero `AzInt`s. -/
theorem nonzeroIntegersFun_bijective : Function.Bijective nonzeroIntegersFun := by
  constructor
  · -- injective: same-parity forces equality, cross-parity can't collide
    intro a b h
    have hv : nonzeroIntegers a = nonzeroIntegers b := congrArg Subtype.val h
    simp only [nonzeroIntegers] at hv
    have h2 := congrArg AzInt.toInt hv
    rw [AzInt.toInt_ofInt, AzInt.toInt_ofInt] at h2
    split_ifs at h2 <;> omega
  · -- surjective: `z ≥ 1` hit at `2·(z-1)`, `z ≤ -1` hit at `-2·z - 1`
    rintro ⟨z, hz⟩
    have hz0 : z.toInt ≠ 0 := fun h0 =>
      hz (by rw [← AzInt.ofInt_toInt z, h0, AzInt.ofInt_zero])
    by_cases hpos : 0 < z.toInt
    · exact ⟨(2 * (z.toInt - 1)).toNat, Subtype.ext (by
        apply toInt_inj
        simp only [nonzeroIntegersFun, nonzeroIntegers, AzInt.toInt_ofInt]
        split_ifs <;> omega)⟩
    · exact ⟨(-2 * z.toInt - 1).toNat, Subtype.ext (by
        apply toInt_inj
        simp only [nonzeroIntegersFun, nonzeroIntegers, AzInt.toInt_ofInt]
        split_ifs <;> omega)⟩

/-- Exhaustive generator for the nonzero `AzInt`s, `1, -1, 2, -2, …`. -/
instance nonzeroIntegersGen : ExhaustiveGenerator {z : AzInt // z ≠ 0} :=
  ExhaustiveGenerator.ofBijective nonzeroIntegersFun nonzeroIntegersFun_bijective

instance : Contiguous {z : AzInt // z ≠ 0} :=
  ExhaustiveGenerator.contiguous_of_gen_some nonzeroIntegersGen rfl

-- Demonstrate the three generators produce Malachite's doctest sequences.
#guard (positiveIntegers 0).toInt == 1
#guard (positiveIntegers 9).toInt == 10
#guard (nonnegativeIntegers 0).toInt == 0
#guard (nonnegativeIntegers 9).toInt == 9
#guard (negativeIntegers 0).toInt == -1
#guard (negativeIntegers 9).toInt == -10
#guard ((ExhaustiveGenerator.firstN {z : AzInt // 0 < z} 10).map (·.val.toInt)) ==
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#guard ((ExhaustiveGenerator.firstN {z : AzInt // 0 ≤ z} 10).map (·.val.toInt)) ==
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
#guard ((ExhaustiveGenerator.firstN {z : AzInt // z < 0} 10).map (·.val.toInt)) ==
  [-1, -2, -3, -4, -5, -6, -7, -8, -9, -10]

-- The two zig-zag generators, previewed via `firstN` (Malachite doctests).
#guard ((ExhaustiveGenerator.firstN AzInt 10).map (·.toInt)) ==
  [0, 1, -1, 2, -2, 3, -3, 4, -4, 5]
#guard ((ExhaustiveGenerator.firstN {z : AzInt // z ≠ 0} 10).map (·.val.toInt)) ==
  [1, -1, 2, -2, 3, -3, 4, -4, 5, -5]

end Azurite

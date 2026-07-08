/-
  `exhaustivePositiveNaturals` — the exhaustive generator producing all
  POSITIVE `AzNat`s in the order `1, 2, 3, …` (Malachite's
  `exhaustive_positive_naturals`).

  Since `0` is never produced, this is NOT an `ExhaustiveGenerator AzNat`
  (that would require `0` to occur). The honest fit is the positive-`AzNat`
  subtype `{n : AzNat // 0 < n}`, for which the generator is a genuine
  bijection with `ℕ`.
-/
import Azurite.ExhaustiveGenerator.Basic
import Azurite.AzNat.Equiv.Compare

namespace Azurite

/-- `AzNat.ofNat (k + 1)` is positive: its `toNat` is `k + 1 > 0`. -/
theorem ofNat_succ_pos (k : ℕ) : 0 < AzNat.ofNat (k + 1) := by
  rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_zero, AzNat.toNat_ofNat]
  exact Nat.succ_pos k

/-- The positive-naturals generator: `positiveNaturals k = AzNat.ofNat (k + 1)`,
producing `1, 2, 3, …`. -/
def positiveNaturals : ℕ → AzNat := fun k => AzNat.ofNat (k + 1)

/-- `positiveNaturals` packaged as a map into the positive-`AzNat` subtype. -/
def positiveNaturalsFun : ℕ → {n : AzNat // 0 < n} :=
  fun k => ⟨AzNat.ofNat (k + 1), ofNat_succ_pos k⟩

/-- `positiveNaturalsFun` is a bijection: the enumeration `1, 2, 3, …` hits every
positive `AzNat` exactly once. -/
theorem positiveNaturalsFun_bijective : Function.Bijective positiveNaturalsFun := by
  constructor
  · -- injective: `ofNat (k+1) = ofNat (j+1) → k+1 = j+1 → k = j`
    intro k j h
    have hval : AzNat.ofNat (k + 1) = AzNat.ofNat (j + 1) := congrArg Subtype.val h
    have := congrArg AzNat.toNat hval
    rw [AzNat.toNat_ofNat, AzNat.toNat_ofNat] at this
    omega
  · -- surjective: a positive `a` has `1 ≤ a.toNat`, so `fun (a.toNat - 1) = a`
    rintro ⟨a, ha⟩
    refine ⟨a.toNat - 1, ?_⟩
    apply Subtype.ext
    show AzNat.ofNat (a.toNat - 1 + 1) = a
    rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_zero] at ha
    rw [Nat.sub_add_cancel ha, AzNat.ofNat_toNat]

/-- The exhaustive generator for the positive `AzNat`s, `1, 2, 3, …`. -/
instance positiveNaturalsGen : ExhaustiveGenerator {n : AzNat // 0 < n} :=
  ExhaustiveGenerator.ofBijective positiveNaturalsFun positiveNaturalsFun_bijective

-- Demonstrate the positive-naturals generator produces `1, 2, 3, …, 10`
-- (Malachite's `exhaustive_positive_naturals` doctest).
#guard (positiveNaturals 0).toNat == 1
#guard (positiveNaturals 1).toNat == 2
#guard (positiveNaturals 9).toNat == 10
#guard ((ExhaustiveGenerator.firstN {n : AzNat // 0 < n} 10).map (·.val.toNat)) ==
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

end Azurite

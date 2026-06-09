import Azurite.AzRat.Basic
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzNat.Equiv.Basic
import Mathlib.Data.Rat.Defs

/-!
# Equivalence: `AzRat` ↔ `ℚ`

Conversions `toRat : AzRat → ℚ` and `ofRat : ℚ → AzRat` (both computable, since `ℚ` is a
computable type), with round-trip equivalence in both directions (`toRat_ofRat`, `ofRat_toRat`).

`toRat` builds the `ℚ` directly with `Rat.mk'` from the signed numerator and denominator: the
nonzero-denominator and coprimality invariants of `AzRat` are exactly what `Rat.mk'` needs (via
`AzNat.coprime_iff`), so the resulting `ℚ` has those `num`/`den` by construction.
-/

namespace Azurite.AzRat

/-- The exact `ℚ` represented by an `AzRat`. -/
def toRat (q : AzRat) : ℚ :=
  Rat.mk' (if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) q.den.toNat
    (fun h => q.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)))
    (by
      have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
      cases hs : q.sign <;> simpa using hcop)

/-- The `AzRat` representing a given `ℚ`. -/
def ofRat (r : ℚ) : AzRat where
  sign := decide (0 ≤ r.num)
  num := AzNat.ofNat r.num.natAbs
  den := AzNat.ofNat r.den
  den_nz := fun h => r.den_nz (by
    have := congrArg AzNat.toNat h
    rwa [AzNat.toNat_ofNat, AzNat.toNat_zero] at this)
  zero_sign := fun h => by
    have h1 : r.num.natAbs = 0 := by
      have := congrArg AzNat.toNat h
      rwa [AzNat.toNat_ofNat, AzNat.toNat_zero] at this
    rw [Int.natAbs_eq_zero.mp h1]; rfl
  reduced := (AzNat.coprime_iff _ _).mpr (by
    rw [AzNat.toNat_ofNat, AzNat.toNat_ofNat]; exact r.reduced)

/-- Round-trip `ℚ → AzRat → ℚ`. -/
theorem toRat_ofRat (r : ℚ) : toRat (ofRat r) = r := by
  apply Rat.ext
  · show (if (decide (0 ≤ r.num)) then ((AzNat.ofNat r.num.natAbs).toNat : ℤ)
            else -((AzNat.ofNat r.num.natAbs).toNat : ℤ)) = r.num
    rw [AzNat.toNat_ofNat]
    split
    · rename_i h; rw [decide_eq_true_eq] at h
      exact Int.natAbs_of_nonneg h
    · rename_i h; rw [decide_eq_true_eq] at h
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt (not_le.mp h)), neg_neg]
  · show (AzNat.ofNat r.den).toNat = r.den
    rw [AzNat.toNat_ofNat]

/-- Round-trip `AzRat → ℚ → AzRat`. -/
theorem ofRat_toRat (q : AzRat) : ofRat (toRat q) = q := by
  have hnum : (toRat q).num = if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ) := rfl
  have hden : (toRat q).den = q.den.toNat := rfl
  apply AzRat.ext
  · -- sign
    show decide (0 ≤ (toRat q).num) = q.sign
    rw [hnum]
    cases hs : q.sign
    · have hnz' : q.num.toNat ≠ 0 := by
        intro h
        have hz : q.num = 0 := AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)
        rw [q.zero_sign hz] at hs; exact absurd hs (by decide)
      simp only [Bool.false_eq_true, if_false, decide_eq_false_iff_not]
      omega
    · simp only [if_true, decide_eq_true_eq]; omega
  · -- num
    show AzNat.ofNat (toRat q).num.natAbs = q.num
    rw [hnum]
    cases hs : q.sign <;>
      simp only [Bool.false_eq_true, if_false, if_true, Int.natAbs_neg, Int.natAbs_natCast] <;>
      exact AzNat.ofNat_toNat q.num
  · -- den
    show AzNat.ofNat (toRat q).den = q.den
    rw [hden, AzNat.ofNat_toNat]

-- Both conversions compute.
#guard toRat (ofRat (3 / 4)) == (3 / 4 : ℚ)
#guard toRat (ofRat (-7 / 12)) == (-7 / 12 : ℚ)
#guard toRat (ofRat 0) == (0 : ℚ)
#guard toRat (ofRat 5) == (5 : ℚ)
#guard ofRat (toRat (ofRat (-2 / 9))) == ofRat (-2 / 9)

end Azurite.AzRat

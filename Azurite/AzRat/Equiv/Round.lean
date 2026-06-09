import Azurite.AzRat.Round
import Azurite.AzRat.Equiv.Basic
import Azurite.AzInt.Equiv.DivRound
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Conversion

/-!
# Correctness of `AzRat.round`

`AzRat.round q mode` returns `(v, ord)` where `v` agrees with the abstract
`RoundingTarget.round` of the real number `(toRat q : ℝ)` against the integer rounding
target `intSet`, and `ord` records how `v` compares to `toRat q`. Both reduce to the
correctness of `AzInt.divRound` once the signed numerator / denominator ratio is identified
with `toRat q` via `Rat.cast_def`.
-/

namespace Azurite
open RoundingTarget AzInt

/-- The denominator lifted to `AzInt` has positive magnitude. -/
private lemma round_den_pos (q : AzRat) : 0 < (q.den.toAzInt).abs.toNat := by
  show 0 < q.den.toNat
  rcases Nat.eq_zero_or_pos q.den.toNat with h | h
  · exact absurd (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)) q.den_nz
  · exact h

/-- The signed-numerator / lifted-denominator real ratio is exactly `toRat q`. -/
private lemma round_ratio_eq (q : AzRat) :
    ((mkNorm q.sign q.num).toInt : ℝ) / ((q.den.toAzInt).toInt : ℝ) =
      ((AzRat.toRat q : ℚ) : ℝ) := by
  -- The signed numerator built by `mkNorm` is the numerator of `toRat q`.
  have hnumI : (mkNorm q.sign q.num).toInt = (AzRat.toRat q).num := by
    have hrfl : (AzRat.toRat q).num
        = if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ) := rfl
    rw [hrfl]
    cases hs : q.sign with
    | false =>
      have hnz : q.num ≠ 0 := by
        intro h
        have hsig := q.zero_sign h
        rw [hs] at hsig
        exact absurd hsig (by decide)
      rw [AzInt.toInt_mkNorm_false q.num hnz]; simp
    | true => rw [AzInt.toInt_mkNorm_true q.num]; simp
  -- The lifted denominator's `toInt` is the denominator of `toRat q`.
  have hdenI : (q.den.toAzInt).toInt = ((AzRat.toRat q).den : ℤ) := by
    rw [Azurite.AzNat.toInt_toAzInt]; rfl
  rw [hnumI, hdenI, Rat.cast_def, Int.cast_natCast]

/-- **Value correctness of `AzRat.round`.** The rounded `AzInt` agrees with abstractly
rounding the real number `(toRat q : ℝ)` to the integers. -/
theorem AzRat.toInt_round (q : AzRat) (mode : RoundingMode) :
    (((q.round mode).1.toInt : ℝ) : EReal) =
      (RoundingTarget.round intSet mode ((AzRat.toRat q : ℚ) : ℝ)).val := by
  unfold AzRat.round
  rw [AzInt.toInt_divRound (mkNorm q.sign q.num) q.den.toAzInt mode (round_den_pos q),
      round_ratio_eq q]

/-- **Ordering tag correctness for `AzRat.round`.** The second component records how the
rounded value compares to the true value `toRat q`: `.lt` if below, `.eq` if equal,
`.gt` if above. -/
theorem AzRat.snd_round (q : AzRat) (mode : RoundingMode) :
    (q.round mode).2 =
      compare (((q.round mode).1.toInt : ℤ) : ℝ) ((AzRat.toRat q : ℚ) : ℝ) := by
  unfold AzRat.round
  rw [AzInt.snd_divRound (mkNorm q.sign q.num) q.den.toAzInt mode (round_den_pos q),
      round_ratio_eq q]

end Azurite

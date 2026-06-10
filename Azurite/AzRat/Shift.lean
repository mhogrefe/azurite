import Azurite.AzRat.Construct
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.TrailingZeros
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.TrailingZeros
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Shifts for `AzRat`: multiplication and division by powers of two

`q <<< n` multiplies by `2^n` and `q >>> n` divides by `2^n`, with **no gcd
computation**: since `q` is in lowest terms, the only common factor a shift
can create is a power of two on the other side of the fraction. Splitting the
shift at `k = min n v₂(·)` (the 2-adic valuation, read off in limb time by
`AzNat.trailingZeros`) gives an exact shift on one component and a pure shift
on the other:

* `q <<< n` divides the denominator by `2^k` (`k = min n v₂(den)`, exact) and
  multiplies the numerator by `2^(n-k)`;
* `q >>> n` divides the numerator by `2^k` (`k = min n v₂(num)`, exact) and
  multiplies the denominator by `2^(n-k)`.

The result is already reduced (`coprime_shift`): the surviving power of two is
coprime to the now-odd (or untouched) other side.
-/

namespace Azurite.AzRat

/-- The `ℕ`-level core of shift reduction: with `a ⊥ b` and the shift split at
`k = min n v₂(b)`, the fraction `(a·2^(n-k)) / (b/2^k)` is in lowest terms. -/
theorem coprime_shift {a b : ℕ} (n : ℕ) (hab : Nat.Coprime a b) (hb : b ≠ 0) :
    Nat.Coprime (a * 2 ^ (n - min n (padicValNat 2 b)))
      (b / 2 ^ min n (padicValNat 2 b)) := by
  have hdvd : 2 ^ min n (padicValNat 2 b) ∣ b :=
    dvd_trans (pow_dvd_pow 2 (min_le_right _ _)) pow_padicValNat_dvd
  have h1 : Nat.Coprime a (b / 2 ^ min n (padicValNat 2 b)) :=
    hab.coprime_dvd_right (Nat.div_dvd_of_dvd hdvd)
  have h2 : Nat.Coprime (2 ^ (n - min n (padicValNat 2 b)))
      (b / 2 ^ min n (padicValNat 2 b)) := by
    rcases Nat.le_total n (padicValNat 2 b) with h | h
    · rw [min_eq_left h, Nat.sub_self, pow_zero]
      exact Nat.coprime_one_left _
    · rw [min_eq_right h]
      have hoc : Nat.Coprime 2 (b / 2 ^ b.factorization 2) :=
        Nat.coprime_ordCompl Nat.prime_two hb
      rw [Nat.factorization_def b Nat.prime_two] at hoc
      exact Nat.Coprime.pow_left _ hoc
  exact Nat.Coprime.mul_left h1 h2

/-- `q <<< n = q · 2^n`: divide the denominator by `2^k` (`k = min n v₂(den)`,
an exact limb-level shift) and multiply the numerator by `2^(n-k)`. No gcd is
computed; the valuation is read off by `AzNat.trailingZeros`. -/
protected def shiftLeft (x : AzRat) (n : Nat) : AzRat :=
  let k := min n ((x.den.trailingZeros).getD 0)
  have hk : k = min n (padicValNat 2 x.den.toNat) := by
    show min n ((x.den.trailingZeros).getD 0) = _
    rw [AzNat.trailingZeros_eq_padicValNat x.den x.den_nz]
    rfl
  have hdvd : 2 ^ k ∣ x.den.toNat := by
    rw [hk]
    exact dvd_trans (pow_dvd_pow 2 (min_le_right _ _)) pow_padicValNat_dvd
  { sign := x.sign
    num := x.num <<< (n - k)
    den := x.den >>> k
    den_nz := fun h => by
      have h0 := congrArg AzNat.toNat h
      rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow, AzNat.toNat_zero] at h0
      exact absurd h0 (Nat.ne_of_gt (Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero fun hd =>
          x.den_nz (AzNat.toNat_injective (hd.trans AzNat.toNat_zero.symm))) hdvd)
        (Nat.two_pow_pos _)))
    zero_sign := fun h => by
      have h0 := congrArg AzNat.toNat h
      rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_zero] at h0
      rcases Nat.mul_eq_zero.mp h0 with h0 | h0
      · exact x.zero_sign (AzNat.toNat_injective (h0.trans AzNat.toNat_zero.symm))
      · exact absurd h0 (Nat.two_pow_pos _).ne'
    reduced := (AzNat.coprime_iff _ _).mpr (by
      rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_hShiftRight,
          Nat.shiftRight_eq_div_pow, hk]
      exact coprime_shift n ((AzNat.coprime_iff _ _).mp x.reduced) (fun hd =>
        x.den_nz (AzNat.toNat_injective (hd.trans AzNat.toNat_zero.symm)))) }

instance : HShiftLeft AzRat Nat AzRat := ⟨AzRat.shiftLeft⟩

/-- `q >>> n = q / 2^n`: divide the numerator by `2^k` (`k = min n v₂(num)`,
an exact limb-level shift) and multiply the denominator by `2^(n-k)`. No gcd
is computed. -/
protected def shiftRight (x : AzRat) (n : Nat) : AzRat :=
  if hx : x.num = 0 then 0
  else
    let k := min n ((x.num.trailingZeros).getD 0)
    have hk : k = min n (padicValNat 2 x.num.toNat) := by
      show min n ((x.num.trailingZeros).getD 0) = _
      rw [AzNat.trailingZeros_eq_padicValNat x.num hx]
      rfl
    have hxn : x.num.toNat ≠ 0 :=
      fun h => hx (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hdvd : 2 ^ k ∣ x.num.toNat := by
      rw [hk]
      exact dvd_trans (pow_dvd_pow 2 (min_le_right _ _)) pow_padicValNat_dvd
    { sign := x.sign
      num := x.num >>> k
      den := x.den <<< (n - k)
      den_nz := fun h => by
        have h0 := congrArg AzNat.toNat h
        rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_zero] at h0
        rcases Nat.mul_eq_zero.mp h0 with h0 | h0
        · exact x.den_nz (AzNat.toNat_injective (h0.trans AzNat.toNat_zero.symm))
        · exact absurd h0 (Nat.two_pow_pos _).ne'
      zero_sign := fun h => by
        have h0 := congrArg AzNat.toNat h
        rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow, AzNat.toNat_zero] at h0
        exact absurd h0 (Nat.ne_of_gt (Nat.div_pos
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hxn) hdvd)
          (Nat.two_pow_pos _)))
      reduced := (AzNat.coprime_iff _ _).mpr (by
        rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow, AzNat.toNat_hShiftLeft,
          Nat.shiftLeft_eq, hk]
        exact Nat.Coprime.symm (coprime_shift n
          (Nat.Coprime.symm ((AzNat.coprime_iff _ _).mp x.reduced)) hxn)) }

instance : HShiftRight AzRat Nat AzRat := ⟨AzRat.shiftRight⟩

end Azurite.AzRat

namespace Azurite

-- Sanity checks (string-anchored via `AzRat.parse`/`AzRat.toString`).

#guard ((fun (q : AzRat) => AzRat.toString (q <<< 2)) <$> AzRat.parse "3/8") == some "3/2"
#guard ((fun (q : AzRat) => AzRat.toString (q <<< 5)) <$> AzRat.parse "3/8") == some "12"
#guard ((fun (q : AzRat) => AzRat.toString (q <<< 1)) <$> AzRat.parse "5/3") == some "10/3"
#guard ((fun (q : AzRat) => AzRat.toString (q <<< 3)) <$> AzRat.parse "-3/8") == some "-3"
#guard ((fun (q : AzRat) => AzRat.toString (q <<< 4)) <$> AzRat.parse "0") == some "0"
#guard ((fun (q : AzRat) => AzRat.toString (q >>> 2)) <$> AzRat.parse "12/5") == some "3/5"
#guard ((fun (q : AzRat) => AzRat.toString (q >>> 1)) <$> AzRat.parse "3/5") == some "3/10"
#guard ((fun (q : AzRat) => AzRat.toString (q >>> 5)) <$> AzRat.parse "8") == some "1/4"
#guard ((fun (q : AzRat) => AzRat.toString (q >>> 3)) <$> AzRat.parse "-12/5") == some "-3/10"
#guard ((fun (q : AzRat) => AzRat.toString (q >>> 3)) <$> AzRat.parse "0") == some "0"

end Azurite

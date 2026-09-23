import Azurite.AzRat.Shift
import Azurite.AzRat.Equiv.Unary
import Mathlib.Tactic.LinearCombination

/-!
# Correctness of the `AzRat` shifts

`toRat_shiftLeft` / `toRat_shiftRight` (and the `ofRat` converses): the
gcd-free shifts compute exactly multiplication and division by `2^n` in `ℚ`.
The proofs follow the multiplication playbook — `divInt` normal form,
`Rat.divInt_mul_divInt`, `Rat.divInt_eq_divInt_iff` — with the cross identity
reduced to a `ℕ` calculation (`shl_cross`/`shr_cross`) that reassembles the
split shift: undo the exact division by `2^k` and merge `2^(n-k) · 2^k` back
into `2^n`.
-/

namespace Azurite.AzRat

/-- `ℕ`-level cross identity for `<<<`: undo the exact division and merge
the split powers of two. -/
private lemma shl_cross {A D k n : ℕ} (hdvd : 2 ^ k ∣ D) (hkn : k ≤ n) :
    A * 2 ^ (n - k) * D = A * 2 ^ n * (D / 2 ^ k) := by
  have hsplit : D / 2 ^ k * 2 ^ k = D := Nat.div_mul_cancel hdvd
  calc A * 2 ^ (n - k) * D
      = A * 2 ^ (n - k) * (D / 2 ^ k * 2 ^ k) := by rw [hsplit]
    _ = A * (2 ^ (n - k) * 2 ^ k) * (D / 2 ^ k) := by ring
    _ = A * 2 ^ n * (D / 2 ^ k) := by rw [← pow_add, Nat.sub_add_cancel hkn]

/-- `ℕ`-level cross identity for `>>>`. -/
private lemma shr_cross {A B k n : ℕ} (hdvd : 2 ^ k ∣ A) (hkn : k ≤ n) :
    A / 2 ^ k * (B * 2 ^ n) = A * (B * 2 ^ (n - k)) := by
  have hsplit : A / 2 ^ k * 2 ^ k = A := Nat.div_mul_cancel hdvd
  calc A / 2 ^ k * (B * 2 ^ n)
      = A / 2 ^ k * (B * (2 ^ k * 2 ^ (n - k))) := by
        rw [← pow_add, Nat.add_sub_cancel' hkn]
    _ = A / 2 ^ k * 2 ^ k * (B * 2 ^ (n - k)) := by ring
    _ = A * (B * 2 ^ (n - k)) := by rw [hsplit]

@[simp] theorem toRat_shiftLeft (q : AzRat) (n : ℕ) :
    toRat (q <<< n) = toRat q * 2 ^ n := by
  show toRat (AzRat.shiftLeft q n) = _
  have hk0 : (q.den.trailingZeros).getD 0 = padicValNat 2 q.den.toNat := by
    rw [AzNat.trailingZeros_eq_padicValNat q.den q.den_nz]
    rfl
  have hdN : q.den.toNat ≠ 0 :=
    fun h => q.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hdvd : 2 ^ min n ((q.den.trailingZeros).getD 0) ∣ q.den.toNat := by
    rw [hk0]
    exact dvd_trans (pow_dvd_pow 2 (min_le_right _ _)) pow_padicValNat_dvd
  have hz1 : ((q.den >>> min n ((q.den.trailingZeros).getD 0)).toNat : ℤ) ≠ 0 := by
    rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
    exact Int.natCast_ne_zero.mpr (Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hdN) hdvd) (Nat.two_pow_pos _)))
  have hz2 : ((q.den.toNat : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr hdN
  have hzZ : ((q.num.toNat : ℤ)) * 2 ^ (n - min n ((q.den.trailingZeros).getD 0)) *
        (q.den.toNat : ℤ)
      = (q.num.toNat : ℤ) * 2 ^ n *
        ((q.den.toNat / 2 ^ min n ((q.den.trailingZeros).getD 0) : ℕ) : ℤ) := by
    exact_mod_cast shl_cross hdvd (min_le_left _ _)
  rw [AzRat.shiftLeft, toRat_eq_divInt, toRat_eq_divInt q,
      show ((2 : ℚ) ^ n) = Rat.divInt (2 ^ n) 1 by rw [Rat.divInt_one]; push_cast; ring,
      Rat.divInt_mul_divInt, mul_one]
  dsimp only
  rw [Rat.divInt_eq_divInt_iff hz1 hz2]
  simp only [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_hShiftRight,
    Nat.shiftRight_eq_div_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs <;>
    first
      | linear_combination hzZ
      | linear_combination -hzZ

@[simp] theorem toRat_shiftRight (q : AzRat) (n : ℕ) :
    toRat (q >>> n) = toRat q / 2 ^ n := by
  show toRat (AzRat.shiftRight q n) = _
  by_cases hx : q.num = 0
  · rw [AzRat.shiftRight, dite_eq_left hx, toRat_zero, toRat_of_num_zero q hx, zero_div]
  have hk0 : (q.num.trailingZeros).getD 0 = padicValNat 2 q.num.toNat := by
    rw [AzNat.trailingZeros_eq_padicValNat q.num hx]
    rfl
  have hnN : q.num.toNat ≠ 0 :=
    fun h => hx (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hdN : q.den.toNat ≠ 0 :=
    fun h => q.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hdvd : 2 ^ min n ((q.num.trailingZeros).getD 0) ∣ q.num.toNat := by
    rw [hk0]
    exact dvd_trans (pow_dvd_pow 2 (min_le_right _ _)) pow_padicValNat_dvd
  have hz1 : ((q.den <<< (n - min n ((q.num.trailingZeros).getD 0))).toNat : ℤ) ≠ 0 := by
    rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
    exact Int.natCast_ne_zero.mpr (Nat.mul_ne_zero hdN (Nat.two_pow_pos _).ne')
  have hz2 : ((q.den.toNat : ℤ)) * 2 ^ n ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr hdN) (pow_ne_zero _ (by decide))
  have hzZ : ((q.num.toNat / 2 ^ min n ((q.num.trailingZeros).getD 0) : ℕ) : ℤ) *
        ((q.den.toNat : ℤ) * 2 ^ n)
      = (q.num.toNat : ℤ) *
        ((q.den.toNat : ℤ) * 2 ^ (n - min n ((q.num.trailingZeros).getD 0))) := by
    exact_mod_cast shr_cross hdvd (min_le_left _ _)
  rw [AzRat.shiftRight, dite_eq_right hx, toRat_eq_divInt, toRat_eq_divInt q, div_eq_mul_inv,
      show ((2 : ℚ) ^ n)⁻¹ = Rat.divInt 1 (2 ^ n) by
        rw [show ((2 : ℚ) ^ n) = Rat.divInt (2 ^ n) 1 by
              rw [Rat.divInt_one]; push_cast; ring,
            Rat.inv_divInt],
      Rat.divInt_mul_divInt, mul_one]
  dsimp only
  rw [Rat.divInt_eq_divInt_iff hz1 hz2]
  simp only [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_hShiftRight,
    Nat.shiftRight_eq_div_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs <;>
    first
      | linear_combination hzZ
      | linear_combination -hzZ

@[simp] theorem ofRat_shiftLeft (r : ℚ) (n : ℕ) :
    ofRat (r * 2 ^ n) = ofRat r <<< n :=
  toRat_injective (by rw [toRat_ofRat, toRat_shiftLeft, toRat_ofRat])

@[simp] theorem ofRat_shiftRight (r : ℚ) (n : ℕ) :
    ofRat (r / 2 ^ n) = ofRat r >>> n :=
  toRat_injective (by rw [toRat_ofRat, toRat_shiftRight, toRat_ofRat])

end Azurite.AzRat

import Azurite.AzNat.NormalizedCompare
import Azurite.AzNat.Equiv.ShiftRight

/-!
# Correctness of the allocation-free `normalizedCompare`

`normalizedCompare_eq_cross`: for positive inputs, `normalizedCompare x y` equals the
cross-multiplication comparison `compare (x.toNat · 2^(size y)) (y.toNat · 2^(size x))` — i.e. it
compares the normalized fractions `x / 2^(size x)` and `y / 2^(size y)`. The proof is
self-contained, working directly from the limb loop.

The core is `cmpShiftedLimbs_eq`: the limb loop computes the radix-`2^64` comparison of
`x.toNat · 2^shift` and `y.toNat`, with each on-the-fly limb read (`shiftedLimb`) equal to the
corresponding limb of the (never materialised) shifted value (`toNat_shiftedLimb`).
-/

namespace Azurite.AzNat

/-- The on-the-fly limb read equals the real `k`-th limb of `a · 2^(64q+r)`. -/
theorem toNat_shiftedLimb (a : AzNat) (q r k : Nat) (hr : r < 64) :
    (shiftedLimb a q r k hr).toNat = a.toNat * 2 ^ (64 * q + r) / 2 ^ (64 * k) % 2 ^ 64 := by
  unfold shiftedLimb
  split
  · -- k < q : the limb is entirely inside the zero region, value 0
    rename_i hk
    have hle : 64 * k ≤ 64 * q + r := by omega
    have hrhs : a.toNat * 2 ^ (64 * q + r) / 2 ^ (64 * k) % 2 ^ 64 = 0 := by
      rw [Nat.mul_div_assoc _ (pow_dvd_pow 2 hle), Nat.pow_div hle (by norm_num),
        show 64 * q + r - 64 * k = 64 + (64 * q + r - 64 * k - 64) by omega, pow_add,
        mul_left_comm, Nat.mul_mod_right]
    rw [hrhs]; rfl
  · split
    · -- k = q : the boundary limb is `a`'s low (64-r) bits shifted up by r
      rename_i hk1 hk2
      rw [hk2, UInt64.toNat_shiftLeft, toNat_getBitsAsLimb]
      have hofn : (UInt64.ofNat r).toNat % 64 = r := by rw [UInt64.toNat_ofNat']; omega
      rw [hofn]
      simp only [pow_zero, Nat.div_one, Nat.sub_zero, Nat.shiftLeft_eq]
      have hmul : a.toNat * 2 ^ (64 * q + r) / 2 ^ (64 * q) = a.toNat * 2 ^ r := by
        rw [pow_add, ← mul_assoc, mul_comm a.toNat (2 ^ (64 * q)), mul_assoc,
          Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
      rw [hmul, show (2 : ℕ) ^ 64 = 2 ^ (64 - r) * 2 ^ r by rw [← pow_add]; congr 1; omega,
        Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, Nat.mod_mod]
    · -- k > q : a straddling 64-bit window of `a`
      rename_i hk1 hk2
      have hkq : q < k := by omega
      rw [toNat_getBitsAsLimb, show 64 * (k - q) - r + 64 - (64 * (k - q) - r) = 64 by omega]
      congr 1
      rw [show (2 : ℕ) ^ (64 * k) = 2 ^ (64 * q + r) * 2 ^ (64 * (k - q) - r) by
            rw [← pow_add]; congr 1; omega,
        mul_comm a.toNat (2 ^ (64 * q + r)), Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]

private lemma ordNat (s t : ℕ) :
    Ord.compare s t = if s < t then Ordering.lt else if s = t then Ordering.eq else Ordering.gt :=
  rfl

/-- Lexicographic comparison of two-"digit" numbers `hi · m + lo` (with `lo < m`): the high digit
decides, the low digit breaks ties. -/
private lemma ordCompare_lex (hiA loA hiB loB m : ℕ) (hloA : loA < m) (hloB : loB < m) :
    Ord.compare (hiA * m + loA) (hiB * m + loB) =
      (match Ord.compare hiA hiB with
       | Ordering.eq => Ord.compare loA loB
       | o => o) := by
  rcases lt_trichotomy hiA hiB with h | h | h
  · have hbm : hiA * m + m ≤ hiB * m := by
      have := Nat.mul_le_mul_right m (show hiA + 1 ≤ hiB by omega); rwa [Nat.add_one_mul] at this
    rw [ordNat hiA hiB, if_pos h, ordNat (hiA * m + loA), if_pos (by omega)]
  · subst h
    rw [ordNat hiA hiA, if_neg (lt_irrefl _), if_pos rfl, ordNat (hiA * m + loA), ordNat loA loB]
    by_cases h2 : loA < loB
    · rw [if_pos (by omega), if_pos h2]
    · by_cases h3 : loA = loB
      · subst h3; rw [if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), if_pos rfl]
      · rw [if_neg (by omega), if_neg (by omega), if_neg h2, if_neg h3]
  · have hbm : hiB * m + m ≤ hiA * m := by
      have := Nat.mul_le_mul_right m (show hiB + 1 ≤ hiA by omega); rwa [Nat.add_one_mul] at this
    rw [ordNat hiA hiB, if_neg (by omega), if_neg (by omega), ordNat (hiA * m + loA),
      if_neg (by omega), if_neg (by omega)]

/-- Radix-`2^64` step: comparing the low `(k+1)` limbs of `A` and `B` reduces to comparing limb `k`,
breaking ties with the low `k` limbs. -/
private lemma ordCompare_radix (A B m : ℕ) (hm : 0 < m) :
    Ord.compare (A % (2 ^ 64 * m)) (B % (2 ^ 64 * m)) =
      (match Ord.compare (A / m % 2 ^ 64) (B / m % 2 ^ 64) with
       | Ordering.eq => Ord.compare (A % m) (B % m)
       | o => o) := by
  have hdec : ∀ X : ℕ, X % (2 ^ 64 * m) = (X / m % 2 ^ 64) * m + X % m := fun X => by
    rw [mul_comm (2 ^ 64) m, Nat.mod_mul]; ring
  rw [hdec A, hdec B]
  exact ordCompare_lex _ _ _ _ _ (Nat.mod_lt _ hm) (Nat.mod_lt _ hm)

/-- The limb loop computes the radix-`2^64` comparison of `a.toNat · 2^(64q+r)` and `b.toNat`,
truncated to the low `k` limbs. -/
theorem cmpShiftedLimbs_eq (a b : AzNat) (q r : Nat) (hr : r < 64) (k : Nat) :
    cmpShiftedLimbs a b q r hr k =
      Ord.compare (a.toNat * 2 ^ (64 * q + r) % 2 ^ (64 * k)) (b.toNat % 2 ^ (64 * k)) := by
  induction k with
  | zero => simp [cmpShiftedLimbs, Nat.mod_one]
  | succ k ih =>
    rw [cmpShiftedLimbs, compare_UInt64_eq_compare_toNat, toNat_shiftedLimb, toNat_getBitsAsLimb,
      show 64 * k + 64 - 64 * k = 64 by omega, ih,
      show (2 : ℕ) ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) by rw [← pow_add]; congr 1; ring]
    exact (ordCompare_radix _ _ _ (Nat.two_pow_pos _)).symm

/-- The loop, run over all of `y`'s limbs, computes `Ord.compare (x.toNat · 2^shift) y.toNat`
(the `% 2^(64·L)` truncations are no-ops since both sides have at most `64·L` bits). -/
theorem cmpShiftedLimbs_full (x y : AzNat) (shift : ℕ)
    (hbound : x.toNat * 2 ^ shift < 2 ^ (64 * y.limbs.size)) :
    cmpShiftedLimbs x y (shift / 64) (shift % 64) (Nat.mod_lt _ (by decide)) y.limbs.size =
      Ord.compare (x.toNat * 2 ^ shift) y.toNat := by
  rw [cmpShiftedLimbs_eq, show 64 * (shift / 64) + shift % 64 = shift by omega,
    Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt (toNat_lt_pow y)]

/-- Scaling both sides of a `ℕ` comparison by a positive factor preserves it. -/
private lemma compare_mul_pos_right (a b c : ℕ) (hc : 0 < c) :
    Ord.compare a b = Ord.compare (a * c) (b * c) := by
  rw [ordNat a b, ordNat (a * c) (b * c)]
  rcases lt_trichotomy a b with h | h | h
  · rw [if_pos h, if_pos ((Nat.mul_lt_mul_right hc).mpr h)]
  · subst h; rw [if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), if_pos rfl]
  · have hba : b * c < a * c := (Nat.mul_lt_mul_right hc).mpr h
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A nonzero `AzNat` is bounded by `2 ^ size`. -/
private lemma toNat_lt_two_pow_size (x : AzNat) : x.toNat < 2 ^ x.size := by
  rw [← size_toNat]; exact Nat.lt_size_self x.toNat

/-- **Correctness of `normalizedCompare`.** For positive inputs it is the cross-multiplication
comparison `compare (x · 2^(size y)) (y · 2^(size x))` — i.e. it compares the normalized fractions
`x / 2^(size x)` and `y / 2^(size y)`. -/
theorem normalizedCompare_eq_cross (x y : AzNat) (hx : 0 < x.toNat) (hy : 0 < y.toNat) :
    normalizedCompare x y = Ord.compare (x.toNat * 2 ^ y.size) (y.toNat * 2 ^ x.size) := by
  have hxne : x ≠ 0 := by rintro rfl; simp at hx
  have hyne : y ≠ 0 := by rintro rfl; simp at hy
  have hSyL : y.size ≤ 64 * y.limbs.size := by rw [← size_toNat]; exact Nat.size_le.mpr (toNat_lt_pow y)
  have hSxL : x.size ≤ 64 * x.limbs.size := by rw [← size_toNat]; exact Nat.size_le.mpr (toNat_lt_pow x)
  unfold normalizedCompare
  rw [if_neg hxne, if_neg hyne]
  simp only []
  split
  · -- x.size = y.size : a direct comparison
    rename_i hsxy
    rw [compare_eq_compare_toNat, hsxy,
      compare_mul_pos_right x.toNat y.toNat (2 ^ y.size) (Nat.two_pow_pos _)]
  · split
    · -- x.size < y.size : shift `x` up by `y.size - x.size`
      rename_i hsxy
      have hbound : x.toNat * 2 ^ (y.size - x.size) < 2 ^ (64 * y.limbs.size) :=
        calc x.toNat * 2 ^ (y.size - x.size)
            < 2 ^ x.size * 2 ^ (y.size - x.size) :=
              (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr (toNat_lt_two_pow_size x)
          _ = 2 ^ y.size := by rw [← pow_add]; congr 1; omega
          _ ≤ 2 ^ (64 * y.limbs.size) := Nat.pow_le_pow_right (by decide) hSyL
      rw [cmpShiftedLimbs_full x y (y.size - x.size) hbound,
        compare_mul_pos_right (x.toNat * 2 ^ (y.size - x.size)) y.toNat (2 ^ x.size)
          (Nat.two_pow_pos _),
        Nat.mul_assoc, ← Nat.pow_add, show y.size - x.size + x.size = y.size by omega]
    · -- x.size > y.size : shift `y` up by `x.size - y.size`, then swap
      rename_i hsxy
      have hbound : y.toNat * 2 ^ (x.size - y.size) < 2 ^ (64 * x.limbs.size) :=
        calc y.toNat * 2 ^ (x.size - y.size)
            < 2 ^ y.size * 2 ^ (x.size - y.size) :=
              (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr (toNat_lt_two_pow_size y)
          _ = 2 ^ x.size := by rw [← pow_add]; congr 1; omega
          _ ≤ 2 ^ (64 * x.limbs.size) := Nat.pow_le_pow_right (by decide) hSxL
      rw [cmpShiftedLimbs_full y x (x.size - y.size) hbound, Nat.compare_swap,
        compare_mul_pos_right x.toNat (y.toNat * 2 ^ (x.size - y.size)) (2 ^ y.size)
          (Nat.two_pow_pos _),
        Nat.mul_assoc, ← Nat.pow_add, show x.size - y.size + y.size = x.size by omega]

end Azurite.AzNat

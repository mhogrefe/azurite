/-
  Gathen–Gerhard, Lemma 14.7: the squares in `F_q^×`, for odd `q`.

  Specializing Lemma 14.6 to `k = 2` (and, for part (iii), squaring up to
  `k = (q−1)/2`): the set `S` of squares in `F_q^×`

  (i)   is a subgroup of order `(q − 1)/2`,
  (ii)  equals `{a ∈ F_q^× : a^((q−1)/2) = 1}`, and
  (iii) every `a ∈ F_q^×` has `a^((q−1)/2) ∈ {1, −1}` — since its square
        is `a^(q−1) = 1` by Fermat, and `±1` are the only square roots of
        `1` over a field.

  `S` is `kthPowers F 2` from Lemma 14.6, linked to Mathlib's `IsSquare`
  by `mem_kthPowers_two_iff_isSquare`.  The field-level restatements
  (Euler's criterion `isSquare_iff_pow_card_sub_one_div_two_eq_one`, and
  the dichotomy `pow_card_sub_one_div_two_eq_one_or_neg_one`) are the
  forms consumed by equal-degree splitting (Cantor–Zassenhaus): raising a
  random nonzero element to the `(q−1)/2` lands in `{1, −1}`, each fibre
  having exactly `(q−1)/2` elements — whence the even split.
-/
import Azurite.GathenGerhard.Chapter14.Lemma_14_6

namespace Azurite

namespace GG

variable {F : Type*} [Field F]

/-- The `2`-nd powers are the squares in Mathlib's `IsSquare` sense. -/
theorem mem_kthPowers_two_iff_isSquare {a : Fˣ} :
    a ∈ kthPowers F 2 ↔ IsSquare a := by
  rw [mem_kthPowers]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, pow_two b⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, pow_two b⟩

omit [Field F] in
/-- Oddness of `q` in divisor form: `2 ∣ q − 1`. -/
private theorem two_dvd_card_sub_one [Fintype F]
    (hq : Odd (Fintype.card F)) : 2 ∣ Fintype.card F - 1 := by
  obtain ⟨m, hm⟩ := hq
  omega

/-- **GG Lemma 14.7 (i).**  For odd `q`, the squares form a subgroup of
`F_q^×` of order `(q − 1)/2`. -/
theorem lemma_14_7_card [Fintype F] (hq : Odd (Fintype.card F)) :
    Nat.card (kthPowers F 2) = (Fintype.card F - 1) / 2 :=
  card_kthPowers two_ne_zero (two_dvd_card_sub_one hq)

/-- **GG Lemma 14.7 (ii).**  For odd `q`, the squares are exactly the
elements with `a^((q−1)/2) = 1`. -/
theorem lemma_14_7_mem [Fintype F] (hq : Odd (Fintype.card F)) {a : Fˣ} :
    IsSquare a ↔ a ^ ((Fintype.card F - 1) / 2) = 1 := by
  rw [← mem_kthPowers_two_iff_isSquare]
  exact mem_kthPowers_iff_pow_eq_one two_ne_zero (two_dvd_card_sub_one hq)

/-- **GG Lemma 14.7 (iii).**  For odd `q`, every `a ∈ F_q^×` has
`a^((q−1)/2) ∈ {1, −1}`: its square is `a^(q−1) = 1` by Fermat, and `±1`
are the only square roots of `1` over a field. -/
theorem lemma_14_7_pow_eq_one_or_neg_one [Fintype F]
    (hq : Odd (Fintype.card F)) (a : Fˣ) :
    a ^ ((Fintype.card F - 1) / 2) = 1
      ∨ a ^ ((Fintype.card F - 1) / 2) = -1 := by
  have h2 := two_dvd_card_sub_one hq
  have hsq : (a ^ ((Fintype.card F - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel h2]
    have h := pow_card_eq_one' (x := a)
    rwa [Nat.card_units, Nat.card_eq_fintype_card] at h
  have hval : ((a ^ ((Fintype.card F - 1) / 2) : Fˣ) : F)
      * ((a ^ ((Fintype.card F - 1) / 2) : Fˣ) : F) = 1 := by
    rw [← pow_two, ← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  rcases mul_self_eq_one_iff.mp hval with h | h
  · left
    exact Units.ext (by rw [h, Units.val_one])
  · right
    exact Units.ext (by rw [h, Units.val_neg, Units.val_one])

/-- Part (ii) at the field level — **Euler's criterion**, GG form: for odd
`q`, a nonzero `a : F_q` is a square exactly when `a^((q−1)/2) = 1`. -/
theorem isSquare_iff_pow_card_sub_one_div_two_eq_one [Fintype F]
    (hq : Odd (Fintype.card F)) {a : F} (ha : a ≠ 0) :
    IsSquare a ↔ a ^ ((Fintype.card F - 1) / 2) = 1 := by
  rw [← exists_pow_eq_iff_pow_card_sub_one_div_eq_one two_ne_zero
    (two_dvd_card_sub_one hq) ha]
  constructor
  · rintro ⟨b, rfl⟩
    have hb : b ≠ 0 := by
      intro hb0
      rw [hb0, mul_zero] at ha
      exact ha rfl
    exact ⟨b, hb, pow_two b⟩
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, pow_two b⟩

/-- Part (iii) at the field level: for odd `q`, every nonzero `a : F_q`
has `a^((q−1)/2) = ±1` (the split tested by equal-degree splitting). -/
theorem pow_card_sub_one_div_two_eq_one_or_neg_one [Fintype F]
    (hq : Odd (Fintype.card F)) {a : F} (ha : a ≠ 0) :
    a ^ ((Fintype.card F - 1) / 2) = 1
      ∨ a ^ ((Fintype.card F - 1) / 2) = -1 := by
  rcases lemma_14_7_pow_eq_one_or_neg_one hq (Units.mk0 a ha) with h | h
  · left
    calc a ^ ((Fintype.card F - 1) / 2)
        = ((Units.mk0 a ha ^ ((Fintype.card F - 1) / 2) : Fˣ) : F) := by
          rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      _ = 1 := by rw [h, Units.val_one]
  · right
    calc a ^ ((Fintype.card F - 1) / 2)
        = ((Units.mk0 a ha ^ ((Fintype.card F - 1) / 2) : Fˣ) : F) := by
          rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      _ = -1 := by rw [h, Units.val_neg, Units.val_one]

end GG

end Azurite

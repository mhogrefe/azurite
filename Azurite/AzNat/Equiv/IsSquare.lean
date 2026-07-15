/-
  **Correctness of the perfect-square test**:
  `isSquare n = true ↔ IsSquare n.toNat` (`isSquare_eq_true_iff`).

  Three ingredients:
  * the low byte of the lowest limb is `n.toNat % 256` (Parity-style
    limb bridge, higher limbs contributing multiples of `2⁶⁴`);
  * the bitpacked filter agrees with "is a square mod 256" on all 256
    byte values — one `decide`;
  * the fallback is exact: `⌊√m⌋² = m ↔ IsSquare m`, from the core
    `Nat.sqrt` bracketing.

  Soundness of the rejection path is the classical residue argument:
  if `n = k²` then `n % 256 = (k % 256)² % 256`, so a square always
  passes the filter.
-/
import Azurite.AzNat.IsSquare
import Azurite.AzNat.Equiv.SqrtRem
import Azurite.AzNat.Equiv.Square.ToomCook3

namespace Azurite.AzNat

private lemma uint64_land_255_toNat (x : UInt64) :
    (x &&& 255).toNat = x.toNat % 256 := by
  show (x.toBitVec &&& 255#64).toNat = x.toBitVec.toNat % 256
  rw [BitVec.toNat_and]
  have h255 : (255#64).toNat = 255 := by decide
  rw [h255, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private lemma toNatLimbsList_mod_256_cons (x : UInt64) (xs : List UInt64) :
    toNatLimbsList (x :: xs) % 256 = x.toNat % 256 := by
  rw [toNatLimbsList_cons]
  omega

/-- The low byte of the lowest limb is `n.toNat % 256`. -/
private lemma lowByte_toNat (n : AzNat) :
    (if _ : n.limbs.size > 0 then n.limbs[0] &&& 255 else 0).toNat
      = n.toNat % 256 := by
  unfold toNat
  cases h : n.limbs.toList with
  | nil =>
    have h_size : n.limbs.size = 0 := by
      have := congr_arg List.length h
      simp at this
      simp [this]
    simp [show ¬(n.limbs.size > 0) from by omega, toNatLimbsList]
  | cons x xs =>
    have h_pos : n.limbs.size > 0 := by
      have := congr_arg List.length h
      simp at this
      omega
    simp only [show (n.limbs.size > 0) = True from by simp [h_pos], dite_true]
    simp only [show n.limbs[0] = n.limbs.toList[(0 : Nat)]'(by omega) from
      Array.getElem_toList (by omega), h]
    simp only [List.getElem_cons_zero, uint64_land_255_toNat,
      toNatLimbsList_mod_256_cons]

set_option maxRecDepth 8192 in
/-- The bitpacked table agrees with "is a square mod 256" on every
byte. -/
private lemma squareResidueTest_spec : ∀ m : Nat, m < 256 →
    (squareResidueTest (UInt64.ofNat m) = true ↔
      ∃ k, k < 256 ∧ k * k % 256 = m) := by
  decide

/-- The fallback is exact: `⌊√m⌋² = m ↔ IsSquare m`. -/
private lemma sqrt_mul_self_iff (m : Nat) :
    Nat.sqrt m ^ 2 = m ↔ IsSquare m := by
  rw [sq]
  constructor
  · intro h
    exact ⟨Nat.sqrt m, h.symm⟩
  · rintro ⟨r, rfl⟩
    have h1 := Nat.sqrt_le (r * r)
    have h2 := Nat.lt_succ_sqrt (r * r)
    simp only [Nat.succ_eq_add_one] at h2
    set s := Nat.sqrt (r * r) with hs
    have hrs : r ≤ s := by
      by_contra hcon
      have : s + 1 ≤ r := by omega
      have := Nat.mul_le_mul this this
      omega
    have := Nat.mul_le_mul hrs hrs
    omega

/-- **Correctness of the perfect-square test**: `isSquare n` decides
`IsSquare n.toNat`. -/
theorem isSquare_eq_true_iff (n : AzNat) :
    isSquare n = true ↔ IsSquare n.toNat := by
  unfold isSquare
  have hbval := lowByte_toNat n
  set b : UInt64 := if _ : n.limbs.size > 0 then n.limbs[0] &&& 255 else 0
    with hb
  have hblt : b.toNat < 256 := by omega
  have hspec := squareResidueTest_spec b.toNat hblt
  rw [UInt64.ofNat_toNat] at hspec
  by_cases hfilter : squareResidueTest b = true
  · rw [if_pos hfilter, beq_iff_eq]
    constructor
    · intro h
      have := congrArg toNat h
      rw [toNat_square, toNat_sqrt] at this
      exact (sqrt_mul_self_iff n.toNat).mp this
    · intro h
      apply toNat_injective
      rw [toNat_square, toNat_sqrt]
      exact (sqrt_mul_self_iff n.toNat).mpr h
  · rw [if_neg hfilter]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨r, hr⟩
    apply hfilter
    apply hspec.mpr
    refine ⟨r % 256, Nat.mod_lt _ (by omega), ?_⟩
    rw [← Nat.mul_mod, hbval, hr]

/-- `ofNat` version. -/
theorem isSquare_ofNat_eq_true_iff (m : Nat) :
    isSquare (ofNat m) = true ↔ IsSquare m := by
  rw [isSquare_eq_true_iff, toNat_ofNat]

end Azurite.AzNat

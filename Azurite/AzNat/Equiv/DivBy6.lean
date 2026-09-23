import Azurite.AzNat.DivBy6
import Azurite.AzNat.Equiv.Div.DivModLimb

namespace Azurite.AzNat

/-! ### Constant correctness for `divBy6_dNorm` and `divBy6_inv` -/

theorem divBy6_d_ne : (6 : UInt64) ≠ 0 := by decide

theorem divBy6_dNorm_toNat : divBy6_dNorm.toNat = 13835058055282163712 := rfl

theorem divBy6_dNorm_norm : 2 ^ 63 ≤ divBy6_dNorm.toNat := by
  rw [divBy6_dNorm_toNat]; norm_num

/-- `divBy6_inv` is the precomputed reciprocal of `6 <<< 61`. -/
theorem divBy6_inv_eq :
    divBy6_inv = UInt64.reciprocal divBy6_dNorm divBy6_dNorm_norm := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_reciprocal, divBy6_dNorm_toNat]
  decide

/-- `6`'s `UInt64.leadingZeros` is `61`. -/
theorem divBy6_leadingZeros : UInt64.leadingZeros (6 : UInt64) = 61 := by decide

/-! ### Top-level: `divBy6` matches `divModUInt64` at `d = 6` -/

/-- The constant-folded `divBy6` agrees with the generic `divModUInt64 U 6 _`.
    After simplifying the leading-zero count and the `r0`-initialization
    branches, the two sides reduce to definitionally equal calls to
    `divModLimb.go`. -/
theorem divBy6_eq_divModUInt64 (U : AzNat) :
    divBy6 U = divModUInt64 U 6 divBy6_d_ne := by
  unfold divBy6 divModUInt64
  by_cases h0 : U.limbs.size = 0
  · simp [h0]
  · simp only [h0, ↓reduceDIte]
    by_cases h1 : U.limbs.size = 1
    · simp [h1]
    · simp only [h1, ↓reduceDIte]
      unfold divModLimb
      simp only [divBy6_leadingZeros, show ((UInt64.ofNat 61 : UInt64) = 61) from rfl,
                 show ((UInt64.ofNat 3 : UInt64) = 3) from rfl,
                 show (64 - 61 : Nat) = 3 from rfl,
                 Nat.sub_zero,
                 show ((61 : Nat) = 0) ↔ False from ⟨by decide, fun h => h.elim⟩,
                 ite_false]
      simp only [h0, dite_false]
      rfl

/-- **Correctness of `divBy6`.** Returns `(Q, r)` with
    `Q.toNat * 6 + r.toNat = U.toNat` and `r.toNat < 6`. -/
theorem toNat_divBy6 (U : AzNat) :
    (divBy6 U).1.toNat * 6 + (divBy6 U).2.toNat = U.toNat
    ∧ (divBy6 U).2.toNat < 6 := by
  rw [divBy6_eq_divModUInt64]
  have h := toNat_divModUInt64 U 6 divBy6_d_ne
  show _ * (6 : UInt64).toNat + _ = _ ∧ _ < (6 : UInt64).toNat
  exact h

end Azurite.AzNat

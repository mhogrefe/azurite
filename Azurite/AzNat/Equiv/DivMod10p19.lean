import Azurite.AzNat.DivMod10p19
import Azurite.AzNat.Equiv.Div.DivModLimb

namespace Azurite.AzNat

/-! ### Constant correctness for `divMod10p19_d` and `divMod10p19_inv` -/

theorem divMod10p19_d_ne : divMod10p19_d ≠ 0 := by
  show (10000000000000000000 : UInt64) ≠ 0
  decide

theorem divMod10p19_d_toNat : divMod10p19_d.toNat = 10000000000000000000 := rfl

theorem divMod10p19_d_norm : 2 ^ 63 ≤ divMod10p19_d.toNat := by
  rw [divMod10p19_d_toNat]; norm_num

/-- `divMod10p19_inv` is the precomputed reciprocal of `10^19`. The
    equation is checked at compile time via `native_decide` — kernel
    reduction would walk the entire `reciprocal` body and exhaust
    memory (see `feedback_kernel_runaway_global_constants`). -/
theorem divMod10p19_inv_eq :
    divMod10p19_inv = UInt64.reciprocal divMod10p19_d divMod10p19_d_norm := by
  native_decide

/-- `10^19`'s `UInt64.leadingZeros` is `0`: the divisor is already
    normalized, so the shift bookkeeping in the general `divModLimb`
    loop collapses to the identity, which `divMod10p19_go` skips. -/
theorem divMod10p19_d_leadingZeros : UInt64.leadingZeros divMod10p19_d = 0 := by
  native_decide

/-! ### Inner loop: `divMod10p19_go` matches `divModLimb.go` at `k = 0`

This equivalence is structurally clear (both functions iterate the same
`div2By1` over the array, since `k = 0` collapses the carry-shift in
`divModLimb.go`'s body to the identity). A full proof would parallel the
existing `divModLimb.go_correct` proof; we leave it as future work and
instead state the consequences. -/

/-- `divMod10p19_go` matches the `k = 0`, `lo = 0` specialization of
    `divModLimb.go`. With `k = 0` the carry-shift bookkeeping collapses
    via Lean core's `UInt64.shiftLeft_zero` and `UInt64.or_zero`. -/
private theorem divMod10p19_go_eq_divModLimb_go (d inv : UInt64) :
    ∀ (j : Nat) (a : Array UInt64) (r : UInt64) (hbnd : j ≤ a.size),
      divMod10p19_go d inv a j r hbnd =
        divModLimb.go d inv 0 (by omega) a 0 j r (by omega) := by
  intro j
  induction j with
  | zero =>
    intro a r hbnd
    rw [divMod10p19_go, divModLimb.go]
  | succ f ih =>
    intro a r hbnd
    have h_idx : f < a.size := Nat.lt_of_succ_le hbnd
    rw [divMod10p19_go, divModLimb.go]
    simp only [show (0 : Nat) + f = f from Nat.zero_add f, ↓reduceIte,
               show (UInt64.ofNat 0 : UInt64) = 0 from rfl,
               UInt64.shiftLeft_zero, UInt64.or_zero]
    exact ih _ _ _

/-! ### Top-level: `divMod10p19` matches `divModUInt64` at `d = 10^19` -/

/-- The constant-folded `divMod10p19` agrees with the generic
    `divModUInt64 U 10^19 _`. -/
theorem divMod10p19_eq_divModUInt64 (U : AzNat) :
    divMod10p19 U = divModUInt64 U divMod10p19_d divMod10p19_d_ne := by
  unfold divMod10p19 divModUInt64
  by_cases h0 : U.limbs.size = 0
  · simp [h0]
  · simp only [h0, ↓reduceDIte]
    by_cases h1 : U.limbs.size = 1
    · simp [h1]
    · simp only [h1, ↓reduceDIte]
      -- size ≥ 2 case: both compute via the inner loop.
      unfold divModLimb
      -- `k = leadingZeros d = 0` for `d = 10^19`.
      simp only [divMod10p19_d_leadingZeros]
      -- With `k = 0`: `kU = 0`, `d <<< 0 = d`, `r0 = 0`, and the final
      -- shift `>>> 0` is the identity.
      have h_kU : (UInt64.ofNat 0 : UInt64) = 0 := rfl
      simp only [h_kU, UInt64.shiftLeft_zero, ↓reduceIte]
      -- The inv used inside `divModLimb` is `reciprocal d _`; rewrite to
      -- our pre-computed `divMod10p19_inv` via `divMod10p19_inv_eq`.
      rw [show UInt64.reciprocal divMod10p19_d
            (UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros divMod10p19_d
              divMod10p19_d_ne) = divMod10p19_inv from divMod10p19_inv_eq.symm]
      -- Reduce `>>> 0` and apply the loop equality.
      have h_shr_zero : ∀ x : UInt64, x >>> (0 : UInt64) = x := fun x => by
        apply UInt64.toNat.inj
        rw [UInt64.toNat_shiftRight]
        show x.toNat >>> (0 % 64) = x.toNat
        rw [Nat.zero_mod, Nat.shiftRight_zero]
      simp only [h_shr_zero, Nat.sub_zero]
      have h_loop := divMod10p19_go_eq_divModLimb_go divMod10p19_d divMod10p19_inv
        U.limbs.size U.limbs 0
        (by exact Nat.le_refl _)
      rw [h_loop]

/-- **Correctness of `divMod10p19`.** Returns `(Q, r)` with
    `Q.toNat * 10^19 + r.toNat = U.toNat` and `r.toNat < 10^19`. -/
theorem toNat_divMod10p19 (U : AzNat) :
    (divMod10p19 U).1.toNat * 10000000000000000000
        + (divMod10p19 U).2.toNat = U.toNat ∧
      (divMod10p19 U).2.toNat < 10000000000000000000 := by
  rw [divMod10p19_eq_divModUInt64]
  have h := toNat_divModUInt64 U divMod10p19_d divMod10p19_d_ne
  rw [divMod10p19_d_toNat] at h
  exact h

end Azurite.AzNat

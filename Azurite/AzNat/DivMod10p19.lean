import Azurite.AzNat.Div.Schoolbook
import Azurite.UInt64.MaxPow

namespace Azurite.AzNat

/-! ### Constant-folded `divModUInt64 _ 10^19`

`limbDigits b` for base `b = 10` repeatedly divides an `AzNat` by
`10^19` to extract base-`10^19` "super-digits". This file specializes
`divModUInt64` to that fixed divisor, hardcoding:

* the divisor `d = UInt64.maxPow10 = 10^19`,
* the Möller–Granlund reciprocal `inv = 15581492618384294730`
  (`#eval`'d once from `UInt64.reciprocal 10^19`),
* the leading-zero shift `k = 0` (since `2^63 < d < 2^64`, `d` is
  already normalized — every `<<<` and `>>>` by `k` in `divModLimb`
  collapses to the identity).

`divMod10p19_go` takes `d` and `inv` as explicit parameters rather
than referencing them as globals. Without this, the kernel can unfold
the global constants during type-checking and tumble into a deep
`reduce_bin_nat_op` recursion that exhausts memory; see
`feedback_kernel_runaway_global_constants`. The per-limb step is then
just one `div2By1` call. -/

/-- Divisor constant: `10^19`, reusing `UInt64.maxPow10`. -/
def divMod10p19_d : UInt64 := UInt64.maxPow10

/-- Möller–Granlund reciprocal of `10^19`. Hardcoded literal; the
    correctness proof in `Equiv/DivMod10p19.lean` checks this
    against `UInt64.reciprocal divMod10p19_d`. -/
def divMod10p19_inv : UInt64 := 15581492618384294730

/-- Inner loop, specialized to `k = 0` (no shift/carry). Process limb
    `a[j-1]` top-down: feed it as the low half of a 2-by-1 division whose
    high half is the running remainder `r`. Takes `d` and `inv` as
    explicit parameters — the call site fixes them to `10^19` and its
    reciprocal. -/
def divMod10p19_go (d inv : UInt64) (a : Array UInt64) (j : Nat) (r : UInt64)
    (hbnd : j ≤ a.size) : Array UInt64 × UInt64 :=
  match j with
  | 0 => (a, r)
  | j + 1 =>
    have h_idx : j < a.size := Nat.lt_of_succ_le hbnd
    let qr := UInt64.div2By1 r a[j] d inv
    divMod10p19_go d inv (a.set j qr.1) j qr.2
      ((Array.size_set h_idx (v := qr.1)).symm ▸ Nat.le_of_succ_le hbnd)
  termination_by j

/-- Divide an `AzNat` by `10^19`. Equivalent to
    `divModUInt64 U 10000000000000000000 (by decide)`, but with all
    constants folded in. -/
def divMod10p19 (U : AzNat) : AzNat × UInt64 :=
  if _h0 : U.limbs.size = 0 then (0, 0)
  else if h1 : U.limbs.size = 1 then
    have h_pos : 0 < U.limbs.size := h1 ▸ Nat.one_pos
    let qr := UInt64.divMod (U.limbs[0]'h_pos) divMod10p19_d
    (ofLimbs #[qr.1], qr.2)
  else
    let res := divMod10p19_go divMod10p19_d divMod10p19_inv
      U.limbs U.limbs.size 0 (Nat.le_refl _)
    (ofLimbs res.1, res.2)

end Azurite.AzNat

import Azurite.UInt64.Pow2

namespace UInt64

/-- Recursive helper for `digitsPow2`: emit digits of `u` in base `2^k`,
    LSB-first, while `u > 0`. `mask = 2^k - 1`, `shift = k` (as `UInt64`).
    `hs` records the caller-side guarantee `1 ≤ shift.toNat < 64` and is
    used only in the termination proof; it is erased at runtime. -/
def digitsPow2Aux (mask shift : UInt64) (hs : 1 ≤ shift.toNat ∧ shift.toNat < 64)
    (u : UInt64) (acc : Array UInt64) : Array UInt64 :=
  if _hu : u = 0 then acc
  else digitsPow2Aux mask shift hs (u >>> shift) (acc.push (u &&& mask))
termination_by u.toNat
decreasing_by
  show (u >>> shift).toNat < u.toNat
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs.2, Nat.shiftRight_eq_div_pow]
  refine Nat.div_lt_self
    (Nat.pos_of_ne_zero (fun he => _hu (UInt64.toNat.inj (he.trans UInt64.toNat_zero.symm))))
    (Nat.one_lt_pow (Nat.one_le_iff_ne_zero.mp hs.1) (by omega))

/-- Recursive helper for `digits` on non-power-of-two bases. `hb` records
    the caller-side guarantee `2 ≤ b.toNat` and is used only in the
    termination proof; it is erased at runtime. -/
def digitsGenericAux (b : UInt64) (hb : 2 ≤ b.toNat) (u : UInt64) (acc : Array UInt64) :
    Array UInt64 :=
  if _hu : u = 0 then acc
  else digitsGenericAux b hb (u / b) (acc.push (u % b))
termination_by u.toNat
decreasing_by
  show (u / b).toNat < u.toNat
  rw [UInt64.toNat_div]
  exact Nat.div_lt_self
    (Nat.pos_of_ne_zero (fun he => _hu (UInt64.toNat.inj (he.trans UInt64.toNat_zero.symm))))
    hb

/-- `digitsPow2 k u` returns the digits of `u` in base `2^k`, LSB-first,
    dropping trailing zeros (matching `Nat.digits (2^k) u.toNat`).
    Implemented with `>>>` and `&&&` only — no division.

    * `k ∈ [1, 63]` (the intended range): standard shift+mask loop.
    * `k = 0` (base `2^0 = 1`): degenerate; returns `#[]` rather than
      Mathlib's `List.replicate u.toNat 1`, which would allocate up to
      `2^64` entries.
    * `k ≥ 64` (base `≥ 2^64`, exceeds `UInt64`): one digit suffices —
      returns `#[u]` for `u ≠ 0`, `#[]` otherwise. -/
def digitsPow2 (k : Nat) (u : UInt64) : Array UInt64 :=
  if hk0 : k = 0 then #[]
  else if hk64 : 64 ≤ k then
    if u = 0 then #[] else #[u]
  else
    have hs : 1 ≤ (UInt64.ofNat k).toNat ∧ (UInt64.ofNat k).toNat < 64 := by
      have h_eq : (UInt64.ofNat k).toNat = k := Nat.mod_eq_of_lt (by omega)
      omega
    digitsPow2Aux ((1 <<< UInt64.ofNat k) - 1) (UInt64.ofNat k) hs u #[]

/-- `digits b u` returns the digits of `u` in base `b`, LSB-first, dropping
    trailing zeros (matching `Nat.digits b.toNat u.toNat` for `b ≥ 2`).
    Dispatches to `digitsPow2` (shift+mask) when `b` is a power of two,
    otherwise uses `/` and `%`. Returns `#[]` for `b < 2`.

    The runtime power-of-two check costs one extra `&&&` and comparison —
    if you statically know the base is `2^k`, call `digitsPow2 k u`
    directly. -/
def digits (b u : UInt64) : Array UInt64 :=
  if hb : b < 2 then #[]
  else if b.isPowerOfTwo then
    digitsPow2 b.toBitVec.ctz.toNat u
  else
    have hb' : 2 ≤ b.toNat := by
      have h2 : (2 : UInt64).toNat = 2 := rfl
      have h_lt : ¬ b.toNat < (2 : UInt64).toNat := fun h => hb (by
        rw [UInt64.lt_iff_toNat_lt]; exact h)
      omega
    digitsGenericAux b hb' u #[]

-- Sanity checks (hex, octal, decimal, base 2).
-- 0xDEADBEEF in hex, LSB-first: [F, E, E, B, D, A, E, D].
#guard UInt64.digitsPow2 4 0xDEADBEEF ==
       #[0xF, 0xE, 0xE, 0xB, 0xD, 0xA, 0xE, 0xD]
-- 0o755 in octal, LSB-first: [5, 5, 7].
#guard UInt64.digitsPow2 3 0o755 == #[5, 5, 7]
-- Single bits.
#guard UInt64.digitsPow2 1 0b10110 == #[0, 1, 1, 0, 1]
-- Zero.
#guard UInt64.digitsPow2 4 0 == #[]
-- Top-bit-set UInt64 (matches the boxed-Nat boundary).
#guard UInt64.digitsPow2 4 0xF000_0000_0000_0000 ==
       #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xF]

-- Generic dispatcher: hex routes through digitsPow2.
#guard UInt64.digits 16 0xDEADBEEF == UInt64.digitsPow2 4 0xDEADBEEF
-- Generic dispatcher: base 10 uses div+mod.
#guard UInt64.digits 10 12345 == #[5, 4, 3, 2, 1]
#guard UInt64.digits 10 0 == #[]
-- Degenerate bases.
#guard UInt64.digits 0 42 == #[]
#guard UInt64.digits 1 42 == #[]

end UInt64

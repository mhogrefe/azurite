import Azurite.AzNat.Mul.Karatsuba
import Azurite.AzNat.MulModPow2.Schoolbook
import Azurite.AzNat.AddModPow2
import Azurite.AzNat.OfLimbs

/-!
## `AzNat.mulKaratsubaModPow2` — low (mod `2 ^ k`) Karatsuba multiplication

A genuine short product: to compute the low `len` limbs of a balanced `len × len`
product, split at `k = ⌈len/2⌉`, `m = len - k`:

  `a·b ≡ A₀·B₀ + (A₀·B₁ + A₁·B₀)·βᵏ   (mod βˡᵉⁿ)`

because the `A₁·B₁·β²ᵏ` term vanishes modulo `βˡᵉⁿ` (`2k ≥ len`).  So the top half
is never formed: one full sub-product `A₀·B₀` (via the existing full Karatsuba)
plus two recursive low sub-products `A₀·B₁` and `A₁·B₀` of half the size, falling
back to `schoolbookMulLowLimbs` at the base.  Here `β = 2 ^ 64`.
-/

namespace Azurite.AzNat

/-- Low `len` limbs of `a[loA : loA+len] * b[loB : loB+len]`, returned as an
    `AzNat` (value `< 2 ^ (64·len)`).  Short-product Karatsuba: drops the
    `A₁·B₁·β²ᵏ` term, recurses on the two cross low products.

    The split uses a **Mulders' tuned point** `k = ⌈11·len/16⌉ ≈ 0.6875·len`
    (clamped to `len − 1`) rather than the balanced `⌈len/2⌉`.  The recurrence
    `SP(n) = M(k) + 2·SP(n − k)` has leading constant
    `(k/n)^α / (1 − 2·(1 − k/n)^α)` (`α = log₂3`), which equals `1` at the
    balanced split but drops to `≈ 0.808` near `k/n = 0.694` — a genuine
    constant-factor speedup over masking a full product.  Any `k` with
    `⌈len/2⌉ ≤ k ≤ len − 1` keeps the recursion correct. -/
def karatsubaMulLowLimbs (threshold : Nat) (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) : AzNat :=
  if h_base : len < 2 ∨ len < threshold then
    ofLimbs (schoolbookMulLowLimbs a b loA len loB len len hA hB)
  else
    have hlen : 2 ≤ len := by omega
    let k := min ((11 * len + 15) / 16) (len - 1)
    let m := len - k
    have hk_pos : 0 < k := by show 0 < min ((11 * len + 15) / 16) (len - 1); omega
    have hm_pos : 0 < m := by show 0 < len - min ((11 * len + 15) / 16) (len - 1); omega
    have hm_le : m ≤ k := by
      show len - min ((11 * len + 15) / 16) (len - 1) ≤ min ((11 * len + 15) / 16) (len - 1)
      omega
    have hkm : k + m = len := by
      show min ((11 * len + 15) / 16) (len - 1) + (len - min ((11 * len + 15) / 16) (len - 1)) = len
      omega
    have hm_lt : m < len := by show len - min ((11 * len + 15) / 16) (len - 1) < len; omega
    have hA0 : loA + k ≤ a.size := by omega
    have hB0 : loB + k ≤ b.size := by omega
    let C0 := ofLimbs (karatsubaMulLimbs threshold a b loA loB k hA0 hB0)
    have hMidA_a : loA + m ≤ a.size := by omega
    have hMidA_b : loB + k + m ≤ b.size := by omega
    let midA := karatsubaMulLowLimbs threshold a b loA (loB + k) m hMidA_a hMidA_b
    have hMidB_a : loA + k + m ≤ a.size := by omega
    have hMidB_b : loB + m ≤ b.size := by omega
    let midB := karatsubaMulLowLimbs threshold a b (loA + k) loB m hMidB_a hMidB_b
    let middle := addModPow2 midA midB (64 * m)
    let shifted := ofLimbs (Array.replicate k 0 ++ middle.limbs)
    addModPow2 C0 shifted (64 * len)
  termination_by len
  decreasing_by all_goals (simp_wf; omega)

/-- **Low (mod `2 ^ k`) Karatsuba multiplication.** `(a * b) mod 2 ^ k`, computing
    only the low `L = (k + 63) / 64` limbs of the product via the short-product
    recursion.  `threshold` is the limb size below which the recursion falls back
    to `schoolbookMulLowLimbs`. -/
def mulKaratsubaModPow2 (threshold : Nat) (a b : AzNat) (k : Nat) : AzNat :=
  let L := (k + 63) / 64
  let aPad : Array UInt64 := a.limbs ++ Array.replicate (L - a.limbs.size) 0
  let bPad : Array UInt64 := b.limbs ++ Array.replicate (L - b.limbs.size) 0
  have hA : 0 + L ≤ aPad.size := by
    show 0 + L ≤ (a.limbs ++ Array.replicate (L - a.limbs.size) (0 : UInt64)).size
    rw [Array.size_append, Array.size_replicate]; omega
  have hB : 0 + L ≤ bPad.size := by
    show 0 + L ≤ (b.limbs ++ Array.replicate (L - b.limbs.size) (0 : UInt64)).size
    rw [Array.size_append, Array.size_replicate]; omega
  modPow2 (karatsubaMulLowLimbs threshold aPad bPad 0 0 L hA hB) k

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def parse (s : String) : AzNat := (AzNat.parse s).get!

-- Cross-check against `(x * y) % 2^k` for a range of sizes and thresholds.
-- Force the recursion (threshold 2) on multi-limb operands.
#guard (mulKaratsubaModPow2 2 (parse "7") (parse "9") 4).toNat == 63 % 16
#guard (mulKaratsubaModPow2 2 (parse "255") (parse "255") 8).toNat == 65025 % 256
#guard (mulKaratsubaModPow2 2 (parse "255") (parse "255") 16).toNat == 65025
#guard (mulKaratsubaModPow2 2 (parse "0") (parse "12345") 32).toNat == 0
#guard (mulKaratsubaModPow2 2 (parse "1") (parse "12345") 32).toNat == 12345
-- `(2^64 + 1)^2 = 2^128 + 2^65 + 1`; mod 2^64 → 1, mod 2^128 → 2^65 + 1.
#guard (mulKaratsubaModPow2 2 (parse "18446744073709551617")
  (parse "18446744073709551617") 64).toNat == 1
#guard (mulKaratsubaModPow2 2 (parse "18446744073709551617")
  (parse "18446744073709551617") 128).toNat == 36893488147419103233
-- Large multi-limb, forcing several levels of recursion; low 200 / 100 / 333 bits.
#guard (mulKaratsubaModPow2 2 (parse "123456789012345678901234567890")
  (parse "987654321098765432109876543210") 200).toNat ==
  (123456789012345678901234567890 * 987654321098765432109876543210) % (2 ^ 200)
#guard (mulKaratsubaModPow2 3 (parse "123456789012345678901234567890")
  (parse "987654321098765432109876543210") 100).toNat ==
  (123456789012345678901234567890 * 987654321098765432109876543210) % (2 ^ 100)
#guard (mulKaratsubaModPow2 2
  (parse "31415926535897932384626433832795028841971693993751058209749445923")
  (parse "27182818284590452353602874713526624977572470936999595749669676277") 333).toNat ==
  (31415926535897932384626433832795028841971693993751058209749445923 *
   27182818284590452353602874713526624977572470936999595749669676277) % (2 ^ 333)
-- `k = 0`.
#guard (mulKaratsubaModPow2 2 (parse "123456789") (parse "987654321") 0).toNat == 0
-- Agreement with the schoolbook-low variant on a random-ish case.
#guard (mulKaratsubaModPow2 2 (parse "123456789012345678901234567890")
  (parse "987654321098765432109876543210") 150).toNat ==
  (mulSchoolbookModPow2 (parse "123456789012345678901234567890")
    (parse "987654321098765432109876543210") 150).toNat

end Tests

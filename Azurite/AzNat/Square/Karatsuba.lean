import Azurite.AzNat.Square.Schoolbook
import Azurite.AzNat.Mul.Karatsuba

namespace Azurite.AzNat

/-!
# Karatsuba squaring

For `a = a₀ + a₁ β^k` with `β = 2^64`, `k = ⌈n/2⌉`, `m = n - k`, `m ≤ k`,

  `a² = a₀² + 2 a₀ a₁ β^k + a₁² β^{2k}`.

Computing `2 a₀ a₁` directly costs a multiplication; the Karatsuba-for-squaring
identity replaces that with a third **squaring**:

  `(a₀ − a₁)² = a₀² − 2 a₀ a₁ + a₁²`
  `⇒  2 a₀ a₁ = a₀² + a₁² − (a₀ − a₁)²`.

Crucially, `(a₀ − a₁)² = (a₁ − a₀)²`, so we square `|a₀ − a₁|` and never
need a sign for `C₂` — the middle term `D₀ + D₂ − C` is always non-negative
because it equals `2 a₀ a₁ ≥ 0`. This is the main simplification vs.
`karatsubaMulLimbsRec`.

The implementation reuses `absSubLimbsKM`, `middleBuf` (with the subtract
branch always taken), and `assemble` from `AzNat.Mul.Karatsuba`.
-/

/-- Karatsuba squaring of an `n`-limb slice `a[lo, lo + n)`. Returns a fresh
    `2 n`-limb array.

    The `threshold` parameter is the size below which we fall back to
    `schoolbookSquareLimbs`. When `n < max 2 threshold`, schoolbook is used
    directly (`n ≥ 2` is needed to split). -/
def karatsubaSquareLimbsRec (threshold : Nat) (a : Array UInt64)
    (lo len : Nat) (hA : lo + len ≤ a.size) :
    { c : Array UInt64 // c.size = 2 * len } :=
  if h_base : len < 2 ∨ len < threshold then
    ⟨schoolbookSquareLimbs a lo len hA, schoolbookSquareLimbs_size a lo len hA⟩
  else
    have hlen : 2 ≤ len := by omega
    let k := (len + 1) / 2
    let m := len - k
    have hk_pos : 0 < k := by show 0 < (len + 1) / 2; omega
    have hk_lt : k < len := by show (len + 1) / 2 < len; omega
    have hm_pos : 0 < m := by show 0 < len - (len + 1) / 2; omega
    have hm_le : m ≤ k := by show len - (len + 1) / 2 ≤ (len + 1) / 2; omega
    have hm_lt : m < len := by show len - (len + 1) / 2 < len; omega
    have hkm : k + m = len := by
      show (len + 1) / 2 + (len - (len + 1) / 2) = len; omega
    -- D₀ = a₀² (low k limbs squared, 2k limbs)
    have hA0 : lo + k ≤ a.size := by omega
    let D0 := karatsubaSquareLimbsRec threshold a lo k hA0
    -- D₂ = a₁² (high m limbs squared, 2m limbs)
    have hA1 : (lo + k) + m ≤ a.size := by omega
    let D2 := karatsubaSquareLimbsRec threshold a (lo + k) m hA1
    -- |a₀ − a₁| as a k-limb buffer (sign discarded — we'll square it).
    have hAabs : lo + k + m ≤ a.size := by omega
    let absA := absSubLimbsKM a lo k m hAabs hm_le hk_pos hm_pos
    -- C = |a₀ − a₁|²
    have hAabs_lim : 0 + k ≤ absA.1.1.size := by rw [absA.1.2]; omega
    let C := karatsubaSquareLimbsRec threshold absA.1.1 0 k hAabs_lim
    -- middle = D₀ + D₂ − C  (always ≥ 0 since it equals 2 a₀ a₁)
    let middle := karatsubaMulLimbsRec.middleBuf k m D0.1 D2.1 C.1
                    true D0.2 D2.2 C.2 hk_pos hm_pos hm_le
    -- Assemble: D₀ in [0, 2k), D₂ in [2k, 2n), add middle · β^k on top.
    karatsubaMulLimbsRec.assemble k m len D0.1 D2.1 middle.1
      D0.2 D2.2 middle.2 hkm hk_pos hm_pos hm_le
  termination_by len
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Karatsuba squaring of an `n`-limb slice, mirroring the signature of
    `schoolbookSquareLimbs`. Falls back to `schoolbookSquareLimbs` when
    `len < max 2 threshold`. -/
def karatsubaSquareLimbs (threshold : Nat) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : Array UInt64 :=
  (karatsubaSquareLimbsRec threshold a lo len hA).1

/-- The result of Karatsuba squaring has size `2 * len`. -/
theorem karatsubaSquareLimbs_size (threshold : Nat) (a : Array UInt64)
    (lo len : Nat) (hA : lo + len ≤ a.size) :
    (karatsubaSquareLimbs threshold a lo len hA).size = 2 * len :=
  (karatsubaSquareLimbsRec threshold a lo len hA).2

end Azurite.AzNat

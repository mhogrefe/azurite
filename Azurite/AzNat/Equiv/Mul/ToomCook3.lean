import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.DivBy6
import Azurite.AzNat.Equiv.Mul.Basic
import Azurite.AzNat.Equiv.Mul.Karatsuba
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Mul.ToomCook3

/-!
# Toom-Cook 3-way multiplication: correctness

`toomCook3MulLimbsRec_toNat`: the recursive algorithm of
`Azurite.AzNat.toomCook3MulLimbsRec` computes the product of the two
input slices.

The algorithm performs all linear-time interpolation via `AzNat`-level
operations (`addLimbs`, `subLimbs`, `mulUInt64`, `shiftLeft`, `shiftRight`,
`divBy6`); no value is ever materialized as a `Nat ≥ 2^64`.  The proof
mirrors this structure: each algebraic step is a `toNat_*` lemma about
the corresponding `AzNat` op.

The Nat-level polynomial identity `toomCook3_nat_identity` is the same as
before (4-way case analysis on `(sgnA, sgnB)`).
-/

namespace Azurite.AzNat

-- ── Convenience: name the slice toNat ───────────────────────────────────────

/-- Value of a length-`len` slice `a[lo, lo+len)`.  Local to the proof
    file; the algorithm itself never names this value. -/
private def sliceToNat (a : Array UInt64) (lo len : Nat) : Nat :=
  toNatLimbsList ((a.toList.drop lo).take len)

private lemma sliceToNat_lt_pow (a : Array UInt64) (lo len : Nat) :
    sliceToNat a lo len < 2 ^ (64 * len) :=
  slice_lt_pow a lo len

/-- AzNat strict ordering matches `Nat` strict ordering on `toNat`. -/
private lemma azNat_lt_iff_toNat_lt (a b : AzNat) : a < b ↔ a.toNat < b.toNat := by
  constructor
  · intro h
    have h_cmp : compare a b = Ordering.lt := h
    rw [compare_eq_compare_toNat] at h_cmp
    exact Nat.compare_eq_lt.mp h_cmp
  · intro h
    show compare a b = Ordering.lt
    rw [compare_eq_compare_toNat]
    exact Nat.compare_eq_lt.mpr h

/-- The toNat of `ofLimbs (a.extract lo (lo + k))` is exactly the
    `sliceToNat a lo k`. -/
private lemma toNat_ofLimbs_extract (a : Array UInt64) (lo k : Nat) :
    (ofLimbs (a.extract lo (lo + k))).toNat = sliceToNat a lo k := by
  rw [toNat_ofLimbs, Array.toList_extract]
  show toNatLimbsList ((a.toList.drop lo).take (lo + k - lo)) = _
  rw [Nat.add_sub_cancel_left]
  rfl

-- ── `truncatePad` correctness ───────────────────────────────────────────────

/-- `truncatePad` is value-preserving when the input fits in `n` limbs. -/
theorem truncatePad_toNat (a : Array UInt64) (n : Nat)
    (h : toNatLimbsList a.toList < 2 ^ (64 * n)) :
    toNatLimbsList (truncatePad a n).toList = toNatLimbsList a.toList := by
  unfold truncatePad
  rw [Array.toList_append, Array.toList_replicate, toNatLimbsList_append_zeros]
  -- Goal: toNatLimbsList (a.extract 0 n).toList = toNatLimbsList a.toList
  rw [Array.toList_extract]
  show toNatLimbsList ((a.toList.drop 0).take (n - 0)) = _
  rw [List.drop_zero, Nat.sub_zero]
  -- Goal: toNatLimbsList (a.toList.take n) = toNatLimbsList a.toList
  by_cases hsize : a.toList.length ≤ n
  · rw [List.take_of_length_le hsize]
  · -- Use the bound: high limbs past `n` are zero.
    have h_split := toNatLimbsList_append (a.toList.take n) (a.toList.drop n)
    rw [List.take_append_drop] at h_split
    rw [h_split]
    have h_take_len : (a.toList.take n).length = n := by
      rw [List.length_take]; omega
    rw [h_take_len]
    -- We need (a.toList.drop n) to be all zeros — i.e., toNatLimbsList of it = 0.
    have h_drop_lt : toNatLimbsList (a.toList.take n) < 2 ^ (64 * n) := by
      have := toNatLimbsList_lt_pow (a.toList.take n)
      rw [h_take_len] at this; exact this
    have h_drop_zero : toNatLimbsList (a.toList.drop n) = 0 := by
      -- toNatLimbsList a.toList = (take part) + (drop part) * 2^(64*n)
      -- LHS < 2^(64*n), and (take part) < 2^(64*n), so (drop part) * 2^(64*n) < 2^(64*n)
      -- forcing (drop part) = 0.
      have h_pow_pos : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
      have h_sum := h
      rw [h_split, h_take_len] at h_sum
      -- h_sum : (a.toList.take n).toNat + (a.toList.drop n).toNat * 2^(64*n) < 2^(64*n)
      have h_drop_part : toNatLimbsList (a.toList.drop n) * 2 ^ (64 * n) < 2 ^ (64 * n) := by
        omega
      by_contra h_ne
      have h_pos : 0 < toNatLimbsList (a.toList.drop n) := Nat.pos_of_ne_zero h_ne
      have h_ge : 2 ^ (64 * n) ≤ toNatLimbsList (a.toList.drop n) * 2 ^ (64 * n) := by
        have := Nat.mul_le_mul_right (2 ^ (64 * n)) h_pos
        linarith
      omega
    rw [h_drop_zero]; ring

-- ── `sum012`, `sum124`, `diffM1` correctness ────────────────────────────────

private lemma three_slices_lt (k m : Nat) (h_mk : m ≤ k) (A0 A1 A2 : Nat)
    (h0 : A0 < 2 ^ (64 * k)) (h1 : A1 < 2 ^ (64 * k)) (h2 : A2 < 2 ^ (64 * m)) :
    A0 + A1 + A2 < 2 ^ (64 * (k + 1)) := by
  have h2' : A2 < 2 ^ (64 * k) :=
    h2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have h_step : (2 : Nat) ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
    rw [show 64 * (k + 1) = 64 * k + 64 from by ring, Nat.pow_add]
  rw [h_step]
  have h_pow : (3 : Nat) ≤ 2 ^ 64 := by decide
  have h_pos : 0 < 2 ^ (64 * k) := Nat.two_pow_pos _
  nlinarith [Nat.mul_le_mul_left (2 ^ (64 * k)) h_pow]

private lemma sum124_lt (k m : Nat) (h_mk : m ≤ k) (A0 A1 A2 : Nat)
    (h0 : A0 < 2 ^ (64 * k)) (h1 : A1 < 2 ^ (64 * k)) (h2 : A2 < 2 ^ (64 * m)) :
    A0 + 2 * A1 + 4 * A2 < 2 ^ (64 * (k + 1)) := by
  have h2' : A2 < 2 ^ (64 * k) :=
    h2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have h_step : (2 : Nat) ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
    rw [show 64 * (k + 1) = 64 * k + 64 from by ring, Nat.pow_add]
  rw [h_step]
  have h_pow : (7 : Nat) ≤ 2 ^ 64 := by decide
  have h_pos : 0 < 2 ^ (64 * k) := Nat.two_pow_pos _
  nlinarith [Nat.mul_le_mul_left (2 ^ (64 * k)) h_pow]

private lemma abs_diff_lt (k m : Nat) (h_mk : m ≤ k) (A0 A1 A2 : Nat)
    (h0 : A0 < 2 ^ (64 * k)) (h1 : A1 < 2 ^ (64 * k)) (h2 : A2 < 2 ^ (64 * m)) :
    (if A0 + A2 ≥ A1 then A0 + A2 - A1 else A1 - (A0 + A2)) < 2 ^ (64 * (k + 1)) := by
  have h_lt : A0 + A2 < 2 ^ (64 * (k + 1)) := by
    have h_sum : A0 + A2 < 2 * 2 ^ (64 * k) := by
      have h2' : A2 < 2 ^ (64 * k) :=
        h2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      omega
    have h_step : (2 : Nat) ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
      rw [show 64 * (k + 1) = 64 * k + 64 from by ring, Nat.pow_add]
    rw [h_step]
    have h_pow : (2 : Nat) ≤ 2 ^ 64 := by decide
    nlinarith [Nat.two_pow_pos (64 * k)]
  have h1_lt : A1 < 2 ^ (64 * (k + 1)) :=
    h1.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  by_cases h : A0 + A2 ≥ A1
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- `sum012` returns `A_0 + A_1 + A_2` exactly when the input bounds hold. -/
theorem sum012_toNat (a : Array UInt64) (lo k m : Nat) (h_mk : m ≤ k) :
    toNatLimbsList (sum012 a lo k m).toList
      = sliceToNat a lo k + sliceToNat a (lo + k) k + sliceToNat a (lo + 2 * k) m := by
  unfold sum012
  rw [truncatePad_toNat]
  · -- The AzNat sum's toNat unfolds to the sum of the slice toNats.
    rw [show ((ofLimbs (a.extract lo (lo + k)) + ofLimbs (a.extract (lo + k) (lo + k + k))
            + ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))).limbs)
          = ((ofLimbs (a.extract lo (lo + k)) + ofLimbs (a.extract (lo + k) (lo + k + k))
            + ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))) : AzNat).limbs from rfl]
    show (ofLimbs (a.extract lo (lo + k)) + ofLimbs (a.extract (lo + k) (lo + k + k))
            + ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))).toNat = _
    rw [toNat_add, toNat_add, toNat_ofLimbs_extract, toNat_ofLimbs_extract,
        toNat_ofLimbs_extract]
  · -- Bound: sum < 2^(64*(k+1)).
    show (_ : AzNat).toNat < 2^(64*(k+1))
    rw [toNat_add, toNat_add, toNat_ofLimbs_extract, toNat_ofLimbs_extract,
        toNat_ofLimbs_extract]
    exact three_slices_lt k m h_mk _ _ _
      (sliceToNat_lt_pow a lo k)
      (sliceToNat_lt_pow a (lo + k) k)
      (sliceToNat_lt_pow a (lo + 2 * k) m)

/-- `sum124` returns `A_0 + 2·A_1 + 4·A_2` exactly. -/
theorem sum124_toNat (a : Array UInt64) (lo k m : Nat) (h_mk : m ≤ k) :
    toNatLimbsList (sum124 a lo k m).toList
      = sliceToNat a lo k + 2 * sliceToNat a (lo + k) k + 4 * sliceToNat a (lo + 2 * k) m := by
  unfold sum124
  rw [truncatePad_toNat]
  · show (ofLimbs (a.extract lo (lo + k)) + mulUInt64 (ofLimbs (a.extract (lo + k) (lo + k + k))) 2
          + mulUInt64 (ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))) 4).toNat = _
    rw [toNat_add, toNat_add, toNat_mulUInt64, toNat_mulUInt64,
        toNat_ofLimbs_extract, toNat_ofLimbs_extract, toNat_ofLimbs_extract]
    show _ + _ * (2 : UInt64).toNat + _ * (4 : UInt64).toNat = _
    rw [show (2 : UInt64).toNat = 2 from rfl, show (4 : UInt64).toNat = 4 from rfl]
    ring
  · show (_ : AzNat).toNat < 2^(64*(k+1))
    rw [toNat_add, toNat_add, toNat_mulUInt64, toNat_mulUInt64,
        toNat_ofLimbs_extract, toNat_ofLimbs_extract, toNat_ofLimbs_extract]
    show _ + _ * (2 : UInt64).toNat + _ * (4 : UInt64).toNat < _
    rw [show (2 : UInt64).toNat = 2 from rfl, show (4 : UInt64).toNat = 4 from rfl]
    have h_bound : sliceToNat a lo k + 2 * sliceToNat a (lo + k) k
                  + 4 * sliceToNat a (lo + 2 * k) m < 2 ^ (64 * (k + 1)) :=
      sum124_lt k m h_mk _ _ _
        (sliceToNat_lt_pow a lo k)
        (sliceToNat_lt_pow a (lo + k) k)
        (sliceToNat_lt_pow a (lo + 2 * k) m)
    linarith

/-- `diffM1` returns `|A_0 + A_2 - A_1|` with the corresponding sign. -/
theorem diffM1_toNat (a : Array UInt64) (lo k m : Nat) (h_mk : m ≤ k) :
    let A0 := sliceToNat a lo k
    let A1 := sliceToNat a (lo + k) k
    let A2 := sliceToNat a (lo + 2 * k) m
    toNatLimbsList (diffM1 a lo k m).1.toList
      = (if A0 + A2 ≥ A1 then A0 + A2 - A1 else A1 - (A0 + A2))
    ∧ ((diffM1 a lo k m).2 = true ↔ A0 + A2 ≥ A1) := by
  intro A0 A1 A2
  unfold diffM1
  refine ⟨?_, ?_⟩
  · -- toNat of the buffer.
    by_cases h : ofLimbs (a.extract lo (lo + k))
                  + ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))
                < ofLimbs (a.extract (lo + k) (lo + k + k))
    · -- s0 + s2 < s1: return s1 - (s0 + s2), sign false.
      simp only [h, ↓reduceIte]
      have h_lt_nat : A0 + A2 < A1 := by
        rw [show A0 = (ofLimbs (a.extract lo (lo + k))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm,
            show A2 = (ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm,
            show A1 = (ofLimbs (a.extract (lo + k) (lo + k + k))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm]
        rw [← toNat_add]
        exact (azNat_lt_iff_toNat_lt _ _).mp h
      rw [if_neg (by omega)]
      rw [truncatePad_toNat]
      · show (_ : AzNat).toNat = _
        rw [toNat_sub, toNat_ofLimbs_extract, toNat_add, toNat_ofLimbs_extract,
            toNat_ofLimbs_extract]
      · show (_ : AzNat).toNat < 2^(64*(k+1))
        rw [toNat_sub, toNat_ofLimbs_extract, toNat_add, toNat_ofLimbs_extract,
            toNat_ofLimbs_extract]
        have h_a := abs_diff_lt k m h_mk A0 A1 A2
                      (sliceToNat_lt_pow a lo k)
                      (sliceToNat_lt_pow a (lo + k) k)
                      (sliceToNat_lt_pow a (lo + 2 * k) m)
        simp only [if_neg (by omega : ¬ A0 + A2 ≥ A1)] at h_a
        omega
    · -- s0 + s2 ≥ s1: return (s0 + s2) - s1, sign true.
      simp only [h, ↓reduceIte]
      have h_ge_nat : A0 + A2 ≥ A1 := by
        rw [show A0 = (ofLimbs (a.extract lo (lo + k))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm,
            show A2 = (ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm,
            show A1 = (ofLimbs (a.extract (lo + k) (lo + k + k))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm]
        rw [← toNat_add]
        exact Nat.le_of_not_lt fun hlt => h ((azNat_lt_iff_toNat_lt _ _).mpr hlt)
      rw [if_pos h_ge_nat]
      rw [truncatePad_toNat]
      · show (_ : AzNat).toNat = _
        rw [toNat_sub, toNat_add, toNat_ofLimbs_extract, toNat_ofLimbs_extract,
            toNat_ofLimbs_extract]
      · show (_ : AzNat).toNat < 2^(64*(k+1))
        rw [toNat_sub, toNat_add, toNat_ofLimbs_extract, toNat_ofLimbs_extract,
            toNat_ofLimbs_extract]
        have h_a := abs_diff_lt k m h_mk A0 A1 A2
                      (sliceToNat_lt_pow a lo k)
                      (sliceToNat_lt_pow a (lo + k) k)
                      (sliceToNat_lt_pow a (lo + 2 * k) m)
        simp only [if_pos h_ge_nat] at h_a
        exact h_a
  · -- Sign bit.
    by_cases h : ofLimbs (a.extract lo (lo + k))
                  + ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))
                < ofLimbs (a.extract (lo + k) (lo + k + k))
    · simp only [h, ↓reduceIte]
      have h_lt_nat : A0 + A2 < A1 := by
        rw [show A0 = (ofLimbs (a.extract lo (lo + k))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm,
            show A2 = (ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm,
            show A1 = (ofLimbs (a.extract (lo + k) (lo + k + k))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm]
        rw [← toNat_add]
        exact (azNat_lt_iff_toNat_lt _ _).mp h
      simp; omega
    · simp only [h, ↓reduceIte]
      have h_ge_nat : A0 + A2 ≥ A1 := by
        rw [show A0 = (ofLimbs (a.extract lo (lo + k))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm,
            show A2 = (ofLimbs (a.extract (lo + 2 * k) (lo + 2 * k + m))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm,
            show A1 = (ofLimbs (a.extract (lo + k) (lo + k + k))).toNat
              from (toNat_ofLimbs_extract _ _ _).symm]
        rw [← toNat_add]
        exact Nat.le_of_not_lt fun hlt => h ((azNat_lt_iff_toNat_lt _ _).mpr hlt)
      simp; omega

-- ── Slice values as a single nat decomposition ─────────────────────────────

/-- The slice of length `k + k + m` decomposes as `A_0 + A_1·β^k + A_2·β^{2k}`. -/
private lemma slice_decomp_3 (a : Array UInt64) (lo k m : Nat)
    (h : lo + (k + k + m) ≤ a.size) :
    toNatLimbsList ((a.toList.drop lo).take (k + k + m))
      = sliceToNat a lo k
        + sliceToNat a (lo + k) k * 2 ^ (64 * k)
        + sliceToNat a (lo + 2 * k) m * 2 ^ (64 * (2 * k)) := by
  have h_split1 : toNatLimbsList ((a.toList.drop lo).take (k + (k + m)))
                    = toNatLimbsList ((a.toList.drop lo).take k)
                      + toNatLimbsList ((a.toList.drop (lo + k)).take (k + m)) * 2 ^ (64 * k) := by
    exact toNat_slice_split a lo k (k + m) (by omega)
  have h_split2 : toNatLimbsList ((a.toList.drop (lo + k)).take (k + m))
                    = toNatLimbsList ((a.toList.drop (lo + k)).take k)
                      + toNatLimbsList ((a.toList.drop (lo + k + k)).take m) * 2 ^ (64 * k) := by
    exact toNat_slice_split a (lo + k) k m (by omega)
  rw [show k + k + m = k + (k + m) from by ring, h_split1, h_split2]
  rw [show lo + k + k = lo + 2 * k from by ring]
  unfold sliceToNat
  rw [show (2 : Nat) ^ (64 * (2 * k)) = 2 ^ (64 * k) * 2 ^ (64 * k) from pow_double_factor k]
  ring

-- ── Toom-Cook 3 polynomial identity (Nat) ──────────────────────────────────

/-- Toom-Cook 3-way polynomial identity (cleared of denominators).  Given the
    five evaluation points `v_0, v_1, v_{-1}, v_2, v_∞` and the algorithm's
    formulas for `t_1, t_2, c_0, …, c_4`, the assembled polynomial
    evaluated at `K` recovers the product of the input polynomials.

    Proved by 4-way case analysis on `(sgnA, sgnB)`; see the original
    `toomCook3_nat_identity` for the algebraic skeleton. -/
theorem toomCook3_nat_identity (A0 A1 A2 B0 B1 B2 K : ℕ)
    (sgnA sgnB : Bool)
    (h_sgnA : sgnA = true ↔ A1 ≤ A0 + A2)
    (h_sgnB : sgnB = true ↔ B1 ≤ B0 + B2) :
    let v0      := A0 * B0
    let v1      := (A0 + A1 + A2) * (B0 + B1 + B2)
    let vm1_abs := (if A1 ≤ A0 + A2 then A0 + A2 - A1 else A1 - (A0 + A2))
                    * (if B1 ≤ B0 + B2 then B0 + B2 - B1 else B1 - (B0 + B2))
    let v2      := (A0 + 2 * A1 + 4 * A2) * (B0 + 2 * B1 + 4 * B2)
    let vinf    := A2 * B2
    let vm1_sign : Bool := sgnA == sgnB
    let t1_num := if vm1_sign then 3 * v0 + v2 + 2 * vm1_abs
                  else 3 * v0 + v2 - 2 * vm1_abs
    let t1 := t1_num / 6 - 2 * vinf
    let t2_num := if vm1_sign then v1 + vm1_abs else v1 - vm1_abs
    let t2 := t2_num / 2
    let c0 := v0
    let c1 := v1 - t1
    let c2 := t2 - v0 - vinf
    let c3 := t1 - t2
    let c4 := vinf
    c0 + c1 * K + c2 * K ^ 2 + c3 * K ^ 3 + c4 * K ^ 4
      = (A0 + A1 * K + A2 * K ^ 2) * (B0 + B1 * K + B2 * K ^ 2) := by
  set Q := A0*B0 + A0*B2 + A1*B1 + A1*B2 + A2*B0 + A2*B1 + 3*(A2*B2) with hQ_def
  set P := A0*B0 + A0*B2 + A1*B1 + A2*B0 + A2*B2 with hP_def
  by_cases hA : A1 ≤ A0 + A2 <;> by_cases hB : B1 ≤ B0 + B2
  -- ── Case (T, T) ────────────────────────────────────────────────────────
  · have hsA : sgnA = true := h_sgnA.mpr hA
    have hsB : sgnB = true := h_sgnB.mpr hB
    simp only [hsA, hsB, if_pos hA, if_pos hB, beq_self_eq_true, if_true]
    have h_t1_eq6 : 3 * (A0 * B0) + (A0 + 2 * A1 + 4 * A2) * (B0 + 2 * B1 + 4 * B2)
                    + 2 * ((A0 + A2 - A1) * (B0 + B2 - B1)) = 6 * Q := by
      rw [hQ_def]; zify [hA, hB]; ring
    have h_t2_eq2 : (A0 + A1 + A2) * (B0 + B1 + B2) + (A0 + A2 - A1) * (B0 + B2 - B1)
                    = 2 * P := by
      rw [hP_def]; zify [hA, hB]; ring
    rw [h_t1_eq6, h_t2_eq2,
        Nat.mul_div_right _ (by decide : 0 < 6), Nat.mul_div_right _ (by decide : 0 < 2)]
    have h_v1_eq : (A0 + A1 + A2) * (B0 + B1 + B2)
                   = A0*B0 + A0*B1 + A0*B2 + A1*B0 + A1*B1 + A1*B2 + A2*B0 + A2*B1 + A2*B2 := by
      ring
    rw [h_v1_eq, hQ_def, hP_def]
    have h_c1 : A0*B0+A0*B1+A0*B2+A1*B0+A1*B1+A1*B2+A2*B0+A2*B1+A2*B2
                - (A0*B0+A0*B2+A1*B1+A1*B2+A2*B0+A2*B1+3*(A2*B2) - 2*(A2*B2))
                = A0*B1 + A1*B0 := by omega
    have h_c2 : A0*B0+A0*B2+A1*B1+A2*B0+A2*B2 - A0*B0 - A2*B2
                = A0*B2 + A1*B1 + A2*B0 := by omega
    have h_c3 : A0*B0+A0*B2+A1*B1+A1*B2+A2*B0+A2*B1+3*(A2*B2) - 2*(A2*B2)
                - (A0*B0+A0*B2+A1*B1+A2*B0+A2*B2) = A1*B2 + A2*B1 := by omega
    rw [h_c1, h_c2, h_c3]; ring
  -- ── Case (T, F) ────────────────────────────────────────────────────────
  · have hsA : sgnA = true := h_sgnA.mpr hA
    have hsB : sgnB = false := by
      rcases h_b : sgnB with _ | _
      · rfl
      · exact absurd (h_sgnB.mp h_b) hB
    have hB' : B0 + B2 ≤ B1 := Nat.le_of_lt (Nat.lt_of_not_le hB)
    simp only [hsA, hsB, if_pos hA, if_neg hB,
               show ((true : Bool) == false) = false from rfl,
               Bool.false_eq_true, if_false]
    have h_t1_safe : 2 * ((A0 + A2 - A1) * (B1 - (B0 + B2)))
                    ≤ 3 * (A0 * B0) + (A0 + 2 * A1 + 4 * A2) * (B0 + 2 * B1 + 4 * B2) := by
      zify [hA, hB']
      nlinarith [mul_nonneg (Nat.cast_nonneg A0 : (0:ℤ) ≤ _) (Nat.cast_nonneg B0 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A0 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A1 : (0:ℤ) ≤ _) (Nat.cast_nonneg B1 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A1 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B0 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B1 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _)]
    have h_t2_safe : (A0 + A2 - A1) * (B1 - (B0 + B2)) ≤ (A0 + A1 + A2) * (B0 + B1 + B2) := by
      zify [hA, hB']
      nlinarith [mul_nonneg (Nat.cast_nonneg A0 : (0:ℤ) ≤ _) (Nat.cast_nonneg B0 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A0 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A1 : (0:ℤ) ≤ _) (Nat.cast_nonneg B1 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B0 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _)]
    have h_t1_eq6 : 3 * (A0 * B0) + (A0 + 2 * A1 + 4 * A2) * (B0 + 2 * B1 + 4 * B2)
                    - 2 * ((A0 + A2 - A1) * (B1 - (B0 + B2))) = 6 * Q := by
      rw [hQ_def]; zify [h_t1_safe, hA, hB']; ring
    have h_t2_eq2 : (A0 + A1 + A2) * (B0 + B1 + B2) - (A0 + A2 - A1) * (B1 - (B0 + B2))
                    = 2 * P := by
      rw [hP_def]; zify [h_t2_safe, hA, hB']; ring
    rw [h_t1_eq6, h_t2_eq2,
        Nat.mul_div_right _ (by decide : 0 < 6), Nat.mul_div_right _ (by decide : 0 < 2)]
    have h_v1_eq : (A0 + A1 + A2) * (B0 + B1 + B2)
                   = A0*B0 + A0*B1 + A0*B2 + A1*B0 + A1*B1 + A1*B2 + A2*B0 + A2*B1 + A2*B2 := by
      ring
    rw [h_v1_eq, hQ_def, hP_def]
    have h_c1 : A0*B0+A0*B1+A0*B2+A1*B0+A1*B1+A1*B2+A2*B0+A2*B1+A2*B2
                - (A0*B0+A0*B2+A1*B1+A1*B2+A2*B0+A2*B1+3*(A2*B2) - 2*(A2*B2))
                = A0*B1 + A1*B0 := by omega
    have h_c2 : A0*B0+A0*B2+A1*B1+A2*B0+A2*B2 - A0*B0 - A2*B2
                = A0*B2 + A1*B1 + A2*B0 := by omega
    have h_c3 : A0*B0+A0*B2+A1*B1+A1*B2+A2*B0+A2*B1+3*(A2*B2) - 2*(A2*B2)
                - (A0*B0+A0*B2+A1*B1+A2*B0+A2*B2) = A1*B2 + A2*B1 := by omega
    rw [h_c1, h_c2, h_c3]; ring
  -- ── Case (F, T) ────────────────────────────────────────────────────────
  · have hsA : sgnA = false := by
      rcases h_a : sgnA with _ | _
      · rfl
      · exact absurd (h_sgnA.mp h_a) hA
    have hsB : sgnB = true := h_sgnB.mpr hB
    have hA' : A0 + A2 ≤ A1 := Nat.le_of_lt (Nat.lt_of_not_le hA)
    simp only [hsA, hsB, if_neg hA, if_pos hB,
               show ((false : Bool) == true) = false from rfl,
               Bool.false_eq_true, if_false]
    have h_t1_safe : 2 * ((A1 - (A0 + A2)) * (B0 + B2 - B1))
                    ≤ 3 * (A0 * B0) + (A0 + 2 * A1 + 4 * A2) * (B0 + 2 * B1 + 4 * B2) := by
      zify [hA', hB]
      nlinarith [mul_nonneg (Nat.cast_nonneg A0 : (0:ℤ) ≤ _) (Nat.cast_nonneg B0 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A0 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A1 : (0:ℤ) ≤ _) (Nat.cast_nonneg B1 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A1 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B0 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B1 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _)]
    have h_t2_safe : (A1 - (A0 + A2)) * (B0 + B2 - B1) ≤ (A0 + A1 + A2) * (B0 + B1 + B2) := by
      zify [hA', hB]
      nlinarith [mul_nonneg (Nat.cast_nonneg A0 : (0:ℤ) ≤ _) (Nat.cast_nonneg B0 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A0 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A1 : (0:ℤ) ≤ _) (Nat.cast_nonneg B1 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A1 : (0:ℤ) ≤ _) (Nat.cast_nonneg B2 : (0:ℤ) ≤ _),
                 mul_nonneg (Nat.cast_nonneg A2 : (0:ℤ) ≤ _) (Nat.cast_nonneg B0 : (0:ℤ) ≤ _)]
    have h_t1_eq6 : 3 * (A0 * B0) + (A0 + 2 * A1 + 4 * A2) * (B0 + 2 * B1 + 4 * B2)
                    - 2 * ((A1 - (A0 + A2)) * (B0 + B2 - B1)) = 6 * Q := by
      rw [hQ_def]; zify [h_t1_safe, hA', hB]; ring
    have h_t2_eq2 : (A0 + A1 + A2) * (B0 + B1 + B2) - (A1 - (A0 + A2)) * (B0 + B2 - B1)
                    = 2 * P := by
      rw [hP_def]; zify [h_t2_safe, hA', hB]; ring
    rw [h_t1_eq6, h_t2_eq2,
        Nat.mul_div_right _ (by decide : 0 < 6), Nat.mul_div_right _ (by decide : 0 < 2)]
    have h_v1_eq : (A0 + A1 + A2) * (B0 + B1 + B2)
                   = A0*B0 + A0*B1 + A0*B2 + A1*B0 + A1*B1 + A1*B2 + A2*B0 + A2*B1 + A2*B2 := by
      ring
    rw [h_v1_eq, hQ_def, hP_def]
    have h_c1 : A0*B0+A0*B1+A0*B2+A1*B0+A1*B1+A1*B2+A2*B0+A2*B1+A2*B2
                - (A0*B0+A0*B2+A1*B1+A1*B2+A2*B0+A2*B1+3*(A2*B2) - 2*(A2*B2))
                = A0*B1 + A1*B0 := by omega
    have h_c2 : A0*B0+A0*B2+A1*B1+A2*B0+A2*B2 - A0*B0 - A2*B2
                = A0*B2 + A1*B1 + A2*B0 := by omega
    have h_c3 : A0*B0+A0*B2+A1*B1+A1*B2+A2*B0+A2*B1+3*(A2*B2) - 2*(A2*B2)
                - (A0*B0+A0*B2+A1*B1+A2*B0+A2*B2) = A1*B2 + A2*B1 := by omega
    rw [h_c1, h_c2, h_c3]; ring
  -- ── Case (F, F) ────────────────────────────────────────────────────────
  · have hsA : sgnA = false := by
      rcases h_a : sgnA with _ | _
      · rfl
      · exact absurd (h_sgnA.mp h_a) hA
    have hsB : sgnB = false := by
      rcases h_b : sgnB with _ | _
      · rfl
      · exact absurd (h_sgnB.mp h_b) hB
    have hA' : A0 + A2 ≤ A1 := Nat.le_of_lt (Nat.lt_of_not_le hA)
    have hB' : B0 + B2 ≤ B1 := Nat.le_of_lt (Nat.lt_of_not_le hB)
    simp only [hsA, hsB, if_neg hA, if_neg hB, beq_self_eq_true, if_true]
    have h_t1_eq6 : 3 * (A0 * B0) + (A0 + 2 * A1 + 4 * A2) * (B0 + 2 * B1 + 4 * B2)
                    + 2 * ((A1 - (A0 + A2)) * (B1 - (B0 + B2))) = 6 * Q := by
      rw [hQ_def]; zify [hA', hB']; ring
    have h_t2_eq2 : (A0 + A1 + A2) * (B0 + B1 + B2) + (A1 - (A0 + A2)) * (B1 - (B0 + B2))
                    = 2 * P := by
      rw [hP_def]; zify [hA', hB']; ring
    rw [h_t1_eq6, h_t2_eq2,
        Nat.mul_div_right _ (by decide : 0 < 6), Nat.mul_div_right _ (by decide : 0 < 2)]
    have h_v1_eq : (A0 + A1 + A2) * (B0 + B1 + B2)
                   = A0*B0 + A0*B1 + A0*B2 + A1*B0 + A1*B1 + A1*B2 + A2*B0 + A2*B1 + A2*B2 := by
      ring
    rw [h_v1_eq, hQ_def, hP_def]
    have h_c1 : A0*B0+A0*B1+A0*B2+A1*B0+A1*B1+A1*B2+A2*B0+A2*B1+A2*B2
                - (A0*B0+A0*B2+A1*B1+A1*B2+A2*B0+A2*B1+3*(A2*B2) - 2*(A2*B2))
                = A0*B1 + A1*B0 := by omega
    have h_c2 : A0*B0+A0*B2+A1*B1+A2*B0+A2*B2 - A0*B0 - A2*B2
                = A0*B2 + A1*B1 + A2*B0 := by omega
    have h_c3 : A0*B0+A0*B2+A1*B1+A1*B2+A2*B0+A2*B1+3*(A2*B2) - 2*(A2*B2)
                - (A0*B0+A0*B2+A1*B1+A2*B0+A2*B2) = A1*B2 + A2*B1 := by omega
    rw [h_c1, h_c2, h_c3]; ring

-- ── Interpolation helper correctness ────────────────────────────────────────

/-- `divBy6`'s quotient `toNat` is exactly `Nat`-division by `6`. -/
private lemma divBy6_quotient_toNat (U : AzNat) : (divBy6 U).1.toNat = U.toNat / 6 := by
  have ⟨h_eq, h_r⟩ := toNat_divBy6 U
  omega

/-- `<<<` notation version of `toNat_shiftLeft`. -/
private lemma azNat_toNat_hShiftLeft (a : AzNat) (sh : Nat) :
    (a <<< sh).toNat = a.toNat * 2 ^ sh :=
  toNat_shiftLeft a sh

/-- `>>>` notation version of `toNat_shiftRight`. -/
private lemma azNat_toNat_hShiftRight (a : AzNat) (sh : Nat) :
    (a >>> sh).toNat = a.toNat / 2 ^ sh :=
  toNat_shiftRight a sh

/-- The interpolation helper's `toNat` matches the Nat-level interpolation
    formula.  Stated to plug directly into `toomCook3_nat_identity`.

    Note that AzNat `-` is truncated subtraction (matching `Nat`-sub), so the
    Nat-side formula uses the same `let`-binding shape as the algorithm. -/
theorem toomCook3Interpolate_toNat (v0_az v1_az v2_az vm1_az vinf_az : AzNat)
    (vm1_sign : Bool) (k : Nat) :
    let v0 := v0_az.toNat
    let v1 := v1_az.toNat
    let v2 := v2_az.toNat
    let vm1 := vm1_az.toNat
    let vinf := vinf_az.toNat
    let t1_num := if vm1_sign then 3 * v0 + v2 + 2 * vm1
                  else 3 * v0 + v2 - 2 * vm1
    let t1 := t1_num / 6 - 2 * vinf
    let t2_num := if vm1_sign then v1 + vm1 else v1 - vm1
    let t2 := t2_num / 2
    let c0 := v0
    let c1 := v1 - t1
    let c2 := t2 - v0 - vinf
    let c3 := t1 - t2
    let c4 := vinf
    let K := 2 ^ (64 * k)
    (toomCook3Interpolate v0_az v1_az v2_az vm1_az vinf_az vm1_sign k).toNat
      = c0 + c1 * K + c2 * K ^ 2 + c3 * K ^ 3 + c4 * K ^ 4 := by
  unfold toomCook3Interpolate
  cases vm1_sign with
  | false =>
    simp only [Bool.false_eq_true, if_false,
               azNat_toNat_hShiftLeft, azNat_toNat_hShiftRight,
               toNat_add, toNat_sub, toNat_mulUInt64, divBy6_quotient_toNat,
               show (2 : UInt64).toNat = 2 from rfl,
               show (3 : UInt64).toNat = 3 from rfl,
               show (2 : Nat) ^ 1 = 2 from rfl]
    ring_nf
  | true =>
    simp only [if_true,
               azNat_toNat_hShiftLeft, azNat_toNat_hShiftRight,
               toNat_add, toNat_sub, toNat_mulUInt64, divBy6_quotient_toNat,
               show (2 : UInt64).toNat = 2 from rfl,
               show (3 : UInt64).toNat = 3 from rfl,
               show (2 : Nat) ^ 1 = 2 from rfl]
    ring_nf

-- ── Main theorem ────────────────────────────────────────────────────────────

/-- Correctness of `toomCook3MulLimbsRec`.  Strong induction on `len`; base
    case delegates to Karatsuba; recursive case applies the IH to each of
    the five sub-products and assembles via `toomCook3Interpolate_toNat`
    + `toomCook3_nat_identity`. -/
theorem toomCook3MulLimbsRec_toNat (toomThreshold karaThreshold : Nat) :
    ∀ (len : Nat) (a b : Array UInt64) (loA loB : Nat)
      (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size),
    toNatLimbsList
        (toomCook3MulLimbsRec toomThreshold karaThreshold a b loA loB len hA hB).val.toList
      = toNatLimbsList ((a.toList.drop loA).take len)
        * toNatLimbsList ((b.toList.drop loB).take len) := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intros a b loA loB hA hB
    unfold toomCook3MulLimbsRec
    by_cases h_base : len < toomThreshold ∨ len < 3
    · simp only [h_base, ↓reduceDIte]
      exact karatsubaMulLimbs_toNat karaThreshold a b loA loB len hA hB
    · simp only [h_base, ↓reduceDIte]
      have hlen : 3 ≤ len := by omega
      let k := (len + 2) / 3
      let m := len - 2 * k
      have hk_pos : 0 < k := by show 0 < (len + 2) / 3; omega
      have hk_lt : k < len := by show (len + 2) / 3 < len; omega
      have hk1_lt : k + 1 < len := by show (len + 2) / 3 + 1 < len; omega
      have hm_le_k : m ≤ k := by show len - 2 * ((len + 2) / 3) ≤ (len + 2) / 3; omega
      have hm_lt : m < len := by show len - 2 * ((len + 2) / 3) < len; omega
      have hA0 : loA + k ≤ a.size := by omega
      have hB0 : loB + k ≤ b.size := by omega
      have hA2 : (loA + 2 * k) + m ≤ a.size := by omega
      have hB2 : (loB + 2 * k) + m ≤ b.size := by omega
      let s0a := sum012 a loA k m
      let s0b := sum012 b loB k m
      let s2a := sum124 a loA k m
      let s2b := sum124 b loB k m
      let da := diffM1 a loA k m
      let db := diffM1 b loB k m
      have hs0a_sz : 0 + (k + 1) ≤ s0a.size := by
        show 0 + (k + 1) ≤ (sum012 a loA k m).size
        unfold sum012; rw [truncatePad_size]; omega
      have hs0b_sz : 0 + (k + 1) ≤ s0b.size := by
        show 0 + (k + 1) ≤ (sum012 b loB k m).size
        unfold sum012; rw [truncatePad_size]; omega
      have hs2a_sz : 0 + (k + 1) ≤ s2a.size := by
        show 0 + (k + 1) ≤ (sum124 a loA k m).size
        unfold sum124; rw [truncatePad_size]; omega
      have hs2b_sz : 0 + (k + 1) ≤ s2b.size := by
        show 0 + (k + 1) ≤ (sum124 b loB k m).size
        unfold sum124; rw [truncatePad_size]; omega
      have hda_sz : 0 + (k + 1) ≤ da.1.size := diffM1_size_ge _ _ _ _
      have hdb_sz : 0 + (k + 1) ≤ db.1.size := diffM1_size_ge _ _ _ _
      -- IH applications.
      have h_v0_eq := ih k hk_lt a b loA loB hA0 hB0
      have h_v1_eq := ih (k + 1) hk1_lt s0a s0b 0 0 hs0a_sz hs0b_sz
      have h_v2_eq := ih (k + 1) hk1_lt s2a s2b 0 0 hs2a_sz hs2b_sz
      have h_vm1_eq := ih (k + 1) hk1_lt da.1 db.1 0 0 hda_sz hdb_sz
      have h_vinf_eq := ih m hm_lt a b (loA + 2 * k) (loB + 2 * k) hA2 hB2
      have h_s0a_eq := sum012_toNat a loA k m hm_le_k
      have h_s0b_eq := sum012_toNat b loB k m hm_le_k
      have h_s2a_eq := sum124_toNat a loA k m hm_le_k
      have h_s2b_eq := sum124_toNat b loB k m hm_le_k
      have h_da_eq := diffM1_toNat a loA k m hm_le_k
      have h_db_eq := diffM1_toNat b loB k m hm_le_k
      let A0 := sliceToNat a loA k
      let A1 := sliceToNat a (loA + k) k
      let A2 := sliceToNat a (loA + 2 * k) m
      let B0 := sliceToNat b loB k
      let B1 := sliceToNat b (loB + k) k
      let B2 := sliceToNat b (loB + 2 * k) m
      let v0  := toomCook3MulLimbsRec toomThreshold karaThreshold a b loA loB k hA0 hB0
      let v1  := toomCook3MulLimbsRec toomThreshold karaThreshold
                   s0a s0b 0 0 (k + 1) hs0a_sz hs0b_sz
      let v2  := toomCook3MulLimbsRec toomThreshold karaThreshold
                   s2a s2b 0 0 (k + 1) hs2a_sz hs2b_sz
      let vm1 := toomCook3MulLimbsRec toomThreshold karaThreshold
                   da.1 db.1 0 0 (k + 1) hda_sz hdb_sz
      let vinf := toomCook3MulLimbsRec toomThreshold karaThreshold
                    a b (loA + 2 * k) (loB + 2 * k) m hA2 hB2
      have hv0_sz : v0.1.size = 2 * k := v0.2
      have hv1_sz : v1.1.size = 2 * (k + 1) := v1.2
      have hv2_sz : v2.1.size = 2 * (k + 1) := v2.2
      have hvm1_sz : vm1.1.size = 2 * (k + 1) := vm1.2
      have hvinf_sz : vinf.1.size = 2 * m := vinf.2
      -- AzNat-level toNats of the recursive products.
      have h_v0_n : (ofLimbs v0.1).toNat = A0 * B0 := by
        rw [toNat_ofLimbs, h_v0_eq]; rfl
      have h_vinf_n : (ofLimbs vinf.1).toNat = A2 * B2 := by
        rw [toNat_ofLimbs, h_vinf_eq]; rfl
      have h_s0a_size : s0a.size = k + 1 := by
        show (sum012 a loA k m).size = k + 1
        unfold sum012; exact truncatePad_size _ _
      have h_s0b_size : s0b.size = k + 1 := by
        show (sum012 b loB k m).size = k + 1
        unfold sum012; exact truncatePad_size _ _
      have h_s2a_size : s2a.size = k + 1 := by
        show (sum124 a loA k m).size = k + 1
        unfold sum124; exact truncatePad_size _ _
      have h_s2b_size : s2b.size = k + 1 := by
        show (sum124 b loB k m).size = k + 1
        unfold sum124; exact truncatePad_size _ _
      have h_da_size : da.1.size = k + 1 := diffM1_size _ _ _ _
      have h_db_size : db.1.size = k + 1 := diffM1_size _ _ _ _
      have h_v1_n : (ofLimbs v1.1).toNat = (A0 + A1 + A2) * (B0 + B1 + B2) := by
        rw [toNat_ofLimbs, h_v1_eq]
        rw [List.drop_zero, List.drop_zero]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_s0a_size])]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_s0b_size])]
        rw [h_s0a_eq, h_s0b_eq]
      have h_v2_n : (ofLimbs v2.1).toNat
                      = (A0 + 2 * A1 + 4 * A2) * (B0 + 2 * B1 + 4 * B2) := by
        rw [toNat_ofLimbs, h_v2_eq]
        rw [List.drop_zero, List.drop_zero]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_s2a_size])]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_s2b_size])]
        rw [h_s2a_eq, h_s2b_eq]
      have h_vm1_n : (ofLimbs vm1.1).toNat
                      = (if A0 + A2 ≥ A1 then A0 + A2 - A1 else A1 - (A0 + A2))
                        * (if B0 + B2 ≥ B1 then B0 + B2 - B1 else B1 - (B0 + B2)) := by
        rw [toNat_ofLimbs, h_vm1_eq]
        rw [List.drop_zero, List.drop_zero]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_da_size])]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_db_size])]
        rw [h_da_eq.1, h_db_eq.1]
      -- Apply the interpolation helper's correctness.
      have h_interp := toomCook3Interpolate_toNat (ofLimbs v0.1) (ofLimbs v1.1)
        (ofLimbs v2.1) (ofLimbs vm1.1) (ofLimbs vinf.1) (da.2 == db.2) k
      simp only [h_v0_n, h_v1_n, h_v2_n, h_vm1_n, h_vinf_n] at h_interp
      -- Now apply the Nat polynomial identity.
      have h_identity := toomCook3_nat_identity A0 A1 A2 B0 B1 B2 (2 ^ (64 * k))
        da.2 db.2 h_da_eq.2 h_db_eq.2
      -- The interpolate result's toNat equals the polynomial product.
      have h_result_toNat :
          (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
              (ofLimbs vm1.1) (ofLimbs vinf.1) (da.2 == db.2) k).toNat
            = (A0 + A1 * 2 ^ (64 * k) + A2 * (2 ^ (64 * k)) ^ 2)
              * (B0 + B1 * 2 ^ (64 * k) + B2 * (2 ^ (64 * k)) ^ 2) := by
        rw [h_interp]; exact h_identity
      -- Slice decompositions of the operand slices.
      have hk_K_sq : (2 ^ (64 * k)) ^ 2 = 2 ^ (64 * (2 * k)) := by
        rw [← pow_mul]; ring_nf
      have h_a_decomp : toNatLimbsList ((a.toList.drop loA).take len)
                       = A0 + A1 * 2 ^ (64 * k) + A2 * (2 ^ (64 * k)) ^ 2 := by
        rw [hk_K_sq, show len = k + k + m from by omega]
        exact slice_decomp_3 a loA k m (by omega)
      have h_b_decomp : toNatLimbsList ((b.toList.drop loB).take len)
                       = B0 + B1 * 2 ^ (64 * k) + B2 * (2 ^ (64 * k)) ^ 2 := by
        rw [hk_K_sq, show len = k + k + m from by omega]
        exact slice_decomp_3 b loB k m (by omega)
      have h_a_lt : toNatLimbsList ((a.toList.drop loA).take len) < 2 ^ (64 * len) :=
        slice_lt_pow a loA len
      have h_b_lt : toNatLimbsList ((b.toList.drop loB).take len) < 2 ^ (64 * len) :=
        slice_lt_pow b loB len
      have h_prod_bound : (A0 + A1 * 2 ^ (64 * k) + A2 * (2 ^ (64 * k)) ^ 2)
                          * (B0 + B1 * 2 ^ (64 * k) + B2 * (2 ^ (64 * k)) ^ 2)
                          < 2 ^ (64 * (2 * len)) := by
        rw [← h_a_decomp, ← h_b_decomp,
            show 64 * (2 * len) = 64 * len + 64 * len from by ring, pow_add]
        exact Nat.mul_lt_mul'' h_a_lt h_b_lt
      -- Use `show` to convert the goal into the truncatePad form (definitionally
      -- equal to the algorithm's `⟨truncatePad ..., _⟩.val.toList`).
      show toNatLimbsList (truncatePad
          (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
            (ofLimbs vm1.1) (ofLimbs vinf.1) (da.2 == db.2) k).limbs
          (2 * len)).toList = _
      -- Bridge `(interpolate).toNat` to `toNatLimbsList (interpolate).limbs.toList`
      -- (definitionally equal) and use the polynomial-product bound.
      have h_bound : toNatLimbsList
            (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
              (ofLimbs vm1.1) (ofLimbs vinf.1) (da.2 == db.2) k).limbs.toList
            < 2 ^ (64 * (2 * len)) := by
        show (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
              (ofLimbs vm1.1) (ofLimbs vinf.1) (da.2 == db.2) k).toNat < _
        rw [h_result_toNat]; exact h_prod_bound
      rw [truncatePad_toNat _ _ h_bound]
      -- Goal: toNatLimbsList (interpolate ...).limbs.toList = (slice a) * (slice b).
      show (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
            (ofLimbs vm1.1) (ofLimbs vinf.1) (da.2 == db.2) k).toNat = _
      rw [h_result_toNat, ← h_a_decomp, ← h_b_decomp]

/-- Correctness of `toomCook3MulLimbs` (un-Subtyped). -/
theorem toomCook3MulLimbs_toNat (toomThreshold karaThreshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    toNatLimbsList (toomCook3MulLimbs toomThreshold karaThreshold a b loA loB len hA hB).toList
      = toNatLimbsList ((a.toList.drop loA).take len)
        * toNatLimbsList ((b.toList.drop loB).take len) :=
  toomCook3MulLimbsRec_toNat toomThreshold karaThreshold len a b loA loB hA hB

/-- AzNat-level correctness of `mulToomCook3`. -/
theorem toNat_mulToomCook3 (toomThreshold karaThreshold : Nat) (a b : AzNat) :
    (mulToomCook3 toomThreshold karaThreshold a b).toNat = a.toNat * b.toNat := by
  unfold mulToomCook3
  by_cases h : a.limbs.size = 0 ∨ b.limbs.size = 0
  · rw [if_pos h]
    show (0 : AzNat).toNat = a.toNat * b.toNat
    rcases h with ha | hb
    · have ha_toNat : a.toNat = 0 := by
        show toNatLimbsList a.limbs.toList = 0
        have : a.limbs.toList = [] := by
          rw [← Array.length_toList] at ha
          exact List.eq_nil_of_length_eq_zero ha
        rw [this]; rfl
      simp [ha_toNat]
    · have hb_toNat : b.toNat = 0 := by
        show toNatLimbsList b.limbs.toList = 0
        have : b.limbs.toList = [] := by
          rw [← Array.length_toList] at hb
          exact List.eq_nil_of_length_eq_zero hb
        rw [this]; rfl
      simp [hb_toNat]
  · rw [if_neg h]
    set n := max a.limbs.size b.limbs.size
    set aPadded : Array UInt64 := a.limbs ++ Array.replicate (n - a.limbs.size) 0
    set bPadded : Array UInt64 := b.limbs ++ Array.replicate (n - b.limbs.size) 0
    show (ofLimbs (toomCook3MulLimbs toomThreshold karaThreshold aPadded bPadded
            0 0 n _ _)).toNat = a.toNat * b.toNat
    rw [toNat_ofLimbs, toomCook3MulLimbs_toNat]
    have h_aPadded_size : aPadded.size = n := by
      show (a.limbs ++ Array.replicate (n - a.limbs.size) (0 : UInt64)).size = n
      rw [Array.size_append, Array.size_replicate]
      have h_le : a.limbs.size ≤ n := Nat.le_max_left _ _
      omega
    have h_bPadded_size : bPadded.size = n := by
      show (b.limbs ++ Array.replicate (n - b.limbs.size) (0 : UInt64)).size = n
      rw [Array.size_append, Array.size_replicate]
      have h_le : b.limbs.size ≤ n := Nat.le_max_right _ _
      omega
    rw [List.drop_zero, List.drop_zero]
    rw [List.take_of_length_le (by rw [Array.length_toList, h_aPadded_size])]
    rw [List.take_of_length_le (by rw [Array.length_toList, h_bPadded_size])]
    show toNatLimbsList aPadded.toList * toNatLimbsList bPadded.toList = a.toNat * b.toNat
    have h_a_eq : toNatLimbsList aPadded.toList = a.toNat := by
      show toNatLimbsList (a.limbs ++ Array.replicate (n - a.limbs.size) (0 : UInt64)).toList
              = a.toNat
      rw [Array.toList_append, Array.toList_replicate]
      rw [toNatLimbsList_append_zeros]
      rfl
    have h_b_eq : toNatLimbsList bPadded.toList = b.toNat := by
      show toNatLimbsList (b.limbs ++ Array.replicate (n - b.limbs.size) (0 : UInt64)).toList
              = b.toNat
      rw [Array.toList_append, Array.toList_replicate]
      rw [toNatLimbsList_append_zeros]
      rfl
    rw [h_a_eq, h_b_eq]

-- ── 3-way dispatch correctness ──────────────────────────────────────────────

/-- Correctness of `mulLimbs`: agrees with `Nat` multiplication over the
    slices, regardless of which branch (schoolbook / Karatsuba / Toom-Cook 3)
    fires. -/
theorem mulLimbs_toNat (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    toNatLimbsList (mulLimbs a b loA lenA loB lenB hA hB).toList
      = toNatLimbsList ((a.toList.drop loA).take lenA)
        * toNatLimbsList ((b.toList.drop loB).take lenB) := by
  unfold mulLimbs mulLimbsParam
  by_cases h : (mulDispatchThreshold ≤ min lenA lenB
                && mulDispatchKDen * min lenA lenB ≥ mulDispatchKNum * max lenA lenB) = true
  · -- Balanced branch.  The padded slices are shared between the Karatsuba
    -- and Toom-Cook 3 sub-branches.
    rw [if_pos h]
    set lenMax := max lenA lenB with hlenMax_def
    set aSlice : Array UInt64 := a.extract loA (loA + lenA) with hAslice_def
    set bSlice : Array UInt64 := b.extract loB (loB + lenB) with hBslice_def
    set aPadded : Array UInt64 := aSlice ++ Array.replicate (lenMax - lenA) 0
      with haPad_def
    set bPadded : Array UInt64 := bSlice ++ Array.replicate (lenMax - lenB) 0
      with hbPad_def
    have hAslice_toList : aSlice.toList = (a.toList.drop loA).take lenA := by
      rw [hAslice_def, Array.toList_extract, List.extract_eq_take_drop]
      congr 1; omega
    have hBslice_toList : bSlice.toList = (b.toList.drop loB).take lenB := by
      rw [hBslice_def, Array.toList_extract, List.extract_eq_take_drop]
      congr 1; omega
    have hAslice_size : aSlice.size = lenA := by
      rw [hAslice_def, Array.size_extract]; omega
    have hBslice_size : bSlice.size = lenB := by
      rw [hBslice_def, Array.size_extract]; omega
    have hLenA_le : lenA ≤ lenMax := by rw [hlenMax_def]; exact Nat.le_max_left _ _
    have hLenB_le : lenB ≤ lenMax := by rw [hlenMax_def]; exact Nat.le_max_right _ _
    have haPad_size : aPadded.size = lenMax := by
      rw [haPad_def]
      show (aSlice ++ Array.replicate (lenMax - lenA) (0 : UInt64)).size = lenMax
      rw [Array.size_append, hAslice_size, Array.size_replicate]; omega
    have hbPad_size : bPadded.size = lenMax := by
      rw [hbPad_def]
      show (bSlice ++ Array.replicate (lenMax - lenB) (0 : UInt64)).size = lenMax
      rw [Array.size_append, hBslice_size, Array.size_replicate]; omega
    have haPad_toNat :
        toNatLimbsList aPadded.toList = toNatLimbsList ((a.toList.drop loA).take lenA) := by
      rw [haPad_def]
      show toNatLimbsList ((aSlice ++ Array.replicate (lenMax - lenA) (0 : UInt64)).toList)
            = toNatLimbsList ((a.toList.drop loA).take lenA)
      rw [Array.toList_append, Array.toList_replicate]
      rw [toNatLimbsList_append_zeros, hAslice_toList]
    have hbPad_toNat :
        toNatLimbsList bPadded.toList = toNatLimbsList ((b.toList.drop loB).take lenB) := by
      rw [hbPad_def]
      show toNatLimbsList ((bSlice ++ Array.replicate (lenMax - lenB) (0 : UInt64)).toList)
            = toNatLimbsList ((b.toList.drop loB).take lenB)
      rw [Array.toList_append, Array.toList_replicate]
      rw [toNatLimbsList_append_zeros, hBslice_toList]
    have h_aslice_full :
        (aPadded.toList.drop 0).take lenMax = aPadded.toList := by
      rw [List.drop_zero, List.take_of_length_le]
      rw [Array.length_toList, haPad_size]
    have h_bslice_full :
        (bPadded.toList.drop 0).take lenMax = bPadded.toList := by
      rw [List.drop_zero, List.take_of_length_le]
      rw [Array.length_toList, hbPad_size]
    by_cases h' : mulDispatchToomCook3Cutoff ≤ lenMax
    · -- Toom-Cook 3 sub-branch.
      rw [if_pos h']
      have h_toom :=
        toomCook3MulLimbs_toNat mulDispatchToomCook3Cutoff mulDispatchThreshold
          aPadded bPadded 0 0 lenMax
          (by rw [haPad_size]; omega) (by rw [hbPad_size]; omega)
      rw [h_aslice_full, h_bslice_full] at h_toom
      rw [h_toom, haPad_toNat, hbPad_toNat]
    · -- Karatsuba sub-branch.
      rw [if_neg h']
      have h_kara :=
        karatsubaMulLimbs_toNat mulDispatchThreshold aPadded bPadded 0 0 lenMax
          (by rw [haPad_size]; omega) (by rw [hbPad_size]; omega)
      rw [h_aslice_full, h_bslice_full] at h_kara
      rw [h_kara, haPad_toNat, hbPad_toNat]
  · -- Schoolbook branch.
    rw [if_neg h]
    exact schoolbookMulLimbs_toNat a b loA lenA loB lenB hA hB

/-- Correctness of `mul` (the dispatched AzNat multiplication, used by `*`). -/
theorem toNat_mul (a b : AzNat) : (a * b).toNat = a.toNat * b.toNat := by
  show (mul a b).toNat = _
  unfold mul
  rw [toNat_ofLimbs, mulLimbs_toNat]
  show toNatLimbsList ((a.limbs.toList.drop 0).take a.limbs.size)
        * toNatLimbsList ((b.limbs.toList.drop 0).take b.limbs.size) = a.toNat * b.toNat
  rw [List.drop_zero, List.drop_zero]
  rw [List.take_of_length_le (by rw [Array.length_toList])]
  rw [List.take_of_length_le (by rw [Array.length_toList])]
  rfl

/-- `ofNat`-version of `toNat_mul`. -/
theorem ofNat_mul (m n : Nat) : ofNat (m * n) = ofNat m * ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_mul, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat

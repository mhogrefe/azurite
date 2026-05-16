import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.LimbDigits
import Azurite.AzNat.Equiv.Mul.Karatsuba
import Azurite.AzNat.Equiv.OfLimbDigitsPow2
import Azurite.AzNat.OfLimbDigits
import Azurite.UInt64.Equiv.MaxPow
import Azurite.UInt64.Equiv.OfDigits
import Mathlib.Data.Nat.Digits.Defs

namespace Azurite.AzNat

/-! ### Horner correctness for AzNat foldr -/

private theorem toNat_ofLimbs_single (u : UInt64) :
    (AzNat.ofLimbs #[u]).toNat = u.toNat := by
  rw [toNat_ofLimbs]
  show toNatLimbsList [u] = u.toNat
  simp [toNatLimbsList]

private theorem toNat_horner_foldr (P : UInt64) (digits : Array UInt64) :
    (digits.foldr (init := (0 : AzNat))
        (fun d acc => acc * AzNat.ofLimbs #[P] + AzNat.ofLimbs #[d])).toNat =
      Nat.ofDigits (P.toNat : Nat) (digits.toList.map UInt64.toNat) := by
  rw [← Array.foldr_toList]
  induction digits.toList with
  | nil =>
    show (0 : AzNat).toNat = Nat.ofDigits (P.toNat : Nat) []
    simp [Nat.ofDigits]
  | cons d ds ih =>
    rw [List.foldr_cons]
    rw [toNat_add, toNat_mul, toNat_ofLimbs_single, toNat_ofLimbs_single, ih]
    rw [List.map_cons, Nat.ofDigits_cons]
    ring

/-! ### Regrouping: `Fin`-indexed chunked `Nat.ofDigits`

If we group base-`b` digits into `n` chunks of size `E` (with the last
chunk possibly shorter), then `Nat.ofDigits b` of the flattened sequence
equals `Nat.ofDigits (b ^ E)` of the per-chunk `Nat.ofDigits b` values. -/

private theorem ofDigits_chunks_ofFn (b E : Nat) :
    ∀ (n : Nat) (chunk : Fin n → List Nat)
      (_h_len : ∀ i : Fin n, i.val + 1 < n → (chunk i).length = E),
    Nat.ofDigits ((b ^ E : Nat))
        (List.ofFn fun i : Fin n => Nat.ofDigits b (chunk i)) =
      Nat.ofDigits b (List.ofFn chunk).flatten := by
  intro n
  induction n with
  | zero =>
    intro _ _
    show (0 : Nat) = Nat.ofDigits b ([] : List Nat)
    rfl
  | succ n ih =>
    intro chunk h_len
    rw [List.ofFn_succ, List.ofFn_succ, Nat.ofDigits_cons, List.flatten_cons,
        Nat.ofDigits_append]
    by_cases h_n_zero : n = 0
    · subst h_n_zero
      show Nat.ofDigits b (chunk 0) + (b ^ E) * Nat.ofDigits ((b ^ E : Nat)) [] =
           Nat.ofDigits b (chunk 0) + b ^ (chunk 0).length * Nat.ofDigits b []
      simp
    · have h_first_len : (chunk 0).length = E :=
        h_len 0 (by show 0 + 1 < n + 1; omega)
      rw [h_first_len]
      have h_rest_len : ∀ i : Fin n, i.val + 1 < n →
          ((fun j : Fin n => chunk j.succ) i).length = E := by
        intro i hi_lt
        apply h_len i.succ
        show i.val + 1 + 1 < n + 1
        omega
      rw [ih _ h_rest_len]

/-! ### Super-digit value: chunk → `UInt64.ofDigits` → `Nat.ofDigits` -/

private theorem toNat_uint64_ofDigits_chunk (b : UInt64) (chunk : Array UInt64)
    (h_val_lt : Nat.ofDigits (b.toNat : Nat) (chunk.toList.map UInt64.toNat) < 2 ^ 64) :
    (UInt64.ofDigits b chunk).toNat =
      Nat.ofDigits (b.toNat : Nat) (chunk.toList.map UInt64.toNat) := by
  rw [UInt64.ofDigits_eq]
  exact Nat.mod_eq_of_lt h_val_lt

/-! ### Partitioning identity: chunks of an array reconstruct the original -/

private theorem flatten_chunks_eq_toList (digits : Array UInt64) (E : Nat) (hE : 1 ≤ E) :
    (List.ofFn (n := (digits.size + E - 1) / E) fun i : Fin _ =>
        (digits.extract (i.val * E) (min (i.val * E + E) digits.size)).toList).flatten
      = digits.toList := by
  set n := (digits.size + E - 1) / E with hn_def
  suffices h : ∀ k : Nat, k ≤ n →
      (List.ofFn (n := k) fun i : Fin k =>
          (digits.extract (i.val * E) (min (i.val * E + E) digits.size)).toList).flatten
        = digits.toList.take (min (k * E) digits.size) by
    have h_full := h n (Nat.le_refl n)
    rw [h_full]
    have h_n_ge : n * E ≥ digits.size := by
      have h_dm := Nat.div_add_mod (digits.size + E - 1) E
      have h_mod_lt : (digits.size + E - 1) % E < E := Nat.mod_lt _ hE
      rw [hn_def, Nat.mul_comm]
      omega
    rw [min_eq_right h_n_ge]
    apply List.take_of_length_le
    rw [Array.length_toList]
  intro k hk
  induction k with
  | zero =>
    show ([] : List (List UInt64)).flatten = digits.toList.take (min (0 * E) digits.size)
    simp
  | succ k ih =>
    have hk' : k ≤ n := by omega
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.flatten_singleton]
    have h_castSucc_eq :
        (List.ofFn fun i : Fin k =>
            (digits.extract (i.castSucc.val * E)
              (min (i.castSucc.val * E + E) digits.size)).toList)
          = List.ofFn fun i : Fin k =>
              (digits.extract (i.val * E) (min (i.val * E + E) digits.size)).toList := by
      congr 1
    rw [h_castSucc_eq, ih hk']
    rw [Fin.val_last, Array.toList_extract, List.extract_eq_drop_take']
    rw [show (k + 1) * E = k * E + E from by ring]
    rw [show digits.toList.take (min (k * E) digits.size) =
          (digits.toList.take (min (k * E + E) digits.size)).take (k * E) from by
      rw [List.take_take]
      congr 1
      omega]
    exact List.take_append_drop _ _

/-! ### Generic Horner build correctness

For any `b ≥ 2` and a precomputed `(P, E)` with `P.toNat = b.toNat ^ E`
(plus `E ≥ 1` and `b.toNat ^ E < 2 ^ 64` so each super-digit fits in a
`UInt64`), the chunked Horner build matches `Nat.ofDigits b`. Both
`ofLimbDigits` (with `P, E = UInt64.maxPow b`) and `ofBase10Digits`
(with the precomputed `UInt64.maxPow10`, `UInt64.maxPow10Exp`) reduce
to this. -/

private theorem toNat_hornerBuild (b : UInt64) (hb : 2 ≤ b.toNat)
    (P : UInt64) (E : Nat) (hP_val : P.toNat = b.toNat ^ E)
    (hE_pos : 1 ≤ E) (hbE_lt : b.toNat ^ E < 2 ^ 64)
    (digits : Array UInt64)
    (hd : ∀ x ∈ digits.toList.map UInt64.toNat, x < b.toNat) :
    ((Array.ofFn (n := (digits.size + E - 1) / E) fun i : Fin _ =>
        UInt64.ofDigits b
          (digits.extract (i.val * E) (min (i.val * E + E) digits.size))).foldr
        (init := (0 : AzNat))
        (fun d acc => acc * AzNat.ofLimbs #[P] + AzNat.ofLimbs #[d])).toNat =
      Nat.ofDigits (b.toNat : Nat) (digits.toList.map UInt64.toNat) := by
  set numSuperDigits := (digits.size + E - 1) / E with hN_def
  -- For each chunk, the digits are bounded by b.
  have h_chunk_digit_lt : ∀ (i : Nat) x,
      x ∈ (digits.extract (i * E) (min (i * E + E) digits.size)).toList.map UInt64.toNat →
        x < b.toNat := by
    intro i x hx
    apply hd
    rw [Array.toList_extract] at hx
    rw [List.mem_map] at hx
    obtain ⟨u, hu_mem, hu_eq⟩ := hx
    rw [List.extract_eq_drop_take'] at hu_mem
    have h_u_in : u ∈ digits.toList :=
      List.mem_of_mem_take (List.mem_of_mem_drop hu_mem)
    rw [List.mem_map]
    exact ⟨u, h_u_in, hu_eq⟩
  -- Each chunk's value is less than 2^64.
  have h_chunk_val_lt : ∀ i : Nat,
      Nat.ofDigits (b.toNat : Nat)
          ((digits.extract (i * E) (min (i * E + E) digits.size)).toList.map UInt64.toNat)
        < 2 ^ 64 := by
    intro i
    have h_chunk_size_le : ((digits.extract (i * E)
          (min (i * E + E) digits.size)).toList.map UInt64.toNat).length ≤ E := by
      rw [List.length_map, Array.length_toList, Array.size_extract]
      omega
    have h_lt := Nat.ofDigits_lt_base_pow_length (b := b.toNat) (by omega)
      (h_chunk_digit_lt i)
    have h_pow_le : b.toNat ^ _ ≤ b.toNat ^ E :=
      Nat.pow_le_pow_right (by omega) h_chunk_size_le
    omega
  -- Apply Horner correctness; convert P.toNat → b^E.
  rw [toNat_horner_foldr, hP_val]
  -- Rewrite the super-digit list: each entry is `Nat.ofDigits b chunk`.
  rw [show (Array.ofFn (n := numSuperDigits) fun i : Fin numSuperDigits =>
            UInt64.ofDigits b
              (digits.extract (i.val * E) (min (i.val * E + E) digits.size))).toList.map
            UInt64.toNat =
          List.ofFn (n := numSuperDigits) fun i : Fin numSuperDigits =>
            Nat.ofDigits (b.toNat : Nat)
              ((digits.extract (i.val * E) (min (i.val * E + E) digits.size)).toList.map
                UInt64.toNat) from by
    rw [Array.toList_ofFn, List.map_ofFn]
    congr 1
    funext i
    exact toNat_uint64_ofDigits_chunk b _ (h_chunk_val_lt i.val)]
  -- Apply chunked-Nat.ofDigits regrouping.
  rw [ofDigits_chunks_ofFn _ _ numSuperDigits
      (fun i : Fin numSuperDigits =>
        (digits.extract (i.val * E) (min (i.val * E + E) digits.size)).toList.map
          UInt64.toNat)
      (by
        intro i hi_lt
        rw [List.length_map, Array.length_toList, Array.size_extract]
        have h_n_ge : (numSuperDigits - 1) * E ≤ digits.size := by
          have h_dm := Nat.div_add_mod (digits.size + E - 1) E
          have h_mod_lt : (digits.size + E - 1) % E < E := Nat.mod_lt _ hE_pos
          have h_dm' : (digits.size + E - 1) / E * E + (digits.size + E - 1) % E
                        = digits.size + E - 1 := by
            rw [Nat.mul_comm]; exact h_dm
          have h_n_E_le : numSuperDigits * E ≤ digits.size + E - 1 := by
            rw [hN_def]; omega
          rw [Nat.sub_one_mul]
          omega
        have h_i_succ_le : i.val + 1 ≤ numSuperDigits - 1 := by omega
        have h_i_succ_E_le : (i.val + 1) * E ≤ (numSuperDigits - 1) * E :=
          Nat.mul_le_mul_right E h_i_succ_le
        have h_chunk_full : i.val * E + E ≤ digits.size := by
          have : (i.val + 1) * E = i.val * E + E := by ring
          omega
        rw [min_eq_left h_chunk_full]
        omega)]
  -- Apply flatten = digits.toList.map.
  rw [List.ofFn_comp' (n := numSuperDigits)
      (fun i : Fin numSuperDigits =>
        (digits.extract (i.val * E) (min (i.val * E + E) digits.size)).toList)
      (List.map UInt64.toNat)]
  rw [← List.map_flatten]
  rw [flatten_chunks_eq_toList _ _ hE_pos]

/-! ### Base-10 specialisation correctness -/

/-- **Correctness of `AzNat.ofBase10Digits`.** For each input digit `< 10`,
    the reconstructed `AzNat` has the value `Nat.ofDigits 10` of the digit
    list. -/
theorem toNat_ofBase10Digits (digits : Array UInt64)
    (hd : ∀ x ∈ digits.toList.map UInt64.toNat, x < 10) :
    (AzNat.ofBase10Digits digits).toNat =
      Nat.ofDigits (10 : Nat) (digits.toList.map UInt64.toNat) := by
  unfold AzNat.ofBase10Digits
  have h10 : (10 : UInt64).toNat = 10 := rfl
  have hb : 2 ≤ (10 : UInt64).toNat := by rw [h10]; omega
  have h_P_val : UInt64.maxPow10.toNat = (10 : UInt64).toNat ^ UInt64.maxPow10Exp := by decide
  have h_E_pos : 1 ≤ UInt64.maxPow10Exp := by decide
  have h_bE_lt : (10 : UInt64).toNat ^ UInt64.maxPow10Exp < 2 ^ 64 := by decide
  have hd' : ∀ x ∈ digits.toList.map UInt64.toNat, x < (10 : UInt64).toNat := by
    rw [h10]; exact hd
  rw [toNat_hornerBuild (10 : UInt64) hb UInt64.maxPow10 UInt64.maxPow10Exp h_P_val h_E_pos
    h_bE_lt digits hd', h10]

/-! ### Main correctness theorem -/

/-- **Correctness of `AzNat.ofLimbDigits`.** For `2 ≤ b.toNat` and each input
    digit `< b.toNat`, the reconstructed `AzNat` has the value `Nat.ofDigits b`
    of the digit list. -/
theorem toNat_ofLimbDigits (b : UInt64) (hb : 2 ≤ b.toNat) (digits : Array UInt64)
    (hd : ∀ x ∈ digits.toList.map UInt64.toNat, x < b.toNat) :
    (AzNat.ofLimbDigits b digits).toNat =
      Nat.ofDigits (b.toNat : Nat) (digits.toList.map UInt64.toNat) := by
  unfold AzNat.ofLimbDigits
  have hb_uint : ¬ b < 2 := by
    rw [UInt64.lt_iff_toNat_lt_toNat]
    show ¬ b.toNat < (2 : UInt64).toNat
    show ¬ b.toNat < 2
    omega
  rw [if_neg hb_uint]
  by_cases hpow : b.isPowerOfTwo
  · -- Power-of-two branch: delegate to `ofLimbDigitsPow2`.
    rw [if_pos hpow]
    have h_b_ne : b ≠ 0 := by
      intro he; unfold UInt64.isPowerOfTwo at hpow; rw [he] at hpow; simp at hpow
    have h_bv_ne : b.toBitVec ≠ 0#64 := fun hb' =>
      h_b_ne (UInt64.eq_of_toBitVec_eq hb')
    have h_bv_lt := BitVec.ctz_lt_iff_ne_zero.mpr h_bv_ne
    rw [BitVec.lt_def] at h_bv_lt
    have h_64_eq : ((↑(64 : Nat) : BitVec 64)).toNat = 64 := by decide
    have h_b_eq : b.toNat = 2 ^ b.toBitVec.ctz.toNat :=
      UInt64.toNat_eq_two_pow_ctz b hpow
    have h_ctz_ge : 1 ≤ b.toBitVec.ctz.toNat := by
      have h_2_le : 2 ≤ 2 ^ b.toBitVec.ctz.toNat := by omega
      by_contra hc
      push Not at hc
      have : b.toBitVec.ctz.toNat = 0 := by omega
      rw [this] at h_2_le; simp at h_2_le
    have h_ctz_le : b.toBitVec.ctz.toNat ≤ 64 := by omega
    have h_digits_lt : ∀ x ∈ digits.toList.map UInt64.toNat, x < 2 ^ b.toBitVec.ctz.toNat := by
      intro x hx; rw [← h_b_eq]; exact hd x hx
    rw [toNat_ofLimbDigitsPow2 _ h_ctz_ge h_ctz_le digits h_digits_lt, ← h_b_eq]
  · rw [if_neg hpow]
    by_cases hb10 : b = 10
    · -- Base-10 branch.
      rw [if_pos hb10]
      subst hb10
      exact toNat_ofBase10Digits digits hd
    · -- Generic Horner branch.
      rw [if_neg hb10]
      have h_correct := UInt64.maxPow_correct b hb
      have h_P_val : (UInt64.maxPow b).1.toNat = b.toNat ^ (UInt64.maxPow b).2 := h_correct.1
      have h_overflow : 2 ^ 64 ≤ b.toNat ^ ((UInt64.maxPow b).2 + 1) := h_correct.2
      have h_E_pos : 1 ≤ (UInt64.maxPow b).2 := by
        by_contra h; push Not at h
        have h_E_zero : (UInt64.maxPow b).2 = 0 := by omega
        rw [h_E_zero] at h_overflow; simp at h_overflow
        have : b.toNat < 2 ^ 64 := UInt64.toNat_lt b
        omega
      have h_bE_lt : b.toNat ^ (UInt64.maxPow b).2 < 2 ^ 64 := by
        have : (UInt64.maxPow b).1.toNat < 2 ^ 64 := UInt64.toNat_lt _
        omega
      exact toNat_hornerBuild b hb (UInt64.maxPow b).1 (UInt64.maxPow b).2
        h_P_val h_E_pos h_bE_lt digits hd

/-! ### Round-trip: `ofLimbDigits ∘ limbDigits = id` -/

/-- **Round-trip with `limbDigits`.** For `2 ≤ b.toNat`, reconstructing an
    `AzNat` from its base-`b` digits gives back the original. -/
theorem ofLimbDigits_limbDigits (b : UInt64) (hb : 2 ≤ b.toNat) (n : AzNat) :
    AzNat.ofLimbDigits b (n.limbDigits b) = n := by
  apply toNat_injective
  have h_digits_lt : ∀ x ∈ (n.limbDigits b).toList.map UInt64.toNat, x < b.toNat := by
    intro x hx
    rw [limbDigits_eq b hb n] at hx
    exact Nat.digits_lt_base (by omega) hx
  rw [toNat_ofLimbDigits b hb _ h_digits_lt]
  rw [limbDigits_eq b hb n]
  rw [Nat.ofDigits_digits]

end Azurite.AzNat

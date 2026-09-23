import Azurite.AzNat.Equiv.LimbDigits
import Azurite.AzNat.ToStringBase
import Batteries.Data.Char.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace Azurite

/-! ### Bridge: Lean core's `Nat.toDigits` matches Mathlib's `Nat.digits`

Lean core's `Nat.toDigits b n` produces digit characters MSB-first by
repeated division. Mathlib's `Nat.digits b n` produces the same digit
*values* LSB-first. For `b ≥ 2` and `n > 0`, reversing `Nat.digits` and
mapping through `Nat.digitChar` recovers `Nat.toDigits`.

The two functions diverge at `n = 0` (Lean's `toDigits` produces
`['0']`, Mathlib's `digits` produces `[]`); we handle that separately
where it matters. -/

private theorem nat_toDigits_eq_reverse_map_digits {b n : Nat} (hb : 1 < b) (hn : 0 < n) :
    Nat.toDigits b n = (Nat.digits b n).reverse.map Nat.digitChar := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h_lt : n < b
    · rw [Nat.toDigits_of_lt_base h_lt]
      have h_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
      rw [Nat.digits_of_lt b n h_ne h_lt]
      simp
    · push Not at h_lt
      have h_n_div_pos : 0 < n / b :=
        Nat.div_pos_iff.mpr ⟨by omega, h_lt⟩
      have h_n_div_lt : n / b < n := Nat.div_lt_self hn hb
      rw [Nat.toDigits_of_base_le hb h_lt]
      rw [Nat.digits_def' hb hn]
      rw [List.reverse_cons, List.map_append]
      rw [ih (n / b) h_n_div_lt h_n_div_pos]
      simp

/-! ### Per-digit character agreement

For digit values `< 16`, `AzNat.digitToChar d false` matches
`Nat.digitChar d.toNat`. Beyond that point our function continues to
emit `g`–`z` (i.e., we extend the alphabet up to base 36), whereas
`Nat.digitChar` emits `'*'`. -/

private theorem digitToChar_eq_digitChar (d : UInt64) (hd : d.toNat < 16) :
    AzNat.digitToChar d false = Nat.digitChar d.toNat := by
  unfold AzNat.digitToChar
  generalize h_d_nat : d.toNat = k at hd
  interval_cases k <;> rfl

/-! ### Main equivalences -/

/-- For `b.toNat ∈ [2, 16]`, `AzNat.toStringBase b n` matches Lean core's
    `String.ofList (Nat.toDigits b.toNat n.toNat)`. The two agree on the
    digit alphabet (`0`–`9`, `a`–`f`); we extend to `g`–`z` for digits
    `16`–`35` when `b.toNat ∈ [17, 36]`, whereas `Nat.toDigits` emits
    `'*'` outside `b ≤ 16` — see `AzNat.ToStringBase` for the wider
    alphabet contract. -/
theorem AzNat.toStringBase_eq (n : AzNat) (b : UInt64)
    (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 16) :
    n.toStringBase b = String.ofList (Nat.toDigits b.toNat n.toNat) := by
  unfold AzNat.toStringBase AzNat.toStringBaseWith
  have hb_lt : ¬ (b < 2 ∨ 36 < b) := by
    push Not
    rw [UInt64.not_lt, UInt64.not_lt]
    refine ⟨?_, ?_⟩
    · show (2 : UInt64).toNat ≤ b.toNat
      show (2 : Nat) ≤ b.toNat
      omega
    · show b.toNat ≤ (36 : UInt64).toNat
      show b.toNat ≤ (36 : Nat)
      omega
  rw [ite_eq_right hb_lt]
  -- usePrefix = false ⇒ no prefix branch
  show (if (n.limbs.size = 0) then "0" else
        String.ofList ((n.limbDigits b).toList.reverse.map (fun d =>
          AzNat.digitToChar d false))) = _
  by_cases h_zero : n.limbs.size = 0
  · rw [ite_eq_left h_zero]
    have h_n_zero : n.toNat = 0 := by
      show toNatLimbsList n.limbs.toList = 0
      have h_nil : n.limbs.toList = [] :=
        List.length_eq_zero_iff.mp (by rw [Array.length_toList, h_zero])
      rw [h_nil]; rfl
    rw [h_n_zero, Nat.toDigits_zero]
  · rw [ite_eq_right h_zero]
    have h_n_pos : 0 < n.toNat := by
      by_contra h_nlt
      push Not at h_nlt
      have h_zero_eq : n.toNat = 0 := by omega
      have h_last := n.last_ne_zero
      have h_nil : n.limbs.toList = [] := by
        apply toNatLimbsList_eq_zero_of_getLast_ne_zero
        · rw [← Array.getLast?_toList] at h_last
          exact h_last
        · exact h_zero_eq
      apply h_zero
      rw [← Array.length_toList, h_nil]
      rfl
    -- Compute LHS chars
    have h_chars_eq : (n.limbDigits b).toList.reverse.map (fun d =>
        AzNat.digitToChar d false) = Nat.toDigits b.toNat n.toNat := by
      rw [nat_toDigits_eq_reverse_map_digits (by omega) h_n_pos]
      have h_limbs_eq := limbDigits_eq b (by omega : 2 ≤ b.toNat) n
      have h_lt_b : ∀ x ∈ (n.limbDigits b).toList.map UInt64.toNat, x < b.toNat := by
        intro x hx
        rw [h_limbs_eq] at hx
        exact Nat.digits_lt_base (by omega) hx
      rw [← h_limbs_eq, ← List.map_reverse, List.map_map]
      apply List.map_congr_left
      intro u hu
      have hu_orig : u ∈ (n.limbDigits b).toList := List.mem_reverse.mp hu
      have hu_lt : u.toNat < b.toNat := by
        apply h_lt_b
        rw [List.mem_map]
        exact ⟨u, hu_orig, rfl⟩
      show AzNat.digitToChar u false = Nat.digitChar u.toNat
      exact digitToChar_eq_digitChar u (by omega)
    rw [h_chars_eq]

/-- The `ToString AzNat` instance produces the same string as the
    `ToString Nat` instance on `n.toNat`. (Stated against `Nat.repr`,
    which is what the `ToString Nat` instance is.) -/
theorem AzNat.toString_eq (n : AzNat) :
    (toString n : String) = Nat.repr n.toNat := by
  show AzNat.toString n = Nat.repr n.toNat
  unfold AzNat.toString
  rw [AzNat.toStringBase_eq n 10 (by decide) (by decide)]
  rfl

/-- `AzNat.toString n` is never the empty string (it is at least `"0"`). -/
theorem AzNat.toString_ne_empty (n : AzNat) : (AzNat.toString n).toList ≠ [] := by
  have h_b_in : ¬ ((10 : UInt64) < 2 ∨ 36 < (10 : UInt64)) := by decide
  by_cases h_size : n.limbs.size = 0
  · have h_str : AzNat.toString n = "0" := by
      unfold AzNat.toString AzNat.toStringBase AzNat.toStringBaseWith
      rw [ite_eq_right h_b_in]; simp [h_size]
    rw [h_str]; decide
  · have h_str : AzNat.toString n = String.ofList
        ((n.limbDigits 10).toList.reverse.map fun d => AzNat.digitToChar d false) := by
      unfold AzNat.toString AzNat.toStringBase AzNat.toStringBaseWith
      rw [ite_eq_right h_b_in]; simp [h_size]
    rw [h_str, String.toList_ofList]
    intro he
    rw [List.map_eq_nil_iff, List.reverse_eq_nil_iff] at he
    have h_n_pos : 0 < n.toNat := by
      by_contra h_nlt; push Not at h_nlt
      have h_zero : n.toNat = 0 := by omega
      have h_last_inv := n.last_ne_zero
      have h_nil : n.limbs.toList = [] := by
        apply toNatLimbsList_eq_zero_of_getLast_ne_zero
        · rw [← Array.getLast?_toList] at h_last_inv; exact h_last_inv
        · exact h_zero
      apply h_size
      rw [← Array.length_toList, h_nil]; rfl
    have h_digits_ne : Nat.digits 10 n.toNat ≠ [] :=
      Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have h_lim_eq := Azurite.AzNat.limbDigits_eq 10 (by decide) n
    rw [he] at h_lim_eq
    simp at h_lim_eq
    exact h_digits_ne h_lim_eq

/-- `AzNat.toString 0 = "0"`. -/
theorem AzNat.toString_zero : (AzNat.toString 0).toList = ['0'] := rfl

/-- Every character of `AzNat.toString n` is a decimal digit `'0'`–`'9'`. -/
theorem AzNat.toString_char_digit (n : AzNat) (c : Char)
    (hc : c ∈ (AzNat.toString n).toList) :
    '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat := by
  have h_b_in : ¬ ((10 : UInt64) < 2 ∨ 36 < (10 : UInt64)) := by decide
  by_cases h_size : n.limbs.size = 0
  · have h_str : AzNat.toString n = "0" := by
      unfold AzNat.toString AzNat.toStringBase AzNat.toStringBaseWith
      rw [ite_eq_right h_b_in]; simp [h_size]
    rw [h_str] at hc
    have h_c_eq : c = '0' := by
      rw [show ("0" : String).toList = ['0'] from rfl] at hc
      exact List.mem_singleton.mp hc
    subst h_c_eq
    exact ⟨le_refl _, by decide⟩
  · have h_str : AzNat.toString n = String.ofList
        ((n.limbDigits 10).toList.reverse.map fun d => AzNat.digitToChar d false) := by
      unfold AzNat.toString AzNat.toStringBase AzNat.toStringBaseWith
      rw [ite_eq_right h_b_in]; simp [h_size]
    rw [h_str, String.toList_ofList, List.mem_map] at hc
    obtain ⟨d, hd_mem, hd_eq⟩ := hc
    rw [List.mem_reverse] at hd_mem
    have h_mapped : d.toNat ∈ (n.limbDigits 10).toList.map UInt64.toNat :=
      List.mem_map_of_mem hd_mem
    rw [Azurite.AzNat.limbDigits_eq 10 (by decide) n] at h_mapped
    have h_d_lt : d.toNat < 10 :=
      Nat.digits_lt_base (by decide : 1 < (10 : UInt64).toNat) h_mapped
    -- digitToChar d false for d < 10 gives Char.ofNat ('0'.toNat + d.toNat).
    have h_dc : AzNat.digitToChar d false = Char.ofNat ('0'.toNat + d.toNat) := by
      unfold AzNat.digitToChar
      rw [ite_eq_left h_d_lt]
    rw [h_dc] at hd_eq
    subst hd_eq
    have h_zero : ('0' : Char).toNat = 48 := rfl
    have h_nine : ('9' : Char).toNat = 57 := rfl
    have h_valid : ('0'.toNat + d.toNat).isValidChar := by
      show '0'.toNat + d.toNat < 0xd800 ∨ _
      left; omega
    have h_char_toNat : (Char.ofNat ('0'.toNat + d.toNat)).toNat = '0'.toNat + d.toNat := by
      rw [Char.toNat_ofNat, ite_eq_left h_valid]
    rw [h_char_toNat]
    omega

end Azurite

import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Parse
import Azurite.AzNat.Equiv.ParseBase
import Batteries.Data.Char.Basic

namespace Azurite.AzInt

private lemma azInt_ext (z1 z2 : AzInt) :
    z1.sign = z2.sign → z1.abs = z2.abs → z1 = z2 := by
  intro h1 h2; cases z1; cases z2; dsimp at h1 h2; subst h1 h2; rfl

/-- `AzNat.toString` never emits a leading `'-'` (all chars are decimal
digits). Used to rule out the negative-sign branch when round-tripping
positive `AzInt` values. -/
private lemma azNat_toString_not_dash (n : AzNat) :
    (AzNat.toString n).startsWith "-" = false := by
  rw [Bool.eq_false_iff, Ne, String.startsWith_string_iff]
  rintro ⟨t, ht⟩
  have h_min : ('-' : Char) ∈ (AzNat.toString n).toList := by rw [← ht]; simp
  have h_b_in : ¬ ((10 : UInt64) < 2 ∨ 36 < (10 : UInt64)) := by decide
  by_cases h_size : n.limbs.size = 0
  · have h_str : AzNat.toString n = "0" := by
      unfold AzNat.toString AzNat.toStringBase AzNat.toStringBaseWith
      rw [if_neg h_b_in]; simp [h_size]
    rw [h_str] at h_min; revert h_min; decide
  · have h_str : AzNat.toString n = String.ofList
        ((n.limbDigits 10).toList.reverse.map fun d => AzNat.digitToChar d false) := by
      unfold AzNat.toString AzNat.toStringBase AzNat.toStringBaseWith
      rw [if_neg h_b_in]; simp [h_size]
    rw [h_str, String.toList_ofList, List.mem_map] at h_min
    obtain ⟨d, hd_mem, hd_eq⟩ := h_min
    rw [List.mem_reverse] at hd_mem
    have h_mapped : d.toNat ∈ (n.limbDigits 10).toList.map UInt64.toNat :=
      List.mem_map_of_mem hd_mem
    rw [Azurite.AzNat.limbDigits_eq 10 (by decide) n] at h_mapped
    have h_d_lt : d.toNat < 10 :=
      Nat.digits_lt_base (by decide : 1 < (10 : UInt64).toNat) h_mapped
    have h_dc : AzNat.digitToChar d false = '-' := hd_eq
    unfold AzNat.digitToChar at h_dc
    rw [if_pos (by omega : d.toNat < 10)] at h_dc
    have h_eq_tonat := congrArg Char.toNat h_dc
    have h_45 : ('-' : Char).toNat = 45 := rfl
    have h_zero : ('0' : Char).toNat = 48 := rfl
    rw [h_45] at h_eq_tonat
    rw [Char.toNat_ofNat] at h_eq_tonat
    have h_valid : ('0'.toNat + d.toNat).isValidChar := by
      rw [h_zero]
      left; omega
    rw [if_pos h_valid, h_zero] at h_eq_tonat
    omega

private lemma drop_one_dash_append (s : String) :
    (("-" ++ s).drop 1).copy = s := by
  apply String.toList_inj.mp
  rw [String.toList_copy_drop, String.toList_append]
  rfl

/-- Round-trip: parsing the string rendered by `AzInt.toString` recovers the
original `AzInt`. -/
theorem parse_toString (z : AzInt) : AzInt.parse (AzInt.toString z) = some z := by
  unfold AzInt.parse AzInt.toString
  by_cases h_sign : z.sign
  · -- Positive: toString = AzNat.toString z.abs (no leading dash).
    rw [if_pos h_sign]
    rw [if_neg (by rw [azNat_toString_not_dash z.abs]; decide)]
    rw [AzNat.parse_toString z.abs]
    exact congrArg some (azInt_ext _ _ h_sign.symm rfl)
  · -- Negative: toString = "-" ++ AzNat.toString z.abs.
    rw [if_neg h_sign]
    have h_dash : ("-" ++ AzNat.toString z.abs).startsWith "-" = true := by
      rw [String.startsWith_string_iff]
      exact ⟨(AzNat.toString z.abs).toList, by simp⟩
    rw [if_pos h_dash]
    rw [drop_one_dash_append, AzNat.parse_toString z.abs]
    have h_abs_ne : z.abs ≠ 0 := by
      intro h_abs_zero
      have := z.zero_sign h_abs_zero
      rw [this] at h_sign; exact h_sign rfl
    simp only  -- reduce `match some _ with | some n => …` to its arm
    rw [dif_neg h_abs_ne]
    apply congrArg
    apply azInt_ext
    · show false = z.sign
      cases h_sign_val : z.sign
      · rfl
      · exact absurd h_sign_val h_sign
    · rfl

/-! ### Equivalence with `String.toInt?` (digit + optional `-` inputs)

For non-empty strings whose characters are decimal digits, optionally
preceded by a single `'-'`, `AzInt.parse` and Lean core's `String.toInt?`
agree (up to the `AzInt ↔ Int` translation). The digit-only precondition
rules out the `0x`/`0o`/`0b` prefix path that `AzNat.parse` accepts but
`String.toInt?` rejects; the non-zero precondition on the magnitude rules
out `"-0"` (which `String.toInt?` accepts as `0` but `AzInt.parse`
rejects, since `AzInt` has no negative-zero encoding). -/

private lemma startsWith_dash_decomp (s : String) (h : s.startsWith "-") :
    s = "-" ++ (s.drop 1).copy := by
  apply String.toList_inj.mp
  rw [String.toList_append, String.toList_copy_drop]
  rw [String.startsWith_string_iff] at h
  obtain ⟨t, ht⟩ := h
  rw [← ht]; rfl

private lemma drop_copy_toList (s : String) : (s.drop 1).copy.toList = s.toList.drop 1 := by
  rw [String.toList_copy_drop]

/-! ### Re-establishing the deleted `String.toInt?` lemmas

Lean v4.32 reimplemented `String.toInt?` via the new `String.Slice` API
(`s.toInt? = s.toSlice.toInt?`, with `Slice.toInt?` branching on
`s.dropPrefix? '-'`) and removed the lemmas the round-trip proofs below used.
The two private helpers `toInt?_pos` and `toInt?_minus_append'` re-establish
the needed facts against the new core definitions. -/

/-- `Slice.toNat?` depends only on the slice's character list (via `copy`):
two slices with equal `copy` parse to the same `Option Nat`. Needed because the
remainder slice produced by `dropPrefix? '-'` has the same characters as the
original tail but is not definitionally `rest.toSlice`. -/
private theorem slice_toNat?_congr (a b : String.Slice) (h : a.copy = b.copy) :
    a.toNat? = b.toNat? := by
  have hisnat : a.isNat = b.isNat := by
    unfold String.Slice.isNat
    simp only [String.Slice.forIn_eq_forIn_chars, ← Std.Iter.forIn_toList,
      String.Slice.toList_chars, h]
  unfold String.Slice.toNat?
  rw [hisnat, String.Slice.foldl_eq_foldl_toList, String.Slice.foldl_eq_foldl_toList, h]

/-- No leading dash ⇒ `String.toInt?` reduces to the natural-number parse.
Replaces the deleted `String.toInt?_eq_toNat?_of_startsWith_eq_false`. -/
private theorem toInt?_pos (s : String) (h : s.startsWith ('-' : Char) = false) :
    s.toInt? = s.toNat?.map Int.ofNat := by
  show s.toSlice.toInt? = _
  unfold String.Slice.toInt?
  have hnone : s.toSlice.dropPrefix? ('-' : Char) = none := by
    rw [String.Slice.dropPrefix?_eq_none_iff, String.startsWith_toSlice, h]
  rw [hnone]; rfl

/-- A single leading dash ⇒ `String.toInt?` negates the natural-number parse of
the remainder. Replaces the deleted `String.toInt?_minus_append`. -/
private theorem toInt?_minus_append' (rest : String) :
    ("-" ++ rest).toInt? = rest.toNat?.map Int.negOfNat := by
  show ("-" ++ rest).toSlice.toInt? = _
  unfold String.Slice.toInt?
  have hstart : ("-" ++ rest).toSlice.startsWith ('-' : Char) = true := by
    rw [String.startsWith_toSlice, String.startsWith_char_eq_head?]
    simp
  cases hdp : ("-" ++ rest).toSlice.dropPrefix? ('-' : Char) with
  | none =>
    rw [String.Slice.dropPrefix?_eq_none_iff] at hdp
    rw [hdp] at hstart; exact absurd hstart (by simp)
  | some R =>
    simp only
    have happ := String.Slice.eq_append_of_dropPrefix?_char_eq_some hdp
    rw [String.copy_toSlice] at happ
    have hsingle : String.singleton ('-' : Char) = "-" := rfl
    rw [hsingle] at happ
    -- happ : "-" ++ rest = "-" ++ R.copy
    have hrest : R.copy = rest := (String.append_right_inj "-" |>.mp happ).symm
    have hR : R.toNat? = rest.toSlice.toNat? :=
      slice_toNat?_congr R rest.toSlice (by rw [hrest, String.copy_toSlice])
    rw [hR]; rfl

/-- Positive case: no leading dash, decimal digits only. -/
theorem parse_eq_toInt?_of_digits (s : String) (h_ne : s ≠ "")
    (h_dig : ∀ c ∈ s.toList, '0' ≤ c ∧ c ≤ '9') :
    (AzInt.parse s).map AzInt.toInt = s.toInt? := by
  have h_dash : s.startsWith "-" = false := by
    rw [Bool.eq_false_iff, Ne, String.startsWith_string_iff]
    rintro ⟨t, ht⟩
    have h_min : ('-' : Char) ∈ s.toList := by rw [← ht]; simp
    have := h_dig '-' h_min
    have h_lo : (45 : Nat) ≥ 48 := this.1
    omega
  unfold AzInt.parse
  rw [if_neg (by rw [h_dash]; decide)]
  -- AzInt.parse s ≡ AzNat.parse s wrapped in positive AzInt.
  have h_nat_eq := AzNat.parse_eq_toNat? s h_ne h_dig
  have h_dash_char : s.startsWith ('-' : Char) = false := by
    rw [String.startsWith_char_eq_head?]
    cases h_head : s.toList.head? with
    | none => rfl
    | some c =>
      simp
      intro h_dash_c
      subst h_dash_c
      have h_mem : ('-' : Char) ∈ s.toList := List.mem_of_head? h_head
      have := h_dig '-' h_mem
      have h_lo : (45 : Nat) ≥ 48 := this.1
      omega
  rw [toInt?_pos s h_dash_char]
  rw [← h_nat_eq]
  cases h_an : AzNat.parse s with
  | none => simp
  | some n =>
    simp only [Option.map_some]
    show some (AzInt.toInt _) = some (n.toNat : Int)
    apply congrArg
    show ({ sign := true, abs := n, zero_sign := _ } : AzInt).toInt = (n.toNat : Int)
    unfold AzInt.toInt; simp

/-- Negative case: leading dash, non-empty digit-only magnitude with
non-zero value. -/
theorem parse_neg_eq_toInt?_of_digits (rest : String) (h_ne : rest ≠ "")
    (h_dig : ∀ c ∈ rest.toList, '0' ≤ c ∧ c ≤ '9')
    (h_nonzero : ∀ n, AzNat.parse rest = some n → n.toNat ≠ 0) :
    (AzInt.parse ("-" ++ rest)).map AzInt.toInt = ("-" ++ rest).toInt? := by
  unfold AzInt.parse
  have h_starts : ("-" ++ rest).startsWith "-" = true := by
    rw [String.startsWith_string_iff]
    exact ⟨rest.toList, by simp⟩
  rw [if_pos h_starts]
  rw [drop_one_dash_append]
  rw [toInt?_minus_append']
  have h_nat_eq := AzNat.parse_eq_toNat? rest h_ne h_dig
  cases h_an : AzNat.parse rest with
  | none =>
    simp only [Option.map_none]
    rw [h_an] at h_nat_eq; simp at h_nat_eq; rw [← h_nat_eq]; rfl
  | some n =>
    rw [h_an] at h_nat_eq
    have h_n_ne : n ≠ 0 := by
      intro h_n_zero
      have h_n_toNat : n.toNat = 0 := by rw [h_n_zero]; rfl
      exact (h_nonzero n h_an) h_n_toNat
    simp only
    rw [dif_neg h_n_ne]
    rw [← h_nat_eq]
    simp only [Option.map_some]
    apply congrArg
    show ({ sign := false, abs := n, zero_sign := _ } : AzInt).toInt = -(n.toNat : Int)
    unfold AzInt.toInt; simp

end Azurite.AzInt

import Azurite.AzNat.Equiv.OfLimbDigits
import Azurite.AzNat.Equiv.ToStringBase
import Azurite.AzNat.ParseBase

namespace Azurite

namespace AzNat

/-! ### Per-character inverse: `charToDigit ∘ digitToChar = id` -/

theorem charToDigit_digitToChar (d : UInt64) (hd : d.toNat < 36) :
    AzNat.charToDigit (AzNat.digitToChar d false) = some d := by
  have h_eq : d = UInt64.ofNat d.toNat := by
    apply UInt64.toNat.inj
    show d.toNat = d.toNat % 2^64
    omega
  conv_rhs => rw [h_eq]
  rw [h_eq]
  generalize h_d_nat : d.toNat = k at hd
  interval_cases k <;> decide

/-! ### `parseDigitsInto ∘ map digitToChar = id` -/

private theorem parseDigitsInto_foldl_aux (b : UInt64) (hb_36 : b.toNat ≤ 36) :
    ∀ (ds : List UInt64) (arr0 : Array UInt64),
      (∀ d ∈ ds, d.toNat < b.toNat) →
      (ds.map (fun d => AzNat.digitToChar d false)).foldl
          (fun acc c =>
            match acc with
            | none => none
            | some arr =>
              match AzNat.charToDigit c with
              | none => none
              | some d => if d < b then some (arr.push d) else none)
          (some arr0)
        = some { toList := arr0.toList ++ ds } := by
  intro ds
  induction ds with
  | nil =>
    intro arr0 _
    show some arr0 = some { toList := arr0.toList ++ [] }
    simp
  | cons d ds' ih =>
    intro arr0 h_lt
    have h_d_lt : d.toNat < b.toNat := h_lt d List.mem_cons_self
    have h_d_lt_36 : d.toNat < 36 := lt_of_lt_of_le h_d_lt hb_36
    have h_d_lt_b_uint : d < b := by
      rw [UInt64.lt_iff_toNat_lt_toNat]; exact h_d_lt
    have h_inv := charToDigit_digitToChar d h_d_lt_36
    show ((d :: ds').map (fun d => AzNat.digitToChar d false)).foldl _ (some arr0) = _
    rw [List.map_cons, List.foldl_cons]
    rw [h_inv]
    simp only [h_d_lt_b_uint, ↓reduceIte]
    have h_rest : ∀ x ∈ ds', x.toNat < b.toNat := fun x hx =>
      h_lt x (List.mem_cons_of_mem _ hx)
    rw [ih (arr0.push d) h_rest]
    show some ({ toList := (arr0.push d).toList ++ ds' } : Array UInt64) =
         some ({ toList := arr0.toList ++ (d :: ds') } : Array UInt64)
    rw [Array.toList_push]; simp

private theorem parseDigitsInto_map_digitToChar (b : UInt64) (hb_36 : b.toNat ≤ 36)
    (ds : List UInt64) (h_lt : ∀ d ∈ ds, d.toNat < b.toNat) :
    AzNat.parseDigitsInto b (ds.map (fun d => AzNat.digitToChar d false)) =
      some { toList := ds } := by
  unfold AzNat.parseDigitsInto
  have h := parseDigitsInto_foldl_aux b hb_36 ds #[] h_lt
  refine h.trans ?_
  congr 1

/-! ### Properties of `n.limbDigits b`: non-empty and last (MSB) digit is non-zero -/

private theorem limbDigits_ne_nil_of_pos (b : UInt64) (hb : 2 ≤ b.toNat) (n : AzNat)
    (hn : 0 < n.toNat) : (n.limbDigits b).toList ≠ [] := by
  intro he
  have h_mapped : (n.limbDigits b).toList.map UInt64.toNat = [] := by rw [he]; rfl
  rw [limbDigits_eq b hb n] at h_mapped
  exact (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega : n.toNat ≠ 0)) h_mapped

private theorem n_toNat_pos_of_size_ne_zero (n : AzNat) (h_size : n.limbs.size ≠ 0) :
    0 < n.toNat := by
  by_contra h_nlt
  push Not at h_nlt
  have h_zero : n.toNat = 0 := by omega
  have h_last_inv := n.last_ne_zero
  have h_nil : n.limbs.toList = [] := by
    apply toNatLimbsList_eq_zero_of_getLast_ne_zero
    · rw [← Array.getLast?_toList] at h_last_inv; exact h_last_inv
    · exact h_zero
  apply h_size
  rw [← Array.length_toList, h_nil]; rfl

/-! ### `stripPrefix` returns `none` on `toStringBase b n` -/

private theorem startsWith_eq_false_of_head_ne (s p : String) (c : Char)
    (h_head_eq : p.toList.head? = some c) (h_head_s : s.toList.head? ≠ some c) :
    s.startsWith p = false := by
  rw [Bool.eq_false_iff, Ne, String.startsWith_string_iff]
  intro h_pre
  apply h_head_s
  obtain ⟨t, ht⟩ := h_pre
  have h_p_ne : p.toList ≠ [] := by
    intro he; rw [he] at h_head_eq; cases h_head_eq
  rw [← h_head_eq]
  rcases hl : p.toList with _ | ⟨a, as⟩
  · exact absurd hl h_p_ne
  · rw [hl] at ht
    show s.toList.head? = (a :: as).head?
    rw [← ht]; rfl

private theorem toStringBase_head_ne_zero (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36)
    (n : AzNat) (h_size : n.limbs.size ≠ 0) :
    (n.toStringBase b).toList.head? ≠ some '0' := by
  have h_b_in : ¬ (b < 2 ∨ 36 < b) := by
    push Not
    rw [UInt64.not_lt, UInt64.not_lt]
    refine ⟨?_, ?_⟩
    · show (2 : UInt64).toNat ≤ b.toNat; show (2 : Nat) ≤ b.toNat; omega
    · show b.toNat ≤ (36 : UInt64).toNat; show b.toNat ≤ (36 : Nat); omega
  have h_str : n.toStringBase b = String.ofList
      ((n.limbDigits b).toList.reverse.map fun d => AzNat.digitToChar d false) := by
    unfold AzNat.toStringBase AzNat.toStringBaseWith
    rw [if_neg h_b_in]; simp [h_size]
  rw [h_str, String.toList_ofList]
  have h_n_pos : 0 < n.toNat := n_toNat_pos_of_size_ne_zero n h_size
  have h_dne := limbDigits_ne_nil_of_pos b hb n h_n_pos
  -- The last digit of (n.limbDigits b).toList is non-zero.
  have h_last_ne : ((n.limbDigits b).toList.getLast h_dne).toNat ≠ 0 := by
    have h_digits_ne : Nat.digits b.toNat n.toNat ≠ [] :=
      Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have h_last_ne_n := Nat.getLast_digit_ne_zero b.toNat (by omega : n.toNat ≠ 0)
    have h_eq_lists := limbDigits_eq b hb n
    have h_mapped_ne : (n.limbDigits b).toList.map UInt64.toNat ≠ [] := by
      rw [h_eq_lists]; exact h_digits_ne
    have h_map_last := List.getLast_map (l := (n.limbDigits b).toList) (f := UInt64.toNat) h_mapped_ne
    -- h_map_last : ((n.limbDigits b).toList.map UInt64.toNat).getLast h_mapped_ne =
    --              ((n.limbDigits b).toList.getLast _).toNat
    have h_mapped_last : ((n.limbDigits b).toList.map UInt64.toNat).getLast h_mapped_ne =
        (Nat.digits b.toNat n.toNat).getLast h_digits_ne := by
      congr 1
    rw [← h_map_last, h_mapped_last]
    exact h_last_ne_n
  -- Reverse: the head of the reversed list is the last of the original.
  rw [show (n.limbDigits b).toList.reverse =
      (n.limbDigits b).toList.getLast h_dne :: (n.limbDigits b).toList.dropLast.reverse from ?_]
  · rw [List.map_cons, List.head?_cons]
    intro h_eq
    injection h_eq with h_char
    -- h_char : digitToChar (last) false = '0'.
    have h_last_lt_36 :
        ((n.limbDigits b).toList.getLast h_dne).toNat < 36 := by
      have h_mem : (n.limbDigits b).toList.getLast h_dne ∈ (n.limbDigits b).toList :=
        List.getLast_mem h_dne
      have h_mapped_mem : ((n.limbDigits b).toList.getLast h_dne).toNat ∈
          (n.limbDigits b).toList.map UInt64.toNat := List.mem_map_of_mem h_mem
      rw [limbDigits_eq b hb n] at h_mapped_mem
      have h_lt_b := Nat.digits_lt_base (by omega) h_mapped_mem
      omega
    have h_inv := charToDigit_digitToChar _ h_last_lt_36
    rw [h_char] at h_inv
    -- h_inv : charToDigit '0' = some (last). But charToDigit '0' = some 0.
    have h_char_zero : AzNat.charToDigit '0' = some 0 := by decide
    rw [h_char_zero] at h_inv
    have h_last_zero : (0 : UInt64) = (n.limbDigits b).toList.getLast h_dne := by
      injection h_inv
    apply h_last_ne
    rw [← h_last_zero]; rfl
  · -- (xs.reverse = (xs.getLast h) :: xs.dropLast.reverse) for non-empty xs.
    conv_lhs => rw [← List.dropLast_append_getLast h_dne]
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]

private theorem stripPrefix_toStringBase (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36)
    (n : AzNat) :
    AzNat.stripPrefix (n.toStringBase b) = none := by
  unfold AzNat.stripPrefix
  by_cases h_size : n.limbs.size = 0
  · -- Body = "0"; all 3 startsWith fail by computation.
    have h_b_in : ¬ (b < 2 ∨ 36 < b) := by
      push Not
      rw [UInt64.not_lt, UInt64.not_lt]
      refine ⟨?_, ?_⟩
      · show (2 : UInt64).toNat ≤ b.toNat; show (2 : Nat) ≤ b.toNat; omega
      · show b.toNat ≤ (36 : UInt64).toNat; show b.toNat ≤ (36 : Nat); omega
    have h_str : n.toStringBase b = "0" := by
      unfold AzNat.toStringBase AzNat.toStringBaseWith
      rw [if_neg h_b_in]; simp [h_size]
    rw [h_str]
    decide
  · have h_head := toStringBase_head_ne_zero b hb hb' n h_size
    have h_b := startsWith_eq_false_of_head_ne (n.toStringBase b) "0b" '0' rfl h_head
    have h_o := startsWith_eq_false_of_head_ne (n.toStringBase b) "0o" '0' rfl h_head
    have h_x := startsWith_eq_false_of_head_ne (n.toStringBase b) "0x" '0' rfl h_head
    rw [h_b, h_o, h_x]
    rfl

/-! ### Round-trip with `toStringBase` -/

theorem parseBase_toStringBase (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36)
    (n : AzNat) : AzNat.parseBase b (n.toStringBase b) = some n := by
  unfold AzNat.parseBase
  have h_b_in : ¬ (b < 2 ∨ 36 < b) := by
    push Not
    rw [UInt64.not_lt, UInt64.not_lt]
    refine ⟨?_, ?_⟩
    · show (2 : UInt64).toNat ≤ b.toNat; show (2 : Nat) ≤ b.toNat; omega
    · show b.toNat ≤ (36 : UInt64).toNat; show b.toNat ≤ (36 : Nat); omega
  rw [if_neg h_b_in]
  have h_strip := stripPrefix_toStringBase b hb hb' n
  simp only [h_strip]
  by_cases h_size : n.limbs.size = 0
  · -- toStringBase b n = "0"; parses to 0.
    have h_n_zero : n.toNat = 0 := by
      show toNatLimbsList n.limbs.toList = 0
      have h_nil : n.limbs.toList = [] :=
        List.length_eq_zero_iff.mp (by rw [Array.length_toList, h_size])
      rw [h_nil]; rfl
    have h_str : n.toStringBase b = "0" := by
      unfold AzNat.toStringBase AzNat.toStringBaseWith
      rw [if_neg h_b_in]; simp [h_size]
    rw [h_str]
    show (if ("0" : String).isEmpty then none else AzNat.buildFromChars b "0".toList) = some n
    rw [show ("0" : String).isEmpty = false from rfl, if_neg (by decide)]
    show (match AzNat.parseDigitsInto b "0".toList with
          | none => none
          | some arr => some (AzNat.ofLimbDigits b arr.reverse)) = some n
    have h_lt : (0 : UInt64).toNat < b.toNat := by show 0 < b.toNat; omega
    have h_pd : AzNat.parseDigitsInto b ['0'] = some ⟨[0]⟩ := by
      have := parseDigitsInto_map_digitToChar b hb' [0] (by
        intro d hd; rw [List.mem_singleton] at hd; subst hd; exact h_lt)
      have h_dc : AzNat.digitToChar 0 false = '0' := by decide
      simpa [h_dc] using this
    rw [show "0".toList = ['0'] from rfl, h_pd]
    apply congrArg some
    apply toNat_injective
    rw [toNat_ofLimbDigits b hb (⟨[0]⟩ : Array UInt64).reverse (by
      intro x hx
      simp at hx; subst hx
      show 0 < b.toNat; omega)]
    show Nat.ofDigits b.toNat ((⟨[0]⟩ : Array UInt64).reverse.toList.map UInt64.toNat) = n.toNat
    rw [Array.toList_reverse]; show Nat.ofDigits b.toNat ([(0 : UInt64)].reverse.map UInt64.toNat) = _
    rw [List.reverse_singleton]
    show Nat.ofDigits b.toNat [(0 : UInt64).toNat] = n.toNat
    rw [h_n_zero]
    simp [Nat.ofDigits]
  · -- toStringBase b n = String.ofList chars; buildFromChars recovers via ofLimbDigits_limbDigits.
    have h_str : n.toStringBase b = String.ofList
        ((n.limbDigits b).toList.reverse.map fun d => AzNat.digitToChar d false) := by
      unfold AzNat.toStringBase AzNat.toStringBaseWith
      rw [if_neg h_b_in]; simp [h_size]
    rw [h_str]
    have h_n_pos : 0 < n.toNat := n_toNat_pos_of_size_ne_zero n h_size
    have h_dne : (n.limbDigits b).toList ≠ [] := limbDigits_ne_nil_of_pos b hb n h_n_pos
    have h_chars_ne :
        ((n.limbDigits b).toList.reverse.map fun d => AzNat.digitToChar d false) ≠ [] := by
      rw [Ne, List.map_eq_nil_iff, List.reverse_eq_nil_iff]; exact h_dne
    have h_isEmpty :
        (String.ofList
          ((n.limbDigits b).toList.reverse.map fun d => AzNat.digitToChar d false)).isEmpty
          = false := by
      rw [Bool.eq_false_iff, Ne, String.isEmpty_iff]
      intro he
      apply h_chars_ne
      have := congrArg String.toList he
      rw [String.toList_ofList] at this
      exact this
    rw [show (if (String.ofList _).isEmpty then none
              else AzNat.buildFromChars b (String.ofList _).toList) =
              AzNat.buildFromChars b (String.ofList _).toList from if_neg
              (by rw [h_isEmpty]; decide)]
    rw [String.toList_ofList]
    show (match AzNat.parseDigitsInto b _ with
          | none => none
          | some arr => some (AzNat.ofLimbDigits b arr.reverse)) = some n
    have h_lt_b : ∀ d ∈ (n.limbDigits b).toList.reverse, d.toNat < b.toNat := by
      intro d hd
      rw [List.mem_reverse] at hd
      have h_mem_map : d.toNat ∈ (n.limbDigits b).toList.map UInt64.toNat :=
        List.mem_map_of_mem hd
      rw [limbDigits_eq b hb n] at h_mem_map
      exact Nat.digits_lt_base (by omega) h_mem_map
    rw [parseDigitsInto_map_digitToChar b hb' _ h_lt_b]
    -- Now: some (ofLimbDigits b (⟨reverse⟩).reverse) = some n.
    have h_arr_eq : (⟨(n.limbDigits b).toList.reverse⟩ : Array UInt64).reverse =
        n.limbDigits b := by
      apply Array.toList_inj.mp
      rw [Array.toList_reverse]
      show (n.limbDigits b).toList.reverse.reverse = (n.limbDigits b).toList
      exact List.reverse_reverse _
    show some (AzNat.ofLimbDigits b _) = some n
    rw [h_arr_eq]
    exact congrArg some (ofLimbDigits_limbDigits b hb n)

/-! ### Round-trip with `toString` (decimal corollary) -/

theorem parse_toString (n : AzNat) : AzNat.parse (AzNat.toString n) = some n := by
  -- toString = toStringBase 10. Both `parse` and `parseBase 10` apply the same body
  -- after the stripPrefix returns none.
  show AzNat.parse (n.toStringBase 10) = some n
  unfold AzNat.parse
  simp only [stripPrefix_toStringBase 10 (by decide) (by decide) n]
  have h := parseBase_toStringBase 10 (by decide) (by decide) n
  unfold AzNat.parseBase at h
  rw [if_neg (by decide : ¬ ((10 : UInt64) < 2 ∨ 36 < (10 : UInt64)))] at h
  simp only [stripPrefix_toStringBase 10 (by decide) (by decide) n] at h
  exact h

/-! ### Decimal equivalence with `String.toNat?` (digit-only inputs)

For inputs consisting purely of digits `'0'`–`'9'` (no underscores, no
prefix), `AzNat.parse` agrees with `String.toNat?` up to the `AzNat ↔ Nat`
translation. -/

private theorem digitToChar_digitValue (c : Char) (h_lo : '0' ≤ c) (h_hi : c ≤ '9') :
    AzNat.digitToChar (UInt64.ofNat (c.toNat - '0'.toNat)) false = c := by
  have h_zero_eq : ('0' : Char).toNat = 48 := rfl
  have h_c_range : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := ⟨h_lo, h_hi⟩
  have h_k_lt : c.toNat - '0'.toNat < 10 := by rw [h_zero_eq]; omega
  have h_toNat : (UInt64.ofNat (c.toNat - '0'.toNat)).toNat = c.toNat - '0'.toNat := by
    show (c.toNat - '0'.toNat) % 2^64 = c.toNat - '0'.toNat
    rw [h_zero_eq]; omega
  unfold AzNat.digitToChar
  rw [h_toNat, if_pos h_k_lt]
  rw [h_zero_eq, show 48 + (c.toNat - 48) = c.toNat from by omega]
  exact Char.ofNat_toNat c

private theorem map_digitToChar_eq_self (cs : List Char)
    (h : ∀ c ∈ cs, '0' ≤ c ∧ c ≤ '9') :
    (cs.map (fun c => UInt64.ofNat (c.toNat - '0'.toNat))).map
        (fun d => AzNat.digitToChar d false) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs' ih =>
    rw [List.map_cons, List.map_cons]
    rw [digitToChar_digitValue c (h c List.mem_cons_self).1 (h c List.mem_cons_self).2]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem parseDigitsInto_of_digits (cs : List Char)
    (h : ∀ c ∈ cs, '0' ≤ c ∧ c ≤ '9') :
    AzNat.parseDigitsInto 10 cs =
      some ⟨cs.map (fun c => UInt64.ofNat (c.toNat - '0'.toNat))⟩ := by
  have h_lt : ∀ d ∈ cs.map (fun c => UInt64.ofNat (c.toNat - '0'.toNat)),
      d.toNat < (10 : UInt64).toNat := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨c, hc_mem, hc_eq⟩ := hd
    rw [← hc_eq]
    have h_c := h c hc_mem
    have h_c_range : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := ⟨h_c.1, h_c.2⟩
    show (c.toNat - '0'.toNat) % 2^64 < 10
    have h_zero_eq : '0'.toNat = 48 := rfl
    rw [h_zero_eq]
    omega
  have h_eq := parseDigitsInto_map_digitToChar 10 (by decide) _ h_lt
  rw [map_digitToChar_eq_self cs h] at h_eq
  exact h_eq

/-- `Nat.ofDigits 10` of a reversed digit-value list equals the
MSB-first foldl that defines `Nat.ofDigitChars`. -/
private theorem ofDigits_reverse_eq_foldl (cs : List Char) :
    Nat.ofDigits (10 : Nat) ((cs.map fun c => (UInt64.ofNat (c.toNat - '0'.toNat)).toNat).reverse)
      = cs.foldl (init := 0) (fun sofar c => 10 * sofar + (c.toNat - '0'.toNat)) := by
  -- Generalize: prove via foldl-vs-reverse-ofDigits.
  -- Strategy: induct on cs from the right by writing cs = pref ++ [last] or use length induction.
  -- Simpler: use that ofDigitChars 10 cs 0 = foldl ... and prove against that.
  show _ = Nat.ofDigitChars 10 cs 0
  induction cs with
  | nil => simp
  | cons c cs' ih =>
    rw [List.map_cons, List.reverse_cons]
    rw [show Nat.ofDigits (10 : Nat)
            ((cs'.map fun c => (UInt64.ofNat (c.toNat - '0'.toNat)).toNat).reverse ++
              [(UInt64.ofNat (c.toNat - '0'.toNat)).toNat]) =
          Nat.ofDigits (10 : Nat)
              ((cs'.map fun c => (UInt64.ofNat (c.toNat - '0'.toNat)).toNat).reverse) +
            10 ^ (cs'.map fun c => (UInt64.ofNat (c.toNat - '0'.toNat)).toNat).length *
              (UInt64.ofNat (c.toNat - '0'.toNat)).toNat
          from ?_]
    · rw [ih]
      rw [List.length_map]
      rw [Nat.ofDigitChars_cons]
      simp only [Nat.mul_zero, Nat.zero_add]
      -- RHS = Nat.ofDigitChars 10 cs' (c.toNat - '0'.toNat)
      -- = Nat.ofDigitChars 10 cs' 0 + 10^cs'.length * (c.toNat - '0'.toNat)
      rw [Nat.ofDigitChars_eq_ofDigitChars_zero (init := c.toNat - '0'.toNat)]
      -- And (UInt64.ofNat k).toNat = k % 2^64. For k = c.toNat - '0'.toNat ≤ c.toNat ≤ 0x110000 < 2^64.
      have h_c_bound : c.toNat - '0'.toNat < 2^64 := by
        have h32 : c.val.toNat < 2^32 := UInt32.toNat_lt c.val
        have : c.toNat < 2^64 := by
          show c.val.toNat < 2^64; exact lt_of_lt_of_le h32 (by decide : (2^32 : Nat) ≤ 2^64)
        omega
      have h_toNat : (UInt64.ofNat (c.toNat - '0'.toNat)).toNat = c.toNat - '0'.toNat := by
        show (c.toNat - '0'.toNat) % 2^64 = c.toNat - '0'.toNat
        exact Nat.mod_eq_of_lt h_c_bound
      rw [h_toNat]
      ring
    · -- ofDigits append: Nat.ofDigits b (l ++ [d]) = Nat.ofDigits b l + b^l.length * d.
      -- We use `ofDigits_reverse_cons` on the list `cs'.map ...` directly:
      --   Nat.ofDigits b (d :: l).reverse = Nat.ofDigits b l.reverse + b^l.length * d.
      have h_rev := Nat.ofDigits_reverse_cons (b := 10)
        (cs'.map fun c => (UInt64.ofNat (c.toNat - '0'.toNat)).toNat)
        (UInt64.ofNat (c.toNat - '0'.toNat)).toNat
      rw [List.reverse_cons] at h_rev
      exact h_rev

private theorem startsWith_eq_false_of_head_ne_digit (s p : String) (c : Char)
    (h_p_2nd : p.toList = ['0', c]) (h_c_nd : ¬ ('0' ≤ c ∧ c ≤ '9'))
    (h_digits : ∀ x ∈ s.toList, '0' ≤ x ∧ x ≤ '9') : s.startsWith p = false := by
  rw [Bool.eq_false_iff, Ne, String.startsWith_string_iff]
  intro h_pre
  obtain ⟨t, ht⟩ := h_pre
  rw [h_p_2nd] at ht
  have h_c_mem : c ∈ s.toList := by rw [← ht]; simp
  exact h_c_nd (h_digits c h_c_mem)

private theorem filter_underscore_eq_self_of_digits (cs : List Char)
    (h : ∀ c ∈ cs, '0' ≤ c ∧ c ≤ '9') :
    cs.filter (· != '_') = cs := by
  rw [List.filter_eq_self]
  intro c hc
  have hc' := h c hc
  have h_hi : c.toNat ≤ 57 := hc'.2
  rw [bne_iff_ne]
  intro h_eq
  rw [h_eq] at h_hi
  exact absurd h_hi (by decide)

theorem parse_eq_toNat? (s : String) (h_ne : s ≠ "")
    (h_digits : ∀ c ∈ s.toList, '0' ≤ c ∧ c ≤ '9') :
    (AzNat.parse s).map AzNat.toNat = s.toNat? := by
  have h_strip : AzNat.stripPrefix s = none := by
    unfold AzNat.stripPrefix
    have h_b : s.startsWith "0b" = false :=
      startsWith_eq_false_of_head_ne_digit s "0b" 'b' rfl (by decide) h_digits
    have h_o : s.startsWith "0o" = false :=
      startsWith_eq_false_of_head_ne_digit s "0o" 'o' rfl (by decide) h_digits
    have h_x : s.startsWith "0x" = false :=
      startsWith_eq_false_of_head_ne_digit s "0x" 'x' rfl (by decide) h_digits
    rw [h_b, h_o, h_x]; rfl
  unfold AzNat.parse
  simp only [h_strip]
  have h_s_ne_empty : s.isEmpty = false := by
    rw [Bool.eq_false_iff, Ne, String.isEmpty_iff]; exact h_ne
  rw [h_s_ne_empty, if_neg (by decide)]
  unfold AzNat.buildFromChars
  rw [parseDigitsInto_of_digits s.toList h_digits]
  rw [Option.map_some]
  have h_zero_eq : ('0' : Char).toNat = 48 := rfl
  have h_lt_b : ∀ x ∈ ((⟨s.toList.map
        (fun c => UInt64.ofNat (c.toNat - '0'.toNat))⟩ : Array UInt64).reverse.toList.map
          UInt64.toNat), x < (10 : UInt64).toNat := by
    intro x hx
    rw [Array.toList_reverse, List.map_reverse, List.mem_reverse, List.mem_map] at hx
    obtain ⟨d, hd_mem, hd_eq⟩ := hx
    rw [List.mem_map] at hd_mem
    obtain ⟨c, hc_mem, hc_eq⟩ := hd_mem
    rw [← hd_eq, ← hc_eq]
    have h_c := h_digits c hc_mem
    have h_lo : 48 ≤ c.toNat := h_c.1
    have h_hi : c.toNat ≤ 57 := h_c.2
    show (c.toNat - '0'.toNat) % 2^64 < (10 : UInt64).toNat
    rw [h_zero_eq]
    show (c.toNat - 48) % 2^64 < 10
    have h_c_lt : c.toNat - 48 < 10 := by omega
    have h_c_mod : (c.toNat - 48) % 2^64 = c.toNat - 48 := by
      apply Nat.mod_eq_of_lt; omega
    rw [h_c_mod]; exact h_c_lt
  rw [toNat_ofLimbDigits 10 (by decide) _ h_lt_b]
  rw [Array.toList_reverse]
  show some (Nat.ofDigits (10 : UInt64).toNat
        ((s.toList.map (fun c => UInt64.ofNat (c.toNat - '0'.toNat))).reverse.map
          UInt64.toNat)) = s.toNat?
  rw [List.map_reverse]
  rw [show (s.toList.map fun c => UInt64.ofNat (c.toNat - '0'.toNat)).map UInt64.toNat =
        s.toList.map (fun c => (UInt64.ofNat (c.toNat - '0'.toNat)).toNat) from by
    rw [List.map_map]; rfl]
  show some (Nat.ofDigits (10 : Nat) _) = s.toNat?
  rw [ofDigits_reverse_eq_foldl s.toList]
  show some (Nat.ofDigitChars 10 s.toList 0) = s.toNat?
  -- s.toNat? = some (Nat.ofDigitChars 10 (s.toList.filter (· != '_')) 0).
  have h_isDigit : ∀ c ∈ s.toList, c.isDigit := by
    intro c hc
    have h := h_digits c hc
    show (c.val ≥ '0'.val && c.val ≤ '9'.val) = true
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact h
  have h_isNat : s.isNat = true := String.isNat_of_isDigit h_ne h_isDigit
  rw [String.toNat?_eq_some_ofDigitChars h_isNat]
  rw [filter_underscore_eq_self_of_digits s.toList h_digits]

/-! ### Forward correctness for `parseBase b` (general `b`)

For an `s : String` whose characters are all valid base-`b` digits (no
prefix, no underscores), `parseBase b s` succeeds and its `.toNat` is
the MSB-first base-`b` Horner fold over `s.toList`. -/

private theorem parseDigitsInto_foldl_charValid (b : UInt64) :
    ∀ (cs : List Char) (arr0 : Array UInt64),
      (∀ c ∈ cs, ∃ d, AzNat.charToDigit c = some d ∧ d < b) →
      cs.foldl
          (fun acc c =>
            match acc with
            | none => none
            | some arr =>
              match AzNat.charToDigit c with
              | none => none
              | some d => if d < b then some (arr.push d) else none)
          (some arr0)
        = some { toList := arr0.toList ++ cs.map fun c => (AzNat.charToDigit c).getD 0 } := by
  intro cs
  induction cs with
  | nil =>
    intro arr0 _
    show some arr0 = some { toList := arr0.toList ++ [] }
    simp
  | cons c cs' ih =>
    intro arr0 h_valid
    obtain ⟨d, hd_eq, hd_lt⟩ := h_valid c List.mem_cons_self
    show ((c :: cs').foldl _ (some arr0)) = _
    rw [List.foldl_cons]
    rw [hd_eq]
    simp only [hd_lt, ↓reduceIte]
    have h_rest : ∀ x ∈ cs', ∃ d, AzNat.charToDigit x = some d ∧ d < b := fun x hx =>
      h_valid x (List.mem_cons_of_mem _ hx)
    rw [ih (arr0.push d) h_rest]
    show some ({ toList := (arr0.push d).toList ++
                  cs'.map fun c => (AzNat.charToDigit c).getD 0 } : Array UInt64) =
         some ({ toList := arr0.toList ++ (c :: cs').map fun c => (AzNat.charToDigit c).getD 0 }
                : Array UInt64)
    rw [Array.toList_push, List.map_cons]
    show some ({ toList := (arr0.toList ++ [d]) ++ _ } : Array UInt64) =
         some ({ toList := arr0.toList ++ ((AzNat.charToDigit c).getD 0 :: _) } : Array UInt64)
    rw [hd_eq]; simp

private theorem parseDigitsInto_eq_charToDigit (b : UInt64) (cs : List Char)
    (h_valid : ∀ c ∈ cs, ∃ d, AzNat.charToDigit c = some d ∧ d < b) :
    AzNat.parseDigitsInto b cs =
      some ⟨cs.map fun c => (AzNat.charToDigit c).getD 0⟩ := by
  unfold AzNat.parseDigitsInto
  have h := parseDigitsInto_foldl_charValid b cs #[] h_valid
  refine h.trans ?_
  congr 1

/-- `Nat.ofDigits b` of a reversed digit-value list equals the MSB-first
base-`b` Horner fold over the character list. Base-parameterized analogue
of `ofDigits_reverse_eq_foldl`. -/
private theorem ofDigits_reverse_eq_foldl_general (b : Nat) (cs : List Char) :
    Nat.ofDigits b ((cs.map fun c => ((AzNat.charToDigit c).getD 0).toNat).reverse)
      = cs.foldl (init := 0) fun acc c =>
          b * acc + ((AzNat.charToDigit c).getD 0).toNat := by
  -- Strengthen to a single fold parameterized by the initial accumulator.
  suffices h : ∀ (init : Nat),
      init * b ^ cs.length +
        Nat.ofDigits b ((cs.map fun c => ((AzNat.charToDigit c).getD 0).toNat).reverse) =
        cs.foldl (init := init) fun acc c =>
          b * acc + ((AzNat.charToDigit c).getD 0).toNat by
    have := h 0
    simpa using this
  intro init
  induction cs generalizing init with
  | nil => simp
  | cons c cs' ih =>
    rw [List.map_cons, List.reverse_cons, List.foldl_cons, List.length_cons]
    have h_rev := Nat.ofDigits_reverse_cons (b := b)
      (cs'.map fun c => ((AzNat.charToDigit c).getD 0).toNat)
      ((AzNat.charToDigit c).getD 0).toNat
    rw [List.reverse_cons] at h_rev
    rw [h_rev]
    rw [List.length_map]
    have h_pow : b ^ (cs'.length + 1) = b ^ cs'.length * b := by
      rw [Nat.pow_succ]
    rw [h_pow]
    have h_new_init :
        init * (b ^ cs'.length * b) +
          (Nat.ofDigits b (cs'.map fun c => ((AzNat.charToDigit c).getD 0).toNat).reverse +
            b ^ cs'.length * ((AzNat.charToDigit c).getD 0).toNat) =
        (b * init + ((AzNat.charToDigit c).getD 0).toNat) * b ^ cs'.length +
          Nat.ofDigits b (cs'.map fun c => ((AzNat.charToDigit c).getD 0).toNat).reverse := by
      ring
    rw [h_new_init]
    exact ih (b * init + ((AzNat.charToDigit c).getD 0).toNat)

theorem toNat_parseBase (b : UInt64) (hb : 2 ≤ b.toNat) (hb' : b.toNat ≤ 36)
    (s : String) (h_ne : s ≠ "")
    (h_no_prefix : AzNat.stripPrefix s = none)
    (h_valid : ∀ c ∈ s.toList, ∃ d, AzNat.charToDigit c = some d ∧ d.toNat < b.toNat) :
    (AzNat.parseBase b s).map AzNat.toNat =
      some (s.toList.foldl (init := 0) fun acc c =>
        b.toNat * acc + ((AzNat.charToDigit c).getD 0).toNat) := by
  unfold AzNat.parseBase
  have h_b_in : ¬ (b < 2 ∨ 36 < b) := by
    push Not
    rw [UInt64.not_lt, UInt64.not_lt]
    refine ⟨?_, ?_⟩
    · show (2 : UInt64).toNat ≤ b.toNat; show (2 : Nat) ≤ b.toNat; omega
    · show b.toNat ≤ (36 : UInt64).toNat; show b.toNat ≤ (36 : Nat); omega
  rw [if_neg h_b_in]
  simp only [h_no_prefix]
  have h_s_ne_empty : s.isEmpty = false := by
    rw [Bool.eq_false_iff, Ne, String.isEmpty_iff]; exact h_ne
  rw [h_s_ne_empty, if_neg (by decide)]
  -- `h_valid` is `d.toNat < b.toNat` on Nat; `parseDigitsInto_eq_charToDigit` needs `d < b` on UInt64.
  have h_valid_uint : ∀ c ∈ s.toList, ∃ d, AzNat.charToDigit c = some d ∧ d < b := by
    intro c hc
    obtain ⟨d, hd_eq, hd_lt⟩ := h_valid c hc
    exact ⟨d, hd_eq, (UInt64.lt_iff_toNat_lt_toNat).mpr hd_lt⟩
  unfold AzNat.buildFromChars
  rw [parseDigitsInto_eq_charToDigit b s.toList h_valid_uint]
  rw [Option.map_some]
  have h_lt_b : ∀ x ∈ ((⟨s.toList.map fun c => (AzNat.charToDigit c).getD 0⟩ :
        Array UInt64).reverse.toList.map UInt64.toNat), x < b.toNat := by
    intro x hx
    rw [Array.toList_reverse, List.map_reverse, List.mem_reverse, List.mem_map] at hx
    obtain ⟨d, hd_mem, hd_eq⟩ := hx
    rw [List.mem_map] at hd_mem
    obtain ⟨c, hc_mem, hc_eq⟩ := hd_mem
    rw [← hd_eq, ← hc_eq]
    obtain ⟨d', hd'_eq, hd'_lt⟩ := h_valid c hc_mem
    rw [hd'_eq]; show d'.toNat < b.toNat; exact hd'_lt
  rw [toNat_ofLimbDigits b hb _ h_lt_b]
  rw [Array.toList_reverse]
  show some (Nat.ofDigits b.toNat
        ((s.toList.map fun c => (AzNat.charToDigit c).getD 0).reverse.map UInt64.toNat)) = _
  rw [List.map_reverse]
  rw [show (s.toList.map fun c => (AzNat.charToDigit c).getD 0).map UInt64.toNat =
        s.toList.map fun c => ((AzNat.charToDigit c).getD 0).toNat from by
    rw [List.map_map]; rfl]
  rw [ofDigits_reverse_eq_foldl_general]

end AzNat
end Azurite

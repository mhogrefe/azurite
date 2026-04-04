import Mathlib.Tactic.Ring
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.ToString

namespace Azurite

def parseNatCharsAux (cs : List Char) (acc : ℕ) : Option ℕ :=
  match cs with
  | [] => some acc
  | c :: cs =>
    if c.isDigit then
      parseNatCharsAux cs (acc * 10 + (c.toNat - '0'.toNat))
    else none

def parseNatChars (cs : List Char) : Option ℕ :=
  match cs with
  | [] => none
  | _ => parseNatCharsAux cs 0

lemma aux_0 (n : ℕ) (h : n < 10^0) : n = 0 := by
  omega

lemma length_natToCharsAux (fuel n : ℕ) (acc : List Char) :
  (natToCharsAux fuel n acc).length = (natToCharsAux fuel n []).length + acc.length := by
  induction fuel generalizing n acc with
  | zero => simp [natToCharsAux]
  | succ f ih =>
    dsimp [natToCharsAux]
    split_ifs with hn
    · simp
    · let digit := Char.ofNat ('0'.toNat + (n % 10))
      have ih1 := ih (n / 10) (digit :: acc)
      have ih2 := ih (n / 10) [digit]
      show (natToCharsAux f (n / 10) (Char.ofNat (48 + n % 10) :: acc)).length = _
      change (natToCharsAux f (n / 10) (digit :: acc)).length = (natToCharsAux f (n / 10) [digit]).length + acc.length
      rw [ih1, ih2]
      simp [add_assoc]
      omega

lemma hf_ineq (f n : ℕ) (h : n < 10^(f+1)) : n / 10 < 10^f := by
  omega

lemma isDigit_digit_mod (m : ℕ) (h : m < 10) : (Char.ofNat (48 + m)).isDigit = true := by
  match m with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
  | m + 10 => omega

lemma isDigit_digit (n : ℕ) : (Char.ofNat (48 + n % 10)).isDigit = true := by
  apply isDigit_digit_mod
  exact Nat.mod_lt _ (by decide)

lemma toNat_digit_mod (m : ℕ) (h : m < 10) : (Char.ofNat (48 + m)).toNat - 48 = m := by
  match m with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
  | m + 10 => omega

lemma toNat_digit (n : ℕ) : (Char.ofNat (48 + n % 10)).toNat - 48 = n % 10 := by
  apply toNat_digit_mod
  exact Nat.mod_lt _ (by decide)

lemma parseNatCharsAux_natToCharsAux (fuel n acc : ℕ) (h_fuel : n < 10^fuel) (cs : List Char) :
  parseNatCharsAux (natToCharsAux fuel n cs) acc = parseNatCharsAux cs (acc * 10^(natToCharsAux fuel n []).length + n) := by
  induction fuel generalizing n acc cs with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    dsimp [natToCharsAux]
    simp
  | succ f ih =>
    dsimp [natToCharsAux]
    split_ifs with hn
    · subst hn
      simp
    · let digit := Char.ofNat (48 + (n % 10))
      show parseNatCharsAux (natToCharsAux f (n / 10) (digit :: cs)) acc = _
      have hf : n / 10 < 10^f := by omega
      have ih2 := ih (n / 10) acc hf (digit :: cs)
      rw [ih2]
      show parseNatCharsAux (digit :: cs) _ = _
      dsimp [parseNatCharsAux]
      have h_dig : digit.isDigit = true := isDigit_digit n
      have h_val : digit.toNat - 48 = n % 10 := toNat_digit n
      show (if digit.isDigit then _ else _) = _
      rw [h_dig, if_pos rfl]
      rw [h_val]
      congr 1
      have hl := length_natToCharsAux f (n / 10) [digit]
      show _ * 10 + n % 10 = acc * 10 ^ (natToCharsAux f (n / 10) [digit]).length + n
      rw [hl]
      dsimp
      set L := (natToCharsAux f (n / 10) []).length
      have h_pow : 10 ^ (L + 1) = 10 ^ L * 10 := rfl
      rw [h_pow]
      have h_div_mod : (n / 10) * 10 + n % 10 = n := by omega
      calc (acc * 10 ^ L + n / 10) * 10 + n % 10
        _ = acc * (10 ^ L * 10) + ((n / 10) * 10 + n % 10) := by ring
        _ = acc * (10 ^ L * 10) + n := by rw [h_div_mod]

lemma parseNatChars_eq (cs : List Char) (h : cs ≠ []) : parseNatChars cs = parseNatCharsAux cs 0 := by
  cases cs
  · contradiction
  · rfl

lemma natToCharsAux_ne_nil (n : ℕ) (hn : n ≠ 0) : natToCharsAux n n [] ≠ [] := by
  cases n with
  | zero => contradiction
  | succ n' =>
    dsimp [natToCharsAux]
    let digit := Char.ofNat (48 + (n' + 1) % 10)
    have hl := length_natToCharsAux n' ((n' + 1) / 10) [digit]
    have h_len : [digit].length = 1 := rfl
    intro contra
    rw [contra] at hl
    change 0 = _ at hl
    omega

lemma lt_pow_self (n : ℕ) : n < 10 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : 10 ^ n * 1 ≤ 10 ^ n * 10 := Nat.mul_le_mul_left _ (by decide)
    omega

/-! ### Parse round-trip lemmas -/

lemma parseNatChars_natToChars (n : ℕ) : parseNatChars (natToChars n) = some n := by
  unfold natToChars
  split_ifs with hn
  · subst hn
    rfl
  · have h_neq := natToCharsAux_ne_nil n hn
    rw [parseNatChars_eq _ h_neq]
    have h_fuel := lt_pow_self n
    have h_aux := parseNatCharsAux_natToCharsAux n n 0 h_fuel []
    rw [h_aux]
    simp [parseNatCharsAux]

namespace AzNat

def parse (cs : List Char) : Option AzNat :=
  (parseNatChars cs).map ofNat

theorem parse_toChars (n : AzNat) : parse (toChars n) = some n := by
  unfold parse toChars
  rw [parseNatChars_natToChars (toNat n)]
  exact congrArg some (ofNat_toNat n)

end AzNat
end Azurite

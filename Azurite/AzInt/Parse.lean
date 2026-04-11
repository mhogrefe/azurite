import Azurite.AzInt.ToString
import Azurite.AzNat.Parse

namespace Azurite.AzInt

def parse (cs : List Char) : Option AzInt :=
  if cs.head? == some '-' then
    match AzNat.parse cs.tail with
    | some n =>
      if h : n = 0 then none
      else
        some { sign := false, abs := n, zero_sign := fun h_abs => False.elim (h h_abs) }
    | none => none
  else
    match AzNat.parse cs with
    | some n => some { sign := true, abs := n, zero_sign := fun _ => rfl}
    | none => none

lemma azInt_ext (z1 z2 : AzInt) : z1.sign = z2.sign → z1.abs = z2.abs → z1 = z2 := by
  intro h1 h2
  cases z1; cases z2
  dsimp at h1 h2
  subst h1 h2
  rfl

lemma nat_not_dash (cs : List Char) (n : Nat) (hc : parseNatChars cs = some n) : cs.head? ≠ some '-' := by
  cases cs with
  | nil =>
    simp
  | cons c cs =>
    intro contra
    simp at contra
    subst contra
    unfold parseNatChars parseNatCharsAux at hc
    have h_dig : ('-').isDigit = false := rfl
    rw [h_dig] at hc
    dsimp at hc
    contradiction

theorem parse_toChars (z : AzInt) : parse (toChars z) = some z := by
  unfold parse toChars
  split_ifs with h_sign h_head h_head
  · -- positive, but cs.head? = '-'
    have hz_abs := AzNat.parse_toChars z.abs
    have hc : parseNatChars (AzNat.toChars z.abs) = some (z.abs.toNat) := by
      unfold AzNat.parse at hz_abs
      have hh := parseNatChars_natToChars z.abs.toNat
      rw [← AzNat.toChars] at hh
      exact hh
    have hnd := nat_not_dash _ _ hc
    have hh : z.abs.toChars.head? = some '-' := eq_of_beq h_head
    exact False.elim (hnd hh)
  · -- positive
    have hz_abs := AzNat.parse_toChars z.abs
    change (match AzNat.parse (AzNat.toChars z.abs) with | some n => some { sign := true, abs := n, zero_sign := _} | none => none) = some z
    rw [hz_abs]
    dsimp
    apply congrArg
    apply azInt_ext
    · exact h_sign.symm
    · rfl
  · -- negative, cs.head? = '-'
    have hz_abs := AzNat.parse_toChars z.abs
    change (match AzNat.parse ('-' :: AzNat.toChars z.abs).tail with | some n => if h : n = 0 then none else some _ | none => none) = some z
    have h_tail : ('-' :: AzNat.toChars z.abs).tail = AzNat.toChars z.abs := rfl
    rw [h_tail]
    rw [hz_abs]
    dsimp
    split_ifs with hz
    · -- n = 0, but sign is false
      have hz_sign := z.zero_sign hz
      rw [hz_sign] at h_sign
      contradiction
    · apply congrArg
      apply azInt_ext
      · exact (eq_false_of_ne_true h_sign).symm
      · rfl
  · -- negative, cs.head? != '-'
    have h_head2 : ('-' :: AzNat.toChars z.abs).head? = some '-' := rfl
    have h_true : (some '-' == some '-') = true := rfl
    rw [h_head2] at h_head
    rw [h_true] at h_head
    contradiction

end Azurite.AzInt

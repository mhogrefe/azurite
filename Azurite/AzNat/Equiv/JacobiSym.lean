import Azurite.AzNat.JacobiSym
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.TrailingZeros
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Size

namespace Azurite.AzNat

/-!
Correctness of the binary Jacobi-symbol algorithm.

  1. `jacobiNat_eq`: the ℕ reference computes Mathlib's `jacobiSym` for odd
     `n`, by strong induction on `n` — one unfolding per step:
     `mod_left`, the factorization `a = 2^t a'` with `J(2 | n) = χ₈(n)`
     (`at_two`, `χ₈_nat_eq_if_mod_eight`), reciprocity
     (`quadratic_reciprocity_if`), and `mod_left` again.
  2. `jacobi_loop_eq`: the `AzNat` loop mirrors the ℕ reference step by
     step (`toNat_mod`, `trailingZeros_eq_padicValNat`, `toNat_hShiftRight`,
     `toNat_modPow2`) for fuel `≥ n`.
  3. `jacobi_eq`: the top-level `AzNat` symbol is `jacobiSym`.
-/

open Nat

/-- The odd part `a / 2^(v₂ a)` is odd. -/
theorem odd_div_pow_padicValNat_two {a : ℕ} (ha : a ≠ 0) :
    (a / 2 ^ padicValNat 2 a) % 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t := padicValNat 2 a with ht
  have hdvd : 2 ^ t ∣ a := pow_padicValNat_dvd
  obtain ⟨c, hc⟩ := hdvd
  have hpos : 0 < 2 ^ t := Nat.pow_pos (by norm_num)
  have hdiv : a / 2 ^ t = c := by rw [hc, Nat.mul_div_cancel_left _ hpos]
  rw [hdiv]
  by_contra h
  have h2 : 2 ∣ c := by omega
  apply pow_succ_padicValNat_not_dvd (p := 2) ha
  show 2 ^ (t + 1) ∣ a
  rw [pow_succ, hc]
  exact Nat.mul_dvd_mul_left _ h2

/-- `χ₈(n)^t` for odd `n`, as the algorithm computes it. -/
theorem chi8_pow (n t : ℕ) (hn : n % 2 = 1) :
    (ZMod.χ₈ (n : ZMod 8)) ^ t
      = if t % 2 = 0 then 1 else if n % 8 = 1 ∨ n % 8 = 7 then (1 : ℤ) else -1 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega)]
  by_cases h8 : n % 8 = 1 ∨ n % 8 = 7
  · rw [ite_eq_left h8, one_pow]
    split_ifs <;> rfl
  · rw [ite_eq_right h8]
    rcases Nat.even_or_odd t with ht | ht
    · rw [ht.neg_one_pow, ite_eq_left (Nat.even_iff.mp ht)]
    · rw [ht.neg_one_pow, ite_eq_right (by rw [Nat.odd_iff.mp ht]; omega)]

/-- **The ℕ reference computes Mathlib's Jacobi symbol** for odd `n`. -/
theorem jacobiNat_eq (a n : ℕ) (hn : n % 2 = 1) : jacobiNat a n = jacobiSym a n := by
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    rw [jacobiNat]
    by_cases hn1 : n ≤ 1
    · rw [ite_eq_left hn1]
      have : n = 1 := by omega
      subst this
      exact (jacobiSym.one_right _).symm
    · rw [ite_eq_right hn1]
      have hn1' : 1 < n := by omega
      have hmod : jacobiSym (a : ℤ) n = jacobiSym ((a % n : ℕ) : ℤ) n := by
        rw [jacobiSym.mod_left]
        push_cast
        rfl
      by_cases h0 : a % n = 0
      · rw [ite_eq_left h0, hmod, h0, Nat.cast_zero, jacobiSym.zero_left hn1']
      · rw [ite_eq_right h0]
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        set a₁ := a % n with ha₁
        set t := padicValNat 2 a₁ with ht
        set a' := a₁ / 2 ^ t with ha'
        have hpos : 0 < 2 ^ t := Nat.pow_pos (by norm_num)
        have hsplit : a₁ = 2 ^ t * a' := by
          rw [ha', Nat.mul_div_cancel' pow_padicValNat_dvd]
        have hodd : a' % 2 = 1 := odd_div_pow_padicValNat_two h0
        have ha'lt : a' < n := lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by omega))
        -- `J(a | n) = χ₈(n)^t · J(a' | n)`
        have hfac : jacobiSym (a : ℤ) n
            = (ZMod.χ₈ (n : ZMod 8)) ^ t * jacobiSym (a' : ℤ) n := by
          rw [hmod, hsplit, Nat.cast_mul, jacobiSym.mul_left, Nat.cast_pow, Nat.cast_ofNat,
            jacobiSym.pow_left, jacobiSym.at_two (Nat.odd_iff.mpr hn)]
        rw [hfac, chi8_pow n t hn]
        by_cases h1 : a' = 1
        · rw [ite_eq_left h1, h1, Nat.cast_one, jacobiSym.one_left, mul_one]
        · rw [ite_eq_right h1]
          have hrec := jacobiSym.quadratic_reciprocity_if hodd hn
          have hih : jacobiNat (n % a') a' = jacobiSym ((n % a' : ℕ) : ℤ) a' :=
            ih a' ha'lt (n % a') hodd
          have hmod' : jacobiSym (n : ℤ) a' = jacobiSym ((n % a' : ℕ) : ℤ) a' := by
            rw [jacobiSym.mod_left]
            push_cast
            rfl
          rw [hih, ← hmod', ← hrec]
          split_ifs <;> ring

/-! ### The `AzNat` loop mirrors the ℕ reference -/

private theorem eq_zero_iff_toNat (x : AzNat) : x = 0 ↔ x.toNat = 0 := by
  refine ⟨fun h => h ▸ rfl, fun h => toNat_injective (by rw [h]; rfl)⟩

private theorem eq_one_iff_toNat (x : AzNat) : x = 1 ↔ x.toNat = 1 := by
  refine ⟨fun h => h ▸ rfl, fun h => toNat_injective (by rw [h]; rfl)⟩

private theorem modPow2_eq_ofNat_iff (x : AzNat) (k c : ℕ) :
    x.modPow2 k = ofNat c ↔ x.toNat % 2 ^ k = c := by
  constructor
  · intro h
    have := congrArg toNat h
    rwa [toNat_modPow2, toNat_ofNat] at this
  · intro h
    exact toNat_injective (by rw [toNat_modPow2, toNat_ofNat, h])

theorem jacobi_loop_eq (a n : AzNat) :
    ∀ fuel : ℕ, n.toNat ≤ fuel → jacobi.loop a n fuel = jacobiNat a.toNat n.toNat := by
  intro fuel
  induction fuel generalizing a n with
  | zero =>
    intro hf
    have h0 : n.toNat = 0 := by omega
    rw [jacobi.loop, jacobiNat]
    dsimp only
    rw [ite_eq_left (show n.toNat ≤ 1 by omega)]
  | succ fuel ih =>
    intro hf
    rw [jacobi.loop, jacobiNat]
    dsimp only
    by_cases hn1 : n ≤ 1
    · have hn1n : n.toNat ≤ 1 := (le_iff_toNat_le n 1).mp hn1
      rw [ite_eq_left hn1, ite_eq_left hn1n]
    · have hn1' : ¬ n.toNat ≤ 1 := fun h => hn1 ((le_iff_toNat_le n 1).mpr h)
      rw [ite_eq_right hn1, ite_eq_right hn1']
      by_cases h0 : a % n = 0
      · have h0' : a.toNat % n.toNat = 0 := by
          have := (eq_zero_iff_toNat _).mp h0
          rwa [toNat_mod] at this
        rw [ite_eq_left h0, ite_eq_left h0']
      · have h0' : ¬ a.toNat % n.toNat = 0 := fun h =>
          h0 ((eq_zero_iff_toNat _).mpr (by rw [toNat_mod]; exact h))
        rw [ite_eq_right h0, ite_eq_right h0']
        rw [trailingZeros_eq_padicValNat _ h0, toNat_mod]
        dsimp only
        have hsh : ((a % n) >>> padicValNat 2 (a.toNat % n.toNat)).toNat
            = a.toNat % n.toNat / 2 ^ padicValNat 2 (a.toNat % n.toNat) := by
          rw [toNat_hShiftRight, toNat_mod, Nat.shiftRight_eq_div_pow]
        have hs : (if padicValNat 2 (a.toNat % n.toNat) % 2 = 0 then (1 : ℤ)
              else if n.modPow2 3 = ofNat 1 ∨ n.modPow2 3 = ofNat 7 then 1 else -1)
            = (if padicValNat 2 (a.toNat % n.toNat) % 2 = 0 then 1
              else if n.toNat % 8 = 1 ∨ n.toNat % 8 = 7 then 1 else -1) := by
          simp only [modPow2_eq_ofNat_iff, show (2 : ℕ) ^ 3 = 8 by norm_num]
        rw [hs]
        by_cases h1 : (a % n) >>> padicValNat 2 (a.toNat % n.toNat) = 1
        · have h1' := (eq_one_iff_toNat _).mp h1
          rw [hsh] at h1'
          rw [ite_eq_left h1, ite_eq_left h1']
        · have h1' : ¬ a.toNat % n.toNat / 2 ^ padicValNat 2 (a.toNat % n.toNat) = 1 :=
            fun h => h1 ((eq_one_iff_toNat _).mpr (by rw [hsh]; exact h))
          rw [ite_eq_right h1, ite_eq_right h1']
          have hcond : (((a % n) >>> padicValNat 2 (a.toNat % n.toNat)).modPow2 2 = ofNat 3
                ∧ n.modPow2 2 = ofNat 3)
              ↔ (a.toNat % n.toNat / 2 ^ padicValNat 2 (a.toNat % n.toNat) % 4 = 3
                ∧ n.toNat % 4 = 3) := by
            rw [modPow2_eq_ofNat_iff, modPow2_eq_ofNat_iff, hsh,
              show (2 : ℕ) ^ 2 = 4 by norm_num]
          have hrec := ih (n % ((a % n) >>> padicValNat 2 (a.toNat % n.toNat)))
            ((a % n) >>> padicValNat 2 (a.toNat % n.toNat)) (by
              rw [hsh]
              have h2 : a.toNat % n.toNat / 2 ^ padicValNat 2 (a.toNat % n.toNat)
                  ≤ a.toNat % n.toNat := Nat.div_le_self _ _
              have h3 : a.toNat % n.toNat < n.toNat := Nat.mod_lt _ (by omega)
              omega)
          rw [hrec, toNat_mod, hsh]
          simp only [hcond]

/-- **The `AzNat` Jacobi symbol is Mathlib's** for odd `n`. -/
theorem jacobi_eq (a n : AzNat) (hn : n.toNat % 2 = 1) :
    jacobi a n = jacobiSym a.toNat n.toNat := by
  rw [jacobi, jacobi_loop_eq a n _ ?_, jacobiNat_eq _ _ hn]
  rw [Nat.shiftLeft_eq, one_mul, ← size_toNat]
  exact (Nat.lt_size_self _).le

end Azurite.AzNat

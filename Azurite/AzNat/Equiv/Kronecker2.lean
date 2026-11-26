/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Kronecker2
import Azurite.AzNat.Equiv.Kronecker
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Sub
import Azurite.Kronecker.Theory

/-!
# Kronecker substitution at two points: the values

The functions of `AzNat/Kronecker2.lean` compute what `Kronecker/Theory.lean` talks about:
with `L` the list of the values of the coefficients and `B = 2^(64 w)`,

* `kroneckerPackEven_toNat`, `kroneckerPackOdd_toNat`: `evenValue (natPoly L) B` and
  `oddValue (natPoly L) B`;
* `kroneckerEvalPair_fst`, `kroneckerEvalPair_snd`: the values at `B` and at `−B`;
* `kroneckerHalves_fst`, `kroneckerHalves_snd`: the two half sums of a product;
* `kroneckerCoeff2_toNat`: the coefficients of a polynomial read from its two half sums.
-/

open Polynomial

namespace Azurite.AzNat

open Azurite.Kronecker

theorem limbBlock_toNat (x : AzNat) (i n : Nat) :
    (limbBlock x i n).toNat = x.toNat / 2 ^ (64 * i) % 2 ^ (64 * n) := by
  unfold limbBlock
  rw [toNat_ofLimbs, Array.toList_extract]
  show toNatLimbsList ((x.limbs.toList.drop i).take (i + n - i)) = _
  rw [Nat.add_sub_cancel_left, toNatLimbsList_take, toNatLimbsList_drop]
  rfl

theorem toNat_abs_of_toInt (z : AzInt) (N : ℕ) (h : z.toInt = N) : z.abs.toNat = N := by
  unfold AzInt.toInt at h
  split at h
  · exact_mod_cast h
  · omega

theorem limbBlock_toNat_list (x : AzNat) (i n : Nat) :
    (limbBlock x i n).toNat = toNatLimbsList ((x.limbs.toList.drop i).take n) := by
  unfold limbBlock
  rw [toNat_ofLimbs, Array.toList_extract]
  show toNatLimbsList ((x.limbs.toList.drop i).take (i + n - i)) = _
  rw [Nat.add_sub_cancel_left]

theorem kroneckerCoeff_toNat_list (w : Nat) (x : AzNat) (k : Nat) :
    (kroneckerCoeff w x k).toNat = toNatLimbsList ((x.limbs.toList.drop (k * w)).take w) :=
  limbBlock_toNat_list x (k * w) w

theorem natCast_abs_toNat (z : AzInt) : (z.abs.toNat : ℤ) = |z.toInt| := by
  unfold AzInt.toInt
  split <;> simp

/-- The entries of even index are the coefficients of the even part. -/
theorem natPoly_evens (a : Array AzNat) :
    natPoly ((Array.ofFn fun (i : Fin ((a.size + 1) / 2)) =>
      a[2 * i.val]'(by omega)).toList.map toNat) = evenPart (natPoly (a.toList.map toNat)) := by
  ext j
  rw [natPoly_coeff, evenPart_coeff, natPoly_coeff]
  by_cases hj : 2 * j < a.size
  · have hj' : j < (a.size + 1) / 2 := by omega
    simp [List.getD, hj, hj']
  · have hj' : ¬ j < (a.size + 1) / 2 := by omega
    simp [List.getD, hj, hj']

/-- The entries of odd index are the coefficients of the odd part. -/
theorem natPoly_odds (a : Array AzNat) :
    natPoly ((Array.ofFn fun (i : Fin (a.size / 2)) =>
      a[2 * i.val + 1]'(by omega)).toList.map toNat) = oddPart (natPoly (a.toList.map toNat)) := by
  ext j
  rw [natPoly_coeff, oddPart_coeff, natPoly_coeff]
  by_cases hj : 2 * j + 1 < a.size
  · have hj' : j < a.size / 2 := by omega
    simp [List.getD, hj, hj']
  · have hj' : ¬ j < a.size / 2 := by omega
    simp [List.getD, hj, hj']

theorem pow_two_mul_eq (w : ℕ) : (2 : ℕ) ^ (64 * (2 * w)) = (2 ^ (64 * w)) ^ 2 := by
  rw [← pow_mul]
  congr 1
  ring

theorem kroneckerPackEven_toNat (w : Nat) (a : Array AzNat)
    (ha : ∀ c ∈ a, c.toNat < 2 ^ (64 * (2 * w))) :
    (kroneckerPackEven w a).toNat = evenValue (natPoly (a.toList.map toNat)) (2 ^ (64 * w)) := by
  unfold kroneckerPackEven evenValue
  rw [kroneckerPack_toNat_eval, natPoly_evens, pow_two_mul_eq]
  intro c hc
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hc
  exact ha _ (Array.getElem_mem _)

theorem toNatLimbsList_replicate_zero (w : ℕ) :
    toNatLimbsList (List.replicate w (0 : UInt64)) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    unfold toNatLimbsList at ih ⊢
    rw [List.replicate_succ, List.foldr_cons, ih]
    rfl

theorem kroneckerPackOdd_toNat (w : Nat) (a : Array AzNat)
    (ha : ∀ c ∈ a, c.toNat < 2 ^ (64 * (2 * w))) :
    (kroneckerPackOdd w a).toNat = oddValue (natPoly (a.toList.map toNat)) (2 ^ (64 * w)) := by
  unfold kroneckerPackOdd oddValue
  rw [toNat_ofLimbs, ← Array.foldl_toList, toNatLimbsList_foldl_pack, Array.toList_replicate,
    toNatLimbsList_replicate_zero, Array.size_replicate, Nat.zero_add, ← natPoly_eval,
    natPoly_odds, pow_two_mul_eq]
  intro c hc
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp (by simpa using hc)
  exact ha _ (Array.getElem_mem _)

/-- The first component of `kroneckerEvalPair` is the value at `2^(64 w)`. -/
theorem kroneckerEvalPair_fst (w : Nat) (a : Array AzNat)
    (ha : ∀ c ∈ a, c.toNat < 2 ^ (64 * (2 * w))) :
    (kroneckerEvalPair w a).1.toNat = (natPoly (a.toList.map toNat)).eval (2 ^ (64 * w)) := by
  unfold kroneckerEvalPair
  dsimp only
  rw [toNat_add, kroneckerPackEven_toNat w a ha, kroneckerPackOdd_toNat w a ha,
    eval_eq_even_add_odd]

/-- The second component of `kroneckerEvalPair` is the value at `−2^(64 w)`. -/
theorem kroneckerEvalPair_snd (w : Nat) (a : Array AzNat)
    (ha : ∀ c ∈ a, c.toNat < 2 ^ (64 * (2 * w))) :
    (kroneckerEvalPair w a).2.toInt =
      (evenValue (natPoly (a.toList.map toNat)) (2 ^ (64 * w)) : ℤ) -
        oddValue (natPoly (a.toList.map toNat)) (2 ^ (64 * w)) := by
  unfold kroneckerEvalPair
  dsimp only
  rw [AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, kroneckerPackEven_toNat w a ha,
    kroneckerPackOdd_toNat w a ha]

/-- **The even half sum of a product** from the products of the values at `±B`. -/
theorem kroneckerHalves_fst (P Q : ℕ[X]) (B : ℕ) (u : AzNat) (v : AzInt)
    (hu : u.toNat = P.eval B * Q.eval B)
    (hv : v.toInt = ((evenValue P B : ℤ) - oddValue P B) * ((evenValue Q B : ℤ) - oddValue Q B)) :
    (kroneckerHalves u v).1.toNat = evenValue (P * Q) B := by
  unfold kroneckerHalves
  dsimp only
  have h := two_mul_evenValue_mul P Q B
  have habs : (u.toAzInt + v).abs.toNat = 2 * evenValue (P * Q) B := by
    apply toNat_abs_of_toInt
    rw [AzInt.toInt_add, toInt_toAzInt, hu, hv]
    push_cast at h ⊢
    linarith
  show (shiftRight _ _).toNat = _
  rw [toNat_shiftRight, habs]
  omega

/-- **The odd half sum of a product** from the products of the values at `±B`. -/
theorem kroneckerHalves_snd (P Q : ℕ[X]) (B : ℕ) (u : AzNat) (v : AzInt)
    (hu : u.toNat = P.eval B * Q.eval B)
    (hv : v.toInt = ((evenValue P B : ℤ) - oddValue P B) * ((evenValue Q B : ℤ) - oddValue Q B)) :
    (kroneckerHalves u v).2.toNat = oddValue (P * Q) B := by
  have h1 := kroneckerHalves_fst P Q B u v hu hv
  have h2 := eval_eq_even_add_odd (P * Q) B
  rw [eval_mul, ← hu] at h2
  unfold kroneckerHalves at h1 ⊢
  dsimp only at h1 ⊢
  rw [toNat_sub, h1]
  omega

/-- **The coefficients from the two half sums.**  For `R` with coefficients below `B²`,
`B = 2^(64 w)`, the `k`-th block is the `k`-th coefficient. -/
theorem kroneckerCoeff2_toNat (w : Nat) (R : ℕ[X]) (N : ℕ) (hdeg : ∀ i, N ≤ i → R.coeff i = 0)
    (hlt : ∀ i, i < N → R.coeff i < 2 ^ (64 * (2 * w))) (xe xo : AzNat)
    (he : xe.toNat = evenValue R (2 ^ (64 * w))) (ho : xo.toNat = oddValue R (2 ^ (64 * w)))
    (k : ℕ) : (kroneckerCoeff2 w xe xo k).toNat = R.coeff k := by
  have hall : ∀ i, R.coeff i < (2 ^ (64 * w)) ^ 2 := by
    intro i
    rw [← pow_two_mul_eq]
    by_cases hi : i < N
    · exact hlt i hi
    · rw [hdeg i (by omega)]
      positivity
  unfold kroneckerCoeff2
  rw [limbBlock_toNat, pow_two_mul_eq]
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hpar : 2 * j % 2 = 0 := by omega
    simp only [hpar, ↓reduceIte]
    rw [he, evenValue,
      show (2 : ℕ) ^ (64 * (2 * j * w)) = ((2 ^ (64 * w)) ^ 2) ^ j by
        rw [← pow_mul, ← pow_mul]; congr 1; ring,
      eval_div_pow_mod (evenPart R) _ N
        (fun i hi => by rw [evenPart_coeff]; exact hdeg _ (by omega))
        (fun i _ => by rw [evenPart_coeff]; exact hall _), evenPart_coeff]
  · have hpar : ¬ (2 * j + 1) % 2 = 0 := by omega
    simp only [hpar, ↓reduceIte]
    rw [ho, oddValue,
      show (2 : ℕ) ^ (64 * ((2 * j + 1) * w)) = 2 ^ (64 * w) * ((2 ^ (64 * w)) ^ 2) ^ j by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring,
      Nat.mul_div_mul_left _ _ (by positivity),
      eval_div_pow_mod (oddPart R) _ N
        (fun i hi => by rw [oddPart_coeff]; exact hdeg _ (by omega))
        (fun i _ => by rw [oddPart_coeff]; exact hall _), oddPart_coeff]

end Azurite.AzNat

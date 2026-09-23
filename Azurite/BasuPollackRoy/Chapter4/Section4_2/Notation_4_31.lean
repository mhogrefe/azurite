/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_27
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_32
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Mathlib.Basic.Sign.Basic
import Mathlib.Data.List.TakeWhile

/-!
# BPR Notation 4.31: generalized permanences minus variations `PmV`

For a finite list `s = s_p, …, s_0` of elements of an ordered (commutative)
domain `K` with
`s_p ≠ 0`, let `q < p` be largest with `s_q ≠ 0` (so `s_{p-1} = … = s_{q+1} = 0`)
and `s' = s_q, …, s_0`. BPR define inductively

  `PmV(s) = 0`                                   if `s' = ∅`,
  `PmV(s) = PmV(s') + ε_{p-q}·sign(s_p s_q)`     if `p − q` is odd,
  `PmV(s) = PmV(s')`                             if `p − q` is even,

with `ε` as in Notation 4.27 (`Azurite.BPR.Chapter4.ε`).

We represent `s` as a `List K` ordered **high index first** (`s_p` is the head),
matching the way BPR writes the sequence. The next nonzero `s_q` together with the
tail `s'` is obtained as `rest.dropWhile (· = 0)` after removing the head `s_p`, and
the gap `p − q` equals `(s_p :: rest).length − s'.length`.

This file also records:

* `PmV_nil`, `PmV_singleton`, and the defining `PmV_cons` equation;
* the worked recursion when there are no intervening zeros (`PmV_cons_cons_ne`);
* **Note (1)** of BPR: when every entry is nonzero, `PmV(s)` is the difference
  between the numbers of sign permanences and sign variations, i.e.
  `PmV s = (s.length − 1) − 2·Var s` (`PmV_eq_of_forall_ne_zero`);
* **Note (2)** of BPR: when `s` is the leading-coefficient sequence of
  `𝒫 = P_p, …, P_0` with `deg P_i = i`, then `PmV(s) = Var(𝒫; −∞, +∞)`
  (`PmV_eq_varBetween`, using `varBetween` of Notation 2.34). The `−∞` signs
  `(-1)^{deg}·lc` flip every adjacent permanence of `s` into a variation, so
  `Var(𝒫;−∞) + Var(𝒫;+∞) = length − 1` (`Var_negInf_add_Var_posInf`); combined
  with Note (1) this gives `Var(𝒫;−∞) − Var(𝒫;+∞) = PmV(s)`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

-- BPR states `PmV` over a field, but the definition (and all of its properties
-- below) only needs an ordered commutative domain: nothing here divides.
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

-- `hdw` (the `dropWhile` equation) is used only in the termination proof; silence the lint.
set_option linter.unusedVariables false in
/-- **BPR Notation 4.31.** Generalized permanences minus variations of a list
`s = s_p, …, s_0` (head = highest index). After the leading entry `s_p`, the
zeros are skipped to the next nonzero `s_q`; the gap `p − q` contributes
`ε_{p-q}·sign(s_p s_q)` when odd, nothing when even, and the recursion continues
on `s' = s_q, …, s_0`. -/
def PmV : List K → ℤ
  | [] => 0
  | sp :: rest =>
    match hdw : rest.dropWhile (fun x => decide (x = 0)) with
    | [] => 0
    | sq :: tl =>
      PmV (sq :: tl) +
        (if Odd (rest.length + 1 - (sq :: tl).length)
          then ε (rest.length + 1 - (sq :: tl).length) * (SignType.sign (sp * sq) : ℤ)
          else 0)
  termination_by l => l.length
  decreasing_by
    have hle := List.length_dropWhile_le (fun x => decide (x = 0)) rest
    rw [hdw] at hle
    simp only [List.length_cons] at hle ⊢
    omega

omit [IsStrictOrderedRing K] in
@[simp] theorem PmV_nil : PmV ([] : List K) = 0 := by simp only [PmV]

omit [IsStrictOrderedRing K] in
@[simp] theorem PmV_singleton (a : K) : PmV [a] = 0 := by
  rw [PmV]; simp

omit [IsStrictOrderedRing K] in
/-- When the entry immediately after the head is already nonzero (gap `= 1`),
the recursion adds `sign(sp · sq)` (since `ε₁ = 1`). -/
theorem PmV_cons_cons_ne (sp sq : K) (tl : List K) (hsq : sq ≠ 0) :
    PmV (sp :: sq :: tl) = PmV (sq :: tl) + (SignType.sign (sp * sq) : ℤ) := by
  have hdrop : (sq :: tl).dropWhile (fun x => decide (x = 0)) = sq :: tl :=
    List.dropWhile_cons_of_neg (by simp [hsq])
  rw [PmV]
  split
  · next h => rw [hdrop] at h; exact absurd h (by simp)
  · next sq' tl' h =>
    rw [hdrop] at h
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    have hg : (sq :: tl).length + 1 - (sq :: tl).length = 1 := by
      simp only [List.length_cons]; omega
    rw [hg]
    simp [ε_one]

/-- **BPR Notation 4.31, Note (1).** When every entry of `s` is nonzero, `PmV s`
is the difference between the number of sign permanences and the number of sign
variations of `s = s_p, …, s_0`. Equivalently, since permanences and variations
together exhaust the `length − 1` adjacent pairs (`Var s` counting the
variations), `PmV s + 2·Var s = length s − 1`. -/
theorem PmV_eq_of_forall_ne_zero :
    ∀ (s : List K), s ≠ [] → (∀ x ∈ s, x ≠ 0) →
      PmV s + 2 * (Var s : ℤ) = (s.length : ℤ) - 1
  | [], hs, _ => absurd rfl hs
  | [_], _, h0 => by simp [Var_of_forall_ne_zero h0]
  | sp :: sq :: tl, _, h0 => by
    have hsp : sp ≠ 0 := h0 sp (by simp)
    have hsq : sq ≠ 0 := h0 sq (by simp)
    have hIH := PmV_eq_of_forall_ne_zero (sq :: tl) (by simp)
      (fun x hx => h0 x (List.mem_cons_of_mem sp hx))
    have hsign : (SignType.sign (sp * sq) : ℤ)
        + 2 * (if sp * sq < 0 then (1 : ℤ) else 0) = 1 := by
      rcases lt_trichotomy (sp * sq) 0 with hlt | heq | hgt
      · rw [ite_eq_left hlt, sign_neg hlt]; decide
      · exact absurd heq (mul_ne_zero hsp hsq)
      · rw [ite_eq_right (not_lt.mpr hgt.le), sign_pos hgt]; decide
    rw [PmV_cons_cons_ne sp sq tl hsq, Var_of_forall_ne_zero h0, varNonzero_cons_cons,
      ← Var_of_forall_ne_zero (fun x hx => h0 x (List.mem_cons_of_mem sp hx))]
    simp only [List.length_cons] at hIH ⊢
    push_cast at hIH ⊢
    linarith [hIH, hsign]
  termination_by s => s.length
  decreasing_by simp only [List.length_cons]; omega

/-! ### Note (2): `PmV` of a coefficient sequence equals `Var(𝒫; −∞, +∞)` -/

omit [IsStrictOrderedRing K] in
private theorem Var_singleton (x : K) : Var [x] = 0 := by
  rcases eq_or_ne x 0 with hx | hx <;> simp [Var, hx]

omit [IsStrictOrderedRing K] in
private theorem Var_cons_cons_of_ne (a b : K) (l : List K) (h : ∀ x ∈ a :: b :: l, x ≠ 0) :
    Var (a :: b :: l) = (if a * b < 0 then 1 else 0) + Var (b :: l) := by
  rw [Var_of_forall_ne_zero h, varNonzero_cons_cons,
    ← Var_of_forall_ne_zero (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- The leading-coefficient sign sequence (`+∞`) and the `(-1)^{deg}·lc` sign
sequence (`−∞`) of a list of polynomials with nonzero, parity-alternating
degrees have complementary variation counts: each adjacent pair is a permanence
on one side exactly when it is a variation on the other. Hence
`Var(𝒫;−∞) + Var(𝒫;+∞) = length − 1`. -/
private theorem Var_negInf_add_Var_posInf :
    ∀ (P : List K[X]), (∀ Q ∈ P, Q ≠ 0) →
      P.IsChain (fun Q Q' => Odd (Q.natDegree + Q'.natDegree)) →
      Var (P.map fun Q => (-1) ^ Q.natDegree * Q.leadingCoeff)
        + Var (P.map Polynomial.leadingCoeff) = P.length - 1
  | [], _, _ => by simp
  | [Q], _, _ => by simp [Var_singleton]
  | Q :: Q' :: rest, hne, hpar => by
    obtain ⟨hrel, htail⟩ := List.isChain_cons_cons.mp hpar
    have hlcQ : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hne Q (by simp))
    have hlcQ' : Q'.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hne Q' (by simp))
    have hIH := Var_negInf_add_Var_posInf (Q' :: rest)
      (fun x hx => hne x (List.mem_cons_of_mem Q hx)) htail
    -- the two sign sequences are all-nonzero
    have hlcAll : ∀ x ∈ (Q :: Q' :: rest).map Polynomial.leadingCoeff, x ≠ 0 := by
      intro x hx; simp only [List.mem_map] at hx
      obtain ⟨R, hR, rfl⟩ := hx; exact leadingCoeff_ne_zero.mpr (hne R hR)
    have hnegAll : ∀ x ∈ (Q :: Q' :: rest).map (fun Q => (-1) ^ Q.natDegree * Q.leadingCoeff),
        x ≠ 0 := by
      intro x hx; simp only [List.mem_map] at hx
      obtain ⟨R, hR, rfl⟩ := hx
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr (hne R hR))
    -- the `−∞` adjacent product is minus the `+∞` one (parities differ)
    have hprod : ((-1 : K) ^ Q.natDegree * Q.leadingCoeff)
          * ((-1) ^ Q'.natDegree * Q'.leadingCoeff)
        = -(Q.leadingCoeff * Q'.leadingCoeff) := by
      have h1 : ((-1 : K) ^ Q.natDegree * Q.leadingCoeff)
            * ((-1) ^ Q'.natDegree * Q'.leadingCoeff)
          = (-1) ^ (Q.natDegree + Q'.natDegree) * (Q.leadingCoeff * Q'.leadingCoeff) := by
        rw [pow_add]; ring
      rw [h1, hrel.neg_one_pow]; ring
    -- so each adjacent pair is a variation on one side iff a permanence on the other
    have hind : (if ((-1 : K) ^ Q.natDegree * Q.leadingCoeff)
            * ((-1) ^ Q'.natDegree * Q'.leadingCoeff) < 0 then 1 else 0)
          + (if Q.leadingCoeff * Q'.leadingCoeff < 0 then (1 : ℕ) else 0) = 1 := by
      rw [hprod]
      rcases lt_trichotomy (Q.leadingCoeff * Q'.leadingCoeff) 0 with hlt | heq | hgt
      · rw [ite_eq_right (by simpa using hlt.le), ite_eq_left hlt]
      · exact absurd heq (mul_ne_zero hlcQ hlcQ')
      · rw [ite_eq_left (by simpa using hgt), ite_eq_right (by simpa using hgt.le)]
    simp only [List.map_cons, List.length_cons] at hIH ⊢
    rw [Var_cons_cons_of_ne _ _ _ hnegAll, Var_cons_cons_of_ne _ _ _ hlcAll]
    beta_reduce at hIH ⊢
    omega

/-- **BPR Notation 4.31, Note (2).** If `s` is the leading-coefficient sequence of
a list of polynomials `𝒫 = P_p, …, P_0` whose degrees descend by one
(`deg P_i = i`, encoded as nonzeroness together with the chain condition that each
degree is one more than the next), then `PmV(s)` equals the change in sign
variations of `𝒫` from `−∞` to `+∞`, `Var(𝒫; −∞, +∞)` (Notation 2.34). -/
theorem PmV_eq_varBetween (P : List K[X]) (hne : ∀ Q ∈ P, Q ≠ 0)
    (hdeg : P.IsChain (fun Q Q' => Q.natDegree = Q'.natDegree + 1)) :
    (PmV (P.map Polynomial.leadingCoeff) : ℤ)
      = varBetween P ExtendedPoint.negInf ExtendedPoint.posInf := by
  have hpar : P.IsChain (fun Q Q' => Odd (Q.natDegree + Q'.natDegree)) :=
    hdeg.imp (fun a b h => by rw [h]; exact ⟨b.natDegree, by ring⟩)
  have hlcAll : ∀ x ∈ P.map Polynomial.leadingCoeff, x ≠ 0 := by
    intro x hx; simp only [List.mem_map] at hx
    obtain ⟨R, hR, rfl⟩ := hx; exact leadingCoeff_ne_zero.mpr (hne R hR)
  rw [varBetween, varAt_negInf, varAt_posInf]
  rcases eq_or_ne P [] with hP | hP
  · subst hP; simp
  · have hmapne : P.map Polynomial.leadingCoeff ≠ [] := by simpa using hP
    have hnote1 := PmV_eq_of_forall_ne_zero (P.map Polynomial.leadingCoeff) hmapne hlcAll
    have hkey := Var_negInf_add_Var_posInf P hne hpar
    have hlen : 1 ≤ P.length := List.length_pos_iff.mpr hP
    simp only [List.length_map] at hnote1
    omega


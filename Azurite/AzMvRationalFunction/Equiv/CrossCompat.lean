/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Equiv.Parse
import Azurite.AzMvRationalFunction.Equiv.OfAzRationalFunction
import Azurite.AzMvPolynomial.Equiv.ToCharsAlign
import Azurite.AzRationalFunction.ToString
import Azurite.AzRationalFunction.Parse
import Azurite.AzRationalFunction.Equiv.Parse

/-!
# Cross-compatibility: the univariate printer feeds the multivariate parser

The multivariate parser (naming variable `0` as `x`, via `XyzVar n`) reads the
univariate `AzRationalFunction.toString` output back as the lift of the
univariate function into variable `0`.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- Lifting into a variable commutes with `AzInt` scalar multiplication. -/
theorem toAzMvPolynomial_smul (i : Fin n) (c : AzInt) (p : AzPolynomial AzInt) :
    (c • p).toAzMvPolynomial i ord = c • (p.toAzMvPolynomial i ord) := by
  apply toMvPoly_injective
  rw [toMvPoly_smul, toMvPoly_toAzMvPolynomial, toMvPoly_toAzMvPolynomial,
    Azurite.AzPolynomial.toPoly_smul, Algebra.smul_def, Algebra.smul_def, Polynomial.eval₂_mul]
  congr 1
  rw [show (algebraMap AzInt (Polynomial AzInt)) c = Polynomial.C c from rfl, Polynomial.eval₂_C]
  rfl

/-- The displayed numerator of the lift is the lift of the univariate displayed
numerator. -/
theorem displayNum_toAzMvRationalFunction (i : Fin n) (r : AzRationalFunction) :
    displayNum (r.toAzMvRationalFunction i ord)
      = (Azurite.AzRationalFunction.displayNum r).toAzMvPolynomial i ord := by
  rw [displayNum, Azurite.AzRationalFunction.displayNum,
    AzRationalFunction.toAzMvRationalFunction_num]
  exact (toAzMvPolynomial_smul i _ r.num).symm

/-- The displayed denominator of the lift is the lift of the univariate displayed
denominator. -/
theorem displayDen_toAzMvRationalFunction (i : Fin n) (r : AzRationalFunction) :
    displayDen (r.toAzMvRationalFunction i ord)
      = (Azurite.AzRationalFunction.displayDen r).toAzMvPolynomial i ord := by
  rw [displayDen, Azurite.AzRationalFunction.displayDen,
    AzRationalFunction.toAzMvRationalFunction_den]
  exact (toAzMvPolynomial_smul i _ r.den).symm

/-! ### Sub-lemma #1: `toAzMvPolynomial i` is injective (over `AzInt`) -/

/-- `Polynomial.eval₂ C (X i) : Polynomial AzInt → MvPolynomial (Fin n) AzInt` is
injective (left inverse sends `X i ↦ X`, other variables `↦ 0`). -/
private theorem eval₂_C_X_injective (i : Fin n) :
    Function.Injective
      (Polynomial.eval₂ (MvPolynomial.C : AzInt →+* MvPolynomial (Fin n) AzInt)
        (MvPolynomial.X i)) := by
  let f : Polynomial AzInt →+* MvPolynomial (Fin n) AzInt :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i)
  let g : MvPolynomial (Fin n) AzInt →+* Polynomial AzInt :=
    MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = i then Polynomial.X else 0)
  have hcomp : (g.comp f) = RingHom.id (Polynomial AzInt) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.id_apply, f, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, g, MvPolynomial.eval₂Hom_C]
    · simp only [RingHom.comp_apply, RingHom.id_apply, f, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, g, MvPolynomial.eval₂Hom_X']
      simp
  have hli : Function.LeftInverse g f := fun p => by
    have := congrArg (fun h : Polynomial AzInt →+* Polynomial AzInt => h p) hcomp
    simpa [f, g] using this
  intro a b hab
  have := congrArg g hab
  rwa [show Polynomial.eval₂ (MvPolynomial.C : AzInt →+* _) (MvPolynomial.X i) a = f a from rfl,
    show Polynomial.eval₂ (MvPolynomial.C : AzInt →+* _) (MvPolynomial.X i) b = f b from rfl,
    hli a, hli b] at this

/-- The lift `toAzMvPolynomial i` is injective over `AzInt`. -/
private theorem toAzMvPolynomial_injective (i : Fin n) :
    Function.Injective (fun p : AzPolynomial AzInt => p.toAzMvPolynomial i ord) := by
  intro p q h
  apply toPoly_inj.mp
  apply eval₂_C_X_injective i
  rw [← toMvPoly_toAzMvPolynomial, ← toMvPoly_toAzMvPolynomial]
  exact congrArg toMvPoly h

/-- The lift of `q` is `1` iff `q` is `1`. -/
private theorem toAzMvPolynomial_eq_one_iff (i : Fin n) (q : AzPolynomial AzInt) :
    q.toAzMvPolynomial i ord = 1 ↔ q = 1 := by
  constructor
  · intro h
    exact toAzMvPolynomial_injective i (h.trans (AzPolynomial.toAzMvPolynomial_one i).symm)
  · intro h; rw [h]; exact AzPolynomial.toAzMvPolynomial_one i

/-! ### Sub-lemma #2: the two `numTerms` agree -/

/-- The counting `foldl` over a list equals the count of nonzero entries. -/
private theorem list_foldl_count (l : List AzInt) (a : ℕ) :
    l.foldl (fun k c => if c == 0 then k else k + 1) a = a + l.countP (· != 0) := by
  induction l generalizing a with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    by_cases hc : (c == 0) = true
    · have h0 : ((c != 0) = true) = False := by simp [bne, hc]
      rw [ite_eq_left hc]; simp only [h0]; simp
    · have h1 : (c != 0) = true := by simp [bne]; simpa using hc
      rw [ite_eq_right hc]; simp only [h1]; simp; omega

/-- Univariate `numTerms` counts nonzero coefficients. -/
private theorem uni_numTerms_eq_countP (p : AzPolynomial AzInt) :
    Azurite.AzRationalFunction.numTerms p = p.coeffs.toList.countP (· != 0) := by
  rw [Azurite.AzRationalFunction.numTerms, ← Array.foldl_toList, list_foldl_count, Nat.zero_add]

/-- The length of `termsBelow` counts nonzero coefficients among the first `N`. -/
private theorem termsBelow_length (i : Fin n) (coeffs : Array AzInt) (N : ℕ)
    (hN : N ≤ coeffs.size) :
    (Azurite.termsBelow i coeffs (ord := ord) N).length
      = (coeffs.toList.take N).countP (· != 0) := by
  induction N with
  | zero => simp
  | succ k ih =>
    have hk : k < coeffs.size := by omega
    have hget : (coeffs[k]?).getD 0 = coeffs[k]'hk := by
      rw [Array.getElem?_eq_getElem hk]; simp
    rw [Azurite.termsBelow_succ,
      show coeffs.toList.take (k + 1)
        = coeffs.toList.take k ++ [coeffs.toList[k]'(by simpa using hk)] from by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk)]; rfl,
      List.countP_append]
    by_cases hc : (coeffs[k]?).getD 0 = 0
    · rw [dite_eq_left hc, ih (by omega)]
      have hval : ((coeffs[k]'hk) != 0) = false := by rw [← hget]; simp [hc]
      simp [hval]
    · rw [dite_eq_right hc, List.length_cons, ih (by omega)]
      have hval : ((coeffs[k]'hk) != 0) = true := by rw [← hget]; simpa using hc
      simp [hval]

/-- The two `numTerms` agree under the lift. -/
private theorem numTerms_agree (i : Fin n) (p : AzPolynomial AzInt) :
    Azurite.AzRationalFunction.numTerms p = (p.toAzMvPolynomial i ord).numTerms := by
  rw [uni_numTerms_eq_countP, AzMvPolynomial.numTerms, ← Array.length_toList,
    Azurite.image_terms_toList, termsBelow_length i p.coeffs p.coeffs.size le_rfl,
    List.take_of_length_le (by simp)]

/-! ### Sub-lemma #3: `denBare` of the lift matches the univariate wrap rule -/

/-- The total degree of the lift is the univariate `natDegree`. -/
private theorem totalDegree_lift (i : Fin n) (p : AzPolynomial AzInt) :
    (p.toAzMvPolynomial i ord).totalDegree = p.natDegree := by
  rcases Nat.eq_zero_or_pos p.coeffs.size with h | h
  · have hz : p.toAzMvPolynomial i ord = (0 : AzMvPolynomial n AzInt ord) := by
      unfold AzPolynomial.toAzMvPolynomial; rw [dite_eq_left h]; rfl
    rw [hz]; simp [AzMvPolynomial.totalDegree, AzPolynomial.natDegree, h]
  · rw [Azurite.totalDegree_image i p h, AzPolynomial.natDegree]

/-- A pure prime-power monomial `xᵢ^k` has at most one nonzero exponent. -/
private theorem ofVarPow_countP_le_one (i : Fin n) (k : ℕ) :
    (MonicMonomial.ofVarPow i k : MonicMonomial n ord).exponents.toList.countP (· != 0) ≤ 1 := by
  unfold MonicMonomial.ofVarPow
  rw [Vector.toList_ofFn, List.ofFn_eq_map, List.countP_map]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [Function.comp_def]
  · have hcong : ∀ j ∈ List.finRange n,
        (((· != 0) ∘ fun j => if i = j then k else 0) j = true) ↔ ((j == i) = true) := by
      intro j _
      by_cases hij : i = j
      · subst hij; simp [Function.comp_apply, bne_iff_ne, hk.ne']
      · simp only [Function.comp_apply, bne_iff_ne, beq_iff_eq, ite_eq_right hij]
        constructor
        · intro h; exact absurd rfl h
        · intro h; exact absurd h.symm hij
    rw [List.countP_congr hcong]
    calc (List.finRange n).countP (· == i) = (List.finRange n).count i := List.count_eq_countP.symm
      _ = if i ∈ List.finRange n then 1 else 0 := (List.nodup_finRange n).count
      _ ≤ 1 := by split <;> omega

/-- Every term produced by `termsBelow` is a pure prime power, hence has at most
one nonzero exponent. -/
private theorem termsBelow_countP_le_one (i : Fin n) (coeffs : Array AzInt) (N : ℕ) :
    ∀ m ∈ Azurite.termsBelow i coeffs (ord := ord) N,
      (m.monic.exponents.toList.countP (· != 0)) ≤ 1 := by
  induction N with
  | zero => simp
  | succ k ih =>
    intro m hm
    rw [Azurite.termsBelow_succ] at hm
    split at hm
    · exact ih m hm
    · rcases List.mem_cons.mp hm with h | h
      · subst h; exact ofVarPow_countP_le_one i k
      · exact ih m h

/-- `denBare` of the lift coincides with the univariate wrapping condition. -/
private theorem denBare_iff (i : Fin n) (p : AzPolynomial AzInt) :
    denBare (p.toAzMvPolynomial i ord)
      ↔ (p.natDegree = 0
          ∨ (Azurite.AzRationalFunction.numTerms p ≤ 1 ∧ p.leadingCoeff = 1)) := by
  rw [denBare, totalDegree_lift, ← numTerms_agree]
  by_cases hd : p.natDegree = 0
  · simp [hd]
  · have hsize : 0 < p.coeffs.size := by rw [AzPolynomial.natDegree] at hd; omega
    have hne : (p.coeffs[p.coeffs.size - 1]?).getD 0 ≠ 0 := by
      have hb := p.last_ne_zero
      rw [Array.back?_eq_getElem?,
        Array.getElem?_eq_getElem (show p.coeffs.size - 1 < p.coeffs.size by omega)] at hb
      rw [Array.getElem?_eq_getElem (show p.coeffs.size - 1 < p.coeffs.size by omega)]
      simp only [Option.getD_some]
      intro heq; exact hb (by rw [heq])
    have hlc : p.leadingCoeff = (p.coeffs[p.coeffs.size - 1]?).getD 0 := by
      rw [AzPolynomial.leadingCoeff, AzPolynomial.coeff, AzPolynomial.natDegree]
    set mtop : Monomial n AzInt ord :=
      ⟨⟨(p.coeffs[p.coeffs.size - 1]?).getD 0, hne⟩,
        MonicMonomial.ofVarPow i (p.coeffs.size - 1)⟩ with hmtop_def
    have hmemtop : mtop ∈ (p.toAzMvPolynomial i ord).terms.toList := by
      rw [Azurite.image_terms_toList]
      have hs : p.coeffs.size = (p.coeffs.size - 1) + 1 := by omega
      rw [hs, Azurite.termsBelow_succ, dite_eq_right hne]
      exact List.mem_cons_self
    rw [or_iff_right hd, or_iff_right hd]
    apply and_congr_right
    intro hnt
    have hlen : (p.toAzMvPolynomial i ord).terms.toList.length ≤ 1 := by
      rw [Array.length_toList, ← AzMvPolynomial.numTerms, ← numTerms_agree]; exact hnt
    constructor
    · intro h2
      rw [hlc]; exact (h2 mtop hmemtop).1
    · intro hlc1 m hm
      have hmeq : m = mtop := by
        generalize hL : (p.toAzMvPolynomial i ord).terms.toList = l at hm hmemtop hlen
        rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
        · exact absurd hm (List.not_mem_nil)
        · rw [List.mem_singleton] at hm hmemtop; rw [hm, hmemtop]
        · simp only [List.length_cons] at hlen; omega
      subst hmeq
      refine ⟨?_, ofVarPow_countP_le_one i _⟩
      show (p.coeffs[p.coeffs.size - 1]?).getD 0 = 1
      rw [← hlc]; exact hlc1

/-! ### Sub-lemma #4: the `wrap*` strings agree -/

/-- The wrapped numerator component agrees between the univariate and lifted
multivariate printers. -/
private theorem wrapComponent_toList (hn : 0 < n) [Fact (n ≤ 26)] (p : AzPolynomial AzInt) :
    (Azurite.AzRationalFunction.wrapComponent p).toList
      = wrapComponent (XyzVar n) (p.toAzMvPolynomial (⟨0, hn⟩ : Fin n) ord) := by
  unfold Azurite.AzRationalFunction.wrapComponent wrapComponent
  rw [numTerms_agree (⟨0, hn⟩ : Fin n) p]
  by_cases hc : (p.toAzMvPolynomial (⟨0, hn⟩ : Fin n) ord).numTerms ≤ 1
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact AzMvPolynomial.toChars_toAzMvPolynomial_align hn p
  · rw [ite_eq_right hc, ite_eq_right hc, String.toList_append, String.toList_append,
      AzMvPolynomial.toChars_toAzMvPolynomial_align hn p]
    rfl

/-- The wrapped denominator agrees between the univariate and lifted
multivariate printers. -/
private theorem wrapDenominator_toList (hn : 0 < n) [Fact (n ≤ 26)] (p : AzPolynomial AzInt) :
    (Azurite.AzRationalFunction.wrapDenominator p).toList
      = wrapDenominator (XyzVar n) (p.toAzMvPolynomial (⟨0, hn⟩ : Fin n) ord) := by
  unfold Azurite.AzRationalFunction.wrapDenominator wrapDenominator
  by_cases hc : denBare (p.toAzMvPolynomial (⟨0, hn⟩ : Fin n) ord)
  · rw [ite_eq_left hc, ite_eq_left ((denBare_iff (⟨0, hn⟩ : Fin n) p).mp hc)]
    exact AzMvPolynomial.toChars_toAzMvPolynomial_align hn p
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((denBare_iff (⟨0, hn⟩ : Fin n) p).mpr h)),
      String.toList_append, String.toList_append,
      AzMvPolynomial.toChars_toAzMvPolynomial_align hn p]
    rfl

/-! ### Sub-lemma #5: the two string forms agree -/

/-- The lift of `q` equals `1` (as a `Bool` comparison) exactly when `q` does. -/
private theorem beq_toAzMvPolynomial_one (i : Fin n) (q : AzPolynomial AzInt) :
    (q.toAzMvPolynomial i ord == 1) = (q == 1) := by
  by_cases h : q = 1
  · rw [h]; simp [AzPolynomial.toAzMvPolynomial_one]
  · rw [beq_eq_false_iff_ne.mpr (fun he => h ((toAzMvPolynomial_eq_one_iff i q).mp he)),
      beq_eq_false_iff_ne.mpr h]

/-- **String-level cross-compatibility**: the univariate `toString` output is
exactly the multivariate `toStrWith (XyzVar n)` rendering of the lift of `r`
into variable `0`. -/
theorem toString_eq_toStrWith (hn : 0 < n) [Fact (n ≤ 26)] (r : AzRationalFunction) :
    Azurite.AzRationalFunction.toString r
      = toStrWith (XyzVar n) (r.toAzMvRationalFunction (⟨0, hn⟩ : Fin n) ord) := by
  rw [← String.toList_inj, toStrWith, String.toList_ofList]
  unfold Azurite.AzRationalFunction.toString toCharsWith
  rw [displayNum_toAzMvRationalFunction, displayDen_toAzMvRationalFunction,
    beq_toAzMvPolynomial_one]
  by_cases hd : (Azurite.AzRationalFunction.displayDen r == 1) = true
  · rw [ite_eq_left hd, ite_eq_left hd]
    exact AzMvPolynomial.toChars_toAzMvPolynomial_align hn _
  · rw [ite_eq_right hd, ite_eq_right hd, String.toList_append, String.toList_append,
      wrapComponent_toList (ord := ord) hn (Azurite.AzRationalFunction.displayNum r),
      wrapDenominator_toList (ord := ord) hn (Azurite.AzRationalFunction.displayDen r),
      show ("/" : String).toList = ['/'] from rfl, List.append_assoc]
    rfl

/-! ### The cross-compatibility theorem -/

/-- **Cross-compatibility**: the multivariate parser (naming variable `0` as
`x`, via `XyzVar n`) reads the univariate `AzRationalFunction.toString` output
back as the lift of `r` into variable `0`. -/
theorem parseStrWith_toString_toAzMvRationalFunction
    (hn : 0 < n) [Fact (n ≤ 26)] (r : Azurite.AzRationalFunction) :
    parseStrWith (XyzVar n) (Azurite.AzRationalFunction.toString r)
      = some (r.toAzMvRationalFunction (⟨0, hn⟩ : Fin n) ord) := by
  rw [toString_eq_toStrWith hn r]
  exact parseStrWith_toStrWith (XyzVar n) _

/-- **Round-trip with the standard `XyzVar` display** (variable `0` printed
as `x`). Now a direct specialization of the hypothesis-free generic
`parseStrWith_toStrWith`: the grammar reserves `(`, `)`, `/`, so every
`ParsableVar` naming scheme (including `XyzVar`) avoids them automatically. -/
theorem parseStrWith_toStrWith_xyz [Fact (n ≤ 26)]
    (r : AzMvRationalFunction n ord) :
    parseStrWith (XyzVar n) (toStrWith (XyzVar n) r) = some r :=
  parseStrWith_toStrWith (XyzVar n) r

end Azurite.AzMvRationalFunction

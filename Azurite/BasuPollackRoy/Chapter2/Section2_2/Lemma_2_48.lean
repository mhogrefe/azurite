/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Definition_2_45
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_35

/-!
# BPR Lemma 2.48: virtual multiplicity equals sign variation on a root-free
# half-open interval

**Lemma 2.48 (BPR).** Let `P ∈ R[X]` be nonzero and let `d < c` in `R`.
If no iterated derivative `P^{(k)}` (for `k < P.natDegree`) has a root in
`[d, c)`, then the virtual multiplicity of `c` with respect to `P` equals
the sign-variation change of `Der(P)` between `d` and `c`:

  `v(P, c) = Var(Der(P); d, c)`.

The BPR statement names a root `c` of `P`, but the conclusion holds for
arbitrary `c` under the root-free hypothesis, and the induction on
`natDegree P` becomes cleaner in the generalized form. Both directions of
the original BPR statement are immediate corollaries.

## Proof structure

Induct on `n = P.natDegree`.

* **Base `n = 0`.** `P` is a nonzero constant; `Der(P) = [P]`, so every
  `varAt (der P) _ = 0` and `v(P, c) = 0` (empty virtual roots list).

* **Inductive step.** Write `der P = P :: der P'`. We distinguish the two
  cases according to whether `P(c) = 0`:

  1. `P(c) = 0`: by Proposition 2.46 item (1),
     `v(P, c) = v(P', c) + 1`. The induction hypothesis applied to `P'`
     (whose hypothesis is weaker) gives `v(P', c) = Var(Der P'; d, c)`.
     Combined with the **key equation** below
     (`varBetween_der_succ_of_root_at_c_add_one`),
     `Var(Der P; d, c) = Var(Der P'; d, c) + 1 = v(P', c) + 1 = v(P, c)`.

  2. `P(c) ≠ 0`: the analogous equation
     (`varBetween_der_succ_of_not_root_at_c_add_cases`) relates
     `Var(Der P; d, c)` to `Var(Der P'; d, c)` with a correction matching
     the Proposition 2.46 trichotomy case for `v(P, c)` vs. `v(P', c)`.

The key equations are stated here as helper lemmas and proved by sign
analysis using `varAt_cons_der_eq`, `sign_eq_of_no_root_Icc`, and
`Var_zero_cons` from `Theorem_2_35.lean`.
-/

namespace Azurite.BPR.Lemma_2_48

open Polynomial Azurite.BPR Azurite.BPR.VirtualRoots Azurite.BPR.Theorem2_35
  Azurite.BPR.Proposition2_21 Azurite.BPR.Proposition2_22

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Sign-algebra helper

Abstracts the algebraic step used in the LHS computation of both key
equations: given two quantities `a`, `b` whose signs differ by `(-1)^ν`,
the difference of their negativity-indicators matches the parity-based
sign formula on the RHS of `virtualMultiplicity_diff_of_not_root`.

No polynomial content — pure algebra on `SignType` and `if` expressions. -/

omit [IsStrictOrderedRing R] in
/-- **Sign-variation jump formula.** If `sign a = (-1)^ν · sign b` and
    `b ≠ 0`, then the difference of the negativity indicators of `a`
    and `b` equals the `Even ν` / sign-of-`b` branching formula. -/
lemma jump_diff_formula {ν : ℕ} {a b : R} (hb : b ≠ 0)
    (hsign : SignType.sign a = (-1)^ν * SignType.sign b) :
    ((if a < 0 then (1 : ℤ) else 0) - (if b < 0 then 1 else 0)) =
      if Even ν then 0 else if 0 < b then 1 else -1 := by
  rcases Nat.even_or_odd ν with hν | hν
  · rw [ite_eq_left hν]
    have hpow : ((-1 : SignType))^ν = 1 := Even.neg_one_pow hν
    rw [hpow, one_mul] at hsign
    have hiff : (a < 0) ↔ (b < 0) := by
      rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, hsign]
    by_cases h : b < 0
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]; ring
    · rw [ite_eq_right (fun hh => h (hiff.mp hh)), ite_eq_right h]; ring
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hν)]
    have hpow : ((-1 : SignType))^ν = -1 := Odd.neg_one_pow hν
    rw [hpow, neg_one_mul] at hsign
    rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
    · have ha_pos : 0 < a := by
        apply sign_eq_one_iff.mp
        rw [hsign, sign_eq_neg_one_iff.mpr hb_neg]; decide
      rw [ite_eq_right (not_lt.mpr ha_pos.le), ite_eq_left hb_neg,
        ite_eq_right (not_lt.mpr hb_neg.le)]
      ring
    · have ha_neg : a < 0 := by
        apply sign_eq_neg_one_iff.mp
        rw [hsign, sign_eq_one_iff.mpr hb_pos]
      rw [ite_eq_left ha_neg, ite_eq_right (not_lt.mpr hb_pos.le), ite_eq_left hb_pos]
      ring

/-! ## Key equation (root case)

Under Lemma 2.48's hypothesis and the extra assumption `P(c) = 0`, adding
`P` on top of the `Der(P')` sequence increases the sign-variation change by
exactly one. This is the content of BPR's equations (2.1)–(2.5) in this
case: at `d` the first entry `P(d)` is nonzero and forces a sign change
against the next entry of the `Der(P')` chain (by the sign analysis from
Lemma 2.36); at `c` the leading entry `P(c) = 0` is dropped and contributes
nothing. -/

/-- **Key equation (root case).** Under Lemma 2.48's root-free hypothesis
    and `P(c) = 0` (with `natDegree P ≥ 1`):
    `Var(Der P; d, c) = Var(Der P'; d, c) + 1`.

    Proof sketch. `der P = P :: der P'`, so
    `varAt (der P) x = Var (P(x) :: (der P').map (·.eval x))` at any `x`.
    * At `x = d`: `P(d) ≠ 0` (from the hypothesis at `k = 0`), and sign
      analysis shows `P(d) * P'(d) < 0` (see `sign_eq_of_no_root_Icc`),
      so prepending `P(d)` adds exactly one to `varAt (der P') d`.
    * At `x = c`: `P(c) = 0`, so the leading zero drops and
      `varAt (der P) c = varAt (der P') c`.
    Subtracting gives `varBetween (der P) d c = varBetween (der P') d c + 1`. -/
lemma varBetween_der_succ_of_root_at_c_add_one
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hpos : 1 ≤ P.natDegree)
    {c d : R} (hdc : d < c) (hPc : P.eval c = 0)
    (hno_root : ∀ k, k < P.natDegree → ∀ x ∈ Set.Ico d c,
      ((⇑derivative)^[k] P).eval x ≠ 0) :
    varBetween (der P) (.finite d) (.finite c) =
      varBetween (der (derivative P)) (.finite d) (.finite c) + 1 := by
  have hdP : derivative P ≠ 0 := by
    intro h
    have := Polynomial.derivative_eq_zero.mp h
    omega
  have hPd : P.eval d ≠ 0 := by
    have h := hno_root 0 (by omega) d ⟨le_refl d, hdc⟩
    simpa using h
  have hdP_no_root : ∀ x ∈ Set.Ico d c, (derivative P).eval x ≠ 0 := by
    intro x hx
    by_cases h1 : 1 < P.natDegree
    · have := hno_root 1 h1 x hx
      rwa [Function.iterate_one] at this
    · have hnd1 : P.natDegree = 1 := by omega
      have hndP' : (derivative P).natDegree = 0 := by
        rw [natDegree_derivative_of_pos hpos, hnd1]
      obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hndP'
      have ha_ne : a ≠ 0 := fun h => hdP (ha ▸ h ▸ by simp)
      rw [← ha]; simpa
  have hP'd : (derivative P).eval d ≠ 0 :=
    hdP_no_root d ⟨le_refl d, hdc⟩
  -- Apply Rolle to Q = P * (X - C d).
  set Q : R[X] := P * (X - C d) with hQ_def
  have hQd : Q.eval d = 0 := by simp [hQ_def]
  have hQc : Q.eval c = 0 := by simp [hQ_def, hPc]
  obtain ⟨ξ, ⟨hdξ, hξc⟩, hQ'ξ⟩ := proposition_2_22 hIVP Q hdc hQd hQc
  have hQ'_eval : (derivative Q).eval ξ =
      (derivative P).eval ξ * (ξ - d) + P.eval ξ := by
    simp [hQ_def, derivative_mul]
  rw [hQ'_eval] at hQ'ξ
  have hPξ_eq : P.eval ξ = -((derivative P).eval ξ * (ξ - d)) := by linarith
  have hP'ξ : (derivative P).eval ξ ≠ 0 :=
    hdP_no_root ξ ⟨hdξ.le, hξc⟩
  have hξ_d_pos : 0 < ξ - d := sub_pos.mpr hdξ
  have hP'ξ_sq_pos : 0 < (derivative P).eval ξ * (derivative P).eval ξ :=
    mul_self_pos.mpr hP'ξ
  have hPξP'ξ_neg : P.eval ξ * (derivative P).eval ξ < 0 := by
    have heq : P.eval ξ * (derivative P).eval ξ =
        -((ξ - d) * ((derivative P).eval ξ * (derivative P).eval ξ)) := by
      rw [hPξ_eq]; ring
    rw [heq]
    have : 0 < (ξ - d) * ((derivative P).eval ξ * (derivative P).eval ξ) :=
      mul_pos hξ_d_pos hP'ξ_sq_pos
    linarith
  -- Sign transfer [d, ξ] ⊆ [d, c).
  have hP_no_root_Icc : ∀ z ∈ Set.Icc d ξ, P.eval z ≠ 0 := by
    intro z hz
    have := hno_root 0 (by omega) z ⟨hz.1, lt_of_le_of_lt hz.2 hξc⟩
    simpa using this
  have hdP_no_root_Icc : ∀ z ∈ Set.Icc d ξ, (derivative P).eval z ≠ 0 :=
    fun z hz => hdP_no_root z ⟨hz.1, lt_of_le_of_lt hz.2 hξc⟩
  have hsign_P : SignType.sign (P.eval d) = SignType.sign (P.eval ξ) :=
    sign_eq_of_no_root_Icc hIVP P hdξ.le hP_no_root_Icc
  have hsign_P' : SignType.sign ((derivative P).eval d) =
      SignType.sign ((derivative P).eval ξ) :=
    sign_eq_of_no_root_Icc hIVP (derivative P) hdξ.le hdP_no_root_Icc
  have hPdP'd_neg : P.eval d * (derivative P).eval d < 0 := by
    have h : SignType.sign (P.eval ξ * (derivative P).eval ξ) = -1 :=
      sign_eq_neg_one_iff.mpr hPξP'ξ_neg
    rw [sign_mul, ← hsign_P, ← hsign_P', ← sign_mul] at h
    exact sign_eq_neg_one_iff.mp h
  -- Variation equalities and combination.
  have hderP_cons : der P = P :: der (derivative P) := der_eq_cons hpos
  have hvar_c : varAt (der P) (.finite c) =
      varAt (der (derivative P)) (.finite c) := by
    rw [hderP_cons, varAt_finite, varAt_finite]
    simp only [List.map_cons, hPc]
    exact Var_zero_cons _
  have hmult_d : (derivative P).rootMultiplicity d = 0 :=
    Polynomial.rootMultiplicity_eq_zero hP'd
  have hvar_d : varAt (der P) (.finite d) =
      1 + varAt (der (derivative P)) (.finite d) := by
    rw [hderP_cons, varAt_cons_der_eq P (derivative P) hPd hdP,
      hmult_d, Function.iterate_zero_apply, ite_eq_left hPdP'd_neg]
  unfold varBetween
  rw [hvar_c, hvar_d]
  push_cast
  ring

/-! ## Key equation (non-root case)

When `P(c) ≠ 0`, the correction between `Var(Der P; d, c)` and
`Var(Der P'; d, c)` matches the Proposition 2.46 trichotomy for
`v(P, c)` vs. `v(P', c)`. The precise correction is determined by the
signs of `P` and `P^{(μ+1)}` at both endpoints, where `μ` is the
multiplicity of `c` as a root of `P'`. -/

/-- **Key equation (non-root case).** Under Lemma 2.48's root-free
    hypothesis, `natDegree P ≥ 1`, and `P(c) ≠ 0`, the difference
    `Var(Der P; d, c) - Var(Der P'; d, c)` equals `v(P, c) - v(P', c)`
    (so the induction closes via the inductive hypothesis applied to `P'`).

    Proof: both sides are computed to equal the same sign-based expression,
    `if Even ν then 0 else sign(P(c) · P^(ν+1)(c))`, where
    `ν = (derivative P).rootMultiplicity c`. The LHS is computed externally
    using `varAt_cons_der_eq` and Proposition 2.21 sign analysis; the RHS
    is given by `virtualMultiplicity_diff_of_not_root`. -/
lemma varBetween_der_succ_of_not_root_at_c
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (hdP : derivative P ≠ 0) (hpos : 1 ≤ P.natDegree)
    {c d : R} (hdc : d < c) (hPc : P.eval c ≠ 0)
    (hno_root : ∀ k, k < P.natDegree → ∀ x ∈ Set.Ico d c,
      ((⇑derivative)^[k] P).eval x ≠ 0) :
    varBetween (der P) (.finite d) (.finite c) -
        varBetween (der (derivative P)) (.finite d) (.finite c) =
      (virtualMultiplicity hIVP hP c : ℤ) -
        ((virtualRoots hIVP hdP).count c : ℤ) := by
  set ν := (derivative P).rootMultiplicity c with hν_def
  -- Abbreviations for P' and the sign-change jump indicators.
  set Q := derivative P with hQ_def
  -- P(d) ≠ 0 from the hypothesis at k = 0.
  have hPd_ne : P.eval d ≠ 0 := by
    have h := hno_root 0 (by omega) d ⟨le_refl d, hdc⟩
    simpa using h
  -- Q(d) ≠ 0: from k = 1 hypothesis if natDegree P ≥ 2, else Q is a nonzero const.
  have hQd_ne : Q.eval d ≠ 0 := by
    by_cases h1 : 1 < P.natDegree
    · have h := hno_root 1 h1 d ⟨le_refl d, hdc⟩
      rwa [Function.iterate_one] at h
    · have hnd1 : P.natDegree = 1 := by omega
      have hndQ : Q.natDegree = 0 := by
        rw [hQ_def, natDegree_derivative_of_pos hpos, hnd1]
      obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hndQ
      have ha_ne : a ≠ 0 := fun h => hdP (ha ▸ h ▸ by simp)
      rw [← ha]; simpa
  have hQ_ne : Q ≠ 0 := hdP
  -- Sign analysis via Proposition 2.21.
  set σP : SignType := SignType.sign (P.eval c) with hσP_def
  set τ : SignType := SignType.sign (((⇑derivative)^[ν] Q).eval c) with hτ_def
  have hmult_P : P.rootMultiplicity c = 0 := Polynomial.rootMultiplicity_eq_zero hPc
  have hσP_ne : σP ≠ 0 := fun h => hPc (sign_eq_zero_iff.mp h)
  -- Prop 2.21 left-side for P (rootMult = 0): sign σP to the left of c.
  have hP_sl : HasSignLeft P c σP := by
    have h := proposition_2_21_left hIVP hP c
    rw [hmult_P] at h
    simp only [Function.iterate_zero_apply, pow_zero, one_mul] at h
    exact h
  have hQ_sl : HasSignLeft Q c ((-1)^ν * τ) := proposition_2_21_left hIVP hQ_ne c
  -- Sign extensions to d.
  have hP_sign_d : SignType.sign (P.eval d) = σP := by
    obtain ⟨a, had, hsa⟩ := hP_sl
    obtain ⟨ε, hεm, hεc⟩ := exists_between (max_lt had hdc)
    have hεa : a < ε := lt_of_le_of_lt (le_max_left _ _) hεm
    have hdε : d ≤ ε := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hεm)
    have hsε := hsa ε ⟨hεa, hεc⟩
    have hne : ∀ z ∈ Set.Icc d ε, P.eval z ≠ 0 := fun z hz => by
      have h := hno_root 0 (by omega) z
        ⟨hz.1, lt_of_le_of_lt hz.2 hεc⟩
      simpa using h
    rw [sign_eq_of_no_root_Icc hIVP P hdε hne, hsε]
  have hQ_sign_d : SignType.sign (Q.eval d) = (-1)^ν * τ := by
    obtain ⟨a, had, hsa⟩ := hQ_sl
    obtain ⟨ε, hεm, hεc⟩ := exists_between (max_lt had hdc)
    have hεa : a < ε := lt_of_le_of_lt (le_max_left _ _) hεm
    have hdε : d ≤ ε := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hεm)
    have hsε := hsa ε ⟨hεa, hεc⟩
    have hQ_no_root : ∀ z ∈ Set.Icc d ε, Q.eval z ≠ 0 := by
      intro z hz
      by_cases h1 : 1 < P.natDegree
      · have h := hno_root 1 h1 z ⟨hz.1, lt_of_le_of_lt hz.2 hεc⟩
        rwa [Function.iterate_one] at h
      · have hnd1 : P.natDegree = 1 := by omega
        have hndQ : Q.natDegree = 0 := by
          rw [hQ_def, natDegree_derivative_of_pos hpos, hnd1]
        obtain ⟨a', ha'⟩ := Polynomial.natDegree_eq_zero.mp hndQ
        have ha'_ne : a' ≠ 0 := fun h => hdP (ha' ▸ h ▸ by simp)
        rw [← ha']; simpa
    rw [sign_eq_of_no_root_Icc hIVP Q hdε hQ_no_root, hsε]
  -- τ ≠ 0 from Q(d) ≠ 0.
  have hτ_ne : τ ≠ 0 := by
    intro h
    have : SignType.sign (Q.eval d) = (-1)^ν * 0 := by rw [hQ_sign_d, h]
    rw [mul_zero] at this
    exact hQd_ne (sign_eq_zero_iff.mp this)
  have hderνQc_ne : ((⇑derivative)^[ν] Q).eval c ≠ 0 := fun h =>
    hτ_ne (by rw [hτ_def, h, sign_zero])
  -- Sign products at d and c.
  have hsign_d : SignType.sign (P.eval d * Q.eval d) = σP * ((-1)^ν * τ) := by
    rw [sign_mul, hP_sign_d, hQ_sign_d]
  have hsign_c : SignType.sign (P.eval c * ((⇑derivative)^[ν] Q).eval c) = σP * τ :=
    sign_mul _ _
  -- varAt identities.
  have hderP_cons : der P = P :: der Q := der_eq_cons hpos
  have hvar_c : varAt (der P) (.finite c) =
      (if P.eval c * ((⇑derivative)^[ν] Q).eval c < 0 then 1 else 0) +
        varAt (der Q) (.finite c) := by
    rw [hderP_cons]; exact varAt_cons_der_eq P Q hPc hQ_ne
  have hvar_d : varAt (der P) (.finite d) =
      (if P.eval d * Q.eval d < 0 then 1 else 0) + varAt (der Q) (.finite d) := by
    have hmult_d : Q.rootMultiplicity d = 0 :=
      Polynomial.rootMultiplicity_eq_zero hQd_ne
    rw [hderP_cons, varAt_cons_der_eq P Q hPd_ne hQ_ne (c := d), hmult_d,
      Function.iterate_zero_apply]
  -- LHS computation: varBetween(der P) - varBetween(der Q) = jd - jc.
  have hLHS_eq :
      varBetween (der P) (.finite d) (.finite c) -
        varBetween (der Q) (.finite d) (.finite c) =
      (if P.eval d * Q.eval d < 0 then (1 : ℤ) else 0) -
        (if P.eval c * ((⇑derivative)^[ν] Q).eval c < 0 then 1 else 0) := by
    unfold varBetween
    rw [hvar_c, hvar_d]
    push_cast
    ring
  -- The iterate (ν+1)-fold of derivative P equals derivative^[ν] Q.
  have hiter_eq :
      ((⇑derivative)^[ν + 1] P) = ((⇑derivative)^[ν] Q) := by
    rw [hQ_def, ← Function.iterate_succ_apply]
  -- RHS computation via virtualMultiplicity_diff_of_not_root.
  have hRHS := virtualMultiplicity_diff_of_not_root hIVP hP hdP hPc (c := c)
  rw [← hν_def, hiter_eq] at hRHS
  -- Combined sign equation feeding the jump formula.
  have hpcQνc_ne : P.eval c * ((⇑derivative)^[ν] Q).eval c ≠ 0 :=
    mul_ne_zero hPc hderνQc_ne
  have hsign_comb :
      SignType.sign (P.eval d * Q.eval d) =
        (-1)^ν * SignType.sign (P.eval c * ((⇑derivative)^[ν] Q).eval c) := by
    rw [hsign_d, hsign_c, mul_left_comm]
  rw [hLHS_eq, hRHS]
  exact jump_diff_formula hpcQνc_ne hsign_comb

/-! ## Main theorem -/

/-- **BPR Lemma 2.48.** Let `P ≠ 0` and `d < c`. If no `P^{(k)}`
    (`k < P.natDegree`) has a root in `[d, c)`, then the virtual multiplicity
    of `c` with respect to `P` equals `Var(Der P; d, c)`. -/
theorem lemma_2_48 (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) {d c : R} (hdc : d < c)
    (hno_root : ∀ k, k < P.natDegree → ∀ x ∈ Set.Ico d c,
      ((⇑derivative)^[k] P).eval x ≠ 0) :
    (virtualMultiplicity hIVP hP c : ℤ) =
      varBetween (der P) (.finite d) (.finite c) := by
  suffices H : ∀ (n : ℕ) (P : R[X]) (hP : P ≠ 0), P.natDegree = n →
      ∀ {d c : R}, d < c →
      (∀ k, k < P.natDegree → ∀ x ∈ Set.Ico d c,
        ((⇑derivative)^[k] P).eval x ≠ 0) →
      (virtualMultiplicity hIVP hP c : ℤ) =
        varBetween (der P) (.finite d) (.finite c) from
    H P.natDegree P hP rfl hdc hno_root
  intro n
  induction n with
  | zero =>
    intro P hP hn d c _hdc _hno_root
    -- P is a nonzero constant: der P = [P], all varAt are 0, no virtual roots.
    have hder : der P = [P] := by unfold der; rw [hn]; rfl
    have hvm : virtualMultiplicity hIVP hP c = 0 := by
      unfold virtualMultiplicity
      rw [List.count_eq_zero]
      intro hmem
      have hlen := length_virtualRoots hIVP hP
      rw [hn] at hlen
      rw [List.length_eq_zero_iff.mp hlen] at hmem
      exact List.not_mem_nil hmem
    have hvar_eq : ∀ x, varAt (der P) (.finite x) = 0 := fun x => by
      rw [hder, varAt_finite]
      simp only [List.map_cons, List.map_nil]
      by_cases hx : P.eval x = 0
      · rw [hx, Var_zero_cons]; rfl
      · rw [Var_of_forall_ne_zero (by simp [hx])]; rfl
    have hvar : varBetween (der P) (.finite d) (.finite c) = 0 := by
      unfold varBetween; simp [hvar_eq]
    rw [hvm, hvar]; rfl
  | succ n ih =>
    intro P hP hn d c hdc hno_root
    have hpos : 1 ≤ P.natDegree := by rw [hn]; omega
    have hdP : derivative P ≠ 0 := by
      intro h
      have := Polynomial.derivative_eq_zero.mp h
      rw [hn] at this; omega
    have hdP_deg : (derivative P).natDegree = n := by
      have h := Polynomial.natDegree_eq_of_degree_eq_some
        (Polynomial.degree_derivative (Nat.lt_of_lt_of_le Nat.zero_lt_one hpos).ne')
      rw [hn] at h; omega
    -- Derive the no-root hypothesis for P'.
    have hno_root_P' : ∀ k, k < (derivative P).natDegree → ∀ x ∈ Set.Ico d c,
        ((⇑derivative)^[k] (derivative P)).eval x ≠ 0 := by
      intro k hk x hx
      have hk' : k + 1 < P.natDegree := by rw [hdP_deg] at hk; rw [hn]; omega
      have h := hno_root (k + 1) hk' x hx
      rwa [Function.iterate_succ_apply] at h
    -- Apply IH to P'.
    have ih_P' :=
      ih (derivative P) hdP hdP_deg hdc hno_root_P'
    by_cases hPc : P.eval c = 0
    · -- Root case: Prop 2.46(1) + root-case key equation.
      have h46 := virtualMultiplicity_derivative_of_root hIVP hP hdP hPc
      have hkey :=
        varBetween_der_succ_of_root_at_c_add_one hIVP hpos hdc hPc hno_root
      -- Combine: v(P,c) = v(P',c) + 1 = varBetween(der P') + 1 = varBetween(der P).
      unfold virtualMultiplicity at ih_P'
      rw [hkey, ← ih_P']
      unfold virtualMultiplicity at h46 ⊢
      push_cast [← h46]
      ring
    · -- Non-root case: non-root key equation + trichotomy.
      have hkey :=
        varBetween_der_succ_of_not_root_at_c hIVP hP hdP hpos hdc hPc hno_root
      unfold virtualMultiplicity at ih_P' hkey ⊢
      linarith [hkey, ih_P']

end Azurite.BPR.Lemma_2_48

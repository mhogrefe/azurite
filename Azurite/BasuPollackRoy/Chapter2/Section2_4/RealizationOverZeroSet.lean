/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_25
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_56

/-!
# BPR Section 2.4 — Realization of a sign condition over a zero set

Let `Q` be a finite family of univariate polynomials over a real closed
field `R` (a linearly ordered field suffices) and `σ` a sign condition on
`Q` (Definition~2.25), i.e. `σ : ι → SignType`. For `P : R[X]` with zero
set `Z = Zer(P, R) = {x | P(x) = 0}`, the **realization of `σ` over `Z`**
is

`Reali(σ, Z) = {x ∈ R | P(x) = 0 ∧ ⋀_{i} sign((Q i)(x)) = σ i}`,

and its cardinality is denoted `c(σ, Z)`.

This is exactly the intersection of `Z` with the sign-condition
realization `SignCondition.realization` already defined in
`Definition_2_25`; we package it as `SignCondition.realizationOver`
together with a `Finset` form whose cardinality is `c(σ, Z)`.
-/

open scoped Polynomial

namespace Azurite.BPR

open Polynomial

namespace SignCondition

variable {ι : Type*} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Realization of a sign condition `σ` over `Z = Zer(P)`** (BPR §2.4).
For `P : R[X]` and a family `Q : ι → R[X]`, this is the set of roots of
`P` at which `Q` realizes `σ`:
`Reali(σ, Z) = {x | P(x) = 0 ∧ ⋀ᵢ sign((Q i)(x)) = σ i}`. It is the
intersection of `Zer(P)` with `σ.realization` (Definition~2.25). -/
def realizationOver (σ : SignCondition ι) (P : R[X]) (Q : ι → R[X]) : Set R :=
  {x | P.IsRoot x ∧ σ.IsRealizedBy (fun i => (Q i).eval x)}

omit [IsStrictOrderedRing R] in
theorem mem_realizationOver {σ : SignCondition ι} {P : R[X]} {Q : ι → R[X]} {x : R} :
    x ∈ σ.realizationOver P Q ↔
      P.eval x = 0 ∧ ∀ i, SignType.sign ((Q i).eval x) = σ i :=
  Iff.rfl

omit [IsStrictOrderedRing R] in
/-- `Reali(σ, Z)` is `Zer(P)` intersected with the sign-condition
realization `σ.realization`. -/
theorem realizationOver_eq_inter (σ : SignCondition ι) (P : R[X]) (Q : ι → R[X]) :
    σ.realizationOver P Q
      = {x | P.IsRoot x} ∩ σ.realization (fun i x => (Q i).eval x) :=
  rfl

open Classical in
/-- The realization of `σ` over `Z` as a `Finset` of roots of `P`. Its
cardinality is BPR's `c(σ, Z)`. -/
noncomputable def realizationOverFinset [Fintype ι] (σ : SignCondition ι)
    (P : R[X]) (Q : ι → R[X]) : Finset R :=
  P.roots.toFinset.filter (fun x => σ.IsRealizedBy (fun i => (Q i).eval x))

omit [IsStrictOrderedRing R] in
/-- For `P ≠ 0`, the `Finset` form picks out exactly the points of the
set realization `Reali(σ, Z)`. -/
theorem mem_realizationOverFinset [Fintype ι] {σ : SignCondition ι} {P : R[X]}
    {Q : ι → R[X]} (hP : P ≠ 0) {x : R} :
    x ∈ σ.realizationOverFinset P Q ↔ x ∈ σ.realizationOver P Q := by
  classical
  rw [realizationOverFinset, Finset.mem_filter, Multiset.mem_toFinset,
      Polynomial.mem_roots hP]
  rfl

end SignCondition

/-! ### Products `σ^α` and `𝒬^α`

For an exponent assignment `α : ι → ℕ` (BPR takes values in `{0, 1, 2}`),
we form the sign `σ^α = ∏ᵢ σ(i)^{α(i)}` and the polynomial
`𝒬^α = ∏ᵢ (Q i)^{α(i)}` (with the monoid convention `0^0 = 1`). On a
non-empty realization `Reali(σ, Z)` the sign of `𝒬^α` is constant and
equal to `σ^α`. -/

section Pow

variable {ι : Type*} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fintype ι]

/-- `σ^α = ∏ᵢ σ(i)^{α(i)}` for an exponent assignment `α : ι → ℕ`
(`0^0 = 1` by the monoid convention). -/
def SignCondition.pow (σ : SignCondition ι) (α : ι → ℕ) : SignType :=
  ∏ i, σ i ^ α i

/-- `𝒬^α = ∏ᵢ (Q i)^{α(i)}` for a polynomial family `Q : ι → R[X]` and an
exponent assignment `α : ι → ℕ`. -/
noncomputable def familyPow (Q : ι → R[X]) (α : ι → ℕ) : R[X] :=
  ∏ i, Q i ^ α i

omit [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] theorem familyPow_eval (Q : ι → R[X]) (α : ι → ℕ) (x : R) :
    (familyPow Q α).eval x = ∏ i, (Q i).eval x ^ α i := by
  simp [familyPow, Polynomial.eval_prod]

/-- **Sign determination.** On the realization `Reali(σ, Z)`, the sign of
`𝒬^α` equals `σ^α`. (In particular it is constant on `Reali(σ, Z)`.)
The proof uses that `sign` is multiplicative (`sign_mul`, `sign_pow`):
`sign((𝒬^α)(x)) = ∏ᵢ sign(Q_i(x))^{α(i)} = ∏ᵢ σ(i)^{α(i)} = σ^α`. -/
theorem sign_familyPow_eval_eq_signPow (σ : SignCondition ι) (P : R[X])
    (Q : ι → R[X]) (α : ι → ℕ) {x : R} (hx : x ∈ σ.realizationOver P Q) :
    SignType.sign ((familyPow Q α).eval x) = σ.pow α := by
  obtain ⟨-, hreal⟩ := hx
  have hsign_prod : ∀ f : ι → R,
      SignType.sign (∏ i, f i) = ∏ i, SignType.sign (f i) :=
    fun f => map_prod (⟨⟨SignType.sign, sign_one⟩, sign_mul⟩ : R →* SignType) f Finset.univ
  rw [familyPow_eval, hsign_prod, SignCondition.pow]
  exact Finset.prod_congr rfl (fun i _ => by rw [sign_pow, hreal i])

/-- The sign of `𝒬^α` is fixed across the realization `Reali(σ, Z)`. -/
theorem sign_familyPow_eval_eq_of_mem (σ : SignCondition ι) (P : R[X])
    (Q : ι → R[X]) (α : ι → ℕ) {x y : R}
    (hx : x ∈ σ.realizationOver P Q) (hy : y ∈ σ.realizationOver P Q) :
    SignType.sign ((familyPow Q α).eval x) = SignType.sign ((familyPow Q α).eval y) := by
  rw [sign_familyPow_eval_eq_signPow σ P Q α hx,
      sign_familyPow_eval_eq_signPow σ P Q α hy]

/-! ### Lists `𝒬^A` and `TaQ(𝒬^A, P)`

Numbering `𝒬 = {Q₁, …, Q_s}` (so `ι = Fin s`) and ordering
`{0,1,2}^𝒬` and `{0,1,-1}^𝒬` lexicographically (Definition~2.14,
`LexOrder`), a list `A = (α₁, …, α_m)` of exponent assignments (BPR
takes it lex-increasing) yields the list of polynomials `𝒬^A` and the
list of Tarski-queries `TaQ(𝒬^A, P)`, defined entrywise. The
definitions do not depend on the ordering of `A`; lex-sortedness is the
property used to index the matrix of signs downstream. -/

/-- `𝒬^A = (𝒬^{α})_{α ∈ A}`, the list of polynomials `familyPow Q α`
indexed by a list `A` of exponent assignments. -/
noncomputable def familyPowList (Q : ι → R[X]) (A : List (ι → ℕ)) : List R[X] :=
  A.map (familyPow Q)

/-- `TaQ(𝒬^A, P) = (TaQ(𝒬^{α}, P))_{α ∈ A}`, the list of Tarski-queries
of `P` against the `𝒬^{α}`. -/
noncomputable def tarskiQueryList (P : R[X]) (Q : ι → R[X]) (A : List (ι → ℕ)) :
    List ℤ :=
  A.map (fun α => tarskiQuery (familyPow Q α) P)

omit [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] theorem familyPowList_length (Q : ι → R[X]) (A : List (ι → ℕ)) :
    (familyPowList Q A).length = A.length := by
  simp [familyPowList]

omit [IsStrictOrderedRing R] in
@[simp] theorem tarskiQueryList_length (P : R[X]) (Q : ι → R[X]) (A : List (ι → ℕ)) :
    (tarskiQueryList P Q A).length = A.length := by
  simp [tarskiQueryList]

omit [IsStrictOrderedRing R] in
/-- `TaQ(𝒬^A, P)` is the entrywise Tarski-query of `P` against `𝒬^A`. -/
theorem tarskiQueryList_eq_map (P : R[X]) (Q : ι → R[X]) (A : List (ι → ℕ)) :
    tarskiQueryList P Q A = (familyPowList Q A).map (fun p => tarskiQuery p P) := by
  simp [tarskiQueryList, familyPowList, List.map_map, Function.comp_def]

end Pow

/-! ### Lists `Reali(Σ, Z)` and `c(Σ, Z)`

For a list `Σ = (σ₁, …, σₙ)` of sign conditions (BPR takes it
lex-increasing in `{0,1,-1}^𝒬`, Definition~2.14), the realizations over
`Z` and their cardinalities are assembled entrywise into
`Reali(Σ, Z) = (Reali(σ, Z))_{σ ∈ Σ}` and `c(Σ, Z) = (c(σ, Z))_{σ ∈ Σ}`.
As with `𝒬^A`, the definitions do not depend on the ordering of `Σ`. -/

section SignConditionList

variable {ι : Type*} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `Reali(Σ, Z) = (Reali(σ, Z))_{σ ∈ Σ}` for a list `Σ` of sign
conditions. -/
def realizationOverList (S : List (SignCondition ι)) (P : R[X]) (Q : ι → R[X]) :
    List (Set R) :=
  S.map (fun σ => σ.realizationOver P Q)

omit [IsStrictOrderedRing R] in
@[simp] theorem realizationOverList_length (S : List (SignCondition ι)) (P : R[X])
    (Q : ι → R[X]) : (realizationOverList S P Q).length = S.length := by
  simp [realizationOverList]

/-- `c(Σ, Z) = (c(σ, Z))_{σ ∈ Σ}`, the list of cardinalities of the
realizations. -/
noncomputable def realizationOverCardList [Fintype ι] (S : List (SignCondition ι))
    (P : R[X]) (Q : ι → R[X]) : List ℕ :=
  S.map (fun σ => (σ.realizationOverFinset P Q).card)

omit [IsStrictOrderedRing R] in
@[simp] theorem realizationOverCardList_length [Fintype ι]
    (S : List (SignCondition ι)) (P : R[X]) (Q : ι → R[X]) :
    (realizationOverCardList S P Q).length = S.length := by
  simp [realizationOverCardList]

end SignConditionList

end Azurite.BPR

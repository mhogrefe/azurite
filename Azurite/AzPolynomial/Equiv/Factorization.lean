/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Correctness of the complete factorization over `F_q`**
  (`Azurite.AzPolynomial.factorization`, GG Algorithm 14.13-style): for
  monic `f` and `q = card K`, the output pairs are
  `(monic irreducible, multiplicity ≠ 0)` with strictly increasing
  factors, and they multiply to `f` (`factorization_correct`); for
  arbitrary `f`, `canonicalFactorization_correct` adds the leading
  coefficient out front: `f = C(lc f) · ∏ uᵢ^eᵢ`.

  The proof stack, on top of the spec-level lemmas of
  `Azurite/GathenGerhard/Chapter14/Algorithm_14_13.lean` (the generalized
  crux and the leaf criterion) and the Algorithm 14.8 output contract:

  * SEARCH — a sweep candidate that happens to be a prime factor of `g`
    makes the splitting step succeed through the `gcd(a, g)` path
    (`equalDegreeSplittingStep_isSome_of_factor`); every monic degree-`d`
    polynomial appears in the sweep (`exists_sweepCandidate_toPoly`, via
    the noncomputable `ofPoly` transport into the capped exhaustive vector
    enumeration); hence `edsSearch` succeeds within its fuel
    (`edsSearch_isSome`), and everything it returns is a proper monic
    factor (`edsSearch_some_correct`).

  * EQUAL-DEGREE FACTORIZATION and THE OUTER LOOP — by induction on their
    fuels (`equalDegreeFactorizationLoop_correct`,
    `factorizationLoop_correct`), the outer invariants being: the
    remaining part is monic, divides `f`, all its prime factors have
    degree `≥ i`, and `h ≡ x^(qⁱ) mod f`.

  * CANONICALIZATION — sorting is a permutation (`List.mergeSort_perm`),
    and run-length encoding preserves products and members
    (`runLengths_prod_map`, `runLengths_mem`) while turning sortedness
    into strictly increasing firsts (`runLengths_chain'_lt`).

  No oddness of `q` is required: the `±1` power path of equal-degree
  splitting only affects how often the pseudorandom attempts succeed; the
  deterministic `gcd`-path backstop carries the proof.
-/
import Azurite.GathenGerhard.Chapter14.Algorithm_14_13
import Azurite.GathenGerhard.Chapter14.Algorithm_14_8
import Azurite.AzPolynomial.Factorization

namespace Azurite

/-! ### `runLengths` -/

section RunLengths

variable {A : Type _} [DecidableEq A]

/-- `runLengths` of a cons, with the recursive value exposed. -/
private theorem runLengths_cons (a : A) (rest : List A) :
    runLengths (a :: rest)
      = match runLengths rest with
        | [] => [(a, 1)]
        | (b, e) :: t => if a = b then (b, e + 1) :: t
                         else (a, 1) :: (b, e) :: t := rfl

/-- Run-length encoding never produces a zero count, and its elements come
from the list. -/
theorem runLengths_mem : ∀ {l : List A} {u : A} {e : ℕ},
    (u, e) ∈ runLengths l → u ∈ l ∧ e ≠ 0 := by
  intro l
  induction l with
  | nil => intro u e h; exact absurd h (by simp [runLengths])
  | cons a rest ih =>
    intro u e h
    rw [runLengths_cons] at h
    cases hr : runLengths rest with
    | nil =>
      rw [hr] at h
      dsimp only at h
      rw [List.mem_singleton] at h
      injection h with h1 h2
      exact ⟨h1 ▸ List.mem_cons_self, by omega⟩
    | cons be t =>
      obtain ⟨b, e'⟩ := be
      rw [hr] at h
      dsimp only at h
      by_cases hab : a = b
      · rw [ite_eq_left hab] at h
        rcases List.mem_cons.mp h with heq | hmem
        · injection heq with h1 h2
          have hb := (ih (hr ▸ List.mem_cons_self)).1
          exact ⟨List.mem_cons_of_mem a (h1 ▸ hb), by omega⟩
        · have := ih (hr ▸ List.mem_cons_of_mem (b, e') hmem)
          exact ⟨List.mem_cons_of_mem a this.1, this.2⟩
      · rw [ite_eq_right hab] at h
        rcases List.mem_cons.mp h with heq | hmem
        · injection heq with h1 h2
          exact ⟨h1 ▸ List.mem_cons_self, by omega⟩
        · have := ih (hr ▸ hmem)
          exact ⟨List.mem_cons_of_mem a this.1, this.2⟩

/-- `runLengths` of a nonempty list is nonempty. -/
private theorem runLengths_ne_nil {a : A} {rest : List A} :
    runLengths (a :: rest) ≠ [] := by
  rw [runLengths_cons]
  cases runLengths rest with
  | nil => simp
  | cons be t =>
    obtain ⟨b, e⟩ := be
    dsimp only
    by_cases hab : a = b
    · rw [ite_eq_left hab]; simp
    · rw [ite_eq_right hab]; simp

/-- Run-length encoding preserves products, through any map into a
commutative monoid: `∏ F(u)^e = ∏ F(elements)`. -/
theorem runLengths_prod_map {M : Type _} [CommMonoid M] (F : A → M) :
    ∀ l : List A,
      ((runLengths l).map (fun p => F p.1 ^ p.2)).prod = (l.map F).prod := by
  intro l
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [runLengths_cons]
    cases hr : runLengths rest with
    | nil =>
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons b t => exact absurd hr runLengths_ne_nil
      subst hrest
      simp
    | cons be t =>
      obtain ⟨b, e⟩ := be
      rw [hr] at ih
      dsimp only
      by_cases hab : a = b
      · rw [ite_eq_left hab]
        subst hab
        simp only [List.map_cons, List.prod_cons] at ih ⊢
        rw [pow_succ', mul_assoc, ih]
      · rw [ite_eq_right hab]
        simp only [List.map_cons, List.prod_cons, pow_one] at ih ⊢
        rw [ih]

/-- The head of a run-length encoding comes from the list. -/
private theorem runLengths_head_mem : ∀ {l : List A} {b : A} {e : ℕ}
    {t : List (A × ℕ)}, runLengths l = (b, e) :: t → b ∈ l := by
  intro l
  induction l with
  | nil => intro b e t h; exact absurd h (by simp [runLengths])
  | cons a rest ih =>
    intro b e t h
    rw [runLengths_cons] at h
    cases hr : runLengths rest with
    | nil =>
      rw [hr] at h
      dsimp only at h
      injection h with h1 h2
      injection h1 with h3 h4
      exact h3 ▸ List.mem_cons_self
    | cons be t' =>
      obtain ⟨c, e'⟩ := be
      rw [hr] at h
      dsimp only at h
      by_cases hac : a = c
      · rw [ite_eq_left hac] at h
        injection h with h1 h2
        injection h1 with h3 h4
        exact List.mem_cons_of_mem a (h3 ▸ ih hr)
      · rw [ite_eq_right hac] at h
        injection h with h1 h2
        injection h1 with h3 h4
        exact h3 ▸ List.mem_cons_self

/-- On a `≤`-sorted list, run-length encoding produces STRICTLY increasing
firsts (equal neighbors merge). -/
theorem runLengths_chain'_lt {A : Type _} [DecidableEq A] [PartialOrder A] :
    ∀ {l : List A}, l.Pairwise (· ≤ ·) →
      ((runLengths l).map Prod.fst).IsChain (· < ·) := by
  intro l
  induction l with
  | nil =>
    intro _
    simp only [runLengths, List.map_nil]
    exact List.IsChain.nil
  | cons a rest ih =>
    intro hp
    obtain ⟨ha, hrest⟩ := List.pairwise_cons.mp hp
    rw [runLengths_cons]
    cases hr : runLengths rest with
    | nil =>
      dsimp only
      simp only [List.map_cons, List.map_nil]
      exact List.IsChain.singleton _
    | cons be t =>
      obtain ⟨b, e⟩ := be
      have hb : b ∈ rest := runLengths_head_mem hr
      have hab : a ≤ b := ha b hb
      have hihc := ih hrest
      rw [hr] at hihc
      dsimp only
      by_cases haeb : a = b
      · rw [ite_eq_left haeb]
        exact hihc
      · rw [ite_eq_right haeb]
        rw [List.map_cons, List.map_cons]
        rw [List.map_cons] at hihc
        exact List.IsChain.cons_cons (lt_of_le_of_ne hab haeb) hihc

end RunLengths

namespace AzPolynomial

open Polynomial UniqueFactorizationMonoid

/- Prefer Mathlib's `NormalizedGCDMonoid` gcd (same as the sibling files). -/
attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

/-! ### The search succeeds -/

section Search

variable {K : Type _} [Field K] [DecidableEq K]

/-- A candidate representing a prime factor of `g` makes the splitting
step succeed through the `gcd(a, g)` path. -/
theorem equalDegreeSplittingStep_isSome_of_factor {q : AzNat} {d : ℕ}
    {g a : AzPolynomial K} (hg0 : AzPolynomial.toPoly g ≠ 0)
    (hfac : AzPolynomial.toPoly a ∈ primeFactors (AzPolynomial.toPoly g))
    (had : a.natDegree ≠ 0) :
    (AzPolynomial.equalDegreeSplittingStep q d g a).isSome := by
  obtain ⟨hirr, hnorm, hdvd⟩ := (GG.mem_primeFactors_iff'' hg0).mp hfac
  rw [AzPolynomial.equalDegreeSplittingStep, ite_eq_right had]
  simp only []
  have h1 : AzPolynomial.gcdMonic a g ≠ 1 := by
    rw [Ne, ← toPoly_inj, toPoly_one, AzPolynomial.toPoly_gcdMonic]
    have hgcd : GCDMonoid.gcd (AzPolynomial.toPoly a) (AzPolynomial.toPoly g)
        = AzPolynomial.toPoly a := by
      calc GCDMonoid.gcd (AzPolynomial.toPoly a) (AzPolynomial.toPoly g)
          = _root_.normalize
              (GCDMonoid.gcd (AzPolynomial.toPoly a) (AzPolynomial.toPoly g)) :=
            (normalize_gcd _ _).symm
        _ = _root_.normalize (AzPolynomial.toPoly a) :=
            normalize_eq_normalize (gcd_dvd_left _ _) (dvd_gcd dvd_rfl hdvd)
        _ = AzPolynomial.toPoly a := hnorm
    rw [hgcd]
    exact hirr.ne_one
  rw [ite_eq_left h1]
  rfl

variable [ExhaustiveGenerator K] [FiniteGenerator K]

omit [ExhaustiveGenerator K] [FiniteGenerator K] in
/-- `(1 : AzPolynomial K)` is constant. -/
private theorem natDegree_one_az : (1 : AzPolynomial K).natDegree = 0 := by
  rw [← AzPolynomial.natDegree_toPoly, toPoly_one, Polynomial.natDegree_one]

/-- Sweep candidates have degree at most `d`. -/
theorem natDegree_sweepCandidate_le (d j : ℕ) :
    (AzPolynomial.sweepCandidate K d j).natDegree ≤ d := by
  rw [AzPolynomial.sweepCandidate]
  cases hg : ExhaustiveGenerator.gen (T := List.Vector K d) j with
  | none =>
    show (1 : AzPolynomial K).natDegree ≤ d
    rw [natDegree_one_az]
    exact Nat.zero_le d
  | some vec =>
    show (AzPolynomial.monicOfVec vec).natDegree ≤ d
    rw [AzPolynomial.natDegree_monicOfVec]

/-- Every monic polynomial of degree `d` appears in the deterministic
sweep, at an index below the enumeration's cardinality (the noncomputable
`ofPoly` transports it into the capped exhaustive vector enumeration). -/
theorem exists_sweepCandidate_toPoly {d : ℕ} {u : Polynomial K}
    (hm : u.Monic) (hdeg : u.natDegree = d) :
    ∃ j < FiniteGenerator.card (T := List.Vector K d),
      AzPolynomial.toPoly (AzPolynomial.sweepCandidate K d j) = u := by
  -- the Az representative of `u`
  have htoPoly : AzPolynomial.toPoly (AzPolynomial.ofPoly u) = u := toPoly_ofPoly u
  set az := AzPolynomial.ofPoly u with haz
  have haz0 : az ≠ 0 := by
    rw [Ne, ← toPoly_inj, toPoly_zero, htoPoly]
    exact hm.ne_zero
  have hsize : az.coeffs.size = d + 1 := by
    have h1 : az.coeffs.size - 1 = d := by
      show az.natDegree = d
      rw [← AzPolynomial.natDegree_toPoly, htoPoly, hdeg]
    have h2 : az.coeffs.size ≠ 0 := by
      intro h
      exact haz0 (AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h))
    omega
  have hlist_ne : az.coeffs.toList ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [Array.length_toList, hsize] at this
    simp at this
  -- the last entry is the leading coefficient, `1`
  have hlast : az.coeffs.toList.getLast hlist_ne = 1 := by
    have hlead : az.leadingCoeff = 1 := by
      have h := leadingCoeff_toPoly az
      rw [htoPoly, hm.leadingCoeff] at h
      exact h.symm
    have hchain : some (az.coeffs.toList.getLast hlist_ne)
        = some az.leadingCoeff := by
      calc some (az.coeffs.toList.getLast hlist_ne)
          = az.coeffs.toList.getLast? :=
            (List.getLast?_eq_some_getLast hlist_ne).symm
        _ = az.coeffs.back? := Array.getLast?_toList az.coeffs
        _ = az.coeffs[az.coeffs.size - 1]? := Array.back?_eq_getElem?
        _ = some az.leadingCoeff := by
            rw [Array.getElem?_eq_getElem
              (show az.coeffs.size - 1 < az.coeffs.size by omega)]
            congr 1
            show az.coeffs[az.coeffs.size - 1]
              = (az.coeffs[az.natDegree]?).getD 0
            have hnd : az.natDegree = az.coeffs.size - 1 := rfl
            rw [hnd, Array.getElem?_eq_getElem
              (show az.coeffs.size - 1 < az.coeffs.size by omega)]
            rfl
    rw [Option.some.inj hchain, hlead]
  -- the low-coefficient vector
  have hlen : az.coeffs.toList.dropLast.length = d := by
    rw [List.length_dropLast, Array.length_toList, hsize]
    omega
  have hrepr : AzPolynomial.monicOfVec
      (⟨az.coeffs.toList.dropLast, hlen⟩ : List.Vector K d) = az := by
    apply AzPolynomial.ext
    show ((List.Vector.toList
      (⟨az.coeffs.toList.dropLast, hlen⟩ : List.Vector K d)) ++ [1]).toArray
        = az.coeffs
    have hv : List.Vector.toList
        (⟨az.coeffs.toList.dropLast, hlen⟩ : List.Vector K d)
        = az.coeffs.toList.dropLast := rfl
    rw [hv, ← hlast, List.dropLast_concat_getLast hlist_ne,
      Array.toArray_toList]
  -- its index in the enumeration
  obtain ⟨j, hj, -⟩ := ExhaustiveGenerator.occurs_exactly_once
    (T := List.Vector K d) ⟨az.coeffs.toList.dropLast, hlen⟩
  refine ⟨j, ?_, ?_⟩
  · by_contra hge
    rw [FiniteGenerator.gen_none j (by omega)] at hj
    exact Option.some_ne_none _ hj.symm
  · rw [AzPolynomial.sweepCandidate, hj]
    show AzPolynomial.toPoly (AzPolynomial.monicOfVec _) = u
    rw [hrepr, htoPoly]

variable [ExhaustiveGenerator {t : K // t ≠ 0}]
  [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})]

/-- Everything the search returns is a proper monic factor (from the
Algorithm 14.8 output contract; both candidate families have degree
`< deg g`). -/
theorem edsSearch_some_correct {q : AzNat} {d : ℕ} {g : AzPolynomial K}
    {seed : UInt64} (hm : (AzPolynomial.toPoly g).Monic)
    (hdg : d < g.natDegree) :
    ∀ (fuel i : ℕ) {h : AzPolynomial K},
      AzPolynomial.edsSearch q d g seed fuel i = some h →
      (AzPolynomial.toPoly h).Monic ∧
      AzPolynomial.toPoly h ∣ AzPolynomial.toPoly g ∧
      AzPolynomial.toPoly h ≠ 1 ∧
      AzPolynomial.toPoly h ≠ AzPolynomial.toPoly g := by
  intro fuel
  induction fuel with
  | zero => intro i h hsome; exact absurd hsome (by simp [AzPolynomial.edsSearch])
  | succ fuel ih =>
    intro i h hsome
    rw [AzPolynomial.edsSearch] at hsome
    cases hstep : AzPolynomial.equalDegreeSplittingStep q d g
        (if i < 64 then AzPolynomial.hybridPolyCandidate K seed g.natDegree i
         else AzPolynomial.sweepCandidate K d (i - 64)) with
    | some h' =>
      simp only [hstep] at hsome
      obtain rfl : h' = h := Option.some.inj hsome
      refine GG.equalDegreeSplittingStep_correct hm ?_ hstep
      by_cases hi : i < 64
      · rw [ite_eq_left hi]
        exact AzPolynomial.natDegree_hybridPolyCandidate_lt K seed
          (by omega) i
      · rw [ite_eq_right hi]
        have := natDegree_sweepCandidate_le (K := K) d (i - 64)
        omega
    | none =>
      simp only [hstep] at hsome
      exact ih (i + 1) hsome

/-- The fueled search succeeds if some candidate index within reach
succeeds. -/
theorem edsSearch_isSome_of {q : AzNat} {d : ℕ} {g : AzPolynomial K}
    {seed : UInt64} {j : ℕ}
    (hj : (AzPolynomial.equalDegreeSplittingStep q d g
      (if j < 64 then AzPolynomial.hybridPolyCandidate K seed g.natDegree j
       else AzPolynomial.sweepCandidate K d (j - 64))).isSome) :
    ∀ (fuel i : ℕ), i ≤ j → j < i + fuel →
      (AzPolynomial.edsSearch q d g seed fuel i).isSome := by
  intro fuel
  induction fuel with
  | zero => intro i h1 h2; omega
  | succ fuel ih =>
    intro i hij hji
    rw [AzPolynomial.edsSearch]
    cases hstep : AzPolynomial.equalDegreeSplittingStep q d g
        (if i < 64 then AzPolynomial.hybridPolyCandidate K seed g.natDegree i
         else AzPolynomial.sweepCandidate K d (i - 64)) with
    | some h' => rfl
    | none =>
      have hne : i ≠ j := by
        intro heq
        rw [← heq, hstep] at hj
        simp at hj
      exact ih (i + 1) (by omega) (by omega)

/-- **The search succeeds**: for monic `g ≠ 1` whose prime factors all
have degree `d`, with `d ≠ 0` and `d < deg g`, the search (with its
standard fuel) finds a splitting — any prime factor of `g` is a sweep
candidate that splits it through the `gcd` path. -/
theorem edsSearch_isSome {q : AzNat} {d : ℕ} {g : AzPolynomial K}
    {seed : UInt64} (hm : (AzPolynomial.toPoly g).Monic)
    (h1 : AzPolynomial.toPoly g ≠ 1) (hd0 : d ≠ 0)
    (hall : ∀ p ∈ primeFactors (AzPolynomial.toPoly g), p.natDegree = d) :
    (AzPolynomial.edsSearch q d g seed (AzPolynomial.edsSearchFuel K d)
      0).isSome := by
  -- a prime factor of `g`
  obtain ⟨u, hu⟩ := exists_mem_normalizedFactors hm.ne_zero
    (fun hunit => h1 (hm.isUnit_iff.mp hunit))
  have hupf : u ∈ primeFactors (AzPolynomial.toPoly g) := mem_primeFactors.mpr hu
  have hum : u.Monic := GG.monic_of_mem_primeFactors hupf
  have hud : u.natDegree = d := hall u hupf
  -- it appears in the sweep
  obtain ⟨j, hjcard, hjeq⟩ := exists_sweepCandidate_toPoly hum hud
  -- the step succeeds on it
  have hstep : (AzPolynomial.equalDegreeSplittingStep q d g
      (AzPolynomial.sweepCandidate K d j)).isSome := by
    refine equalDegreeSplittingStep_isSome_of_factor hm.ne_zero ?_ ?_
    · rw [hjeq]
      exact hupf
    · rw [← AzPolynomial.natDegree_toPoly, hjeq, hud]
      exact hd0
  -- hence the search succeeds at index `64 + j`
  have hstep' : (AzPolynomial.equalDegreeSplittingStep q d g
      (if 64 + j < 64 then
        AzPolynomial.hybridPolyCandidate K seed g.natDegree (64 + j)
       else AzPolynomial.sweepCandidate K d (64 + j - 64))).isSome := by
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
    exact hstep
  exact edsSearch_isSome_of hstep' _ 0 (by omega)
    (by rw [AzPolynomial.edsSearchFuel]; omega)

/-! ### Equal-degree factorization is correct -/

/-- Correctness of the equal-degree factorization loop, by induction on
the fuel: for monic `g ≠ 1` whose prime factors all have degree `d ≠ 0`,
with fuel at least `deg g − d`, the outputs are monic irreducible and
multiply to `g`. -/
theorem equalDegreeFactorizationLoop_correct {q : AzNat} {d : ℕ}
    {seed : UInt64} (hd0 : d ≠ 0) :
    ∀ (fuel : ℕ) (g : AzPolynomial K),
      (AzPolynomial.toPoly g).Monic → AzPolynomial.toPoly g ≠ 1 →
      (∀ p ∈ primeFactors (AzPolynomial.toPoly g), p.natDegree = d) →
      g.natDegree ≤ fuel + d →
      ((AzPolynomial.equalDegreeFactorizationLoop q d seed fuel g).map
        AzPolynomial.toPoly).prod = AzPolynomial.toPoly g ∧
      ∀ u ∈ AzPolynomial.equalDegreeFactorizationLoop q d seed fuel g,
        (AzPolynomial.toPoly u).Monic ∧ Irreducible (AzPolynomial.toPoly u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro g hm h1 hall hfuel
    -- the fuel-0 output is `[g]`, and `g` is forced to be a leaf
    have hge := GG.natDegree_ge_of_factors_natDegree_eq hm h1 hall
    rw [AzPolynomial.natDegree_toPoly] at hge
    have hdeg : (AzPolynomial.toPoly g).natDegree = d := by
      rw [AzPolynomial.natDegree_toPoly]
      omega
    have hirr := GG.irreducible_of_natDegree_eq_of_factors hm h1 hall hdeg
    constructor
    · show ([g].map AzPolynomial.toPoly).prod = AzPolynomial.toPoly g
      simp
    · intro u hu
      rw [show AzPolynomial.equalDegreeFactorizationLoop q d seed 0 g = [g]
        from rfl, List.mem_singleton] at hu
      rw [hu]
      exact ⟨hm, hirr⟩
  | succ fuel ih =>
    intro g hm h1 hall hfuel
    rw [AzPolynomial.equalDegreeFactorizationLoop]
    by_cases hle : g.natDegree ≤ d
    · -- leaf
      rw [ite_eq_left hle]
      have hge := GG.natDegree_ge_of_factors_natDegree_eq hm h1 hall
      rw [AzPolynomial.natDegree_toPoly] at hge
      have hdeg : (AzPolynomial.toPoly g).natDegree = d := by
        rw [AzPolynomial.natDegree_toPoly]
        omega
      have hirr := GG.irreducible_of_natDegree_eq_of_factors hm h1 hall hdeg
      refine ⟨by simp, ?_⟩
      intro u hu
      rw [List.mem_singleton] at hu
      rw [hu]
      exact ⟨hm, hirr⟩
    · rw [ite_eq_right hle]
      have hdg : d < g.natDegree := by omega
      -- the search succeeds, and its output is a proper factor
      have hsome := edsSearch_isSome (q := q) (seed := seed) hm h1 hd0 hall
      obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hsome
      rw [hh]
      obtain ⟨hmon, hdvd, hne1, hneg⟩ := edsSearch_some_correct hm hdg _ _ hh
      -- the cofactor
      have hg0 : AzPolynomial.toPoly g ≠ 0 := hm.ne_zero
      have hh0 : AzPolynomial.toPoly h ≠ 0 := hmon.ne_zero
      have hrec : AzPolynomial.toPoly g = AzPolynomial.toPoly h
          * (AzPolynomial.toPoly g /ₘ AzPolynomial.toPoly h) := by
        have := Polynomial.modByMonic_add_div (AzPolynomial.toPoly g)
          (AzPolynomial.toPoly h)
        rw [(Polynomial.modByMonic_eq_zero_iff_dvd hmon).mpr hdvd, zero_add]
          at this
        exact this.symm
      have hdivPoly : AzPolynomial.toPoly (AzPolynomial.divByMonic g h)
          = AzPolynomial.toPoly g /ₘ AzPolynomial.toPoly h :=
        AzPolynomial.toPoly_divByMonic hmon hh0 g
      have hcm : (AzPolynomial.toPoly g /ₘ AzPolynomial.toPoly h).Monic :=
        hmon.of_mul_monic_left (hrec ▸ hm)
      have hc0 : AzPolynomial.toPoly g /ₘ AzPolynomial.toPoly h ≠ 0 :=
        hcm.ne_zero
      have hc1 : AzPolynomial.toPoly g /ₘ AzPolynomial.toPoly h ≠ 1 := by
        intro hone
        rw [hone, mul_one] at hrec
        exact hneg hrec.symm
      -- factor sets restrict
      have hsub : ∀ w : Polynomial K, w ≠ 0 →
          w ∣ AzPolynomial.toPoly g →
          ∀ p ∈ primeFactors w, p.natDegree = d := by
        intro w hw0 hwdvd p hp
        obtain ⟨hirr, hnorm, hpdvd⟩ := (GG.mem_primeFactors_iff'' hw0).mp hp
        exact hall p ((GG.mem_primeFactors_iff'' hg0).mpr
          ⟨hirr, hnorm, hpdvd.trans hwdvd⟩)
      have hall_h := hsub _ hh0 hdvd
      have hcdvd_g : (AzPolynomial.toPoly g /ₘ AzPolynomial.toPoly h)
          ∣ AzPolynomial.toPoly g :=
        ⟨AzPolynomial.toPoly h, by rw [mul_comm]; exact hrec⟩
      have hall_c := hsub _ hc0 hcdvd_g
      -- degrees split, both parts nontrivial
      have hdegsum : (AzPolynomial.toPoly h).natDegree
          + (AzPolynomial.toPoly g /ₘ AzPolynomial.toPoly h).natDegree
          = (AzPolynomial.toPoly g).natDegree := by
        conv_rhs => rw [hrec]
        rw [Polynomial.natDegree_mul hh0 hc0]
      have hgeh := GG.natDegree_ge_of_factors_natDegree_eq hmon hne1 hall_h
      have hgec := GG.natDegree_ge_of_factors_natDegree_eq hcm hc1 hall_c
      have hbrg : (AzPolynomial.toPoly g).natDegree = g.natDegree :=
        AzPolynomial.natDegree_toPoly g
      have hbrh : (AzPolynomial.toPoly h).natDegree = h.natDegree :=
        AzPolynomial.natDegree_toPoly h
      have hbrc : (AzPolynomial.toPoly g /ₘ AzPolynomial.toPoly h).natDegree
          = (AzPolynomial.divByMonic g h).natDegree := by
        rw [← hdivPoly, AzPolynomial.natDegree_toPoly]
      -- recurse
      have hih_h := ih h hmon hne1 hall_h (by omega)
      have hih_c := ih (AzPolynomial.divByMonic g h)
        (by rw [← hdivPoly] at hcm; exact hcm)
        (by rw [← hdivPoly] at hc1; exact hc1)
        (by rw [← hdivPoly] at hall_c; exact hall_c)
        (by omega)
      rw [← hdivPoly] at hrec
      constructor
      · rw [List.map_append, List.prod_append, hih_h.1, hih_c.1]
        exact hrec.symm
      · intro u hu
        rcases List.mem_append.mp hu with hcase | hcase
        · exact hih_h.2 u hcase
        · exact hih_c.2 u hcase

/-- **Equal-degree factorization is correct**: for monic `g ≠ 1` whose
prime factors all have degree `d ≠ 0`, the outputs are monic irreducible
and multiply to `g`. -/
theorem equalDegreeFactorization_correct {q : AzNat} {d : ℕ}
    {seed : UInt64} {g : AzPolynomial K} (hd0 : d ≠ 0)
    (hm : (AzPolynomial.toPoly g).Monic) (h1 : AzPolynomial.toPoly g ≠ 1)
    (hall : ∀ p ∈ primeFactors (AzPolynomial.toPoly g), p.natDegree = d) :
    ((AzPolynomial.equalDegreeFactorization q d g seed).map
      AzPolynomial.toPoly).prod = AzPolynomial.toPoly g ∧
    ∀ u ∈ AzPolynomial.equalDegreeFactorization q d g seed,
      (AzPolynomial.toPoly u).Monic ∧ Irreducible (AzPolynomial.toPoly u) :=
  equalDegreeFactorizationLoop_correct hd0 g.natDegree g hm h1 hall
    (Nat.le_add_right _ _)

/-! ### The outer loop is correct -/

/-- Correctness of the outer loop, by induction on the fuel.  Invariants:
the remaining part `v` is monic and divides `f`, all its prime factors
have degree `≥ i ≥ 1`, and `h ≡ x^(qⁱ) mod f`.  Conclusion: the outputs
are monic irreducible and multiply to `v`. -/
theorem factorizationLoop_correct [Fintype K] {q : AzNat} {seed : UInt64}
    (hq : q.toNat = Fintype.card K) {f : AzPolynomial K}
    (hmf : (AzPolynomial.toPoly f).Monic) :
    ∀ (fuel i : ℕ) (h v : AzPolynomial K),
      (AzPolynomial.toPoly v).Monic →
      AzPolynomial.toPoly v ∣ AzPolynomial.toPoly f →
      (∀ p ∈ primeFactors (AzPolynomial.toPoly v), i ≤ p.natDegree) →
      AzPolynomial.toPoly f
        ∣ AzPolynomial.toPoly h - Polynomial.X ^ Fintype.card K ^ i →
      i ≠ 0 →
      GG.ddLength (AzPolynomial.toPoly v)
        + (AzPolynomial.toPoly v).natDegree ≤ i + fuel →
      ((AzPolynomial.factorizationLoop q f seed fuel i h v).map
        AzPolynomial.toPoly).prod = AzPolynomial.toPoly v ∧
      ∀ u ∈ AzPolynomial.factorizationLoop q f seed fuel i h v,
        (AzPolynomial.toPoly u).Monic ∧ Irreducible (AzPolynomial.toPoly u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i h v hvm hvf hall hcong hi hfuel
    -- the invariants force `v = 1` at fuel 0
    have hv1 : AzPolynomial.toPoly v = 1 := by
      by_contra hne
      obtain ⟨p, hp⟩ := exists_mem_normalizedFactors hvm.ne_zero
        (fun hu => hne (hvm.isUnit_iff.mp hu))
      have hppf : p ∈ primeFactors (AzPolynomial.toPoly v) :=
        mem_primeFactors.mpr hp
      have hdd : i ≤ GG.ddLength (AzPolynomial.toPoly v) :=
        le_trans (hall p hppf) (Finset.le_sup (f := Polynomial.natDegree) hppf)
      have hdeg := GG.one_le_natDegree_of_monic_ne_one hvm hne
      omega
    exact ⟨by rw [hv1]; rfl, fun u hu => absurd hu (by simp [AzPolynomial.factorizationLoop])⟩
  | succ fuel ih =>
    intro i h v hvm hvf hall hcong hi hfuel
    have hv0 : AzPolynomial.toPoly v ≠ 0 := hvm.ne_zero
    rw [AzPolynomial.factorizationLoop]
    by_cases hv1 : v = 1
    · rw [ite_eq_left hv1]
      refine ⟨?_, by simp⟩
      rw [hv1, toPoly_one]
      rfl
    · rw [ite_eq_right hv1]
      simp only []
      have hv1' : AzPolynomial.toPoly v ≠ 1 := by
        rw [Ne, ← toPoly_one (R := K), toPoly_inj]
        exact hv1
      -- identify the extracted slice
      have hu_eq : AzPolynomial.toPoly (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)
          = ((primeFactors (AzPolynomial.toPoly v)).filter
              (fun p => p.natDegree = i)).prod id := by
        rw [AzPolynomial.toPoly_gcdMonic, AzPolynomial.toPoly_sub,
          AzPolynomial.toPoly_X]
        have hdvdsub : AzPolynomial.toPoly v
            ∣ (AzPolynomial.toPoly h - Polynomial.X)
              - (Polynomial.X ^ Fintype.card K ^ i - Polynomial.X) := by
          rw [sub_sub_sub_cancel_right]
          exact hvf.trans hcong
        rw [GG.gcd_congr_left_of_dvd_sub hdvdsub]
        exact GG.gcd_X_pow_card_pow_sub_X_eq_prod_filter hvm hi hall
      by_cases hu1 : AzPolynomial.gcdMonic (h - AzPolynomial.X) v = 1
      · -- no degree-`i` factors: advance `i`
        rw [ite_eq_left hu1]
        have hall' : ∀ p ∈ primeFactors (AzPolynomial.toPoly v),
            i + 1 ≤ p.natDegree := by
          intro p hp
          rcases Nat.lt_or_ge i p.natDegree with hlt | hge
          · omega
          · exfalso
            have hpi : p.natDegree = i := le_antisymm hge (hall p hp)
            have hpfil : p ∈ (primeFactors (AzPolynomial.toPoly v)).filter
                (fun p => p.natDegree = i) := Finset.mem_filter.mpr ⟨hp, hpi⟩
            have hpdvd : p ∣ ((primeFactors (AzPolynomial.toPoly v)).filter
                (fun p => p.natDegree = i)).prod id :=
              Finset.dvd_prod_of_mem id hpfil
            rw [← hu_eq, hu1, toPoly_one] at hpdvd
            exact (GG.irreducible_of_mem_primeFactors hp).not_isUnit
              (isUnit_of_dvd_one hpdvd)
        have hcong' : AzPolynomial.toPoly f
            ∣ AzPolynomial.toPoly (AzPolynomial.powModByMonic h q f)
              - Polynomial.X ^ Fintype.card K ^ (i + 1) := by
          rw [GG.toPoly_powModByMonic hmf, hq]
          exact GG.dvd_powModByMonic_sub_pow hcong
        exact ih (i + 1) _ v hvm hvf hall' hcong' (by omega) (by omega)
      · -- extract one copy of each degree-`i` factor
        rw [ite_eq_right hu1]
        have hu1' : AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v) ≠ 1 := by
          rw [Ne, ← toPoly_one (R := K), toPoly_inj]
          exact hu1
        have hum : (AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)).Monic := by
          rw [hu_eq]
          exact GG.monic_prod_subset_primeFactors (Finset.filter_subset _ _)
        have hu0 : AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v) ≠ 0 := hum.ne_zero
        have hall_u : ∀ p ∈ primeFactors (AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)),
            p.natDegree = i := by
          intro p hp
          rw [hu_eq] at hp
          have := (GG.mem_primeFactors_prod_subset hv0
            (Finset.filter_subset _ _)).mp hp
          exact (Finset.mem_filter.mp this).2
        have hudvd : AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)
            ∣ AzPolynomial.toPoly v := by
          rw [hu_eq]
          exact GG.prod_subset_primeFactors_dvd (Finset.filter_subset _ _)
        -- the cofactor
        have hrec : AzPolynomial.toPoly v
            = AzPolynomial.toPoly (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)
              * (AzPolynomial.toPoly v /ₘ AzPolynomial.toPoly
                  (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)) := by
          have := Polynomial.modByMonic_add_div (AzPolynomial.toPoly v)
            (AzPolynomial.toPoly (AzPolynomial.gcdMonic (h - AzPolynomial.X) v))
          rw [(Polynomial.modByMonic_eq_zero_iff_dvd hum).mpr hudvd, zero_add]
            at this
          exact this.symm
        have hdivPoly : AzPolynomial.toPoly
            (AzPolynomial.divByMonic v (AzPolynomial.gcdMonic (h - AzPolynomial.X) v))
            = AzPolynomial.toPoly v /ₘ AzPolynomial.toPoly
                (AzPolynomial.gcdMonic (h - AzPolynomial.X) v) :=
          AzPolynomial.toPoly_divByMonic hum hu0 v
        have hcm : (AzPolynomial.toPoly v /ₘ AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)).Monic :=
          hum.of_mul_monic_left (hrec ▸ hvm)
        have hc0 : AzPolynomial.toPoly v /ₘ AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v) ≠ 0 := hcm.ne_zero
        have hcdvd : (AzPolynomial.toPoly v /ₘ AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v))
            ∣ AzPolynomial.toPoly v :=
          ⟨AzPolynomial.toPoly (AzPolynomial.gcdMonic (h - AzPolynomial.X) v),
            by rw [mul_comm]; exact hrec⟩
        -- the cofactor's factor set restricts
        have hpf_sub : primeFactors (AzPolynomial.toPoly v /ₘ AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v))
            ⊆ primeFactors (AzPolynomial.toPoly v) := by
          intro p hp
          obtain ⟨hirr, hnorm, hpdvd⟩ := (GG.mem_primeFactors_iff'' hc0).mp hp
          exact (GG.mem_primeFactors_iff'' hv0).mpr
            ⟨hirr, hnorm, hpdvd.trans hcdvd⟩
        have hall_c : ∀ p ∈ primeFactors (AzPolynomial.toPoly v /ₘ
            AzPolynomial.toPoly (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)),
            i ≤ p.natDegree := fun p hp => hall p (hpf_sub hp)
        -- degrees: the slice is nontrivial, so the cofactor strictly drops
        have hudeg : 1 ≤ (AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)).natDegree :=
          GG.one_le_natDegree_of_monic_ne_one hum hu1'
        have hdegsum : (AzPolynomial.toPoly
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)).natDegree
            + (AzPolynomial.toPoly v /ₘ AzPolynomial.toPoly
                (AzPolynomial.gcdMonic (h - AzPolynomial.X) v)).natDegree
            = (AzPolynomial.toPoly v).natDegree := by
          conv_rhs => rw [hrec]
          rw [Polynomial.natDegree_mul hu0 hc0]
        have hdd_mono : GG.ddLength (AzPolynomial.toPoly v /ₘ
            AzPolynomial.toPoly (AzPolynomial.gcdMonic (h - AzPolynomial.X) v))
            ≤ GG.ddLength (AzPolynomial.toPoly v) :=
          Finset.sup_mono hpf_sub
        -- the equal-degree stage on the slice
        have hedf := equalDegreeFactorization_correct (q := q) (seed := seed)
          hi hum hu1' hall_u
        -- recurse on the cofactor
        have hih := ih i h (AzPolynomial.divByMonic v
            (AzPolynomial.gcdMonic (h - AzPolynomial.X) v))
          (by rw [hdivPoly]; exact hcm)
          (by rw [hdivPoly]; exact hcdvd.trans hvf)
          (by rw [hdivPoly]; exact hall_c)
          hcong hi
          (by rw [hdivPoly]; omega)
        constructor
        · rw [List.map_append, List.prod_append, hedf.1, hih.1, hdivPoly]
          exact hrec.symm
        · intro u hu
          rcases List.mem_append.mp hu with hcase | hcase
          · exact hedf.2 u hcase
          · exact hih.2 u hcase

/-! ### The canonical pair output -/

/-- **Correctness of the complete factorization** (GG Algorithm
14.13-style): over a finite coefficient field with `q` elements, for
monic `f` the output of `factorization` is the canonical factorization —
`(monic irreducible, multiplicity ≠ 0)` pairs with strictly increasing
factors, multiplying to `f`. -/
theorem factorization_correct [Fintype K] [LinearOrder K] {q : AzNat}
    {seed : UInt64} (hq : q.toNat = Fintype.card K) {f : AzPolynomial K}
    (hm : (AzPolynomial.toPoly f).Monic) :
    ((factorization q f seed).map
      (fun p => AzPolynomial.toPoly p.1 ^ p.2)).prod = AzPolynomial.toPoly f ∧
    (∀ p ∈ factorization q f seed,
      (AzPolynomial.toPoly p.1).Monic ∧ Irreducible (AzPolynomial.toPoly p.1)
        ∧ p.2 ≠ 0) ∧
    ((factorization q f seed).map Prod.fst).IsChain (· < ·) := by
  have hflat := factorizationLoop_correct (seed := seed) hq hm
    (2 * f.natDegree + 1) 1
    (powModByMonic X q f) f hm dvd_rfl
    (fun p hp => (GG.irreducible_of_mem_primeFactors hp).natDegree_pos)
    (by
      rw [GG.toPoly_powModByMonic hm, AzPolynomial.toPoly_X, hq]
      refine GG.dvd_powModByMonic_sub_pow ?_
      rw [pow_zero, pow_one, sub_self]
      exact dvd_zero _)
    one_ne_zero
    (by
      have hdd := GG.ddLength_le_natDegree hm.ne_zero
      have hbr := AzPolynomial.natDegree_toPoly f
      omega)
  set flat := factorizationLoop q f seed (2 * f.natDegree + 1) 1
    (powModByMonic X q f) f with hflatdef
  have hperm : (flat.mergeSort (· ≤ ·)).Perm flat := List.mergeSort_perm _ _
  have hsorted : (flat.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) :=
    (List.sortedLE_mergeSort (l := flat)).pairwise
  refine ⟨?_, ?_, ?_⟩
  · rw [factorization, runLengths_prod_map]
    calc ((flat.mergeSort (· ≤ ·)).map AzPolynomial.toPoly).prod
        = (flat.map AzPolynomial.toPoly).prod :=
          (hperm.map AzPolynomial.toPoly).prod_eq
      _ = AzPolynomial.toPoly f := hflat.1
  · rintro ⟨u, e⟩ hp
    obtain ⟨humem, he⟩ := runLengths_mem hp
    have := hflat.2 u (hperm.mem_iff.mp humem)
    exact ⟨this.1, this.2, he⟩
  · exact runLengths_chain'_lt hsorted

/-- **Correctness of the canonical factorization of an ARBITRARY `f`**:
`f = C(lc f) · ∏ uᵢ^eᵢ` with the pairs canonical — the associate-class
representatives are the monic polynomials, the one remaining unit is the
leading coefficient (and `0` yields `(0, [])`). -/
theorem canonicalFactorization_correct [Fintype K] [LinearOrder K]
    {q : AzNat} {seed : UInt64} (hq : q.toNat = Fintype.card K)
    (f : AzPolynomial K) :
    AzPolynomial.toPoly f
      = Polynomial.C ((canonicalFactorization q f seed).1)
        * (((canonicalFactorization q f seed).2).map
            (fun p => AzPolynomial.toPoly p.1 ^ p.2)).prod ∧
    (∀ p ∈ (canonicalFactorization q f seed).2,
      (AzPolynomial.toPoly p.1).Monic ∧ Irreducible (AzPolynomial.toPoly p.1)
        ∧ p.2 ≠ 0) ∧
    (((canonicalFactorization q f seed).2).map Prod.fst).IsChain (· < ·) := by
  rw [canonicalFactorization]
  by_cases hf0 : f = 0
  · rw [ite_eq_left hf0, hf0]
    refine ⟨?_, by simp, by simp⟩
    rw [toPoly_zero]
    simp
  · rw [ite_eq_right hf0]
    have hf0' : AzPolynomial.toPoly f ≠ 0 := by
      rw [Ne, ← toPoly_zero (R := K), toPoly_inj]
      exact hf0
    have hmono : AzPolynomial.toPoly (monicize f)
        = _root_.normalize (AzPolynomial.toPoly f) := toPoly_monicize f hf0
    have hmonic : (AzPolynomial.toPoly (monicize f)).Monic := by
      rw [hmono]
      exact Polynomial.monic_normalize hf0'
    have hfact := factorization_correct (seed := seed) hq hmonic
    refine ⟨?_, hfact.2.1, hfact.2.2⟩
    rw [hfact.1, hmono]
    -- `f = C(lc f) · normalize f`
    have hlc : (AzPolynomial.leadingCoeff f)
        = (AzPolynomial.toPoly f).leadingCoeff :=
      (leadingCoeff_toPoly f).symm
    have hlc0 : (AzPolynomial.toPoly f).leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hf0'
    rw [hlc, normalize_apply, Polynomial.coe_normUnit,
      ← mul_assoc, mul_comm (Polynomial.C (AzPolynomial.toPoly f).leadingCoeff),
      mul_assoc, ← Polynomial.C_mul]
    have hone : (AzPolynomial.toPoly f).leadingCoeff
        * ↑(normUnit (AzPolynomial.toPoly f).leadingCoeff) = 1 := by
      rw [← normalize_apply]
      exact normalize_eq_one.mpr (isUnit_iff_ne_zero.mpr hlc0)
    rw [hone, Polynomial.C_1, mul_one]

end Search

end AzPolynomial

end Azurite

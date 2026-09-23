/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMatrixMvListProd

/-!
# BPR §8.1: Proposition 8.11 (Substitution)

Let `P(Y, X) ∈ ℤ[Y, X]` with `Y = (Y_1, …, Y_ℓ)`, `X = (X_1, …, X_k)`, and let
`Q_i(Y, Z) ∈ ℤ[Y, Z]` for `i = 1, …, k`, with `Z = (Z_1, …, Z_m)`. Define
`R(Y, Z) := P(Y, Q_1(Y, Z), …, Q_k(Y, Z))`. With

* `d_Y`, `d_X`: degrees of `P` w.r.t. `Y` and `X`,
* `D_Y`, `D_Z`: degrees of every `Q_i` w.r.t. `Y` and `Z`,
* `τ_1`, `τ_2`: bounds on the bitsizes of the coefficients of `P` and the `Q_i`,

we have:

* `Y`-degree of `R` ≤ `d_X · D_Y + d_Y`;
* `Z`-degree of `R` ≤ `d_X · D_Z`;
* bitsize of every coefficient of `R` ≤
  `τ_1 + d_X · (τ_2 + ℓ · bit(D_Y) + m · bit(D_Z) + 1) + d_Y + ℓ + k`.

**Encoding.** We use the nested view with `X` outer and `Y` inner for `P`, and
`Y` outer and `Z` inner for `Q_i` and `R`:

* `P : MvPolynomial (Fin k) (MvPolynomial (Fin ℓ) ℤ)`.
* `Q : Fin k → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)`.
* `R = MvPolynomial.eval₂Hom (MvPolynomial.map MvPolynomial.C) Q P`.

**Note on the bitsize bound.** The Lean bound matches BPR's exact statement.
The tail `+ d_Y + ℓ + k` is achieved via:
(a) the stars-and-bars cardinality bound `support.card ≤ 2^(d+k)`
    (`support_card_le_two_pow`),
(b) the sharper `Int.size_finset_sum_le'` that uses `Nat.size (card - 1)`
    instead of `Nat.size card`, and
(c) a case split on `α = 0` in the per-summand bound to avoid the loose `+1`
    from `Int.size_mul_le` for the constant-product case.
The `bit(D_Y)` / `bit(D_Z)` shape (rather than the slacker `bit(D_Y+1)`
inherited from the naive form of equation (8.2)) is obtained by combining
`p + 1 ≤ 2^bit(p)` with `Int.size_finset_sum_le'` inside the proof of (8.2)
itself; see `Nat.size_prod_succ_sub_one_le` in `BitsizeMatrixMvListProd.lean`. -/

namespace Azurite.BPR

open _root_.Azurite.BPR.MvPolynomial

variable {k ℓ m : ℕ}

/-- The substitution `P(Y, X) ↦ P(Y, Q_1(Y, Z), …, Q_k(Y, Z))`. -/
noncomputable def substitute
    (P : MvPolynomial (Fin k) (MvPolynomial (Fin ℓ) ℤ))
    (Q : Fin k → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) :
    MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ) :=
  MvPolynomial.eval₂Hom (MvPolynomial.map MvPolynomial.C) Q P

/-- Expansion of `substitute` as a sum over the support of `P`. -/
theorem substitute_eq_sum
    (P : MvPolynomial (Fin k) (MvPolynomial (Fin ℓ) ℤ))
    (Q : Fin k → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) :
    substitute P Q =
      ∑ α ∈ P.support,
        (MvPolynomial.map MvPolynomial.C (P.coeff α)) * ∏ i, (Q i) ^ (α i) :=
  MvPolynomial.eval₂_eq' _ _ _

/-! ### Auxiliary lemmas -/

/-- The Z-degree of a polynomial in the nested encoding
    `MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)`. -/
private noncomputable def zDeg
    (p : MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) : ℕ :=
  p.support.sup (fun y => (p.coeff y).totalDegree)

private lemma le_zDeg (p : MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ))
    (y : Fin ℓ →₀ ℕ) : (p.coeff y).totalDegree ≤ zDeg p := by
  by_cases h : y ∈ p.support
  · exact Finset.le_sup (f := fun y => (p.coeff y).totalDegree) h
  · rw [MvPolynomial.notMem_support_iff.mp h]
    simp [MvPolynomial.totalDegree]

private lemma zDeg_add_le (p q : MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) :
    zDeg (p + q) ≤ max (zDeg p) (zDeg q) := by
  unfold zDeg
  apply Finset.sup_le
  intro y hy
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  refine max_le_max ?_ ?_
  · exact le_zDeg p y
  · exact le_zDeg q y

private lemma zDeg_mul_le (p q : MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) :
    zDeg (p * q) ≤ zDeg p + zDeg q := by
  unfold zDeg
  apply Finset.sup_le
  intro y _
  rw [MvPolynomial.coeff_mul]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro ⟨u, v⟩ _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  exact Nat.add_le_add (le_zDeg p u) (le_zDeg q v)

private lemma zDeg_pow_le (p : MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) (n : ℕ) :
    zDeg (p ^ n) ≤ n * zDeg p := by
  induction n with
  | zero => simp [zDeg, MvPolynomial.totalDegree]
  | succ n ih =>
    rw [pow_succ]
    refine (zDeg_mul_le _ _).trans ?_
    have : (n + 1) * zDeg p = n * zDeg p + zDeg p := by ring
    omega

private lemma zDeg_finsetProd_le {ι : Type _} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) :
    zDeg (∏ i ∈ s, f i) ≤ ∑ i ∈ s, zDeg (f i) := by
  induction s using Finset.induction with
  | empty => simp [zDeg, MvPolynomial.totalDegree]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (zDeg_mul_le _ _).trans (Nat.add_le_add_left ih _)

private lemma zDeg_finsetSum_le {ι : Type _} [DecidableEq ι] {s : Finset ι}
    {f : ι → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)} {d : ℕ}
    (h : ∀ i ∈ s, zDeg (f i) ≤ d) : zDeg (∑ i ∈ s, f i) ≤ d := by
  induction s using Finset.induction with
  | empty => simp [zDeg, MvPolynomial.totalDegree]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine (zDeg_add_le _ _).trans ?_
    refine max_le (h i (Finset.mem_insert_self _ _)) ?_
    exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma zDeg_map_C (p : MvPolynomial (Fin ℓ) ℤ) :
    zDeg ((MvPolynomial.map (MvPolynomial.C :
      ℤ →+* MvPolynomial (Fin m) ℤ)) p) = 0 := by
  unfold zDeg
  apply Nat.le_zero.mp
  apply Finset.sup_le
  intro y _
  rw [MvPolynomial.coeff_map]
  show (MvPolynomial.C (p.coeff y) : MvPolynomial (Fin m) ℤ).totalDegree ≤ 0
  rw [MvPolynomial.totalDegree_C]

private lemma zDeg_le_iff (p : MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) (d : ℕ) :
    zDeg p ≤ d ↔ ∀ y, (p.coeff y).totalDegree ≤ d := by
  constructor
  · intro h y
    exact le_trans (le_zDeg p y) h
  · intro h
    apply Finset.sup_le
    intro y _
    exact h y

/-! ### Cardinality and size helpers -/


/-- Combinatorial bound: any `Finset` of finitely-supported maps with bounded
    sum has cardinality `≤ 2^(d+k)`. This is the stars-and-bars bound
    `C(d+k, k) ≤ 2^(d+k)` for the count of `(k+1)`-tuples summing to `d`,
    derived here directly by induction on `k`. -/
private lemma card_finsupp_le_two_pow :
    ∀ (k : ℕ) (s : Finset (Fin k →₀ ℕ)) (d : ℕ),
    (∀ α ∈ s, α.sum (fun _ e => e) ≤ d) → s.card ≤ 2 ^ (d + k) := by
  intro k
  induction k with
  | zero =>
    intro s d _
    rw [Nat.add_zero]
    have h_sub : s ⊆ {(0 : Fin 0 →₀ ℕ)} := by
      intro α _
      simp only [Finset.mem_singleton]
      apply Finsupp.ext; intro i; exact i.elim0
    have h_card_le : s.card ≤ 1 :=
      (Finset.card_le_card h_sub).trans (by simp)
    have h_pos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega
  | succ k ih =>
    intro s d h_bound
    have h_α0_le : ∀ α ∈ s, α 0 ≤ d := by
      intro α hα
      have h_sum_decomp : α.sum (fun _ e => e) = α 0 + α.tail.sum (fun _ e => e) := by
        conv_lhs => rw [← Finsupp.cons_tail α]
        rw [Finsupp.sum_cons]
      have h_α_sum : α.sum (fun _ e => e) ≤ d := h_bound α hα
      omega
    have h_filter_card : ∀ a ∈ Finset.range (d + 1),
        (s.filter (fun α => α 0 = a)).card ≤ 2 ^ ((d - a) + k) := by
      intro a _
      set T_a := (s.filter (fun α => α 0 = a)).image Finsupp.tail with hT_a
      have h_T_a_bound : ∀ α' ∈ T_a, α'.sum (fun _ e => e) ≤ d - a := by
        intro α' hα'
        rw [hT_a, Finset.mem_image] at hα'
        obtain ⟨α, hα_filter, rfl⟩ := hα'
        rw [Finset.mem_filter] at hα_filter
        obtain ⟨hα_s, hα0⟩ := hα_filter
        have h_α_sum : α.sum (fun _ e => e) ≤ d := h_bound α hα_s
        have h_sum_decomp : α.sum (fun _ e => e) = α 0 + α.tail.sum (fun _ e => e) := by
          conv_lhs => rw [← Finsupp.cons_tail α]
          rw [Finsupp.sum_cons]
        omega
      have h_filter_le_T_a :
          (s.filter (fun α => α 0 = a)).card ≤ T_a.card := by
        refine Finset.card_le_card_of_injOn Finsupp.tail
          (fun α hα => Finset.mem_image_of_mem _ hα) ?_
        intro α hα β hβ h_eq
        simp only [Finset.mem_coe, Finset.mem_filter] at hα hβ
        rw [← Finsupp.cons_tail α, ← Finsupp.cons_tail β, hα.2, hβ.2, h_eq]
      exact h_filter_le_T_a.trans (ih T_a (d - a) h_T_a_bound)
    have h_card_eq : s.card =
        ∑ a ∈ Finset.range (d + 1), (s.filter (fun α => α 0 = a)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext α
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
        constructor
        · intro hα
          exact ⟨α 0, Nat.lt_succ_of_le (h_α0_le α hα), hα, rfl⟩
        · rintro ⟨_, _, hα, _⟩; exact hα
      · intro a _ b _ hab
        rw [Function.onFun, Finset.disjoint_left]
        intro α hα_a hα_b
        rw [Finset.mem_filter] at hα_a hα_b
        exact hab (hα_a.2.symm.trans hα_b.2)
    rw [h_card_eq]
    refine (Finset.sum_le_sum h_filter_card).trans ?_
    -- Σ_{a=0}^{d} 2^{(d-a)+k} = 2^k · Σ_{a=0}^d 2^{d-a} = 2^k · (2^{d+1} - 1) ≤ 2^{d+k+1}
    have h_sum_swap : (∑ a ∈ Finset.range (d + 1), 2 ^ (d - a))
        = ∑ b ∈ Finset.range (d + 1), 2 ^ b :=
      Finset.sum_range_reflect (fun j => 2 ^ j) (d + 1)
    -- Simple induction: Σ_{b ∈ range (d+1)} 2^b ≤ 2^(d+1).
    have h_geom_le : (∑ b ∈ Finset.range (d + 1), (2 : ℕ) ^ b) ≤ 2 ^ (d + 1) := by
      clear h_sum_swap h_filter_card h_α0_le h_bound h_card_eq ih
      induction d with
      | zero => simp
      | succ d' ih_d =>
        rw [Finset.sum_range_succ]
        calc (∑ b ∈ Finset.range (d' + 1), (2 : ℕ) ^ b) + 2 ^ (d' + 1)
            ≤ 2 ^ (d' + 1) + 2 ^ (d' + 1) := by omega
          _ = 2 ^ (d' + 2) := by rw [show (d' + 2) = (d' + 1) + 1 from rfl, pow_succ]; ring
    calc ∑ a ∈ Finset.range (d + 1), 2 ^ ((d - a) + k)
        = ∑ a ∈ Finset.range (d + 1), 2 ^ (d - a) * 2 ^ k := by
          apply Finset.sum_congr rfl
          intro a _; rw [pow_add]
      _ = (∑ a ∈ Finset.range (d + 1), 2 ^ (d - a)) * 2 ^ k := by
          rw [← Finset.sum_mul]
      _ ≤ 2 ^ (d + 1) * 2 ^ k :=
          Nat.mul_le_mul_right _ (h_sum_swap ▸ h_geom_le)
      _ = 2 ^ (d + (k + 1)) := by rw [← pow_add]; ring_nf

/-- Sharper bound on the size of a polynomial's monomial support: matches
    BPR's stars-and-bars bound `support.card ≤ 2^(d+k)`. -/
private lemma support_card_le_two_pow
    {R : Type _} [CommSemiring R] {k : ℕ} (p : MvPolynomial (Fin k) R) {d : ℕ}
    (h : p.totalDegree ≤ d) : p.support.card ≤ 2 ^ (d + k) := by
  apply card_finsupp_le_two_pow
  intro α hα
  exact (MvPolynomial.le_totalDegree hα).trans h

private lemma support_card_le_of_totalDegree
    {R : Type _} [CommSemiring R] {k : ℕ} (p : MvPolynomial (Fin k) R) {d : ℕ}
    (h : p.totalDegree ≤ d) : p.support.card ≤ (d + 1) ^ k := by
  rw [show (d + 1) ^ k = (Fintype.piFinset (fun _ : Fin k => Finset.range (d + 1))).card by
    rw [Fintype.card_piFinset]
    simp [Finset.card_range]]
  refine Finset.card_le_card_of_injOn (fun α => (fun i => α i)) ?_ ?_
  · intro α hα
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    -- α i ≤ α.sum (fun _ e => e) ≤ p.totalDegree ≤ d
    have h_sum_eq : α.sum (fun _ e => e) = ∑ j : Fin k, α j :=
      Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)
    have h_sum_le_td : α.sum (fun _ e => e) ≤ p.totalDegree :=
      MvPolynomial.le_totalDegree hα
    have h_i_le_sum : α i ≤ ∑ j : Fin k, α j := Finset.single_le_sum
      (f := fun j => α j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  · intro α _ β _ hαβ
    -- Two Finsupps with the same toFun are equal
    apply Finsupp.ext
    intro i
    exact congrFun hαβ i

/-- Bitsize of a `Nat` product is bounded by the sum of bitsizes. -/
private lemma Nat.size_mul_le_local (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have ha' : a < 2 ^ a.size := Nat.lt_size_self _
  have hb' : b < 2 ^ b.size := Nat.lt_size_self _
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_pos_right ha' hb |>.trans_le (Nat.mul_le_mul le_rfl hb'.le)

/-- Iterated bound: `Nat.size (a^n) ≤ n · Nat.size a + 1`. -/
private lemma Nat.size_pow_le' (a n : ℕ) : Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp [Nat.size]
  | succ n ih =>
    rw [pow_succ]
    refine (Nat.size_mul_le_local _ _).trans ?_
    have : (n + 1) * Nat.size a + 1 = (n * Nat.size a + 1) + Nat.size a := by ring
    omega

/-! ### Decomposition of `((substitute P Q).coeff y).coeff z` -/

/-- The integer coefficient of the substitution `R = substitute P Q` at the
    `(y, z)`-monomial expands as a double sum over the support of `P` and the
    antidiagonal of `y`. -/
private lemma coeff_coeff_substitute
    (P : MvPolynomial (Fin k) (MvPolynomial (Fin ℓ) ℤ))
    (Q : Fin k → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ))
    (y : Fin ℓ →₀ ℕ) (z : Fin m →₀ ℕ) :
    (((substitute P Q).coeff y).coeff z) =
      ∑ α ∈ P.support, ∑ uv ∈ Finset.antidiagonal y,
        ((P.coeff α).coeff uv.1) * (((∏ i, (Q i) ^ (α i)).coeff uv.2).coeff z) := by
  rw [substitute_eq_sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro ⟨u, v⟩ _
  rw [MvPolynomial.coeff_map]
  exact MvPolynomial.coeff_C_mul z _ _

/-- **BPR §8.1 Proposition 8.11 (Substitution).** Bounds on the `Y`-degree,
    `Z`-degree, and coefficient bitsize of the substitution
    `R = P(Y, Q(Y, Z))`. -/
theorem bitsize_substitute_le
    {d_X d_Y D_Y D_Z τ_1 τ_2 : ℕ}
    (P : MvPolynomial (Fin k) (MvPolynomial (Fin ℓ) ℤ))
    (Q : Fin k → MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ))
    (h_dX : P.totalDegree ≤ d_X)
    (h_dY : ∀ α, (P.coeff α).totalDegree ≤ d_Y)
    (h_τ1 : ∀ α y, ((P.coeff α).coeff y).natAbs.size ≤ τ_1)
    (h_DY : ∀ i, (Q i).totalDegree ≤ D_Y)
    (h_DZ : ∀ i y, ((Q i).coeff y).totalDegree ≤ D_Z)
    (h_τ2 : ∀ i y z, (((Q i).coeff y).coeff z).natAbs.size ≤ τ_2) :
    (substitute P Q).totalDegree ≤ d_X * D_Y + d_Y ∧
    (∀ y, ((substitute P Q).coeff y).totalDegree ≤ d_X * D_Z) ∧
    (∀ y z, (((substitute P Q).coeff y).coeff z).natAbs.size ≤
      τ_1 + d_X * (τ_2 + ℓ * Nat.size D_Y + m * Nat.size D_Z + 1) +
        d_Y + ℓ + k) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Y-degree bound.
    rw [substitute_eq_sum]
    refine MvPolynomial.totalDegree_finsetSum_le ?_
    intro α hα
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : ((MvPolynomial.map (MvPolynomial.C :
        ℤ →+* MvPolynomial (Fin m) ℤ)) (P.coeff α)).totalDegree ≤ d_Y := by
      have h_supp : ((MvPolynomial.map (MvPolynomial.C :
        ℤ →+* MvPolynomial (Fin m) ℤ)) (P.coeff α)).support = (P.coeff α).support :=
        MvPolynomial.support_map_of_injective _ (MvPolynomial.C_injective _ _)
      unfold MvPolynomial.totalDegree
      rw [h_supp]
      exact h_dY α
    have h2 : (∏ i, (Q i) ^ (α i)).totalDegree ≤ d_X * D_Y := by
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      have h_each : ∀ i ∈ Finset.univ, ((Q i) ^ (α i)).totalDegree ≤ (α i) * D_Y :=
        fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
          (Nat.mul_le_mul_left _ (h_DY i))
      refine (Finset.sum_le_sum h_each).trans ?_
      rw [← Finset.sum_mul]
      apply Nat.mul_le_mul_right
      have h_sum_eq : α.sum (fun _ e => e) = ∑ i : Fin k, α i :=
        Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)
      have h_sum_α : α.sum (fun _ e => e) ≤ P.totalDegree :=
        MvPolynomial.le_totalDegree hα
      omega
    omega
  · -- Z-degree bound.
    intro y
    have h_zd : zDeg (substitute P Q) ≤ d_X * D_Z := by
      rw [substitute_eq_sum]
      apply zDeg_finsetSum_le
      intro α hα
      have h_zd_C : zDeg ((MvPolynomial.map (MvPolynomial.C :
          ℤ →+* MvPolynomial (Fin m) ℤ)) (P.coeff α)) = 0 := zDeg_map_C _
      have h_zd_prod : zDeg (∏ i, (Q i) ^ (α i)) ≤ d_X * D_Z := by
        refine (zDeg_finsetProd_le _ _).trans ?_
        have h_each : ∀ i ∈ Finset.univ, zDeg ((Q i) ^ (α i)) ≤ α i * D_Z := by
          intro i _
          refine (zDeg_pow_le _ _).trans ?_
          apply Nat.mul_le_mul_left
          rw [zDeg_le_iff]
          exact h_DZ i
        refine (Finset.sum_le_sum h_each).trans ?_
        rw [← Finset.sum_mul]
        apply Nat.mul_le_mul_right
        have h_sum_eq : α.sum (fun _ e => e) = ∑ i : Fin k, α i :=
          Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)
        have h_sum_α : α.sum (fun _ e => e) ≤ P.totalDegree :=
          MvPolynomial.le_totalDegree hα
        omega
      refine (zDeg_mul_le _ _).trans ?_
      omega
    exact le_trans (le_zDeg _ y) h_zd
  · -- Bitsize bound.
    intro y z
    rw [coeff_coeff_substitute]
    set B_in := τ_2 + ℓ * Nat.size D_Y + m * Nat.size D_Z with hB_in_def
    -- Inner-factor bound for α ≠ 0: bit ≤ d_X · B_in via (8.2). The α = 0
    -- case is handled separately at the per-summand level (where the product
    -- collapses to `(P.coeff 0).coeff y` directly, bypassing Int.size_mul_le).
    have h_inner_bound :
        ∀ α : Fin k →₀ ℕ, α ∈ P.support → α ≠ 0 → ∀ v : Fin ℓ →₀ ℕ,
          (((∏ i : Fin k, (Q i) ^ (α i)).coeff v).coeff z).natAbs.size ≤
            d_X * B_in := by
      intro α hα hα_zero v
      -- α ≠ 0: apply (8.2) to a list of α_i copies of each Q_i.
      set Qs : List (MvPolynomial (Fin ℓ) (MvPolynomial (Fin m) ℤ)) :=
        (List.finRange k).flatMap (fun i => List.replicate (α i) (Q i)) with hQs_def
      have h_Qs_prod : Qs.prod = ∏ i : Fin k, (Q i) ^ (α i) := by
        show ((List.finRange k).flatMap _).prod = _
        rw [List.flatMap_def, List.prod_flatten, List.map_map]
        conv_lhs =>
          rw [show (List.prod ∘ fun i : Fin k => List.replicate (α i) (Q i)) =
              fun i : Fin k => (Q i) ^ (α i) by
            funext i; simp [Function.comp, List.prod_replicate]]
        rw [show (List.finRange k).map (fun i : Fin k => (Q i) ^ (α i)) =
            List.ofFn (fun i : Fin k => (Q i) ^ (α i)) by
          rw [List.ofFn_eq_map]]
        exact List.prod_ofFn
      have h_Qs_len_eq : Qs.length = ∑ i : Fin k, α i := by
        show ((List.finRange k).flatMap _).length = _
        rw [List.length_flatMap]
        simp only [List.length_replicate]
        rw [show (List.finRange k).map (fun i : Fin k => α i) =
            List.ofFn (fun i : Fin k => α i) by
          rw [List.ofFn_eq_map]]
        exact List.sum_ofFn
      have h_Qs_len_le : Qs.length ≤ d_X := by
        rw [h_Qs_len_eq]
        have h_sum_eq : α.sum (fun _ e => e) = ∑ i : Fin k, α i :=
          Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)
        have h_le_td : α.sum (fun _ e => e) ≤ P.totalDegree :=
          MvPolynomial.le_totalDegree hα
        omega
      have h_Qs_ne : Qs ≠ [] := by
        intro h_empty
        have hL : Qs.length = 0 := by rw [h_empty]; rfl
        rw [h_Qs_len_eq] at hL
        apply hα_zero
        ext i
        exact (Finset.sum_eq_zero_iff (f := fun j : Fin k => α j)).mp hL i
          (Finset.mem_univ _)
      have h_mem_Qs : ∀ P' ∈ Qs, ∃ i : Fin k, P' = Q i := by
        intro P' hP'
        have h_mem : P' ∈ (List.finRange k).flatMap
            (fun i => List.replicate (α i) (Q i)) := hP'
        rw [List.mem_flatMap] at h_mem
        obtain ⟨i, _, hP'_mem⟩ := h_mem
        rw [List.mem_replicate] at hP'_mem
        exact ⟨i, hP'_mem.2⟩
      have h_τ_Qs : ∀ P' ∈ Qs, ∀ y' x',
          ((P'.coeff y').coeff x').natAbs.size ≤ τ_2 := by
        intro P' hP' y' x'
        obtain ⟨i, rfl⟩ := h_mem_Qs P' hP'
        exact h_τ2 i y' x'
      have h_q_Qs : ∀ P' ∈ Qs, P'.totalDegree ≤ D_Y := by
        intro P' hP'
        obtain ⟨i, rfl⟩ := h_mem_Qs P' hP'
        exact h_DY i
      have h_p_Qs : ∀ P' ∈ Qs, ∀ y', (P'.coeff y').totalDegree ≤ D_Z := by
        intro P' hP' y'
        obtain ⟨i, rfl⟩ := h_mem_Qs P' hP'
        exact h_DZ i y'
      have h_8_2 := MvPolynomial.bitsize_coeff_list_prod_le_bpr_8_2
        ℓ m Qs τ_2 D_Z D_Y h_Qs_ne h_τ_Qs h_q_Qs h_p_Qs v z
      rw [h_Qs_prod] at h_8_2
      -- Convert (8.2)'s expression to use B_in.
      have h_B_eq : τ_2 + m * Nat.size D_Z + ℓ * Nat.size D_Y = B_in := by
        rw [hB_in_def]; ring
      rw [h_B_eq] at h_8_2
      refine h_8_2.trans ?_
      have h_mul : Qs.length * B_in ≤ d_X * B_in :=
        Nat.mul_le_mul_right _ h_Qs_len_le
      omega
    -- Inner sum (over antidiag) bound per α: filter, case-split α = 0,
    -- and use the sharper Int.size_finset_sum_le' to save a bit.
    have h_inner_sum :
        ∀ α ∈ P.support,
          (∑ uv ∈ Finset.antidiagonal y,
            ((P.coeff α).coeff uv.1) *
              (((∏ i, (Q i) ^ (α i)).coeff uv.2).coeff z)).natAbs.size ≤
            τ_1 + d_X * B_in + (d_Y + ℓ) := by
      intro α hα
      -- Filter: only uv.1 ∈ (P.coeff α).support contributes nonzero.
      set s_filtered := (Finset.antidiagonal y).filter
        (fun uv => uv.1 ∈ (P.coeff α).support) with hs_filt
      have h_sum_eq :
          (∑ uv ∈ Finset.antidiagonal y,
            ((P.coeff α).coeff uv.1) *
              (((∏ i, (Q i) ^ (α i)).coeff uv.2).coeff z))
          = ∑ uv ∈ s_filtered,
            ((P.coeff α).coeff uv.1) *
              (((∏ i, (Q i) ^ (α i)).coeff uv.2).coeff z) := by
        apply (Finset.sum_subset (Finset.filter_subset _ _) _).symm
        intro uv huv h_not
        rw [Finset.mem_filter, not_and_or] at h_not
        rcases h_not with h | h
        · exact absurd huv h
        · rw [MvPolynomial.notMem_support_iff] at h
          rw [h, Int.zero_mul]
      rw [h_sum_eq]
      -- Per-summand bound: τ_1 + d_X · B_in. Case split on α = 0 inside.
      have h_summand : ∀ uv ∈ s_filtered,
          (((P.coeff α).coeff uv.1) *
            (((∏ i, (Q i) ^ (α i)).coeff uv.2).coeff z)).natAbs.size ≤
              τ_1 + d_X * B_in := by
        intro uv _
        by_cases hα_zero : α = 0
        · -- α = 0: ∏ Q_i^0 = 1, so the second factor is 0 or 1.
          --   product = (P.coeff 0).coeff uv.1 * 0 (bit 0) or
          --           = (P.coeff 0).coeff uv.1 * 1 (bit ≤ τ_1).
          subst hα_zero
          have h_prod_one : (∏ i : Fin k, (Q i) ^ ((0 : Fin k →₀ ℕ) i)) = 1 := by
            apply Finset.prod_eq_one; intro i _; simp
          rw [h_prod_one, MvPolynomial.coeff_one]
          split_ifs with h1
          · rw [MvPolynomial.coeff_one]
            split_ifs with h2
            · rw [Int.mul_one]
              exact (h_τ1 0 uv.1).trans (Nat.le_add_right _ _)
            · rw [Int.mul_zero]; simp
          · rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Int.mul_zero]; simp
        · -- α ≠ 0: use h_inner_bound (without +1) and Int.size_mul_le.
          have h_P_bound : ((P.coeff α).coeff uv.1).natAbs.size ≤ τ_1 := h_τ1 _ _
          exact Int.size_mul_le _ _ τ_1 (d_X * B_in) h_P_bound
            (h_inner_bound α hα hα_zero uv.2)
      refine (Int.size_finset_sum_le' h_summand).trans ?_
      -- bit(s_filtered.card - 1) ≤ d_Y + ℓ.
      have h_card_inj : s_filtered.card ≤ (P.coeff α).support.card := by
        refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
        · intro uv huv
          simp only [Finset.mem_coe, hs_filt, Finset.mem_filter] at huv
          exact huv.2
        · intro a ha b hb hab
          simp only [Finset.mem_coe, hs_filt, Finset.mem_filter,
            Finset.mem_antidiagonal] at ha hb
          have h_eq : a.1 + a.2 = a.1 + b.2 := by rw [ha.1, hab, hb.1]
          ext1
          · exact hab
          · exact add_left_cancel h_eq
      have h_supp_card : (P.coeff α).support.card ≤ 2 ^ (d_Y + ℓ) :=
        support_card_le_two_pow _ (h_dY α)
      have h_size_lt : s_filtered.card - 1 < 2 ^ (d_Y + ℓ) := by
        have h := h_card_inj.trans h_supp_card
        have h_pow : 0 < 2 ^ (d_Y + ℓ) := Nat.two_pow_pos _
        omega
      have h_size_le : Nat.size (s_filtered.card - 1) ≤ d_Y + ℓ :=
        Nat.size_le.mpr h_size_lt
      omega
    -- Outer sum (over P.support) bound using sharper Int.size_finset_sum_le'.
    refine (Int.size_finset_sum_le' (s := P.support)
      (B := τ_1 + d_X * B_in + (d_Y + ℓ)) h_inner_sum).trans ?_
    -- bit(P.support.card - 1) ≤ d_X + k.
    have h_P_card : P.support.card ≤ 2 ^ (d_X + k) := support_card_le_two_pow _ h_dX
    have h_pow_pos : 0 < 2 ^ (d_X + k) := Nat.two_pow_pos _
    have h_size_lt : P.support.card - 1 < 2 ^ (d_X + k) := by omega
    have h_size_le : Nat.size (P.support.card - 1) ≤ d_X + k :=
      Nat.size_le.mpr h_size_lt
    have h_expand : d_X * (B_in + 1) = d_X * B_in + d_X := by ring
    rw [h_expand]
    omega

end Azurite.BPR

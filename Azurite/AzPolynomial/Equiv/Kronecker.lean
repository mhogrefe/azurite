/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Kronecker
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzNat.Equiv.Kronecker
import Azurite.AzNat.Equiv.Kronecker2
import Azurite.AzNat.Equiv.BlockRem
import Azurite.AzNat.Equiv.Square.Dispatch
import Azurite.AzInt.Equiv.Mul
import Azurite.AzNat.Equiv.LogBase2
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzZMod.Equiv.RingEquiv
import Azurite.AzNat.Equiv.RingEquiv
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Kronecker multiplication over `ℤ/m` is multiplication

`mulKronecker_eq_mulBasecase`, hence `toPoly_mulKronecker` and `mulKronecker_eq_mul`.

The lifts of the two factors are polynomials `P`, `Q` over `ℕ` (`natPoly`); the packed
numbers are `P(B)`, `Q(B)` with `B = 2^(64 w)`, their product is `(PQ)(B)`, and as the
coefficients of `PQ` are below `B` they are the base-`B` digits of that number.
-/

open Polynomial

namespace Azurite.AzPolynomial

open AzNat (natPoly natPoly_eval natPoly_coeff eval_div_pow_mod)

variable {m : AzNat} [NeZero m.toNat]

/-- The lifts of the coefficients. -/
def liftList (p : AzPolynomial (AzZMod m)) : List ℕ :=
  (p.coeffs.map (·.val)).toList.map AzNat.toNat

theorem liftList_getD (p : AzPolynomial (AzZMod m)) (i : ℕ) :
    (liftList p).getD i 0 = (p.coeff i).val.toNat := by
  unfold liftList coeff
  by_cases hi : i < p.coeffs.size
  · simp [List.getD, hi]
  · simp [List.getD, hi]

theorem liftList_lt (p : AzPolynomial (AzZMod m)) (i : ℕ) :
    (liftList p).getD i 0 < m.toNat := by
  rw [liftList_getD]
  exact (p.coeff i).isLt

theorem kroneckerWidth_spec (n : ℕ) :
    n * (m.toNat * m.toNat) < 2 ^ (64 * kroneckerWidth m n) := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact NeZero.ne (0 : AzNat).toNat (by decide)
  have hm := (AzNat.size_bounds m hm0).2
  have hn : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hle : 2 * m.size + n.log2 + 1 ≤ 64 * kroneckerWidth m n := by
    unfold kroneckerWidth
    omega
  calc n * (m.toNat * m.toNat)
      < 2 ^ (n.log2 + 1) * (2 ^ m.size * 2 ^ m.size) := by
        have h1 : m.toNat * m.toNat ≤ 2 ^ m.size * 2 ^ m.size :=
          Nat.mul_le_mul hm.le hm.le
        have h2 : 0 < m.toNat * m.toNat :=
          Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.pos_of_ne_zero (NeZero.ne _))
        calc n * (m.toNat * m.toNat) < 2 ^ (n.log2 + 1) * (m.toNat * m.toNat) :=
              Nat.mul_lt_mul_of_pos_right hn h2
          _ ≤ _ := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (2 * m.size + n.log2 + 1) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hle

theorem packLift_toNat (p : AzPolynomial (AzZMod m)) (w : ℕ) (hw : m.toNat ≤ 2 ^ (64 * w)) :
    (AzNat.kroneckerPack w (p.coeffs.map (·.val))).toNat =
      (natPoly (liftList p)).eval (2 ^ (64 * w)) := by
  rw [natPoly_eval, AzNat.kroneckerPack_toNat]
  · rfl
  · intro c hc
    obtain ⟨a, _, rfl⟩ := Array.mem_map.mp hc
    exact lt_of_lt_of_le a.isLt hw

/-- A coefficient of the product of the lifts. -/
theorem liftProd_coeff (p q : AzPolynomial (AzZMod m)) (k : ℕ) :
    (natPoly (liftList p) * natPoly (liftList q)).coeff k =
      ∑ i ∈ Finset.range (k + 1), (p.coeff i).val.toNat * (q.coeff (k - i)).val.toNat := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (natPoly (liftList p)).coeff i * (natPoly (liftList q)).coeff j)]
  simp only [natPoly_coeff, liftList_getD]

theorem liftCoeff_eq_zero_of_size_le (p : AzPolynomial (AzZMod m)) (i : ℕ)
    (h : p.coeffs.size ≤ i) : (p.coeff i).val.toNat = 0 := by
  unfold coeff
  rw [Array.getElem?_eq_none h]
  rfl

/-- The product of the lifts. -/
noncomputable def liftProd (p q : AzPolynomial (AzZMod m)) : ℕ[X] :=
  natPoly (liftList p) * natPoly (liftList q)

theorem liftProd_coeff_eq_zero (p q : AzPolynomial (AzZMod m)) (i : ℕ)
    (hi : p.coeffs.size + q.coeffs.size - 1 ≤ i) : (liftProd p q).coeff i = 0 := by
  rw [liftProd, liftProd_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  by_cases hjp : p.coeffs.size ≤ j
  · rw [liftCoeff_eq_zero_of_size_le p j hjp, Nat.zero_mul]
  · rw [liftCoeff_eq_zero_of_size_le q (i - j) (by omega), Nat.mul_zero]

theorem liftProd_coeff_lt (p q : AzPolynomial (AzZMod m)) (i B : ℕ)
    (hi : i < p.coeffs.size + q.coeffs.size - 1)
    (hB : (p.coeffs.size + q.coeffs.size) * (m.toNat * m.toNat) < B) :
    (liftProd p q).coeff i < B := by
  rw [liftProd, liftProd_coeff]
  have hle : ∑ j ∈ Finset.range (i + 1),
      (p.coeff j).val.toNat * (q.coeff (i - j)).val.toNat ≤
      (Finset.range (i + 1)).card • (m.toNat * m.toNat) :=
    Finset.sum_le_card_nsmul _ _ _ fun j _ =>
      Nat.mul_le_mul (p.coeff j).isLt.le (q.coeff (i - j)).isLt.le
  rw [Finset.card_range, smul_eq_mul] at hle
  have : (i + 1) * (m.toNat * m.toNat) ≤
      (p.coeffs.size + q.coeffs.size) * (m.toNat * m.toNat) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- A number whose value is a coefficient of the product of the lifts reduces to the
coefficient of the product. -/
theorem ofAzNat_eq_of_toNat_eq (p q : AzPolynomial (AzZMod m)) (k : ℕ) (c : AzNat)
    (hc : c.toNat = (liftProd p q).coeff k) :
    AzZMod.ofAzNat m c = ∑ i ∈ Finset.range (k + 1), p.coeff i * q.coeff (k - i) := by
  apply AzZMod.toZMod_injective
  rw [AzZMod.toZMod_ofAzNat, hc, liftProd, liftProd_coeff]
  change _ = AzZMod.toZModRingHom _
  rw [map_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

/-- The lifts are below any `B` above `N m²`. -/
theorem lift_lt_of_spec (p : AzPolynomial (AzZMod m)) (N B : ℕ) (hN : 0 < N)
    (hB : N * (m.toNat * m.toNat) < B) : ∀ c ∈ p.coeffs.map (·.val), c.toNat < B := by
  intro c hc
  obtain ⟨a, _, rfl⟩ := Array.mem_map.mp hc
  have h0 := a.isLt
  have h1 : m.toNat ≤ m.toNat * m.toNat := Nat.le_mul_self _
  have h2 : m.toNat * m.toNat ≤ N * (m.toNat * m.toNat) := Nat.le_mul_of_pos_left _ hN
  omega

theorem ofAzNat_val_toNat (c : AzNat) : (AzZMod.ofAzNat m c).val.toNat = c.toNat % m.toNat :=
  AzNat.toNat_mod c m

/-- Two numbers with the same residue reduce to the same element. -/
theorem ofAzNat_congr {c d : AzNat} (h : c.toNat % m.toNat = d.toNat % m.toNat) :
    AzZMod.ofAzNat m c = AzZMod.ofAzNat m d := by
  apply AzZMod.ext
  apply AzNat.toNat_injective
  rw [ofAzNat_val_toNat, ofAzNat_val_toNat, h]

/-- **The entries of `blockReduce`**: the `j`-th is the reduction of any number whose value
is the `j`-th block. -/
theorem blockReduce_getElem? (w off cnt : ℕ) (x : Array UInt64) (j : ℕ) (hj : j < cnt)
    (c : AzNat) (hc : c.toNat = AzNat.blockValue x.toList w off j) :
    (blockReduce m w off cnt x)[j]? = some (AzZMod.ofAzNat m c) := by
  have hslow : (blockReduceSlow m w off cnt x)[j]? = some (AzZMod.ofAzNat m c) := by
    unfold blockReduceSlow
    rw [Array.getElem?_ofFn]
    simp only [hj, ↓reduceDIte]
    congr 1
    apply ofAzNat_congr
    rw [hc, AzNat.toNat_ofLimbs, Array.toList_extract]
    show AzNat.toNatLimbsList ((x.toList.drop (off + j * w)).take
      (off + j * w + w - (off + j * w))) % _ = _
    rw [Nat.add_sub_cancel_left]
    rfl
  unfold blockReduce
  split
  · next h1 =>
    obtain ⟨-, h⟩ := AzNat.blockRemsMod_spec m h1 (fun c hc => (⟨c, hc⟩ : AzZMod m)) w off cnt x
    obtain ⟨c', hc', h2, h3⟩ := h j hj
    rw [h2]
    congr 1
    apply AzZMod.ext
    apply AzNat.toNat_injective
    rw [ofAzNat_val_toNat, hc]
    exact h3
  · exact hslow

theorem blockReduce_getD (w off cnt : ℕ) (x : Array UInt64) (j : ℕ) (hj : j < cnt)
    (c : AzNat) (hc : c.toNat = AzNat.blockValue x.toList w off j) :
    (blockReduce m w off cnt x)[j]?.getD 0 = AzZMod.ofAzNat m c := by
  rw [blockReduce_getElem? w off cnt x j hj c hc, Option.getD_some]

theorem blockReduce_size (w off cnt : ℕ) (x : Array UInt64) :
    (blockReduce m w off cnt x).size = cnt := by
  unfold blockReduce
  split
  · next h1 =>
    exact (AzNat.blockRemsMod_spec m h1 (fun c hc => (⟨c, hc⟩ : AzZMod m)) w off cnt x).1
  · simp [blockReduceSlow]

/-- `kroneckerRead` is the block-by-block reading. -/
theorem kroneckerRead_eq (w n : ℕ) (x : AzNat) :
    kroneckerRead m w n x =
      Array.ofFn fun (k : Fin n) => AzZMod.ofAzNat m (AzNat.kroneckerCoeff w x k.val) := by
  unfold kroneckerRead
  apply Array.ext_getElem?
  intro k
  by_cases hk : k < n
  · rw [blockReduce_getElem? w 0 n x.limbs k hk (AzNat.kroneckerCoeff w x k)
      (by rw [AzNat.kroneckerCoeff_toNat_list]; simp [AzNat.blockValue]),
      Array.getElem?_ofFn]
    simp only [hk, ↓reduceDIte]
  · rw [Array.getElem?_eq_none (by rw [blockReduce_size]; omega),
      Array.getElem?_eq_none (by simp; omega)]

/-- `kroneckerRead2` is the block-by-block reading. -/
theorem kroneckerRead2_eq (w n : ℕ) (xe xo : AzNat) :
    kroneckerRead2 m w n xe xo =
      Array.ofFn fun (k : Fin n) =>
        AzZMod.ofAzNat m (AzNat.kroneckerCoeff2 w xe xo k.val) := by
  unfold kroneckerRead2
  dsimp only
  congr 1
  funext k
  obtain ⟨k, hk⟩ := k
  dsimp only
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hpar : 2 * j % 2 = 0 := by omega
    simp only [hpar, ↓reduceIte, Nat.mul_div_cancel_left j (by norm_num : 0 < 2)]
    refine blockReduce_getD (2 * w) 0 ((n + 1) / 2) xe.limbs j (by omega) _ ?_
    unfold AzNat.kroneckerCoeff2
    simp only [hpar, ↓reduceIte]
    rw [AzNat.limbBlock_toNat_list, AzNat.blockValue,
      show 0 + j * (2 * w) = 2 * j * w by ring]
  · have hpar : ¬ (2 * j + 1) % 2 = 0 := by omega
    have hdiv : (2 * j + 1) / 2 = j := by omega
    simp only [hpar, ↓reduceIte, hdiv]
    refine blockReduce_getD (2 * w) w (n / 2) xo.limbs j (by omega) _ ?_
    unfold AzNat.kroneckerCoeff2
    simp only [hpar, ↓reduceIte]
    rw [AzNat.limbBlock_toNat_list, AzNat.blockValue,
      show w + j * (2 * w) = (2 * j + 1) * w by ring]

theorem mulKronecker_eq_mulBasecase (p q : AzPolynomial (AzZMod m)) :
    mulKronecker p q = mulBasecase p q := by
  unfold mulKronecker mulBasecase
  split
  · rfl
  · next hne =>
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hne
    obtain ⟨hp, hq⟩ := hne
    dsimp only
    rw [kroneckerRead_eq]
    congr 1
    congr 1
    funext k
    obtain ⟨k, hk⟩ := k
    dsimp only
    refine ofAzNat_eq_of_toNat_eq p q k _ ?_
    obtain ⟨w, hw⟩ : ∃ w, w = kroneckerWidth m (p.coeffs.size + q.coeffs.size) := ⟨_, rfl⟩
    rw [← hw]
    have hspec : (p.coeffs.size + q.coeffs.size) * (m.toNat * m.toNat) < 2 ^ (64 * w) := by
      rw [hw]
      exact kroneckerWidth_spec _
    have hmB : m.toNat ≤ 2 ^ (64 * w) := by
      have h1 : m.toNat ≤ m.toNat * m.toNat := Nat.le_mul_self _
      have h2 : m.toNat * m.toNat ≤ (p.coeffs.size + q.coeffs.size) * (m.toNat * m.toNat) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hx : (if p = q then AzNat.square (AzNat.kroneckerPack w (p.coeffs.map (·.val)))
        else AzNat.kroneckerPack w (p.coeffs.map (·.val)) *
          AzNat.kroneckerPack w (q.coeffs.map (·.val))).toNat =
        (liftProd p q).eval (2 ^ (64 * w)) := by
      split
      · next hpq =>
        subst hpq
        rw [AzNat.toNat_square, packLift_toNat p w hmB, liftProd, eval_mul, sq]
      · rw [AzNat.toNat_mul, packLift_toNat p w hmB, packLift_toNat q w hmB, liftProd, eval_mul]
    rw [AzNat.kroneckerCoeff_toNat, hx,
      show (2 : ℕ) ^ (64 * (k * w)) = (2 ^ (64 * w)) ^ k by rw [← pow_mul]; congr 1; ring,
      eval_div_pow_mod _ _ (p.coeffs.size + q.coeffs.size - 1)
        (liftProd_coeff_eq_zero p q) (fun i hi => liftProd_coeff_lt p q i _ hi hspec)]

theorem mulKronecker2_eq_mulBasecase (p q : AzPolynomial (AzZMod m)) :
    mulKronecker2 p q = mulBasecase p q := by
  unfold mulKronecker2 mulBasecase
  split
  · rfl
  · next hne =>
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hne
    obtain ⟨hp, hq⟩ := hne
    dsimp only
    rw [kroneckerRead2_eq]
    congr 1
    congr 1
    funext k
    obtain ⟨k, hk⟩ := k
    dsimp only
    refine ofAzNat_eq_of_toNat_eq p q k _ ?_
    obtain ⟨w, hw⟩ :
      ∃ w, w = (kroneckerWidth m (p.coeffs.size + q.coeffs.size) + 1) / 2 := ⟨_, rfl⟩
    rw [← hw]
    have hspec : (p.coeffs.size + q.coeffs.size) * (m.toNat * m.toNat) <
        2 ^ (64 * (2 * w)) :=
      lt_of_lt_of_le (kroneckerWidth_spec _)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hpl := lift_lt_of_spec p _ _ (by omega) hspec
    have hql := lift_lt_of_spec q _ _ (by omega) hspec
    obtain ⟨B, hB⟩ : ∃ B, B = 2 ^ (64 * w) := ⟨_, rfl⟩
    have hp1 := AzNat.kroneckerEvalPair_fst w _ hpl
    have hp2 := AzNat.kroneckerEvalPair_snd w _ hpl
    have hq1 := AzNat.kroneckerEvalPair_fst w _ hql
    have hq2 := AzNat.kroneckerEvalPair_snd w _ hql
    rw [← hB] at hp1 hp2 hq1 hq2
    change _ = (natPoly (liftList p)).eval B at hp1
    change _ = (Kronecker.evenValue (natPoly (liftList p)) B : ℤ) -
      Kronecker.oddValue (natPoly (liftList p)) B at hp2
    change _ = (natPoly (liftList q)).eval B at hq1
    change _ = (Kronecker.evenValue (natPoly (liftList q)) B : ℤ) -
      Kronecker.oddValue (natPoly (liftList q)) B at hq2
    obtain ⟨a, ha⟩ : ∃ a, a = AzNat.kroneckerEvalPair w (p.coeffs.map (·.val)) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = AzNat.kroneckerEvalPair w (q.coeffs.map (·.val)) := ⟨_, rfl⟩
    rw [← ha] at hp1 hp2 ⊢
    rw [← hb] at hq1 hq2 ⊢
    obtain ⟨uv, huv⟩ : ∃ uv : AzNat × AzInt, uv = if p = q then
        (AzNat.square a.1, (AzNat.square a.2.abs).toAzInt) else (a.1 * b.1, a.2 * b.2) :=
      ⟨_, rfl⟩
    rw [← huv]
    have hu : uv.1.toNat = (natPoly (liftList p)).eval B * (natPoly (liftList q)).eval B := by
      rw [huv]
      split
      · next hpq =>
        subst hpq
        rw [AzNat.toNat_square, hp1, sq]
      · rw [AzNat.toNat_mul, hp1, hq1]
    have hv : uv.2.toInt =
        ((Kronecker.evenValue (natPoly (liftList p)) B : ℤ) -
          Kronecker.oddValue (natPoly (liftList p)) B) *
        ((Kronecker.evenValue (natPoly (liftList q)) B : ℤ) -
          Kronecker.oddValue (natPoly (liftList q)) B) := by
      rw [huv]
      split
      · next hpq =>
        subst hpq
        have hab : b = a := by rw [ha, hb]
        subst hab
        rw [AzNat.toInt_toAzInt, AzNat.toNat_square, Nat.cast_pow, AzNat.natCast_abs_toNat,
          sq_abs, hp2, sq]
      · rw [AzInt.toInt_mul, hp2, hq2]
    rw [AzNat.kroneckerCoeff2_toNat w (liftProd p q) (p.coeffs.size + q.coeffs.size - 1)
      (liftProd_coeff_eq_zero p q) (fun i hi => liftProd_coeff_lt p q i _ hi hspec) _ _
      (hB ▸ AzNat.kroneckerHalves_fst _ _ B uv.1 uv.2 hu hv)
      (hB ▸ AzNat.kroneckerHalves_snd _ _ B uv.1 uv.2 hu hv)]

@[simp] theorem toPoly_mulKronecker (p q : AzPolynomial (AzZMod m)) :
    AzPolynomial.toPoly (mulKronecker p q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  rw [mulKronecker_eq_mulBasecase, toPoly_mulBasecase]

@[simp] theorem toPoly_mulKronecker2 (p q : AzPolynomial (AzZMod m)) :
    AzPolynomial.toPoly (mulKronecker2 p q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  rw [mulKronecker2_eq_mulBasecase, toPoly_mulBasecase]

/-! ### Natural-number coefficients -/

/-- `n · 2^(64 s₁) · 2^(64 s₂) < 2^(64 (s₁ + s₂ + e))` when `n < 2^(64 e − c)`. -/
theorem kronecker_width_bound (s₁ s₂ e n t : ℕ) (hn : n < 2 ^ t) (ht : t ≤ 64 * e) :
    n * (2 ^ (64 * s₁) * 2 ^ (64 * s₂)) < 2 ^ (t + 64 * (s₁ + s₂)) ∧
      2 ^ (t + 64 * (s₁ + s₂)) ≤ 2 ^ (64 * (s₁ + s₂ + e)) := by
  constructor
  · rw [Nat.mul_add 64, pow_add, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hn (by positivity)
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem natList_getD (p : AzPolynomial AzNat) (i : ℕ) :
    (p.coeffs.toList.map AzNat.toNat).getD i 0 = (p.coeff i).toNat := by
  unfold coeff
  by_cases hi : i < p.coeffs.size
  · simp [List.getD, hi]
  · simp [List.getD, hi]

theorem mulKroneckerNat_eq_mulBasecase (p q : AzPolynomial AzNat) :
    mulKroneckerNat p q = mulBasecase p q := by
  unfold mulKroneckerNat mulBasecase
  split
  · rfl
  · next hne =>
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hne
    obtain ⟨hp, hq⟩ := hne
    dsimp only
    congr 1
    congr 1
    funext k
    obtain ⟨k, -⟩ := k
    dsimp only
    obtain ⟨n, hn⟩ : ∃ n, n = p.coeffs.size + q.coeffs.size := ⟨_, rfl⟩
    rw [← hn]
    obtain ⟨hb1, hb2⟩ := kronecker_width_bound (AzNat.maxLimbs p.coeffs)
      (AzNat.maxLimbs q.coeffs) ((n.log2 + 1 + 63) / 64) n (n.log2 + 1) Nat.lt_log2_self
      (by omega)
    apply AzNat.toNat_injective
    rw [AzNat.kroneckerCoeff_mul_toNat _ p.coeffs q.coeffs (2 ^ (64 * AzNat.maxLimbs p.coeffs))
      (2 ^ (64 * AzNat.maxLimbs q.coeffs))
      (fun c hc => (AzNat.toNat_lt_pow_maxLimbs _ c hc).le)
      (fun c hc => (AzNat.toNat_lt_pow_maxLimbs _ c hc).le)
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
      (hn ▸ lt_of_lt_of_le hb1 hb2)]
    change _ = AzNat.toNatRingHom _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, natList_getD, natList_getD]
    rfl

@[simp] theorem toPoly_mulKroneckerNat (p q : AzPolynomial AzNat) :
    AzPolynomial.toPoly (mulKroneckerNat p q) =
      AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  rw [mulKroneckerNat_eq_mulBasecase, toPoly_mulBasecase]

end Azurite.AzPolynomial

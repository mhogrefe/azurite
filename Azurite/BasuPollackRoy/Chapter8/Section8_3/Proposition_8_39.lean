import Azurite.BasuPollackRoy.Chapter8.Section8_3.StructureTheorem

/-!
# BPR Proposition 8.39 (Structure Theorem) — euclidean-division foundations

Working over a field `K` (where the euclidean division `P = C·Q + R` is available),
this file develops the ingredients of Proposition 8.39:

`sResP_j(P,Q) = ε_{p-q} · b_q^{p-r} · sResP_j(Q,-R)`  for `j < q-1`,

where `R = Rem(P,Q) = P % Q`, `C = P / Q`, and `r = deg R`.

So far: the degree bound on the quotient `C`, and the key identity expressing each
`R`-shift `X^e·R` as the corresponding `P`-shift `X^e·P` plus a `K`-linear combination
of the `Q`-shifts `X^{e+i}·Q` — the algebraic content of the `P`-rows → `R`-rows
replacement (the first step of the proof, via Lemma 8.28 / `pdetRing_update_add_combination'`).
-/

namespace Azurite.BPR.Chapter8

open Polynomial
open Azurite.BPR.Chapter4 (ε)

variable {K : Type*} [Field K]

/-- The quotient `P / Q` has degree at most `deg P - deg Q`. -/
theorem quotient_natDegree_le (P Q : K[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) :
    (P / Q).natDegree ≤ P.natDegree - Q.natDegree := by
  rcases eq_or_ne (P / Q) 0 with hC | hC
  · simp [hC]
  · have key : Q * (P / Q) = P - P % Q := by
      have h := EuclideanDomain.div_add_mod P Q; linear_combination h
    have hmod : (P % Q).natDegree ≤ Q.natDegree :=
      natDegree_le_natDegree (EuclideanDomain.mod_lt P hQ).le
    have h2 : (Q * (P / Q)).natDegree ≤ P.natDegree := by
      rw [key]
      exact le_trans (natDegree_sub_le _ _) (by rw [max_le_iff]; omega)
    rw [natDegree_mul hQ hC] at h2
    omega

/-- **Key identity for the `P → R` replacement.** Each shift `X^e·(P % Q)` of the remainder
    equals the corresponding shift `X^e·P` plus a `K`-linear combination of the shifts
    `X^{e+i}·Q` of `Q` (the coefficients being `-(P/Q).coeff i`). -/
theorem rem_shift_eq (P Q : K[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) (e : ℕ) :
    X ^ e * (P % Q)
      = X ^ e * P + ∑ i ∈ Finset.range (P.natDegree - Q.natDegree + 1),
          (-((P / Q).coeff i)) • (X ^ (e + i) * Q) := by
  have hCdeg := quotient_natDegree_le P Q hQ hpq
  have hCsum : ∑ i ∈ Finset.range (P.natDegree - Q.natDegree + 1), C ((P / Q).coeff i) * X ^ i
      = P / Q := by
    conv_rhs => rw [as_sum_range' (P / Q) (P.natDegree - Q.natDegree + 1) (by omega)]
    exact Finset.sum_congr rfl (fun i _ => C_mul_X_pow_eq_monomial)
  have hPR : P % Q = P - Q * (P / Q) := by
    have h := EuclideanDomain.div_add_mod P Q; linear_combination h
  have hsum : ∑ i ∈ Finset.range (P.natDegree - Q.natDegree + 1),
        (-((P / Q).coeff i)) • (X ^ (e + i) * Q) = -(X ^ e * Q * (P / Q)) := by
    have step : ∀ i, (-((P / Q).coeff i)) • (X ^ (e + i) * Q)
        = -(X ^ e * Q * (C ((P / Q).coeff i) * X ^ i)) := by
      intro i; rw [smul_eq_C_mul, map_neg, pow_add]; ring
    simp only [step]
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hCsum]
  rw [hPR, hsum]; ring

/-- The euclidean remainder is `K`-linear in its first argument:
    `Rem(c·P, Q) = c·Rem(P, Q)`. -/
theorem rem_C_mul (c : K) (P Q : K[X]) : (C c * P) % Q = C c * (P % Q) := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hd : (C c * (P % Q)).degree < Q.degree := by
    rw [degree_mul, degree_C hc, zero_add]; exact degree_mod_lt P hQ
  have hrw : C c * P = C c * (P % Q) + Q * (C c * (P / Q)) := by
    have h := EuclideanDomain.div_add_mod P Q; linear_combination (-C c) * h
  rw [hrw, Polynomial.add_mod, (mod_eq_self_iff hQ).mpr hd,
    EuclideanDomain.mod_eq_zero.mpr (dvd_mul_right Q _), add_zero]

/-- The `sResP`-sequence with the first `k` of the `P`-block rows replaced by the
    corresponding `R`-block rows (`R = P % Q`). `k = 0` is the `(P,Q)`-sequence,
    `k = q-j` is the `(R,Q)`-sequence. -/
private noncomputable def replaceUpTo (P Q : K[X]) (j k : ℕ) :
    Fin (P.natDegree + Q.natDegree - 2 * j) → K[X] := fun r =>
  if (r : ℕ) < Q.natDegree - j then
    (if (r : ℕ) < k then X ^ (Q.natDegree - j - 1 - (r : ℕ)) * (P % Q)
     else X ^ (Q.natDegree - j - 1 - (r : ℕ)) * P)
  else X ^ ((r : ℕ) - (Q.natDegree - j)) * Q

/-- **Lemma 8.39, step 1 (`P → R` replacement).** Replacing the `P`-block rows of the
    `sResP`-sequence by the corresponding `R`-block rows does not change `pdet`. -/
theorem pdetRing_replaceUpTo_eq (P Q : K[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (j : ℕ) (hj : j < Q.natDegree) :
    pdetRing (P.natDegree + Q.natDegree - j) (replaceUpTo P Q j (Q.natDegree - j))
      = pdetRing (P.natDegree + Q.natDegree - j) (replaceUpTo P Q j 0) := by
  have hstep : ∀ k, k < Q.natDegree - j →
      pdetRing (P.natDegree + Q.natDegree - j) (replaceUpTo P Q j (k + 1))
        = pdetRing (P.natDegree + Q.natDegree - j) (replaceUpTo P Q j k) := by
    intro k hk
    have hrk : k < P.natDegree + Q.natDegree - 2 * j := by omega
    set Qidx : Fin (P.natDegree - Q.natDegree + 1) → Fin (P.natDegree + Q.natDegree - 2 * j) :=
      fun i => ⟨(Q.natDegree - j) + (Q.natDegree - j - 1 - k + (i : ℕ)), by have := i.isLt; omega⟩
      with hQidx
    have heq : replaceUpTo P Q j (k + 1)
        = Function.update (replaceUpTo P Q j k) ⟨k, hrk⟩
            (X ^ (Q.natDegree - j - 1 - k) * (P % Q)) := by
      ext r
      rw [Function.update_apply]
      by_cases hr : r = ⟨k, hrk⟩
      · rw [ite_eq_left hr, hr]
        simp only [replaceUpTo, ite_eq_left hk, ite_eq_left (Nat.lt_succ_self k)]
      · rw [ite_eq_right hr]
        have hrk' : (r : ℕ) ≠ k := fun h => hr (Fin.ext h)
        simp only [replaceUpTo]
        by_cases h1 : (r : ℕ) < Q.natDegree - j
        · rw [ite_eq_left h1, ite_eq_left h1]
          rcases lt_trichotomy (r : ℕ) k with h2 | h2 | h2
          · rw [ite_eq_left (by omega), ite_eq_left h2]
          · exact absurd h2 hrk'
          · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        · rw [ite_eq_right h1, ite_eq_right h1]
    have hk_row : (replaceUpTo P Q j k) ⟨k, hrk⟩ = X ^ (Q.natDegree - j - 1 - k) * P := by
      simp only [replaceUpTo, ite_eq_left hk, ite_eq_right (Nat.lt_irrefl k)]
    have hQ_row : ∀ i : Fin (P.natDegree - Q.natDegree + 1),
        (replaceUpTo P Q j k) (Qidx i) = X ^ (Q.natDegree - j - 1 - k + (i : ℕ)) * Q := by
      intro i
      simp only [replaceUpTo, hQidx]
      rw [ite_eq_right (by omega)]
      congr 2
      omega
    have hval : (replaceUpTo P Q j k) ⟨k, hrk⟩
          + ∑ i : Fin (P.natDegree - Q.natDegree + 1),
              (-((P / Q).coeff (i : ℕ))) • (replaceUpTo P Q j k) (Qidx i)
        = X ^ (Q.natDegree - j - 1 - k) * (P % Q) := by
      rw [hk_row, Finset.sum_congr rfl (fun i _ => by rw [hQ_row i]),
        Fin.sum_univ_eq_sum_range
          (fun i => (-((P / Q).coeff i)) • (X ^ (Q.natDegree - j - 1 - k + i) * Q))
          (P.natDegree - Q.natDegree + 1)]
      exact (rem_shift_eq P Q hQ hpq (Q.natDegree - j - 1 - k)).symm
    rw [heq, ← hval]
    exact pdetRing_update_add_combination' (replaceUpTo P Q j k) ⟨k, hrk⟩ Finset.univ Qidx
      (fun i => -((P / Q).coeff (i : ℕ)))
      (fun i _ => Fin.ne_of_val_ne (by simp only [hQidx]; omega))
  suffices hsuff : ∀ k, k ≤ Q.natDegree - j →
      pdetRing (P.natDegree + Q.natDegree - j) (replaceUpTo P Q j k)
        = pdetRing (P.natDegree + Q.natDegree - j) (replaceUpTo P Q j 0) from
    hsuff (Q.natDegree - j) (le_refl _)
  intro k
  induction k with
  | zero => intro _; rfl
  | succ d ih => intro hd; rw [hstep d (by omega), ih (by omega)]

private theorem aux1 (p q j r : ℕ) (_h : r < p - j) (hjq : j < q) (_hqp : q < p) :
    p - j - 1 - r = p + q - 2 * j - 1 - r - (q - j) := by omega
private theorem aux2 (p q j r : ℕ) (h : p - j ≤ r) (hr : r < p + q - 2 * j) (hjq : j < q)
    (_hqp : q < p) : r - (p - j) = q - j - 1 - (p + q - 2 * j - 1 - r) := by omega
private theorem aux_cond1 (p q j r : ℕ) (h : r < p - j) (hjq : j < q) (_hqp : q < p) :
    ¬ (p + q - 2 * j - 1 - r < q - j) := by omega
private theorem aux_cond2 (p q j r : ℕ) (h : p - j ≤ r) (hr : r < p + q - 2 * j) (hjq : j < q)
    (hqp : q < p) : p + q - 2 * j - 1 - r < q - j := by omega
private theorem aux_card (p q j : ℕ) (hjq : j < q) (hqp : q < p) :
    p + q - 2 * j - (p - j) = q - j := by omega

/-- The `A_j` sequence `X^{p-j-1}Q, …, Q, -R, …, -X^{q-j-1}R` (with `R = P % Q`). -/
private noncomputable def Aseq (P Q : K[X]) (j : ℕ) :
    Fin (P.natDegree + Q.natDegree - 2 * j) → K[X] := fun r =>
  if (r : ℕ) < P.natDegree - j then X ^ (P.natDegree - j - 1 - (r : ℕ)) * Q
  else -(X ^ ((r : ℕ) - (P.natDegree - j)) * (P % Q))

/-- **Lemma 8.39, steps 1–3.** `sResP_j(P,Q) = ε_{p-q} · A_j`, where `A_j` is the
    determinant of the `A_j`-sequence (the `(R,Q)`-sequence reversed and with its
    `R`-block negated). -/
theorem sResP_eq_eps_smul_Aseq (P Q : K[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree)
    (j : ℕ) (hj : j < Q.natDegree) :
    sResP P Q j
      = (ε (P.natDegree - Q.natDegree) : ℤ)
        • pdetRing (P.natDegree + Q.natDegree - j) (Aseq P Q j) := by
  -- `pdetRing` of the `(R,Q)`-sequence equals `sResP`
  have hb : pdetRing (P.natDegree + Q.natDegree - j) (replaceUpTo P Q j 0) = sResP P Q j := by
    have hseq : replaceUpTo P Q j 0 = fun r : Fin (P.natDegree + Q.natDegree - 2 * j) =>
        if (r : ℕ) < Q.natDegree - j then
        X ^ (Q.natDegree - j - 1 - (r : ℕ)) * P else X ^ ((r : ℕ) - (Q.natDegree - j)) * Q := by
      funext r; simp only [replaceUpTo, Nat.not_lt_zero, ite_false]
    rw [hseq, sResP, ite_eq_left (by omega)]
  have hRQ : pdetRing (P.natDegree + Q.natDegree - j)
      (replaceUpTo P Q j (Q.natDegree - j)) = sResP P Q j := by
    rw [pdetRing_replaceUpTo_eq P Q hQ hpq j (by omega), hb]
  -- the `(R,Q)`-sequence in closed form
  have hseqRQ : ∀ s : Fin (P.natDegree + Q.natDegree - 2 * j),
      replaceUpTo P Q j (Q.natDegree - j) s
        = if (s : ℕ) < Q.natDegree - j then X ^ (Q.natDegree - j - 1 - (s : ℕ)) * (P % Q)
          else X ^ ((s : ℕ) - (Q.natDegree - j)) * Q := by
    intro s; by_cases h : (s : ℕ) < Q.natDegree - j <;> simp [replaceUpTo, h]
  -- the `A_j`-sequence is the `R`-block negation of the reversed `(R,Q)`-sequence
  set s : Finset (Fin (P.natDegree + Q.natDegree - 2 * j)) :=
    Finset.univ.filter (fun r => P.natDegree - j ≤ (r : ℕ)) with hs
  have hAeq : Aseq P Q j
      = fun r => if r ∈ s then -((replaceUpTo P Q j (Q.natDegree - j) ∘ ⇑Fin.revPerm) r)
                 else (replaceUpTo P Q j (Q.natDegree - j) ∘ ⇑Fin.revPerm) r := by
    ext r
    have hrlt := r.isLt
    have hrev : ((Fin.revPerm r : Fin (P.natDegree + Q.natDegree - 2 * j)) : ℕ)
        = P.natDegree + Q.natDegree - 2 * j - 1 - (r : ℕ) := by
      rw [show (Fin.revPerm r : Fin (P.natDegree + Q.natDegree - 2 * j)) = Fin.rev r from rfl,
        Fin.val_rev]; omega
    rw [hs]
    simp only [Function.comp_apply, hseqRQ, Finset.mem_filter, Finset.mem_univ, true_and, hrev, Aseq]
    by_cases h : (r : ℕ) < P.natDegree - j
    · rw [ite_eq_left h, ite_eq_right (not_le.mpr h),
        ite_eq_right (aux_cond1 _ _ _ _ h (by omega) hpq), aux1 _ _ _ _ h (by omega) hpq]
    · rw [ite_eq_right h, ite_eq_left (not_lt.mp h),
        ite_eq_left (aux_cond2 _ _ _ _ (not_lt.mp h) hrlt (by omega) hpq),
        aux2 _ _ _ _ (not_lt.mp h) hrlt (by omega) hpq]
  have hcard : s.card = Q.natDegree - j := by
    rw [hs, show (Finset.univ.filter (fun r : Fin (P.natDegree + Q.natDegree - 2 * j) =>
        P.natDegree - j ≤ (r : ℕ))) = Finset.Ici (⟨P.natDegree - j, by omega⟩) from by
      ext r; simp [Finset.mem_filter, Finset.mem_Ici, Fin.le_def], Fin.card_Ici]
    exact aux_card _ _ _ (by omega) hpq
  -- assemble: `pdetRing (Aseq) = ε_{p-q} • sResP`
  have hA : pdetRing (P.natDegree + Q.natDegree - j) (Aseq P Q j)
      = (ε (P.natDegree - Q.natDegree) : ℤ) • sResP P Q j := by
    rw [hAeq, pdetRing_neg_rows, hcard, pdetRing_comp_perm, Azurite.BPR.Chapter4.sign_revPerm,
      smul_smul, hRQ]
    congr 1
    have hε := Azurite.BPR.Chapter4.ε_sub_two_mul (P.natDegree + Q.natDegree - 2 * j)
      (Q.natDegree - j) (by omega)
    rw [show P.natDegree + Q.natDegree - 2 * j - 2 * (Q.natDegree - j) = P.natDegree - Q.natDegree
      from by omega] at hε
    rw [hε]
  -- conclude
  rw [hA, smul_smul, show (ε (P.natDegree - Q.natDegree) : ℤ) * ε (P.natDegree - Q.natDegree) = 1
    from by rw [Azurite.BPR.Chapter4.ε, ← pow_add]; exact Even.neg_one_pow ⟨_, rfl⟩, one_smul]

private theorem aux_ndeg (p q j i : ℕ) (hi : i < p - j) : q + (p - j - 1 - i) = p + q - j - 1 - i := by
  omega
private theorem aux_tailQ (p q j r i : ℕ) (_hjr : j ≤ r) (hrq : r < q) (hqp : q < p)
    (_hi : (p - r) + i < p - j) : p - j - 1 - ((p - r) + i) = r - j - 1 - i := by omega
private theorem aux_tailR (p q j r i : ℕ) (hjr : j ≤ r) (hrq : r < q) (hqp : q < p)
    (hi : ¬ ((p - r) + i < p - j)) : (p - r) + i - (p - j) = i - (r - j) := by omega
private theorem aux_hd2 (p q j r i k : ℕ) (hi : i < p + q - 2 * j) (hipj : ¬ (i < p - j))
    (hk : p + q - j - 1 - (p - r) < k) (hjr : j ≤ r) (hrq : r < q) (hqp : q < p) :
    r + (i - (p - j)) < k := by omega
private theorem aux_condpos (p q j r i : ℕ) (hjr : j ≤ r) (hrq : r < q) (_hqp : q < p)
    (h : i < r - j) : (p - r) + i < p - j := by omega
private theorem aux_condneg (p q j r i : ℕ) (hjr : j ≤ r) (hrq : r < q) (_hqp : q < p)
    (h : ¬ (i < r - j)) : ¬ ((p - r) + i < p - j) := by omega
private theorem aux_prodcond (p q j r i : ℕ) (hi : i < p - r) (hjr : j ≤ r) (_hqp : q < p) :
    i < p - j := by omega

/-- **Lemma 8.39, step 4 (triangular peel), case `j ≤ r`.** `A_j = b_q^{p-r} · sResP_j(Q,-R)`. -/
theorem Aseq_triangular (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (j : ℕ) (_hj : j < Q.natDegree - 1)
    (hjr : j ≤ (P % Q).natDegree) :
    pdetRing (P.natDegree + Q.natDegree - j) (Aseq P Q j)
      = Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) • sResP Q (-(P % Q)) j := by
  set r := (P % Q).natDegree with hr_def
  have hrq : r < Q.natDegree := natDegree_lt_natDegree hR0 (EuclideanDomain.mod_lt P hQ)
  have hnd1 : ∀ i : Fin (P.natDegree + Q.natDegree - 2 * j), (i : ℕ) < P.natDegree - j →
      (Aseq P Q j i).natDegree = P.natDegree + Q.natDegree - j - 1 - (i : ℕ) := by
    intro i hi
    rw [Aseq, ite_eq_left hi, natDegree_X_pow_mul _ hQ]; exact aux_ndeg _ _ _ _ hi
  have hnd2 : ∀ i : Fin (P.natDegree + Q.natDegree - 2 * j), ¬ ((i : ℕ) < P.natDegree - j) →
      (Aseq P Q j i).natDegree = r + ((i : ℕ) - (P.natDegree - j)) := by
    intro i hi
    rw [Aseq, ite_eq_right hi, natDegree_neg, natDegree_X_pow_mul _ hR0]
  rw [pdetRing_triangular (m := P.natDegree + Q.natDegree - 2 * j)
      (n := P.natDegree + Q.natDegree - j) (ℓ := P.natDegree - r) (by omega) (by omega)
      (Aseq P Q j) ?hd1 ?hd2]
  case hd1 =>
    intro i hi k hk
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnd1 i (by omega)]; omega
  case hd2 =>
    intro i hi k hk
    apply coeff_eq_zero_of_natDegree_lt
    by_cases h : (i : ℕ) < P.natDegree - j
    · rw [hnd1 i h]; omega
    · rw [hnd2 i h]; exact aux_hd2 _ _ _ _ _ _ i.isLt h hk hjr hrq hpq
  -- the leading-coefficient product is `b_q^{p-r}`
  have hprod : (∏ i : Fin (P.natDegree - r),
      (Aseq P Q j ⟨(i : ℕ), by omega⟩).coeff (P.natDegree + Q.natDegree - j - 1 - (i : ℕ)))
      = Q.leadingCoeff ^ (P.natDegree - r) := by
    rw [Finset.prod_congr rfl (fun i _ => ?_), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hi := i.isLt
    show (Aseq P Q j ⟨(i : ℕ), _⟩).coeff (P.natDegree + Q.natDegree - j - 1 - (i : ℕ)) = Q.leadingCoeff
    rw [Aseq, ite_eq_left (aux_prodcond _ _ _ _ _ hi hjr hpq),
      (aux_ndeg P.natDegree Q.natDegree j (i : ℕ) (aux_prodcond _ _ _ _ _ hi hjr hpq)).symm,
      coeff_X_pow_mul, Polynomial.coeff_natDegree]
  -- the tail is the `sResP(Q,-R)` sequence
  have htail : sResP Q (-(P % Q)) j
      = pdetRing (P.natDegree + Q.natDegree - j - (P.natDegree - r))
          (fun i' : Fin (P.natDegree + Q.natDegree - 2 * j - (P.natDegree - r)) =>
            Aseq P Q j ⟨P.natDegree - r + (i' : ℕ), by omega⟩) := by
    rw [sResP, ite_eq_left (by rw [natDegree_neg]; omega),
      show Q.natDegree + (-(P % Q)).natDegree - j = P.natDegree + Q.natDegree - j - (P.natDegree - r)
        from by rw [natDegree_neg]; omega]
    apply pdetRing_congr_cast (by rw [natDegree_neg]; omega)
    intro i'
    simp only [Fin.val_cast, natDegree_neg, ← hr_def]
    by_cases h : (i' : ℕ) < r - j
    · rw [ite_eq_left h, Aseq, ite_eq_left (aux_condpos _ _ _ _ _ hjr hrq hpq h),
        aux_tailQ _ _ _ _ _ hjr hrq hpq (aux_condpos _ _ _ _ _ hjr hrq hpq h)]
    · rw [ite_eq_right h, Aseq, ite_eq_right (aux_condneg _ _ _ _ _ hjr hrq hpq h),
        aux_tailR _ _ _ _ _ hjr hrq hpq (aux_condneg _ _ _ _ _ hjr hrq hpq h), mul_neg]
  rw [hprod, htail, smul_eq_C_mul]

private theorem aux_zerodeg (p q j r i : ℕ) (hr : r < j) (hi : i < p + q - 2 * j - (p - j))
    (hjq : j < q) (hqp : q < p) :
    r + ((p - j + i) - (p - j)) < p + q - j - (p - j) - 1 := by omega
private theorem aux_hd2z (p q j r i k : ℕ) (hi : p - j ≤ i) (hik : i < p + q - 2 * j)
    (hk : p + q - j - 1 - (p - j) < k) (hr : r < j) (_hjq : j < q) (_hqp : q < p) :
    r + (i - (p - j)) < k := by omega
private theorem aux_zfin (p q j i : ℕ) (hi : i < p + q - 2 * j - (p - j)) (hjq : j < q)
    (hqp : q < p) : p - j + i < p + q - 2 * j := by omega

/-- **Lemma 8.39, step 4 (triangular peel), case `r < j`.** `A_j = 0`. -/
theorem Aseq_zero (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (j : ℕ) (hj : j < Q.natDegree - 1)
    (hjr : (P % Q).natDegree < j) :
    pdetRing (P.natDegree + Q.natDegree - j) (Aseq P Q j) = 0 := by
  set r := (P % Q).natDegree with hr_def
  have hnd1 : ∀ i : Fin (P.natDegree + Q.natDegree - 2 * j), (i : ℕ) < P.natDegree - j →
      (Aseq P Q j i).natDegree = P.natDegree + Q.natDegree - j - 1 - (i : ℕ) := by
    intro i hi
    rw [Aseq, ite_eq_left hi, natDegree_X_pow_mul _ hQ]; exact aux_ndeg _ _ _ _ hi
  have hnd2 : ∀ i : Fin (P.natDegree + Q.natDegree - 2 * j), ¬ ((i : ℕ) < P.natDegree - j) →
      (Aseq P Q j i).natDegree = r + ((i : ℕ) - (P.natDegree - j)) := by
    intro i hi
    rw [Aseq, ite_eq_right hi, natDegree_neg, natDegree_X_pow_mul _ hR0]
  rw [pdetRing_triangular (m := P.natDegree + Q.natDegree - 2 * j)
      (n := P.natDegree + Q.natDegree - j) (ℓ := P.natDegree - j) (by omega) (by omega)
      (Aseq P Q j) ?hd1 ?hd2]
  case hd1 =>
    intro i hi k hk
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnd1 i hi]; omega
  case hd2 =>
    intro i hi k hk
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnd2 i (not_lt.mpr hi)]; exact aux_hd2z _ _ _ _ _ _ hi i.isLt hk hjr (by omega) hpq
  rw [pdetRing_eq_zero_of_degree_lt (by omega)
      (fun i' : Fin (P.natDegree + Q.natDegree - 2 * j - (P.natDegree - j)) =>
        Aseq P Q j ⟨P.natDegree - j + (i' : ℕ), aux_zfin _ _ _ _ i'.isLt (by omega) hpq⟩)
      (fun i' => ?_), mul_zero]
  rw [Aseq, ite_eq_right (not_lt.mpr (Nat.le_add_right _ _)), degree_neg]
  have hne : X ^ (P.natDegree - j + (i' : ℕ) - (P.natDegree - j)) * (P % Q) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hR0
  rw [degree_eq_natDegree hne, natDegree_X_pow_mul _ hR0]
  exact_mod_cast aux_zerodeg _ _ _ _ _ hjr i'.isLt (by omega) hpq

private theorem aux_qm1card (p q : ℕ) (hqp : q < p) (hq1 : 1 ≤ q) : p - (q - 1) = p - q + 1 := by omega

/-- **Theorem 8.34, base case ingredient.** The `A_{q-1}`-determinant: peel the whole
    `Q`-block, leaving the single `-R` row. `A_{q-1} = -b_q^{p-q+1} · R`. -/
theorem Aseq_qm1 (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    pdetRing (P.natDegree + Q.natDegree - (Q.natDegree - 1)) (Aseq P Q (Q.natDegree - 1))
      = -(Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1) • (P % Q)) := by
  set r := (P % Q).natDegree with hr_def
  have hrq : r < Q.natDegree := natDegree_lt_natDegree hR0 (EuclideanDomain.mod_lt P hQ)
  have hnd1 : ∀ i : Fin (P.natDegree + Q.natDegree - 2 * (Q.natDegree - 1)),
      (i : ℕ) < P.natDegree - (Q.natDegree - 1) →
      (Aseq P Q (Q.natDegree - 1) i).natDegree
        = P.natDegree + Q.natDegree - (Q.natDegree - 1) - 1 - (i : ℕ) := by
    intro i hi
    rw [Aseq, ite_eq_left hi, natDegree_X_pow_mul _ hQ]; omega
  have hnd2 : ∀ i : Fin (P.natDegree + Q.natDegree - 2 * (Q.natDegree - 1)),
      ¬ ((i : ℕ) < P.natDegree - (Q.natDegree - 1)) →
      (Aseq P Q (Q.natDegree - 1) i).natDegree = r + ((i : ℕ) - (P.natDegree - (Q.natDegree - 1))) := by
    intro i hi
    rw [Aseq, ite_eq_right hi, natDegree_neg, natDegree_X_pow_mul _ hR0]
  rw [pdetRing_triangular (m := P.natDegree + Q.natDegree - 2 * (Q.natDegree - 1))
      (n := P.natDegree + Q.natDegree - (Q.natDegree - 1)) (ℓ := P.natDegree - (Q.natDegree - 1))
      (by omega) (by omega) (Aseq P Q (Q.natDegree - 1)) ?hd1 ?hd2]
  case hd1 =>
    intro i hi k hk
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnd1 i (by omega)]; omega
  case hd2 =>
    intro i hi k hk
    apply coeff_eq_zero_of_natDegree_lt
    rw [hnd2 i (not_lt.mpr hi)]; have := i.isLt; omega
  have hprod : (∏ i : Fin (P.natDegree - (Q.natDegree - 1)),
      (Aseq P Q (Q.natDegree - 1) ⟨(i : ℕ), by omega⟩).coeff
        (P.natDegree + Q.natDegree - (Q.natDegree - 1) - 1 - (i : ℕ)))
      = Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1) := by
    rw [Finset.prod_congr rfl (fun i _ => ?_), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      aux_qm1card _ _ hpq hq1]
    have hi := i.isLt
    show (Aseq P Q (Q.natDegree - 1) ⟨(i : ℕ), _⟩).coeff
      (P.natDegree + Q.natDegree - (Q.natDegree - 1) - 1 - (i : ℕ)) = Q.leadingCoeff
    rw [Aseq, ite_eq_left (by omega), show P.natDegree + Q.natDegree - (Q.natDegree - 1) - 1 - (i : ℕ)
      = Q.natDegree + (P.natDegree - (Q.natDegree - 1) - 1 - (i : ℕ)) from by omega,
      coeff_X_pow_mul, Polynomial.coeff_natDegree]
  have htail0 : Aseq P Q (Q.natDegree - 1)
      ⟨P.natDegree - (Q.natDegree - 1) + (0 : ℕ), by omega⟩ = -(P % Q) := by
    rw [Aseq, ite_eq_right (not_lt.mpr (Nat.le_add_right _ _))]
    simp
  rw [hprod, pdetRing_single_of_eq (by omega) (by omega) _ (by rw [htail0, natDegree_neg]; omega),
    htail0, mul_neg, smul_eq_C_mul]

/-- **Theorem 8.34, base-case formula.** `sResP_{q-1}(P,Q) = -ε_{p-q} · b_q^{p-q+1} · R`. -/
theorem sResP_natDegree_sub_one (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    sResP P Q (Q.natDegree - 1)
      = -((ε (P.natDegree - Q.natDegree) : ℤ)
          • (Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1) • (P % Q))) := by
  rw [sResP_eq_eps_smul_Aseq P Q hQ hpq (Q.natDegree - 1) (by omega), Aseq_qm1 P Q hQ hR0 hpq hq1]
  exact smul_neg _ _

/-- **Theorem 8.34, base case (BPR phrasing).** With `s_q = sRes_q(P,Q)`,
    `t_{p-1} = lcof(sResP_{p-1}(P,Q))`, `sResP_p = P`, `sResP_{p-1} = Q`,
    `sResP_{q-1}(P,Q) = -Rem(s_q · t_{p-1} · sResP_p, sResP_{p-1})`. -/
theorem sResP_natDegree_sub_one_rem (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree + 1 < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    sResP P Q (Q.natDegree - 1)
      = -((C (Azurite.BPR.Chapter4.sRes P Q Q.natDegree)
            * C (sResP P Q (P.natDegree - 1)).leadingCoeff
            * sResP P Q P.natDegree) % sResP P Q (P.natDegree - 1)) := by
  rw [sResP_natDegree_sub_one P Q hQ hR0 (by omega) hq1, sResP_eq_self_Q P Q hpq,
    sResP_eq_self P Q (by omega), sRes_natDegree P Q (by omega) hQ, ← C_mul, rem_C_mul]
  congr 1
  rw [smul_eq_C_mul, zsmul_eq_mul, zsmul_eq_mul, ← C_eq_intCast, pow_succ, C_mul, C_mul, C_mul]
  ring

/-- **BPR Proposition 8.39.** `sResP_j(P,Q) = ε_{p-q} · b_q^{p-r} · sResP_j(Q,-R)` for
    `j < q-1`, with `R = P % Q` and `r = deg R`. -/
theorem proposition_8_39 (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (j : ℕ) (hj : j < Q.natDegree - 1) :
    sResP P Q j = (ε (P.natDegree - Q.natDegree) : ℤ)
      • (Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) • sResP Q (-(P % Q)) j) := by
  rw [sResP_eq_eps_smul_Aseq P Q hQ hpq j (by omega)]
  congr 1
  rcases le_or_gt j (P % Q).natDegree with hjr | hjr
  · exact Aseq_triangular P Q hQ hR0 hpq j hj hjr
  · rw [Aseq_zero P Q hQ hR0 hpq j hj hjr,
      sResP_eq_zero Q (-(P % Q)) (by rw [natDegree_neg]; exact hjr) (by omega) (by omega), smul_zero]

end Azurite.BPR.Chapter8

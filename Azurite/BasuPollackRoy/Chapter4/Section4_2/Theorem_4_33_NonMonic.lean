/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_2.Theorem_4_33
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SignedPseudoRemainder

/-!
# BPR Theorem 4.33, non-monic case: exact over an ordered domain

The monic statement `theorem_4_33` requires `P` monic so the remainder
`(P′·Q) %ₘ P` stays in `D[X]`. For non-monic `P` (the practical `ℤ[X]` case),
we use the **signed pseudo-remainder** `pr ∈ D[X]` (Azurite's `PRem`, scaled by
`lc(P)^d` with `d = pRemExp` *even*), which stays in `D[X]` without division.

Because the scaling exponent is even, `lc(P)^d` is a nonzero square, hence
**positive**, so scaling the second argument of `sRes` by it preserves every
sign — and therefore `PmV`. Thus, after mapping into the real closed field `R`
via the order embedding `f`, the pseudo-remainder sequence has the same `PmV` as
the genuine remainder sequence, and the real-closed-field engine
`theorem_4_33_realClosed` finishes the job. No `sign(lc P)` corrections appear,
and the Cauchy-index engine is reused unchanged.

Key new ingredients:
* `PmV_eq_of_sign_eq` — `PmV` depends only on the list of signs;
* `sRes_smul_right_det` / `sRes_sign_smul_right` — `sRes` homogeneity under
  scaling the second argument by a constant (signs preserved for a positive one);
* the pseudo-remainder/remainder bridge over `R`.
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial

section PmVSign

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem dropWhile_map' {α β : Type*} (g : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map g).dropWhile p = (l.dropWhile (fun x => p (g x))).map g
  | [] => rfl
  | a :: l => by
    by_cases h : p (g a)
    · rw [List.map_cons, List.dropWhile_cons_of_pos h,
        List.dropWhile_cons_of_pos (p := fun x => p (g x)) (a := a) (l := l) (by simpa using h),
        dropWhile_map' g p l]
    · rw [List.map_cons, List.dropWhile_cons_of_neg h,
        List.dropWhile_cons_of_neg (p := fun x => p (g x)) (a := a) (l := l) (by simpa using h),
        List.map_cons]

omit [IsStrictOrderedRing K] in
/-- `dropWhile (· = 0)` commutes with `map sign` (since `sign x = 0 ↔ x = 0`). -/
private theorem dropWhile_zero_map_sign (l : List K) :
    (l.dropWhile (fun x => decide (x = 0))).map SignType.sign
      = (l.map SignType.sign).dropWhile (fun s => decide (s = 0)) := by
  rw [dropWhile_map' SignType.sign (fun s => decide (s = 0)) l]
  have hpred : (fun x : K => decide (x = 0)) = (fun x : K => decide (SignType.sign x = 0)) := by
    funext x; exact decide_eq_decide.mpr sign_eq_zero_iff.symm
  rw [hpred]

omit [IsStrictOrderedRing K] in
/-- `PmV` unfolding when the next nonzero after the head does not exist. -/
private theorem PmV_cons_dropWhile_nil (sp : K) (rest : List K)
    (hL : rest.dropWhile (fun x => decide (x = 0)) = []) : PmV (sp :: rest) = 0 := by
  rw [PmV]
  split
  · rfl
  · next sq tl h => rw [hL] at h; simp at h

omit [IsStrictOrderedRing K] in
/-- `PmV` unfolding when the next nonzero after the head is `sq`. -/
private theorem PmV_cons_dropWhile_cons (sp sq : K) (rest tl : List K)
    (hL : rest.dropWhile (fun x => decide (x = 0)) = sq :: tl) :
    PmV (sp :: rest) = PmV (sq :: tl) +
      (if Odd (rest.length + 1 - (sq :: tl).length) then
        ε (rest.length + 1 - (sq :: tl).length) * (SignType.sign (sp * sq) : ℤ) else 0) := by
  rw [PmV]
  split
  · next h => rw [hL] at h; simp at h
  · next sq2 tl2 h => rw [hL] at h; obtain ⟨rfl, rfl⟩ := List.cons.inj h; rfl

/-- **`PmV` depends only on the signs.** Two lists with equal lists of signs have
equal `PmV` (the recursion only reads zero-tests and sign-products). -/
theorem PmV_eq_of_sign_eq (l l' : List K)
    (h : l.map SignType.sign = l'.map SignType.sign) : PmV l = PmV l' := by
  suffices key : ∀ n (l l' : List K), l.length ≤ n →
      l.map SignType.sign = l'.map SignType.sign → PmV l = PmV l' from
    key l.length l l' le_rfl h
  intro n
  induction n with
  | zero =>
    intro l l' hn hmap
    obtain rfl : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
    rw [List.map_nil, eq_comm, List.map_eq_nil_iff] at hmap
    subst hmap
    rfl
  | succ n ih =>
    intro l l' hn hmap
    rcases l with _ | ⟨sp, rest⟩
    · rcases l' with _ | ⟨sp', rest'⟩
      · rfl
      · simp at hmap
    · rcases l' with _ | ⟨sp', rest'⟩
      · simp at hmap
      · simp only [List.map_cons, List.cons.injEq] at hmap
        obtain ⟨hsign, hrest⟩ := hmap
        have hlen : rest.length = rest'.length := by simpa using congrArg List.length hrest
        have hdrop : (rest.dropWhile (fun x => decide (x = 0))).map SignType.sign
            = (rest'.dropWhile (fun x => decide (x = 0))).map SignType.sign := by
          rw [dropWhile_zero_map_sign, dropWhile_zero_map_sign, hrest]
        rcases hd : rest.dropWhile (fun x => decide (x = 0)) with _ | ⟨sq, tl⟩
        · rw [PmV_cons_dropWhile_nil sp rest hd]
          rcases hd' : rest'.dropWhile (fun x => decide (x = 0)) with _ | ⟨sq', tl'⟩
          · rw [PmV_cons_dropWhile_nil sp' rest' hd']
          · rw [hd, hd'] at hdrop; simp at hdrop
        · rw [PmV_cons_dropWhile_cons sp sq rest tl hd]
          rcases hd' : rest'.dropWhile (fun x => decide (x = 0)) with _ | ⟨sq', tl'⟩
          · rw [hd, hd'] at hdrop; simp at hdrop
          · rw [PmV_cons_dropWhile_cons sp' sq' rest' tl' hd']
            rw [hd, hd'] at hdrop
            simp only [List.map_cons, List.cons.injEq] at hdrop
            obtain ⟨hsq, htl⟩ := hdrop
            have htllen : tl.length = tl'.length := by simpa using congrArg List.length htl
            have hsgn : SignType.sign (sp * sq) = SignType.sign (sp' * sq') := by
              rw [sign_mul, sign_mul, hsign, hsq]
            have hsublen : (sq :: tl).length ≤ n := by
              have hle := List.length_dropWhile_le (fun x => decide (x = 0)) rest
              rw [hd] at hle
              simp only [List.length_cons] at hn hle ⊢
              omega
            rw [ih (sq :: tl) (sq' :: tl') hsublen
              (by simp only [List.map_cons, List.cons.injEq]; exact ⟨hsq, htl⟩), hlen]
            simp only [List.length_cons, htllen]
            rw [hsgn]

end PmVSign

/-! ### `sRes` homogeneity: scaling the second argument by a constant -/

section Homogeneity

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsDomain D] in
private theorem prod_ite_one_const (c : D) (m N : ℕ) :
    ∏ i : Fin N, (if i.val < m then (1 : D) else c) = c ^ (N - m) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Fin.val_last]
    have hcong : (∏ x : Fin n, if (x.castSucc).val < m then (1 : D) else c)
        = c ^ (n - m) := by
      rw [← ih]; exact Finset.prod_congr rfl (fun x _ => by rw [Fin.val_castSucc])
    rw [hcong]
    by_cases h : n < m
    · rw [ite_eq_left h, mul_one]; congr 1; omega
    · rw [ite_eq_right h, show n + 1 - m = (n - m) + 1 by omega, pow_succ]

/-- **`sRes` homogeneity (determinant branch).** Scaling the second argument by a
constant `c ≠ 0` multiplies `sRes_j(P, Q)` (for `j ≤ deg Q`) by `c^{p-j}`: the
`p - j` `Q`-rows of the Sylvester-Habicht square each scale by `c`. -/
theorem sRes_smul_right_det {c : D} (hc : c ≠ 0) (P Q : D[X]) {j : ℕ} (hj : j ≤ Q.natDegree) :
    sRes P (Polynomial.C c * Q) j = c ^ (P.natDegree - j) * sRes P Q j := by
  have hQc : (Polynomial.C c * Q).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_C_mul hc]
  unfold sRes
  rw [ite_eq_left hj, ite_eq_left (show j ≤ (Polynomial.C c * Q).natDegree by rw [hQc]; exact hj)]
  have hdim : P.natDegree + Q.natDegree - 2 * j
      = P.natDegree + (Polynomial.C c * Q).natDegree - 2 * j := by rw [hQc]
  set e := finCongr hdim with he
  set v : Fin (P.natDegree + Q.natDegree - 2 * j) → D :=
    fun i => if i.val < Q.natDegree - j then 1 else c with hv
  have hsub : (SyHaSquare P (Polynomial.C c * Q) j).submatrix e e
      = Matrix.diagonal v * SyHaSquare P Q j := by
    ext i k
    rw [Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, SyHaSquare, Matrix.of_apply, SyHa, id_eq, he,
      finCongr_apply, Fin.val_cast, Fin.val_castLE, hv]
    rw [hQc]
    by_cases hc' : i.val < Q.natDegree - j
    · rw [ite_eq_left hc', ite_eq_left hc', ite_eq_left hc', one_mul]
    · rw [ite_eq_right hc', ite_eq_right hc', ite_eq_right hc',
        show X ^ (i.val - (Q.natDegree - j)) * (Polynomial.C c * Q)
          = Polynomial.C c * (X ^ (i.val - (Q.natDegree - j)) * Q) by ring,
        Polynomial.coeff_C_mul]
  rw [← Matrix.det_submatrix_equiv_self e (SyHaSquare P (Polynomial.C c * Q) j), hsub,
    Matrix.det_mul, Matrix.det_diagonal, hv, prod_ite_one_const,
    show P.natDegree + Q.natDegree - 2 * j - (Q.natDegree - j) = P.natDegree - j by omega]

end Homogeneity

/-! ### Sign invariance of `PmV` under positive scaling of the second argument -/

section SignInvariance

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For `c > 0`, scaling the second argument of `sRes` by `c` preserves every sign:
in the determinant branch via `c^{p-j} > 0`, in the degree gap by literal equality
(the gap values are read off `P` alone). -/
theorem sRes_sign_smul_right {c : K} (hc : 0 < c) (P Q : K[X]) (j : ℕ) :
    SignType.sign (sRes P (Polynomial.C c * Q) j) = SignType.sign (sRes P Q j) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hQc : (Polynomial.C c * Q).natDegree = Q.natDegree := Polynomial.natDegree_C_mul hc0
  by_cases hj : j ≤ Q.natDegree
  · rw [sRes_smul_right_det hc0 P Q hj, sign_mul, sign_pos (pow_pos hc _), one_mul]
  · have hgap : sRes P (Polynomial.C c * Q) j = sRes P Q j := by
      rw [sRes, sRes, ite_eq_right (show ¬ j ≤ (Polynomial.C c * Q).natDegree by rw [hQc]; exact hj),
        ite_eq_right hj, hQc]
    rw [hgap]

/-- **`PmV` invariance.** Scaling the second argument by a positive constant leaves
`PmV(sRes(P, ·))` unchanged. -/
theorem PmV_sResSeq_C_mul_right {c : K} (hc : 0 < c) (P Q : K[X]) :
    PmV (sResSeq P (Polynomial.C c * Q)) = PmV (sResSeq P Q) := by
  apply PmV_eq_of_sign_eq
  unfold sResSeq
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  exact sRes_sign_smul_right hc P Q (P.natDegree - j)

end SignInvariance

/-! ### The pseudo-remainder bridge and the non-monic theorem -/

/-- Uniqueness of the Euclidean remainder over a field: if `P ∣ x - r` and
`deg r < deg P`, then `x % P = r`. -/
private theorem emod_eq_of {K : Type*} [Field K] {P x r : K[X]} (hP : P ≠ 0)
    (hdvd : P ∣ x - r) (hr : r.degree < P.degree) : x % P = r := by
  have h1 : (x - r) % P = 0 := EuclideanDomain.mod_eq_zero.mpr hdvd
  rw [Polynomial.sub_mod, sub_eq_zero] at h1
  rw [h1, (Polynomial.mod_eq_self_iff hP).mpr hr]

/-- **BPR Theorem 4.33, non-monic case.** Over an ordered integral domain `D` with
a strictly monotone ring embedding `f : D →+* R` into a real closed field `R`, for
any `P ≠ 0` and any signed pseudo-remainder `pr` of `P′·Q` by `P` — that is,
`C(lc(P)^d)·P′Q = A·P + pr` with `d = pRemExp` (even) and `deg pr < deg P`, as
produced by `pRem_exists_aux` — the subresultant sequence of `P` and `pr`
(computed entirely in `D`) computes the Tarski query:
`PmV(sRes(P, pr)) = TaQ(map f Q, map f P)`. No `Monic` hypothesis is needed.

The even exponent makes the scaling factor `lc(P)^d` a positive square, so passing
from the genuine remainder to the pseudo-remainder preserves every sign and hence
`PmV`; the real-closed-field engine `theorem_4_33_realClosed` finishes. -/
theorem theorem_4_33_nonmonic {D R : Type*}
    [CommRing D] [LinearOrder D] [IsStrictOrderedRing D]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {f : D →+* R} (hf : StrictMono f) (P Q : D[X]) (hP : P ≠ 0)
    (pr A : D[X])
    (hpr : Polynomial.C (P.leadingCoeff ^ pRemExp (P.derivative * Q) P) * (P.derivative * Q)
        = A * P + pr)
    (hdeg : pr.degree < P.degree) :
    PmV (sResSeq P pr) = tarskiQuery (Q.map f) (P.map f) := by
  have hf_inj := hf.injective
  set d := pRemExp (P.derivative * Q) P with hd_def
  have hlcP : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  -- the scaling factor over `R`
  set lam : R := (f P.leadingCoeff) ^ d with hlam
  have hlam_pos : 0 < lam := (pRemExp_even (P.derivative * Q) P).pow_pos
    (by simpa using hf_inj.ne hlcP)
  have hfP : P.map f ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hf_inj]; exact hP
  -- abbreviations over `R`
  set M : R[X] := (P.map f).derivative * Q.map f with hM
  -- map the pseudo-division identity into `R`
  have hidR : Polynomial.C lam * M = A.map f * P.map f + pr.map f := by
    have h := congrArg (Polynomial.map f) hpr
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at h
    rw [map_pow, ← Polynomial.derivative_map] at h
    exact h
  -- `pr.map f` is the remainder of `C lam * M` by `P.map f`
  have hdegR : (pr.map f).degree < (P.map f).degree := by
    rwa [Polynomial.degree_map_eq_of_injective hf_inj,
      Polynomial.degree_map_eq_of_injective hf_inj]
  have hpr_emod : pr.map f = (Polynomial.C lam * M) % (P.map f) := by
    refine (emod_eq_of hfP ⟨A.map f, ?_⟩ hdegR).symm
    rw [hidR]; ring
  -- `(C lam * M) % P = C lam * (M % P)`
  have hC_mul : (Polynomial.C lam * M) % (P.map f) = Polynomial.C lam * (M % (P.map f)) := by
    refine emod_eq_of hfP ⟨Polynomial.C lam * (M / P.map f), ?_⟩ ?_
    · have hdm := EuclideanDomain.div_add_mod M (P.map f)
      linear_combination (-Polynomial.C lam) * hdm
    · rw [Polynomial.degree_mul, Polynomial.degree_C (ne_of_gt hlam_pos), zero_add]
      exact Polynomial.degree_mod_lt M hfP
  -- assemble
  rw [← PmV_map hf (sResSeq P pr), map_sResSeq hf_inj, hpr_emod, hC_mul,
    PmV_sResSeq_C_mul_right hlam_pos (P.map f) (M % (P.map f))]
  -- now `M % (P.map f) = (P.map f).derivative * (Q.map f) % (P.map f)`, the engine's remainder
  exact theorem_4_33_realClosed (P.map f) (Q.map f) hfP

end Azurite.BPR.Chapter4

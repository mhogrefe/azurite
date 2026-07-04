import Azurite.BasuPollackRoy.Chapter4.Section4_2.Theorem_4_32
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Proposition_2_57
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Remark_2_55
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# BPR Theorem 4.33: the Tarski query via subresultants

BPR state this for polynomials in `D[X]` with `D` an integral domain (not
necessarily a field). We give the genuinely-over-a-domain statement
(`theorem_4_33`): `D` is an ordered integral domain with a strictly monotone ring
embedding `f : D →+* R` into a real closed field `R`, `P` is monic, and
`R_rem = (P′·Q) %ₘ P` is the remainder (formed via `modByMonic`, which needs only
a commutative ring once the divisor is monic). Then
`PmV(sRes(P, R_rem)) = TaQ(map f Q, map f P)`,
where the subresultant sequence `sRes(P, R_rem)` is computed entirely in `D`.

This is the bridge that lets the (purely algebraic) signed subresultant sequence
*compute* the Tarski query — the number of roots of `P` counted with the sign of
`Q` — with the subresultants computed over `D` (e.g. `ℤ`) and the query read off
over the real closure.

The engine is the real-closed-field case `theorem_4_33_realClosed`, which composes:

* Proposition 2.57: `TaQ(Q, P) = Ind(P′Q / P)`;
* Remark 2.55(b): `Ind(P′Q / P) = Ind(R / P)`, since the Cauchy index depends
  only on the numerator modulo `P`;
* Theorem 4.32: `PmV(sRes(P, R)) = Ind(R / P)`.

The degenerate case `R = 0` (where Theorem 4.32 does not apply directly) is
handled separately: there `Ind(R/P) = Ind(0/P) = 0` and `PmV(sRes(P, 0)) = 0`
(`PmV_sResSeq_right_zero`).

The domain statement reduces to the engine via two specialization facts: the
subresultant sequence commutes with the injective `f` (`map_sResSeq`), and `PmV`
is invariant under the order-embedding `f` (`PmV_map`, since `f` preserves signs);
`%ₘ` becomes `%` over the field `R` for the now-monic divisor.
-/

namespace Azurite.BPR.Chapter4

-- See `Theorem_4_32`: the Chapter 2 import chain shadows `Polynomial`, so we
-- open the root namespace explicitly to keep the scoped `R[X]` notation.
open _root_.Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `sRes_m(P, 0) = 0` for `m < p`: the second-argument-zero Sylvester-Habicht
square consists entirely of `Q = 0` rows (for `m = 0`, the determinant branch),
or lies in the degree gap below `p` (for `0 < m < p`). -/
theorem sRes_right_zero_eq_zero (P : K[X]) {m : ℕ} (hm : m < P.natDegree) :
    sRes P 0 m = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rw [sRes, if_pos (Nat.zero_le _)]
    have hzero : SyHaSquare P (0 : K[X]) 0 = 0 := by
      ext i k
      simp only [SyHaSquare, Matrix.submatrix_apply, id_eq, SyHa, Matrix.of_apply,
        Matrix.zero_apply]
      rw [if_neg (by simp [Polynomial.natDegree_zero]), mul_zero, Polynomial.coeff_zero]
    rw [hzero]
    haveI : Nonempty (Fin (P.natDegree + Polynomial.natDegree (0 : K[X]) - 2 * 0)) :=
      ⟨⟨0, by simp only [Polynomial.natDegree_zero]; omega⟩⟩
    exact Matrix.det_zero
  · rw [sRes, if_neg (by rw [Polynomial.natDegree_zero]; omega),
      if_pos (by rw [Polynomial.natDegree_zero]; omega), if_neg (by omega)]

omit [IsStrictOrderedRing K] in
/-- `PmV(sRes(P, 0)) = 0` for `P ≠ 0`: the sequence is `a_p, 0, …, 0` (or a
singleton when `p = 0`), all of whose entries below the head vanish. -/
theorem PmV_sResSeq_right_zero (P : K[X]) : PmV (sResSeq P 0) = 0 := by
  rcases Nat.eq_zero_or_pos P.natDegree with hp0 | hp1
  · rw [sResSeq, hp0]
    simp only [Nat.zero_add, List.range_one, List.map_cons, List.map_nil]
    exact PmV_singleton _
  · show PmV (partialSeq P 0 P.natDegree) = 0
    rw [partialSeq_eq_cons]
    apply PmV_cons_all_zero
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact sRes_right_zero_eq_zero P (by omega)

variable [IsRealClosed K]

/-- **BPR Theorem 4.33, real closed field case (the engine).** `PmV(sRes(P, R)) =
TaQ(Q, P)`, where `R = Rem(P′Q, P)`. The signed subresultant sequence of `P` and
`R` computes the Tarski query of `Q` for `P`. Proved by `TaQ(Q,P) = Ind(P′Q/P)`
(Proposition 2.57) `= Ind(R/P)` (Remark 2.55(b)) `= PmV(sRes(P,R))` (Theorem 4.32).
The general domain statement `theorem_4_33` reduces to this. -/
theorem theorem_4_33_realClosed (P Q : K[X]) (hP : P ≠ 0) :
    PmV (sResSeq P ((P.derivative * Q) % P)) = tarskiQuery Q P := by
  have hRHS : tarskiQuery Q P = cauchyIndex ((P.derivative * Q) % P) P := by
    rw [tarskiQuery_eq_tarskiQueryOn_negInf_posInf,
      proposition_2_57 hasIVP_of_isRealClosed Q P hP,
      ← remark_2_55_b hasIVP_of_isRealClosed (P.derivative * Q) P .negInf .posInf hP]
    rfl
  rw [hRHS]
  by_cases hR : (P.derivative * Q) % P = 0
  · rw [hR, PmV_sResSeq_right_zero P, cauchyIndex_eq_cauchyIndexOn_negInf_posInf,
      cauchyIndexOn_zero_left]
  · exact theorem_4_32 P _ hR
      (Polynomial.natDegree_lt_natDegree hR (Polynomial.degree_mod_lt _ hP))

/-! ### Specialization: subresultants and `PmV` commute with an order-embedding -/

section Specialization

private theorem dropWhile_map {α β : Type*} (g : α → β) (p : β → Bool) :
    ∀ l : List α, (l.map g).dropWhile p = (l.dropWhile (fun x => p (g x))).map g
  | [] => rfl
  | a :: l => by
    by_cases h : p (g a)
    · rw [List.map_cons, List.dropWhile_cons_of_pos h,
        List.dropWhile_cons_of_pos (p := fun x => p (g x)) (a := a) (l := l) (by simpa using h),
        dropWhile_map g p l]
    · rw [List.map_cons, List.dropWhile_cons_of_neg h,
        List.dropWhile_cons_of_neg (p := fun x => p (g x)) (a := a) (l := l) (by simpa using h),
        List.map_cons]

/-- **`PmV` is invariant under an order-embedding.** A strictly monotone ring hom
`f : D →+* S` preserves the zero pattern (it is injective) and all sign products
`sign(s_i s_j)`, so `PmV(s.map f) = PmV(s)`. -/
theorem PmV_map {D S : Type*} [CommRing D] [LinearOrder D] [IsStrictOrderedRing D]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] {f : D →+* S} (hf : StrictMono f) :
    ∀ l : List D, PmV (l.map f) = PmV l
  | [] => by simp
  | sp :: rest => by
    have hf0 : f 0 = 0 := map_zero f
    have hpred : (fun x : D => decide (f x = 0)) = (fun x => decide (x = 0)) := by
      funext x
      by_cases hx : x = 0
      · simp [hx, hf0]
      · have hfx : f x ≠ 0 := fun h => hx (hf.injective (by rw [h, hf0]))
        simp [hx, hfx]
    have hdrop : (rest.map f).dropWhile (fun x => decide (x = 0))
        = (rest.dropWhile (fun x => decide (x = 0))).map f := by
      rw [dropWhile_map]; simp only [hpred]
    rw [List.map_cons, PmV, PmV, hdrop]
    rcases hd : rest.dropWhile (fun x => decide (x = 0)) with _ | ⟨sq, tl⟩
    · simp
    · simp only [List.map_cons, List.length_cons, List.length_map]
      have hsign : SignType.sign (f sp * f sq) = SignType.sign (sp * sq) := by
        rw [← map_mul]
        rcases lt_trichotomy (sp * sq) 0 with h | h | h
        · rw [sign_neg h, sign_neg (show f (sp * sq) < 0 by rw [← hf0]; exact hf h)]
        · simp [h, hf0]
        · rw [sign_pos h, sign_pos (show (0 : S) < f (sp * sq) by rw [← hf0]; exact hf h)]
      rw [show (f sq :: tl.map f) = (sq :: tl).map f from rfl, PmV_map hf (sq :: tl), hsign]
  termination_by l => l.length
  decreasing_by
    simp only [List.length_cons]
    have := List.length_dropWhile_le (fun x => decide (x = 0)) rest
    rw [hd] at this
    simp only [List.length_cons] at this
    omega

/-- **`sRes` commutes with an injective ring hom.** Since `sRes` is a determinant
(or a leading coefficient) and the index ranges are degree-preserved under an
injective `f`, `f(sRes P Q m) = sRes (map f P) (map f Q) m`. -/
theorem map_sRes {D R : Type*} [CommRing D] [CommRing R] {f : D →+* R}
    (hf : Function.Injective f) (P Q : D[X]) (m : ℕ) :
    f (sRes P Q m) = sRes (P.map f) (Q.map f) m := by
  have hPd : (P.map f).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf P
  have hQd : (Q.map f).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf Q
  unfold sRes
  by_cases hm : m ≤ Q.natDegree
  · rw [if_pos hm, if_pos (show m ≤ (Q.map f).natDegree by rw [hQd]; exact hm)]
    rw [RingHom.map_det]
    have hdim : P.natDegree + Q.natDegree - 2 * m
        = (P.map f).natDegree + (Q.map f).natDegree - 2 * m := by rw [hPd, hQd]
    set e := finCongr hdim with he
    have hsub : (SyHaSquare P Q m).map f
        = (SyHaSquare (P.map f) (Q.map f) m).submatrix e e := by
      ext i k
      simp only [Matrix.map_apply, Matrix.submatrix_apply, SyHaSquare,
        Matrix.of_apply, SyHa, id_eq, he, finCongr_apply,
        Fin.val_cast, Fin.val_castLE]
      rw [hPd, hQd]
      by_cases hc : i.val < Q.natDegree - m
      · rw [if_pos hc, if_pos hc, ← Polynomial.coeff_map, Polynomial.map_mul,
          Polynomial.map_pow, Polynomial.map_X]
      · rw [if_neg hc, if_neg hc, ← Polynomial.coeff_map, Polynomial.map_mul,
          Polynomial.map_pow, Polynomial.map_X]
    rw [RingHom.mapMatrix_apply, hsub, Matrix.det_submatrix_equiv_self]
  · rw [if_neg hm, if_neg (show ¬ m ≤ (Q.map f).natDegree by rw [hQd]; exact hm)]
    by_cases hqp : Q.natDegree < P.natDegree
    · rw [if_pos hqp, if_pos (show (Q.map f).natDegree < (P.map f).natDegree by
        rw [hQd, hPd]; exact hqp)]
      by_cases hmp : m = P.natDegree
      · rw [if_pos hmp, if_pos (show m = (P.map f).natDegree by rw [hPd]; exact hmp)]
        exact (Polynomial.leadingCoeff_map_of_injective hf P).symm
      · rw [if_neg hmp, if_neg (show ¬ m = (P.map f).natDegree by rw [hPd]; exact hmp),
          map_zero]
    · rw [if_neg hqp, if_neg (show ¬ (Q.map f).natDegree < (P.map f).natDegree by
        rw [hQd, hPd]; exact hqp), map_zero]

/-- **The subresultant sequence commutes with an injective ring hom.** -/
theorem map_sResSeq {D R : Type*} [CommRing D] [CommRing R] {f : D →+* R}
    (hf : Function.Injective f) (P Q : D[X]) :
    (sResSeq P Q).map f = sResSeq (P.map f) (Q.map f) := by
  have hPd : (P.map f).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf P
  unfold sResSeq
  rw [List.map_map, hPd]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  exact map_sRes hf P Q (P.natDegree - j)

end Specialization

/-- **BPR Theorem 4.33.** Over an ordered integral domain `D` with a strictly
monotone ring embedding `f : D →+* R` into a real closed field `R`, for `P` monic
and `R_rem = (P′·Q) %ₘ P`,
`PmV(sRes(P, R_rem)) = TaQ(map f Q, map f P)`,
with the subresultant sequence computed in `D`. Reduces to
`theorem_4_33_realClosed` over `R`: `PmV` and `sRes` commute with `f`
(`PmV_map`, `map_sResSeq`), the remainder maps to `((map f P)′·(map f Q)) %ₘ (map f P)`,
and `%ₘ = %` for the monic `map f P` over the field `R`. -/
theorem theorem_4_33 {D R : Type*}
    [CommRing D] [LinearOrder D] [IsStrictOrderedRing D]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {f : D →+* R} (hf : StrictMono f) (P Q : D[X]) (hP : P.Monic) :
    PmV (sResSeq P ((P.derivative * Q) %ₘ P)) = tarskiQuery (Q.map f) (P.map f) := by
  rw [← PmV_map hf (sResSeq P ((P.derivative * Q) %ₘ P)),
    map_sResSeq hf.injective,
    show ((P.derivative * Q) %ₘ P).map f
        = ((P.map f).derivative * Q.map f) %ₘ (P.map f) by
      rw [Polynomial.map_modByMonic f hP, Polynomial.map_mul, ← Polynomial.derivative_map],
    Polynomial.modByMonic_eq_mod _ (hP.map f)]
  exact theorem_4_33_realClosed (P.map f) (Q.map f) (hP.map f).ne_zero

end Azurite.BPR.Chapter4

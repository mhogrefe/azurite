import Azurite.AzPolynomial.GcdDet
import Azurite.AzPolynomial.Equiv.SignedSubresultant
import Azurite.AzPolynomial.Equiv.Gcd
import Azurite.BasuPollackRoy.Chapter10.Section10_1.Proposition_10_14
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Notation_8_41

/-!
# Correctness of the determinant-route fallback

Over **any** commutative ring `R` (with decidable equality):

* `toPoly_sResPDet` — `sResPDet` represents the abstract determinant-defined
  `Chapter8.sResP` **exactly**;
* `toPoly_sResVDet` — `sResVDet` represents `Chapter8.sResV` **exactly**.

These identifications are by construction: both computable functions mirror
the determinant definitions, with the minors evaluated by the division-free
`detFn` (`detFn_eq_det`), and `toPoly` pushed through by `map_detFn`.

Because the fallback's `sResV` output *is* the abstract `sResV`, the
gcd-free-part correctness of the pair over a field comes straight from the
abstract theory (Theorem 8.34's gcd branch and Proposition 10.14 at
`C = R[i]`) — including the component the exact-division route has not yet
identified (the boundary cofactor).
-/

namespace Azurite.AzPolynomial

open Polynomial

/-- `syhaEntry`, `P`-block rows. -/
private theorem syhaEntry_eq_lt {R : Type _} [CommRing R] [DecidableEq R]
    (P Q : AzPolynomial R) {j i : ℕ} (d : ℕ) (h : i < Q.natDegree - j) :
    syhaEntry P Q j i d
      = (Polynomial.X ^ (Q.natDegree - j - 1 - i) * AzPolynomial.toPoly P).coeff d := by
  rw [syhaEntry, ite_eq_left h, mul_comm, Polynomial.coeff_mul_X_pow']
  split <;> simp

/-- `syhaEntry`, `Q`-block rows. -/
private theorem syhaEntry_eq_ge {R : Type _} [CommRing R] [DecidableEq R]
    (P Q : AzPolynomial R) {j i : ℕ} (d : ℕ) (h : ¬ i < Q.natDegree - j) :
    syhaEntry P Q j i d
      = (Polynomial.X ^ (i - (Q.natDegree - j)) * AzPolynomial.toPoly Q).coeff d := by
  rw [syhaEntry, ite_eq_right h, mul_comm, Polynomial.coeff_mul_X_pow']
  split <;> simp

open Azurite.BPR.Chapter8 in
/-- Coefficient extraction from `pdetRing`: the `k`-th coefficient is the
`k`-th minor (or `0` beyond the top). -/
private theorem pdetRing_coeff {R : Type _} [CommRing R] {m : ℕ} (n : ℕ)
    (F : Fin m → Polynomial R) (k : ℕ) :
    (pdetRing n F).coeff k
      = if k < n - m + 1 then pdetMinorRing n F k else 0 := by
  classical
  rw [pdetRing, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rcases Nat.lt_or_ge k (n - m + 1) with hk | hk
  · rw [ite_eq_left hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin (n - m + 1))
      (fun b _ hb => ite_eq_right (fun h => hb (Fin.ext h.symm)))
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]
  · rw [ite_eq_right (by omega), Finset.sum_eq_zero (fun i _ => ite_eq_right (by
      have := i.isLt
      omega))]

open Azurite.BPR.Chapter8 in
/-- **`sResPDet` represents the abstract signed subresultant** — over any
commutative ring. -/
theorem toPoly_sResPDet {R : Type _} [CommRing R] [DecidableEq R]
    (P Q : AzPolynomial R) (j : ℕ) :
    AzPolynomial.toPoly (sResPDet P Q j)
      = sResP (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j := by
  rw [sResPDet, sResP, AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]
  by_cases hj : j ≤ Q.natDegree
  · rw [ite_eq_left hj, ite_eq_left hj]
    apply Polynomial.ext
    intro k
    rw [toPoly_normalize, coeff_list_toPoly, pdetRing_coeff]
    rw [List.getCoeff, Array.toList_ofFn, List.getElem?_ofFn]
    rcases Nat.lt_or_ge k (P.natDegree + Q.natDegree - j
        - (P.natDegree + Q.natDegree - 2 * j) + 1) with hk | hk
    · rw [dite_eq_left hk, ite_eq_left hk]
      simp only [Option.getD_some]
      -- the `detFn` minor is the abstract minor
      rw [pdetMinorRing]
      refine Azurite.detFn_eq_det _ _ _ ?_
      intro r c hr hc
      rw [pdetMinorMatRing]
      show syhaEntry P Q j r _ = _
      have hcol : pdetColIdx (P.natDegree + Q.natDegree - j)
          (m := P.natDegree + Q.natDegree - 2 * j) k ⟨c, hc⟩
          = if c + 1 < P.natDegree + Q.natDegree - 2 * j then
              P.natDegree + Q.natDegree - j - 1 - c
            else k := rfl
      rw [hcol]
      by_cases hrblock : r < Q.natDegree - j
      · rw [syhaEntry_eq_lt _ _ _ hrblock, ite_eq_left (show ((⟨r, hr⟩ : Fin _) : ℕ)
          < Q.natDegree - j from hrblock)]
      · rw [syhaEntry_eq_ge _ _ _ hrblock, ite_eq_right (show ¬ ((⟨r, hr⟩ : Fin _) : ℕ)
          < Q.natDegree - j from hrblock)]
    · rw [dite_eq_right (by omega), ite_eq_right (by omega)]
      rfl
  · rw [ite_eq_right hj, ite_eq_right hj]
    by_cases hp : j = P.natDegree
    · rw [ite_eq_left hp, ite_eq_left hp]
    · rw [ite_eq_right hp, ite_eq_right hp]
      by_cases hp1 : j = P.natDegree - 1
      · rw [ite_eq_left hp1, ite_eq_left hp1]
      · rw [ite_eq_right hp1, ite_eq_right hp1, toPoly_zero]

open Azurite.BPR.Chapter8 in
/-- **`sResVDet` represents the abstract `V`-cofactor** — over any
commutative ring. -/
theorem toPoly_sResVDet {R : Type _} [CommRing R] [DecidableEq R]
    (P Q : AzPolynomial R) (j : ℕ) :
    AzPolynomial.toPoly (sResVDet P Q j)
      = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) j := by
  have h1 := Azurite.map_detFn (toPolyHom (R := R)) (P.natDegree + Q.natDegree - 2 * j)
    (fun i k =>
      if k + 1 < P.natDegree + Q.natDegree - 2 * j then
        monomial 0 (syhaEntry P Q j i (P.natDegree + Q.natDegree - j - 1 - k))
      else if i < Q.natDegree - j then 0
      else monomial (i - (Q.natDegree - j)) 1)
  have hm : P.natDegree + Q.natDegree - 2 * j
      = (AzPolynomial.toPoly P).natDegree + (AzPolynomial.toPoly Q).natDegree - 2 * j := by
    rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]
  rw [sResVDet, sResV]
  refine Eq.trans h1 ?_
  rw [hm]
  refine Azurite.detFn_eq_det _ _ _ ?_
  intro i k hi hk
  rw [sResVMat]
  show AzPolynomial.toPoly _ = _
  rw [Matrix.of_apply]
  rcases Nat.lt_or_ge (k + 1) ((AzPolynomial.toPoly P).natDegree
      + (AzPolynomial.toPoly Q).natDegree - 2 * j) with hk1 | hk1
  · rw [ite_eq_left hk1, ite_eq_left (show ((⟨k, hk⟩ : Fin _) : ℕ) + 1 < _ from hk1)]
    rw [toPoly_monomial, Polynomial.monomial_zero_left]
    congr 1
    rw [Azurite.BPR.Chapter4.SyHa, Matrix.of_apply]
    rcases Nat.lt_or_ge i (Q.natDegree - j) with hib | hib
    · rw [syhaEntry_eq_lt _ _ _ hib,
        ite_eq_left (show ((⟨i, hi⟩ : Fin _) : ℕ)
          < (AzPolynomial.toPoly Q).natDegree - j from by
            simp only [AzPolynomial.natDegree_toPoly]; exact hib)]
      simp [AzPolynomial.natDegree_toPoly]
    · rw [syhaEntry_eq_ge _ _ _ (by omega),
        ite_eq_right (show ¬ ((⟨i, hi⟩ : Fin _) : ℕ)
          < (AzPolynomial.toPoly Q).natDegree - j from by
            simp only [AzPolynomial.natDegree_toPoly]; omega)]
      simp [AzPolynomial.natDegree_toPoly]
  · rw [ite_eq_right (by omega), ite_eq_right (show ¬ ((⟨k, hk⟩ : Fin _) : ℕ) + 1 < _ from by
      show ¬ k + 1 < _
      omega)]
    rcases Nat.lt_or_ge i (Q.natDegree - j) with hib | hib
    · rw [ite_eq_left hib, ite_eq_left (show ((⟨i, hi⟩ : Fin _) : ℕ)
        < (AzPolynomial.toPoly Q).natDegree - j from by
          simp only [AzPolynomial.natDegree_toPoly]; exact hib), toPoly_zero]
    · rw [ite_eq_right (by omega), ite_eq_right (show ¬ ((⟨i, hi⟩ : Fin _) : ℕ)
        < (AzPolynomial.toPoly Q).natDegree - j from by
          simp only [AzPolynomial.natDegree_toPoly]; omega),
        toPoly_monomial]
      simp only [AzPolynomial.natDegree_toPoly]
      exact (Polynomial.X_pow_eq_monomial _).symm

/-! ### The fallback pair over a field -/

private theorem find?_range_eq_some {p : ℕ → Bool} {n j : ℕ} (hj : j < n)
    (h1 : ∀ i, i < j → p i = false) (h2 : p j = true) :
    (List.range n).find? p = some j := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.find?_append]
    rcases Nat.lt_or_ge j m with hjm | hjm
    · rw [ih hjm]
      rfl
    · have hjeq : j = m := by omega
      subst hjeq
      rw [List.find?_eq_none.mpr (fun x hx => by
        rw [List.mem_range] at hx
        simp [h1 x hx])]
      simp [h2]

open Azurite.BPR.Chapter8 in
/-- **Correctness of the fallback pair over a field** (`deg P > deg Q ≥ 1`,
both nonzero, gcd degree `j ≥ 1`): the first output is associated to the
gcd, and the second output **is** the abstract `sResV_{j−1}` — the gcd-free
part of `P` with respect to `Q` up to a multiplicative constant
(Proposition 10.14). -/
theorem gcdGcdFreePartDet_spec {K : Type _} [Field K] [DecidableEq K]
    (P Q : AzPolynomial K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
      (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)).natDegree = j) :
    Associated (AzPolynomial.toPoly (gcdGcdFreePartDet P Q).1)
        (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
          (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
    ∧ AzPolynomial.toPoly (gcdGcdFreePartDet P Q).2
        = sResV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (j - 1) := by
  have hP' : AzPolynomial.toPoly P ≠ 0 := toPoly_ne_zero hP
  have hQ' : AzPolynomial.toPoly Q ≠ 0 := toPoly_ne_zero hQ
  have hpq' : (AzPolynomial.toPoly Q).natDegree < (AzPolynomial.toPoly P).natDegree := by
    rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]
    exact hpq
  have hjq : j ≤ Q.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd
      (@gcd_dvd_right _ _ Azurite.BPR.gcdMonoidPolynomial
        (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) hQ'
    rw [hj, AzPolynomial.natDegree_toPoly] at h
    exact h
  -- the scan finds exactly the gcd degree
  have hfind : firstNonzeroDet P Q = some j := by
    rw [firstNonzeroDet]
    refine find?_range_eq_some (by omega) ?_ ?_
    · intro i hi
      have hzero : sResPDet P Q i = 0 := by
        apply toPoly_inj.mp
        rw [toPoly_sResPDet, toPoly_zero]
        exact sResP_eq_zero_of_lt_gcd _ _ hP' hQ' hpq'
          (by rw [AzPolynomial.natDegree_toPoly]; omega) (by omega)
      simp [hzero]
    · have hne : sResPDet P Q j ≠ 0 := by
        intro h
        have h2 := toPoly_sResPDet P Q j
        rw [h, toPoly_zero] at h2
        exact sResP_natDegree_gcd_ne_zero _ _ hP' hQ' hpq' (hj ▸ h2.symm)
      simp [hne]
  -- reduce the wrapper: unequal degrees, scan hits `some j` with `j ≥ 1`
  have hpair : gcdGcdFreePartDet P Q = (sResPDet P Q j, sResVDet P Q (j - 1)) := by
    rw [gcdGcdFreePartDet, ite_eq_right hQ, ite_eq_right (by omega), hfind]
    match j, hj1 with
    | jj + 1, _ => rfl
  rw [hpair]
  constructor
  · rw [toPoly_sResPDet]
    exact associated_sResP_gcd _ _ hP' hQ' hpq' hj
  · rw [toPoly_sResVDet]

open Azurite.BPR.Chapter8 in
/-- **Full gcd-free-part correctness of the fallback pair** over a field:
the second output times the gcd is associated to `P` — i.e. it *is* the
gcd-free part of `P` with respect to `Q`, up to a multiplicative constant
(BPR Proposition 10.14 via `sResV_gcdFree_associated`). -/
theorem gcdGcdFreePartDet_snd_gcdFree {K : Type _} [Field K] [DecidableEq K]
    (P Q : AzPolynomial K) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (@GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
      (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)).natDegree = j) :
    Associated
      (AzPolynomial.toPoly (gcdGcdFreePartDet P Q).2
        * @GCDMonoid.gcd _ _ Azurite.BPR.gcdMonoidPolynomial
            (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))
      (AzPolynomial.toPoly P) := by
  obtain ⟨-, hsnd⟩ := gcdGcdFreePartDet_spec P Q hP hQ hpq hj1 hj
  rw [hsnd]
  exact Azurite.BPR.sResV_gcdFree_associated (toPoly_ne_zero hP) (toPoly_ne_zero hQ)
    (by rw [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]; exact hpq)
    hj1 hj

end Azurite.AzPolynomial

import Azurite.BasuPollackRoy.Chapter1.Section1_3.Theorem1_22
import Azurite.BasuPollackRoy.Chapter1.Section1_4.Theorem1_23
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # BPR Section 1.4 — Sentence preservation through QE

This file tracks polynomial `vars` and formula `freeVars` through the QE
construction in `Theorem1_22`/`Theorem1_23`, with the goal of proving:

> If `Φ : Formula (Fin ℓ) (FieldAtom (Fin ℓ) D)` is a *sentence*
> (`Φ.freeVars = ∅`), then the QF formula produced by
> `theorem_1_23_two_fields` is also a sentence.

The strategy is to maintain the invariant that all atom polynomials have
`MvPolynomial.vars = ∅` (i.e., they are constants `MvPolynomial.C d`).
This invariant is preserved through every operation used in the QE
pipeline: `splitLast`, multiplication, `pRemMv`, `Tru`, `TRems`,
`pathLeafParent`, `posgcd`, `degFormula`, `leafFormula`, `projBasic`.

The polynomial-level invariant for `Polynomial (MvPolynomial (Fin k) D)`
is: every coefficient has `vars = ∅`. We package this as
`PolyConst Q := ∀ i, (Q.coeff i).vars = ∅`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ}

/-! ### `MvPolynomial.vars = ∅` is closed under arithmetic -/

variable {D : Type*} [CommRing D]

theorem MvPolynomial.vars_add_empty {p q : MvPolynomial (Fin k) D}
    (hp : p.vars = ∅) (hq : q.vars = ∅) :
    (p + q).vars = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have hsub := MvPolynomial.vars_add_subset p q
  have := hsub hx
  rw [hp, hq, Finset.empty_union] at this
  exact absurd this (Finset.notMem_empty _)

theorem MvPolynomial.vars_mul_empty {p q : MvPolynomial (Fin k) D}
    (hp : p.vars = ∅) (hq : q.vars = ∅) :
    (p * q).vars = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have hsub := MvPolynomial.vars_mul p q
  have := hsub hx
  rw [hp, hq, Finset.empty_union] at this
  exact absurd this (Finset.notMem_empty _)

theorem MvPolynomial.vars_neg_empty {p : MvPolynomial (Fin k) D}
    (hp : p.vars = ∅) : (-p).vars = ∅ := by
  rwa [MvPolynomial.vars_neg]

theorem MvPolynomial.vars_sub_empty {p q : MvPolynomial (Fin k) D}
    (hp : p.vars = ∅) (hq : q.vars = ∅) :
    (p - q).vars = ∅ := by
  rw [sub_eq_add_neg]
  exact MvPolynomial.vars_add_empty hp (MvPolynomial.vars_neg_empty hq)

theorem MvPolynomial.vars_pow_empty {p : MvPolynomial (Fin k) D}
    (hp : p.vars = ∅) (n : ℕ) :
    (p ^ n).vars = ∅ := by
  induction n with
  | zero => simp [pow_zero, MvPolynomial.vars_one]
  | succ n ih =>
    rw [pow_succ]
    exact MvPolynomial.vars_mul_empty ih hp

theorem MvPolynomial.vars_zero_empty :
    (0 : MvPolynomial (Fin k) D).vars = ∅ :=
  MvPolynomial.vars_0

theorem MvPolynomial.vars_one_empty :
    (1 : MvPolynomial (Fin k) D).vars = ∅ :=
  MvPolynomial.vars_one

/-! ### `PolyConst`: a polynomial whose every coefficient has empty vars -/

section PolyConst

variable {D : Type*} [CommRing D]

/-- `Q : Polynomial (MvPolynomial (Fin k) D)` has *constant coefficients*
if each coefficient `Q.coeff i : MvPolynomial (Fin k) D` has empty `vars`,
equivalently is in the image of `MvPolynomial.C : D → MvPolynomial (Fin k) D`. -/
def PolyConst (Q : Polynomial (MvPolynomial (Fin k) D)) : Prop :=
  ∀ i, (Q.coeff i).vars = ∅

namespace PolyConst

theorem zero : PolyConst (0 : Polynomial (MvPolynomial (Fin k) D)) := by
  intro i; simp

theorem one : PolyConst (1 : Polynomial (MvPolynomial (Fin k) D)) := by
  classical
  intro i
  rw [Polynomial.coeff_one]
  split_ifs
  · exact MvPolynomial.vars_one_empty
  · exact MvPolynomial.vars_zero_empty

theorem C_const {c : MvPolynomial (Fin k) D} (hc : c.vars = ∅) :
    PolyConst (Polynomial.C c) := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hc
  · exact MvPolynomial.vars_zero_empty

theorem CC_of_D (d : D) :
    PolyConst (Polynomial.C (MvPolynomial.C d : MvPolynomial (Fin k) D)) :=
  C_const MvPolynomial.vars_C

theorem X : PolyConst (Polynomial.X : Polynomial (MvPolynomial (Fin k) D)) := by
  classical
  intro i
  rw [Polynomial.coeff_X]
  split_ifs
  · exact MvPolynomial.vars_one_empty
  · exact MvPolynomial.vars_zero_empty

theorem add {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) (hQ : PolyConst Q) : PolyConst (P + Q) := by
  intro i
  rw [Polynomial.coeff_add]
  exact MvPolynomial.vars_add_empty (hP i) (hQ i)

theorem neg {P : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) : PolyConst (-P) := by
  intro i
  rw [Polynomial.coeff_neg]
  exact MvPolynomial.vars_neg_empty (hP i)

theorem sub {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) (hQ : PolyConst Q) : PolyConst (P - Q) := by
  rw [sub_eq_add_neg]; exact add hP (neg hQ)

theorem mul {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) (hQ : PolyConst Q) : PolyConst (P * Q) := by
  classical
  intro i
  rw [Polynomial.coeff_mul]
  -- ∑ j ∈ antidiagonal i, P.coeff j.1 * Q.coeff j.2
  -- Each summand has empty vars, so the sum has empty vars.
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have hsub :
      (∑ j ∈ Finset.antidiagonal i, P.coeff j.1 * Q.coeff j.2).vars ⊆
        (Finset.antidiagonal i).biUnion fun j =>
          (P.coeff j.1 * Q.coeff j.2).vars :=
    MvPolynomial.vars_sum_subset _ _
  have hxs := hsub hx
  rw [Finset.mem_biUnion] at hxs
  obtain ⟨j, _, hxj⟩ := hxs
  have hmul : (P.coeff j.1 * Q.coeff j.2).vars = ∅ :=
    MvPolynomial.vars_mul_empty (hP _) (hQ _)
  rw [hmul] at hxj
  exact absurd hxj (Finset.notMem_empty _)

theorem pow {P : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) (n : ℕ) : PolyConst (P ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact one
  | succ n ih => rw [pow_succ]; exact mul ih hP

theorem prod {L : List (Polynomial (MvPolynomial (Fin k) D))}
    (hL : ∀ P ∈ L, PolyConst P) : PolyConst L.prod := by
  induction L with
  | nil => rw [List.prod_nil]; exact one
  | cons P rest ih =>
    rw [List.prod_cons]
    exact mul (hL P (by simp))
      (ih (fun Q hQ => hL Q (List.mem_cons_of_mem _ hQ)))

theorem leadingCoeff_vars_empty {P : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) : P.leadingCoeff.vars = ∅ := by
  unfold Polynomial.leadingCoeff
  exact hP _

end PolyConst

end PolyConst

/-! ### `splitLast` preserves `vars = ∅` at coefficient level -/

section SplitLast

variable {D : Type*} [CommRing D]

theorem splitLast_polyConst_of_vars_empty
    {P : MvPolynomial (Fin (k+1)) D} (hP : P.vars = ∅) :
    PolyConst (splitLast P) := by
  -- P.vars = ∅ ↔ P = MvPolynomial.C (P.coeff 0).
  rw [MvPolynomial.vars_eq_empty_iff_eq_C] at hP
  rw [hP, splitLast_C]
  exact PolyConst.CC_of_D _

/-- Helper: a monomial with support ⊆ {last k} maps via `splitLast` to
a `PolyConst` polynomial. -/
private theorem splitLast_monomial_polyConst_of_supp_subset_last
    {u : Fin (k+1) →₀ ℕ} (hu : u.support ⊆ {Fin.last k}) (d : D) :
    PolyConst (splitLast (MvPolynomial.monomial u d :
      MvPolynomial (Fin (k+1)) D)) := by
  classical
  -- u is a single in the last variable.
  have hu_eq : u = Finsupp.single (Fin.last k) (u (Fin.last k)) := by
    ext j
    by_cases hj : j = Fin.last k
    · subst hj; simp
    · have hj_not_supp : j ∉ u.support := by
        intro hjs
        exact hj (Finset.mem_singleton.mp (hu hjs))
      have hu_j : u j = 0 := Finsupp.notMem_support_iff.mp hj_not_supp
      rw [hu_j, Finsupp.single_apply]
      simp [Ne.symm hj]
  set n := u (Fin.last k)
  have hmono_eq : (MvPolynomial.monomial u d : MvPolynomial (Fin (k+1)) D) =
      MvPolynomial.C d * (MvPolynomial.X (Fin.last k))^n := by
    rw [hu_eq, ← MvPolynomial.C_mul_X_pow_eq_monomial]
  rw [hmono_eq, map_mul, map_pow, splitLast_C, splitLast_X_last]
  exact PolyConst.mul (PolyConst.CC_of_D _) (PolyConst.pow PolyConst.X _)


/-- If `P.vars ⊆ {Fin.last k}`, then `splitLast P` has `PolyConst`
coefficients. -/
theorem splitLast_polyConst_of_vars_subset_last
    {P : MvPolynomial (Fin (k+1)) D}
    (hP : P.vars ⊆ {Fin.last k}) :
    PolyConst (splitLast P) := by
  classical
  -- Use as_sum: P = ∑ v ∈ P.support, monomial v (coeff v P).
  rw [MvPolynomial.as_sum P]
  -- splitLast is a ring hom (so commutes with finite sums).
  rw [map_sum]
  -- Each term satisfies PolyConst.
  refine Finset.sum_induction _ _ (fun A B hA hB => PolyConst.add hA hB)
    PolyConst.zero (fun v hv => ?_)
  -- v ∈ P.support, and we need vars ⊆ {last k} for the monomial.
  apply splitLast_monomial_polyConst_of_supp_subset_last
  -- v.support ⊆ {last k} from P.vars ⊆ {last k}.
  intro j hj
  apply hP
  rw [MvPolynomial.mem_vars_iff_mem_support]
  exact ⟨v, hv, hj⟩


end SplitLast

/-! ### `truncate` and `Tru` preserve `PolyConst` -/

section TruncateTru

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsDomain D] in
theorem PolyConst.truncate {Q : Polynomial (MvPolynomial (Fin k) D)}
    (hQ : PolyConst Q) (i : ℕ) :
    PolyConst (truncate i Q) := by
  intro j
  rw [coeff_truncate]
  split_ifs
  · exact hQ j
  · exact MvPolynomial.vars_zero_empty

omit [IsDomain D] in
theorem PolyConst.of_mem_Tru
    {Q R : Polynomial (MvPolynomial (Fin k) D)}
    (hQ : PolyConst Q) (hR : R ∈ Tru Q) : PolyConst R := by
  by_cases hQ0 : Q = 0
  · subst hQ0; rw [Tru, ite_eq_left rfl] at hR; exact hR.elim
  rw [Tru, ite_eq_right hQ0] at hR
  split_ifs at hR with hbase
  · -- {Q}
    rw [Set.mem_singleton_iff] at hR; subst hR; exact hQ
  · -- {Q} ∪ Tru (truncate (Q.natDegree - 1) Q)
    rw [Set.mem_union, Set.mem_singleton_iff] at hR
    rcases hR with rfl | hR
    · exact hQ
    · exact PolyConst.of_mem_Tru (hQ.truncate _) hR
termination_by Q.natDegree
decreasing_by
  have hQpos : 0 < Q.natDegree := by
    push Not at hbase
    exact Nat.pos_of_ne_zero hbase.2
  have := natDegree_truncate_le (Q.natDegree - 1) Q
  omega

end TruncateTru

/-! ### `pRemMv` preserves `PolyConst`

For `P, Q : Polynomial (MvPolynomial (Fin k) D)` both with `PolyConst`,
we show `PolyConst (pRemMv P Q)`. The key is the pseudo-division identity
`C(b^d) * P = A * Q + pRemMv P Q` together with the uniqueness of the
remainder. The `A` from `pRem_exists_aux` operates by ring operations on
`P, Q` (and `C` of their coefficients), all of which preserve `PolyConst`.

We prove this by extracting from `pRemMv_pseudo_div` the explicit form
`pRemMv P Q = C(b^d) * P - A * Q` and showing `A` itself is `PolyConst`.
This requires a strong-induction argument mirroring `pRem_exists_aux`.
-/

section PRem

variable {D : Type*} [CommRing D] [IsDomain D]

/-- Strong-induction version of `PolyConst` preservation for the
`pRem_exists_aux` construction: when `Q` and `P` are `PolyConst`, the
existential statement holds with `A` and `R` also `PolyConst`. -/
theorem pRem_exists_polyConst_aux
    (Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0)
    (hQc : PolyConst Q) :
    ∀ (p : ℕ) (P : Polynomial (MvPolynomial (Fin k) D)),
      P.natDegree < p → PolyConst P →
    ∀ (n : ℕ),
      (if P.natDegree < Q.natDegree then 0
       else P.natDegree - Q.natDegree + 1) ≤ n →
    ∃ A R : Polynomial (MvPolynomial (Fin k) D),
      Polynomial.C (Q.leadingCoeff ^ n) * P = A * Q + R ∧
      R.degree < Q.degree ∧
      PolyConst A ∧ PolyConst R := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro P hPdeg hPc n hn
    by_cases hP : P = 0
    · refine ⟨0, 0, by simp [hP], ?_, .zero, .zero⟩
      rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
    by_cases hdeg : P.natDegree < Q.natDegree
    · refine ⟨0, Polynomial.C (Q.leadingCoeff ^ n) * P, by ring, ?_, .zero, ?_⟩
      · have hbn : (Q.leadingCoeff ^ n) ≠ 0 :=
          pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hQ)
        have hnat : (Polynomial.C (Q.leadingCoeff ^ n) * P).natDegree = P.natDegree :=
          Polynomial.natDegree_C_mul hbn
        exact Polynomial.degree_lt_degree (hnat ▸ hdeg)
      · exact PolyConst.mul
          (PolyConst.C_const (MvPolynomial.vars_pow_empty
            (PolyConst.leadingCoeff_vars_empty hQc) n)) hPc
    have hdeg' : Q.natDegree ≤ P.natDegree := Nat.not_lt.mp hdeg
    have ha_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hb_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    rw [ite_eq_right hdeg] at hn
    have hn1 : 1 ≤ n := by omega
    set P' : Polynomial (MvPolynomial (Fin k) D) :=
      Polynomial.C Q.leadingCoeff * P -
        Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree) * Q
      with hP'def
    have hP'c : PolyConst P' := by
      apply PolyConst.sub
      · exact PolyConst.mul
          (PolyConst.C_const (PolyConst.leadingCoeff_vars_empty hQc)) hPc
      · exact PolyConst.mul
          (PolyConst.mul
            (PolyConst.C_const (PolyConst.leadingCoeff_vars_empty hPc))
            (PolyConst.pow PolyConst.X _)) hQc
    have hfund : Polynomial.C Q.leadingCoeff * P =
        Polynomial.C P.leadingCoeff *
          Polynomial.X ^ (P.natDegree - Q.natDegree) * Q + P' := by
      rw [hP'def]; ring
    obtain ⟨A', R', hAR', hdR', hA'c, hR'c⟩ :
        ∃ A' R' : Polynomial (MvPolynomial (Fin k) D),
          Polynomial.C (Q.leadingCoeff ^ (n - 1)) * P' = A' * Q + R' ∧
            R'.degree < Q.degree ∧ PolyConst A' ∧ PolyConst R' := by
      by_cases hP' : P' = 0
      · refine ⟨0, 0, by simp [hP'], ?_, .zero, .zero⟩
        rw [Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
      · have hsub : P.natDegree - Q.natDegree + Q.natDegree = P.natDegree :=
          Nat.sub_add_cancel hdeg'
        have hP'_natDeg : P'.natDegree < P.natDegree := by
          have hLdeg : (Polynomial.C Q.leadingCoeff * P).degree =
              (Polynomial.C P.leadingCoeff *
                Polynomial.X ^ (P.natDegree - Q.natDegree) * Q).degree := by
            rw [Polynomial.degree_C_mul hb_ne,
                mul_assoc,
                Polynomial.degree_C_mul ha_ne,
                Polynomial.degree_mul, Polynomial.degree_X_pow,
                Polynomial.degree_eq_natDegree hQ,
                Polynomial.degree_eq_natDegree hP]
            norm_cast
            omega
          have hLne : Polynomial.C Q.leadingCoeff * P ≠ 0 :=
            mul_ne_zero (fun h => hb_ne (Polynomial.C_eq_zero.mp h)) hP
          have hLeadEq : (Polynomial.C Q.leadingCoeff * P).leadingCoeff =
              (Polynomial.C P.leadingCoeff *
                Polynomial.X ^ (P.natDegree - Q.natDegree) * Q).leadingCoeff := by
            rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
                Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
                Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X_pow]
            ring
          have hP'_deg_lt : P'.degree < (Polynomial.C Q.leadingCoeff * P).degree :=
            Polynomial.degree_sub_lt_left hLdeg hLne hLeadEq
          rw [Polynomial.degree_C_mul hb_ne,
              Polynomial.degree_eq_natDegree hP',
              Polynomial.degree_eq_natDegree hP] at hP'_deg_lt
          exact_mod_cast hP'_deg_lt
        have hbound : (if P'.natDegree < Q.natDegree then 0
                       else P'.natDegree - Q.natDegree + 1) ≤ n - 1 := by
          split_ifs with h
          · omega
          · simp only [not_lt] at h
            omega
        exact ih P.natDegree hPdeg P' hP'_natDeg hP'c (n - 1) hbound
    refine ⟨A' + Polynomial.C (Q.leadingCoeff ^ (n - 1) * P.leadingCoeff) *
            Polynomial.X ^ (P.natDegree - Q.natDegree), R', ?_, hdR',
            ?_, hR'c⟩
    · have hbn : Q.leadingCoeff ^ n =
          Q.leadingCoeff ^ (n - 1) * Q.leadingCoeff := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]
      calc Polynomial.C (Q.leadingCoeff ^ n) * P
          = Polynomial.C (Q.leadingCoeff ^ (n - 1)) *
            (Polynomial.C Q.leadingCoeff * P) := by
            rw [hbn, Polynomial.C_mul]; ring
        _ = Polynomial.C (Q.leadingCoeff ^ (n - 1)) *
            (Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree)
              * Q + P') := by rw [hfund]
        _ = (A' + Polynomial.C (Q.leadingCoeff ^ (n - 1) * P.leadingCoeff) *
              Polynomial.X ^ (P.natDegree - Q.natDegree)) * Q + R' := by
            rw [Polynomial.C_mul]
            linear_combination hAR'
    · -- PolyConst on the new A
      apply PolyConst.add hA'c
      apply PolyConst.mul
      · apply PolyConst.C_const
        apply MvPolynomial.vars_mul_empty
        · exact MvPolynomial.vars_pow_empty
            (PolyConst.leadingCoeff_vars_empty hQc) _
        · exact PolyConst.leadingCoeff_vars_empty hPc
      · exact PolyConst.pow PolyConst.X _

/-- `pRemMv P Q` is `PolyConst` when both `P` and `Q` are. The proof
extracts `A, R` from `pRem_exists_polyConst_aux` and identifies `R` with
`pRemMv P Q` via uniqueness in the fraction field. -/
theorem pRemMv_polyConst {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) (hQ : PolyConst Q) :
    PolyConst (pRemMv P Q) := by
  unfold pRemMv
  split_ifs with hQ0
  · exact PolyConst.zero
  · -- Identify the `choose` with the R from pRem_exists_polyConst_aux
    -- by showing both equal the same Polynomial.map-image in the fraction field.
    set K := FractionRing (MvPolynomial (Fin k) D)
    have hbound : (if P.natDegree < Q.natDegree then 0
                   else P.natDegree - Q.natDegree + 1) ≤ pRemExp P Q := by
      split_ifs with h
      · exact Nat.zero_le _
      · exact pRemExp_ge P Q (Nat.not_lt.mp h)
    obtain ⟨A, R, hAR, hdR, hAc, hRc⟩ :=
      pRem_exists_polyConst_aux Q hQ0 hQ (P.natDegree + 1) P
        (Nat.lt_succ_self _) hP (pRemExp P Q) hbound
    -- The chosen `pRemMv` value equals `R` by uniqueness of the
    -- remainder when divided by `Q` in the fraction field.
    set choosePRem :=
      (@PRem_descends (MvPolynomial (Fin k) D) _ _ K _ _ _ P Q hQ0).choose
    have hchoosePRem_eq :
        choosePRem.map (algebraMap (MvPolynomial (Fin k) D) K) = PRem K P Q :=
      (@PRem_descends (MvPolynomial (Fin k) D) _ _ K _ _ _ P Q hQ0).choose_spec
    -- Show choosePRem = R.
    suffices hch : choosePRem = R from by rw [hch]; exact hRc
    have hinj := IsFractionRing.injective (MvPolynomial (Fin k) D) K
    apply Polynomial.map_injective (algebraMap (MvPolynomial (Fin k) D) K) hinj
    rw [hchoosePRem_eq]
    -- PRem K P Q is the unique remainder; show R.map = PRem K P Q.
    have hmap := congrArg (Polynomial.map (algebraMap (MvPolynomial (Fin k) D) K)) hAR
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at hmap
    unfold PRem Rem
    simp only [Polynomial.map_mul, Polynomial.map_C]
    have hQmap_ne : Q.map (algebraMap (MvPolynomial (Fin k) D) K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinj).mpr hQ0
    have hdR_map : (R.map (algebraMap (MvPolynomial (Fin k) D) K)).degree <
        (Q.map (algebraMap (MvPolynomial (Fin k) D) K)).degree := by
      rwa [Polynomial.degree_map_eq_of_injective hinj,
           Polynomial.degree_map_eq_of_injective hinj Q]
    have hdvd : Q.map (algebraMap (MvPolynomial (Fin k) D) K) ∣
        (Polynomial.C ((algebraMap (MvPolynomial (Fin k) D) K)
          (Q.leadingCoeff ^ pRemExp P Q)) *
          P.map (algebraMap (MvPolynomial (Fin k) D) K)) -
          R.map (algebraMap (MvPolynomial (Fin k) D) K) :=
      ⟨A.map (algebraMap (MvPolynomial (Fin k) D) K), by linear_combination hmap⟩
    have hmod_sub :
        ((Polynomial.C ((algebraMap (MvPolynomial (Fin k) D) K)
          (Q.leadingCoeff ^ pRemExp P Q)) *
          P.map (algebraMap (MvPolynomial (Fin k) D) K)) -
          R.map (algebraMap (MvPolynomial (Fin k) D) K)) %
          Q.map (algebraMap (MvPolynomial (Fin k) D) K) = 0 :=
      EuclideanDomain.mod_eq_zero.mpr hdvd
    rw [Polynomial.sub_mod, sub_eq_zero] at hmod_sub
    rw [hmod_sub, (Polynomial.mod_eq_self_iff hQmap_ne).mpr hdR_map]

end PRem

/-! ### Path tracking through `TRems`, `pathLeafParent` -/

section PathTracking

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

/-- Every element appearing in any leafPath of any subtree of `mkTRemsNode`
is `PolyConst`. We state this as a structural property. -/
theorem PolyConst.mkTRemsNode_subtree_root
    {parentPol curPol : Polynomial (MvPolynomial (Fin k) D)}
    (_hp : PolyConst parentPol) (hc : PolyConst curPol) :
    PolyConst (mkTRemsNode parentPol curPol).root := by
  unfold mkTRemsNode
  split_ifs
  · simpa [RoseTree.root] using hc
  · simpa [RoseTree.root] using hc

omit [IsDomain D] in
theorem polyConst_pathLeafParentAux
    {cur : Polynomial (MvPolynomial (Fin k) D)} (hc : PolyConst cur)
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : ∀ P ∈ path, PolyConst P) :
    PolyConst (pathLeafParentAux cur path) := by
  induction path generalizing cur with
  | nil => exact hc
  | cons q rest ih =>
    by_cases hq : q = 0
    · have heq : pathLeafParentAux cur (q :: rest) = cur := by
        simp [pathLeafParentAux, hq]
      rw [heq]; exact hc
    · have heq : pathLeafParentAux cur (q :: rest) = pathLeafParentAux q rest := by
        simp [pathLeafParentAux, hq]
      rw [heq]
      exact ih (hpath q (by simp)) (fun P hP => hpath P (by simp [hP]))

omit [IsDomain D] in
theorem polyConst_pathLeafParent
    {P : Polynomial (MvPolynomial (Fin k) D)} (hP : PolyConst P)
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : ∀ Q ∈ path, PolyConst Q) :
    PolyConst (pathLeafParent P path) := by
  induction path with
  | nil => exact hP
  | cons q rest _ =>
    by_cases hq : q = 0
    · have heq : pathLeafParent P (q :: rest) = P := by
        simp [pathLeafParent, hq]
      rw [heq]; exact hP
    · have heq : pathLeafParent P (q :: rest) = pathLeafParentAux q rest := by
        simp [pathLeafParent, hq]
      rw [heq]
      exact polyConst_pathLeafParentAux (hpath q (by simp))
        (fun Q hQ => hpath Q (List.mem_cons_of_mem _ hQ))

end PathTracking

/-! ### TRems leafPaths and tree-root values are `PolyConst` -/

section TRemsTracking

variable {D : Type*} [CommRing D] [IsDomain D]

/-- All polynomials labeling nodes in the subtree built by `mkTRemsNode`
are `PolyConst`. -/
theorem PolyConst.mkTRemsNode_all
    {parentPol curPol : Polynomial (MvPolynomial (Fin k) D)}
    (hp : PolyConst parentPol) (hc : PolyConst curPol) :
    ∀ path ∈ (mkTRemsNode parentPol curPol).leafPaths,
      ∀ Q ∈ path, PolyConst Q := by
  intro path hpath Q hQ
  by_cases hcur0 : curPol = 0
  · -- curPol = 0: tree is .node curPol []
    rw [mkTRemsNode, ite_eq_left hcur0] at hpath
    simp only [RoseTree.leafPaths, List.mem_singleton] at hpath
    subst hpath
    exact absurd hQ (List.not_mem_nil)
  · -- curPol ≠ 0
    rw [mkTRemsNode, ite_eq_right hcur0] at hpath
    dsimp only at hpath
    set R := -(pRemMv parentPol curPol) with R_def
    have hRc : PolyConst R := PolyConst.neg (pRemMv_polyConst hp hc)
    set cs := (Tru_finite R).toFinset.toList with cs_def
    set tru_trees := cs.attach.map (fun ⟨c, _⟩ => mkTRemsNode curPol c)
      with tt_def
    set ac := tru_trees ++ [RoseTree.node (0 : Polynomial (MvPolynomial (Fin k) D)) []]
      with ac_def
    have hac_ne : ac ≠ [] := by simp [ac_def]
    rw [leafPaths_node_ne_nil curPol ac hac_ne] at hpath
    simp only [List.mem_flatMap, List.mem_map] at hpath
    obtain ⟨child, hchild_mem, sp, hsp_mem, rfl⟩ := hpath
    rw [List.mem_cons] at hQ
    rw [ac_def, List.mem_append, List.mem_singleton] at hchild_mem
    rcases hQ with rfl | hQ
    · -- Q = child.root
      rcases hchild_mem with hchild_mem | rfl
      · rw [tt_def, List.mem_map] at hchild_mem
        obtain ⟨⟨c, hc_mem⟩, _, rfl⟩ := hchild_mem
        have hcc : PolyConst c := by
          have hc_tru : c ∈ Tru R :=
            (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_mem)
          exact PolyConst.of_mem_Tru hRc hc_tru
        rw [mkTRemsNode_root]
        exact hcc
      · simp only [RoseTree.root]; exact PolyConst.zero
    · -- Q ∈ sp; recurse on child
      rcases hchild_mem with hchild_mem | rfl
      · rw [tt_def, List.mem_map] at hchild_mem
        obtain ⟨⟨c, hc_mem⟩, _, rfl⟩ := hchild_mem
        have hcc : PolyConst c := by
          have hc_tru : c ∈ Tru R :=
            (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_mem)
          exact PolyConst.of_mem_Tru hRc hc_tru
        exact PolyConst.mkTRemsNode_all hc hcc sp hsp_mem Q hQ
      · -- terminal .node 0 []: sp = []
        simp only [RoseTree.leafPaths, List.mem_singleton] at hsp_mem
        subst hsp_mem; exact absurd hQ (List.not_mem_nil)
termination_by curPol.natDegree
decreasing_by
  have hmem_tru : c ∈ Tru R :=
    (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_mem)
  by_cases h4 : pRemMv parentPol curPol = 0
  · have hn0 : R = 0 :=
      show -(pRemMv parentPol curPol) = 0 by rw [h4, neg_zero]
    rw [hn0, Tru, ite_eq_left rfl] at hmem_tru; exact hmem_tru.elim
  · have h1 := natDegree_mem_Tru_le hmem_tru
    have h5 := Polynomial.natDegree_lt_natDegree h4
      (degree_pRemMv_lt parentPol curPol hcur0)
    have h6 : R.natDegree = (pRemMv parentPol curPol).natDegree :=
      Polynomial.natDegree_neg _
    omega

/-- All polynomials on any leafPath of `TRems P Q` are `PolyConst` when
both `P` and `Q` are. -/
theorem PolyConst.TRems_leafPaths
    {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) (hQ : PolyConst Q) :
    ∀ path ∈ (TRems P Q).leafPaths, ∀ R ∈ path, PolyConst R := by
  intro path hpath R hR
  rw [TRems] at hpath
  set cs := (Tru_finite Q).toFinset.toList with cs_def
  set tru_trees := cs.map (mkTRemsNode P) with tt_def
  set ac := tru_trees ++ [RoseTree.node (0 : Polynomial (MvPolynomial (Fin k) D)) []]
    with ac_def
  have hac_ne : ac ≠ [] := by simp [ac_def]
  rw [leafPaths_node_ne_nil P ac hac_ne] at hpath
  simp only [List.mem_flatMap, List.mem_map] at hpath
  obtain ⟨child, hchild_mem, sp, hsp_mem, rfl⟩ := hpath
  rw [List.mem_cons] at hR
  rw [ac_def, List.mem_append, List.mem_singleton] at hchild_mem
  rcases hR with rfl | hR
  · rcases hchild_mem with hchild_mem | rfl
    · rw [tt_def, List.mem_map] at hchild_mem
      obtain ⟨c, hc_mem, rfl⟩ := hchild_mem
      have hcc : PolyConst c :=
        PolyConst.of_mem_Tru hQ
          ((Set.Finite.mem_toFinset _).mp ((Finset.mem_toList).mp hc_mem))
      rw [mkTRemsNode_root]
      exact hcc
    · simp only [RoseTree.root]; exact PolyConst.zero
  · rcases hchild_mem with hchild_mem | rfl
    · rw [tt_def, List.mem_map] at hchild_mem
      obtain ⟨c, hc_mem, rfl⟩ := hchild_mem
      have hcc : PolyConst c :=
        PolyConst.of_mem_Tru hQ
          ((Set.Finite.mem_toFinset _).mp ((Finset.mem_toList).mp hc_mem))
      exact PolyConst.mkTRemsNode_all hP hcc sp hsp_mem R hR
    · simp only [RoseTree.leafPaths, List.mem_singleton] at hsp_mem
      subst hsp_mem; exact absurd hR (List.not_mem_nil)

end TRemsTracking

/-! ### Formula-level: empty `freeVars` from `PolyConst` -/

section FormulaTracking

open Classical

variable {D : Type*} [CommRing D]

/-- `conjList` of formulas with empty `freeVars` has empty `freeVars`. -/
theorem Formula.conjList_freeVars_empty
    {σ : Type*} [DecidableEq σ]
    {Φs : List (Formula σ (FieldAtom σ D))}
    (h : ∀ Φ ∈ Φs, Φ.freeVars = ∅) :
    (Formula.conjList Φs).freeVars = ∅ := by
  induction Φs with
  | nil =>
    show Formula.freeVars (Formula.trueFormula : Formula σ (FieldAtom σ D)) = ∅
    show (Formula.eq_zero (0 : MvPolynomial σ D)).freeVars = ∅
    show (Formula.atom (FieldAtom.eqZero 0)).freeVars = ∅
    simp [Formula.freeVars, FieldAtom.vars, FieldAtom.eqZero]
  | cons Φ rest ih =>
    show (Formula.and Φ (Formula.conjList rest)).freeVars = ∅
    show Φ.freeVars ∪ (Formula.conjList rest).freeVars = ∅
    rw [h Φ List.mem_cons_self,
      ih (fun Ψ hΨ => h Ψ (List.mem_cons_of_mem _ hΨ))]
    simp

/-- `disjList` of formulas with empty `freeVars` has empty `freeVars`. -/
theorem Formula.disjList_freeVars_empty
    {σ : Type*} [DecidableEq σ]
    {Φs : List (Formula σ (FieldAtom σ D))}
    (h : ∀ Φ ∈ Φs, Φ.freeVars = ∅) :
    (Formula.disjList Φs).freeVars = ∅ := by
  induction Φs with
  | nil =>
    show Formula.freeVars (Formula.falseFormula : Formula σ (FieldAtom σ D)) = ∅
    show (Formula.ne_zero (0 : MvPolynomial σ D)).freeVars = ∅
    show (Formula.atom (FieldAtom.neZero 0)).freeVars = ∅
    simp [Formula.freeVars, FieldAtom.vars, FieldAtom.neZero]
  | cons Φ rest ih =>
    show (Formula.or Φ (Formula.disjList rest)).freeVars = ∅
    show Φ.freeVars ∪ (Formula.disjList rest).freeVars = ∅
    rw [h Φ List.mem_cons_self,
      ih (fun Ψ hΨ => h Ψ (List.mem_cons_of_mem _ hΨ))]
    simp

/-- `eq_zero P` has freeVars equal to P.vars. -/
theorem Formula.eq_zero_freeVars (P : MvPolynomial (Fin k) D) :
    (Formula.eq_zero P).freeVars = P.vars := by
  show (Formula.atom (FieldAtom.eqZero P)).freeVars = P.vars
  show (FieldAtom.eqZero P).vars = P.vars
  rfl

/-- `ne_zero P` has freeVars equal to P.vars. -/
theorem Formula.ne_zero_freeVars (P : MvPolynomial (Fin k) D) :
    (Formula.ne_zero P).freeVars = P.vars := by
  show (Formula.atom (FieldAtom.neZero P)).freeVars = P.vars
  show (FieldAtom.neZero P).vars = P.vars
  rfl

/-! ### degFormula, degEqFormula, degNeqFormula have empty `freeVars`
when input is `PolyConst`. -/

theorem degFormula_freeVars_empty
    {Q : Polynomial (MvPolynomial (Fin k) D)} (hQ : PolyConst Q)
    (i : WithBot ℕ) :
    (degFormula Q i).freeVars = ∅ := by
  cases i with
  | bot =>
    show (Formula.conjList ((List.range (Q.natDegree + 1)).map fun j =>
        Formula.eq_zero (Q.coeff j))).freeVars = ∅
    apply Formula.conjList_freeVars_empty
    intro Φ hΦ
    rw [List.mem_map] at hΦ
    obtain ⟨j, _, rfl⟩ := hΦ
    rw [Formula.eq_zero_freeVars]
    exact hQ j
  | coe n =>
    show (Formula.and (Formula.ne_zero (Q.coeff n))
      (Formula.conjList ((List.range (Q.natDegree - n)).map fun j =>
        Formula.eq_zero (Q.coeff (n + 1 + j))))).freeVars = ∅
    show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
    rw [Formula.ne_zero_freeVars, hQ n]
    rw [Formula.conjList_freeVars_empty (by
      intro Φ hΦ
      rw [List.mem_map] at hΦ
      obtain ⟨j, _, rfl⟩ := hΦ
      rw [Formula.eq_zero_freeVars]
      exact hQ _)]
    simp

theorem degEqFormula_freeVars_empty
    {Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)}
    (hQ₁ : PolyConst Q₁) (hQ₂ : PolyConst Q₂) :
    (degEqFormula Q₁ Q₂).freeVars = ∅ := by
  unfold degEqFormula
  apply Formula.disjList_freeVars_empty
  intro Φ hΦ
  rw [List.mem_cons] at hΦ
  rcases hΦ with rfl | hΦ
  · show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
    rw [degFormula_freeVars_empty hQ₁, degFormula_freeVars_empty hQ₂]
    simp
  · rw [List.mem_map] at hΦ
    obtain ⟨i, _, rfl⟩ := hΦ
    show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
    rw [degFormula_freeVars_empty hQ₁ (some i),
      degFormula_freeVars_empty hQ₂ (some i)]
    simp

theorem degNeqFormula_freeVars_empty
    {Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)}
    (hQ₁ : PolyConst Q₁) (hQ₂ : PolyConst Q₂) :
    (degNeqFormula Q₁ Q₂).freeVars = ∅ := by
  show (degEqFormula Q₁ Q₂).freeVars = ∅
  exact degEqFormula_freeVars_empty hQ₁ hQ₂

variable [IsDomain D]

theorem leafFormulaAux_freeVars_empty
    {parent cur : Polynomial (MvPolynomial (Fin k) D)}
    (hp : PolyConst parent) (hc : PolyConst cur)
    {rest : List (Polynomial (MvPolynomial (Fin k) D))}
    (hrest : ∀ P ∈ rest, PolyConst P) :
    (leafFormulaAux parent cur rest).freeVars = ∅ := by
  induction rest generalizing parent cur with
  | nil =>
    show (degFormula (-(pRemMv parent cur)) ⊥).freeVars = ∅
    exact degFormula_freeVars_empty (PolyConst.neg (pRemMv_polyConst hp hc)) _
  | cons next rest' ih =>
    by_cases hnext : next = 0
    · have heq : leafFormulaAux parent cur (next :: rest') =
          degFormula (-(pRemMv parent cur)) ⊥ := by
        simp [leafFormulaAux, hnext]
      rw [heq]
      exact degFormula_freeVars_empty (PolyConst.neg (pRemMv_polyConst hp hc)) _
    · have heq : leafFormulaAux parent cur (next :: rest') =
          (degFormula (-(pRemMv parent cur)) (↑next.natDegree)).and
            (leafFormulaAux cur next rest') := by
        simp [leafFormulaAux, hnext]
      rw [heq]
      show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
      rw [degFormula_freeVars_empty (PolyConst.neg (pRemMv_polyConst hp hc))]
      rw [ih hc (hrest next List.mem_cons_self)
        (fun P hP => hrest P (List.mem_cons_of_mem _ hP))]
      simp

theorem leafFormula_freeVars_empty
    {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyConst P) (hQ : PolyConst Q)
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : ∀ R ∈ path, PolyConst R) :
    (leafFormula P Q path).freeVars = ∅ := by
  cases path with
  | nil =>
    show (degFormula Q ⊥).freeVars = ∅
    exact degFormula_freeVars_empty hQ _
  | cons q rest =>
    by_cases hq : q = 0
    · have heq : leafFormula P Q (q :: rest) = degFormula Q ⊥ := by
        simp [leafFormula, hq]
      rw [heq]
      exact degFormula_freeVars_empty hQ _
    · have heq : leafFormula P Q (q :: rest) =
          (degFormula Q (↑q.natDegree)).and (leafFormulaAux P q rest) := by
        simp [leafFormula, hq]
      rw [heq]
      show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
      rw [degFormula_freeVars_empty hQ]
      rw [leafFormulaAux_freeVars_empty hP (hpath q List.mem_cons_self)
        (fun R hR => hpath R (List.mem_cons_of_mem _ hR))]
      simp

end FormulaTracking

/-! ### `posgcd` preserves the empty-freeVars property -/

section PosgcdTracking

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

/-- Every element appearing in `posgcd Ps` consists of a `PolyConst`
polynomial paired with a formula whose `freeVars = ∅`, when all input
polynomials are `PolyConst`. -/
theorem posgcd_polyConst_and_freeVars_empty
    {Ps : List (Polynomial (MvPolynomial (Fin k) D))}
    (hPs : ∀ P ∈ Ps, PolyConst P) :
    ∀ GC ∈ posgcd Ps, PolyConst GC.1 ∧ GC.2.freeVars = ∅ := by
  induction Ps with
  | nil =>
    intro GC hmem
    simp only [posgcd, List.mem_singleton] at hmem
    subst hmem
    refine ⟨PolyConst.zero, ?_⟩
    show Formula.freeVars (Formula.trueFormula : Formula (Fin k) (FieldAtom (Fin k) D)) = ∅
    show (Formula.eq_zero (0 : MvPolynomial (Fin k) D)).freeVars = ∅
    show (Formula.atom (FieldAtom.eqZero 0)).freeVars = ∅
    simp [Formula.freeVars, FieldAtom.vars, FieldAtom.eqZero]
  | cons P rest ih =>
    intro GC hmem
    simp only [posgcd, List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨⟨Q, 𝒞⟩, hQC_mem, path, hpath, h_eq⟩ := hmem
    -- GC = (pathLeafParent P path, 𝒞.and (leafFormula P Q path))
    have hPc : PolyConst P := hPs P List.mem_cons_self
    have hrestPs : ∀ R ∈ rest, PolyConst R :=
      fun R hR => hPs R (List.mem_cons_of_mem _ hR)
    have ⟨hQc, hCfv⟩ := ih hrestPs (Q, 𝒞) hQC_mem
    have hpathPc : ∀ R ∈ path, PolyConst R :=
      PolyConst.TRems_leafPaths hPc hQc path hpath
    refine ⟨?_, ?_⟩
    · rw [← h_eq]
      exact polyConst_pathLeafParent hPc hpathPc
    · rw [← h_eq]
      show (𝒞.and (leafFormula P Q path)).freeVars = ∅
      show 𝒞.freeVars ∪ (leafFormula P Q path).freeVars = ∅
      rw [hCfv, leafFormula_freeVars_empty hPc hQc hpathPc]
      simp

end PosgcdTracking

/-! ### `projBasic` has empty `freeVars` when inputs have empty `vars` -/

section ProjBasic

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsDomain D] in
/-- The "split last" of every poly in `Ps` is `PolyConst` when each
poly has empty `vars`. -/
theorem map_splitLast_polyConst_of_vars_empty
    {Ps : List (MvPolynomial (Fin (k+1)) D)}
    (hPs : ∀ P ∈ Ps, P.vars = ∅) :
    ∀ Q ∈ Ps.map splitLast, PolyConst Q := by
  intro Q hQ
  rw [List.mem_map] at hQ
  obtain ⟨P, hP_mem, rfl⟩ := hQ
  exact splitLast_polyConst_of_vars_empty (hPs P hP_mem)

omit [IsDomain D] in
theorem map_splitLast_polyConst_of_vars_subset_last
    {Ps : List (MvPolynomial (Fin (k+1)) D)}
    (hPs : ∀ P ∈ Ps, P.vars ⊆ {Fin.last k}) :
    ∀ Q ∈ Ps.map splitLast, PolyConst Q := by
  intro Q hQ
  rw [List.mem_map] at hQ
  obtain ⟨P, hP_mem, rfl⟩ := hQ
  exact splitLast_polyConst_of_vars_subset_last (hPs P hP_mem)

/-- **Generalization**: `projBasic Ps Qs` has empty `freeVars` when all
input polynomials have `vars ⊆ {Fin.last k}` (i.e., only the "last"
variable, which becomes the polynomial's X). -/
theorem projBasic_freeVars_empty_of_vars_subset_last
    {Ps Qs : List (MvPolynomial (Fin (k+1)) D)}
    (hPs : ∀ P ∈ Ps, P.vars ⊆ {Fin.last k})
    (hQs : ∀ Q ∈ Qs, Q.vars ⊆ {Fin.last k}) :
    (projBasic Ps Qs).freeVars = ∅ := by
  show (Formula.disjList _).freeVars = ∅
  apply Formula.disjList_freeVars_empty
  intro Φ hΦ
  simp only [List.mem_flatMap, List.mem_map, Prod.exists] at hΦ
  obtain ⟨G_1, C_1, h_mem_posgcd, path, hpath_mem, rfl⟩ := hΦ
  set Ps' : List (Polynomial (MvPolynomial (Fin k) D)) := Ps.map splitLast with Ps'_def
  set Qs' : List (Polynomial (MvPolynomial (Fin k) D)) := Qs.map splitLast with Qs'_def
  set d : ℕ := 1 + (Ps'.map Polynomial.natDegree).foldr max 0
  set extra : Polynomial (MvPolynomial (Fin k) D) := Qs'.prod ^ d
  have hPs'c : ∀ Q ∈ Ps', PolyConst Q :=
    map_splitLast_polyConst_of_vars_subset_last hPs
  have hQs'c : ∀ Q ∈ Qs', PolyConst Q :=
    map_splitLast_polyConst_of_vars_subset_last hQs
  have hextrac : PolyConst extra := PolyConst.pow (PolyConst.prod hQs'c) _
  have ⟨hG_1c, hC_1fv⟩ :=
    posgcd_polyConst_and_freeVars_empty hPs'c (G_1, C_1) h_mem_posgcd
  have hpath_PolyConst : ∀ R ∈ path, PolyConst R :=
    PolyConst.TRems_leafPaths hextrac hG_1c path hpath_mem
  show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
  rw [hC_1fv]
  show ∅ ∪ Formula.freeVars _ = ∅
  rw [Finset.empty_union]
  show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
  rw [leafFormula_freeVars_empty hextrac hG_1c hpath_PolyConst]
  rw [degNeqFormula_freeVars_empty
    (polyConst_pathLeafParent hextrac hpath_PolyConst) hG_1c]
  simp

/-- **Key**: `projBasic Ps Qs` has empty `freeVars` when all input
polynomials have empty `vars`. -/
theorem projBasic_freeVars_empty
    {Ps Qs : List (MvPolynomial (Fin (k+1)) D)}
    (hPs : ∀ P ∈ Ps, P.vars = ∅) (hQs : ∀ Q ∈ Qs, Q.vars = ∅) :
    (projBasic Ps Qs).freeVars = ∅ := by
  -- Unfold projBasic.
  show (Formula.disjList _).freeVars = ∅
  apply Formula.disjList_freeVars_empty
  intro Φ hΦ
  simp only [List.mem_flatMap, List.mem_map, Prod.exists] at hΦ
  obtain ⟨G_1, C_1, h_mem_posgcd, path, hpath_mem, rfl⟩ := hΦ
  -- The polynomials in projBasic's outer let:
  set Ps' : List (Polynomial (MvPolynomial (Fin k) D)) := Ps.map splitLast with Ps'_def
  set Qs' : List (Polynomial (MvPolynomial (Fin k) D)) := Qs.map splitLast with Qs'_def
  set d : ℕ := 1 + (Ps'.map Polynomial.natDegree).foldr max 0
  set extra : Polynomial (MvPolynomial (Fin k) D) := Qs'.prod ^ d
  have hPs'c : ∀ Q ∈ Ps', PolyConst Q :=
    map_splitLast_polyConst_of_vars_empty hPs
  have hQs'c : ∀ Q ∈ Qs', PolyConst Q :=
    map_splitLast_polyConst_of_vars_empty hQs
  have hextrac : PolyConst extra := PolyConst.pow (PolyConst.prod hQs'c) _
  -- From posgcd_polyConst_and_freeVars_empty on (G_1, C_1) ∈ posgcd Ps'
  have ⟨hG_1c, hC_1fv⟩ :=
    posgcd_polyConst_and_freeVars_empty hPs'c (G_1, C_1) h_mem_posgcd
  -- From PolyConst.TRems_leafPaths: every elt of path is PolyConst.
  have hpath_PolyConst : ∀ R ∈ path, PolyConst R :=
    PolyConst.TRems_leafPaths hextrac hG_1c path hpath_mem
  -- Now compute freeVars of:
  --   C_1.and ((leafFormula extra G_1 path).and (degNeqFormula (pathLeafParent extra path) G_1))
  show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
  rw [hC_1fv]
  show ∅ ∪ Formula.freeVars _ = ∅
  rw [Finset.empty_union]
  show Formula.freeVars _ ∪ Formula.freeVars _ = ∅
  rw [leafFormula_freeVars_empty hextrac hG_1c hpath_PolyConst]
  rw [degNeqFormula_freeVars_empty
    (polyConst_pathLeafParent hextrac hpath_PolyConst) hG_1c]
  simp

end ProjBasic

/-! ### `qfDNFAux` polynomials have empty `vars` when input is a sentence -/

section QfDNFTracking

open Classical

variable {D : Type*} [CommRing D]

/-- All polynomials appearing in `qfDNFAux b Φ`'s output pairs have
`vars ⊆ Φ.freeVars`, for any QF `Φ`. -/
theorem qfDNFAux_polys_vars_subset
    {σ : Type*} [DecidableEq σ]
    (b : Bool) {Φ : Formula σ (FieldAtom σ D)}
    (hQF : Φ.IsQuantifierFree) :
    ∀ PQ ∈ qfDNFAux b Φ,
      (∀ P ∈ PQ.1, P.vars ⊆ Φ.freeVars) ∧
        (∀ Q ∈ PQ.2, Q.vars ⊆ Φ.freeVars) := by
  induction Φ generalizing b with
  | atom a =>
    intro PQ hPQ
    have haVars : a.poly.vars = Formula.freeVars (Formula.atom a) := rfl
    simp only [qfDNFAux] at hPQ
    split_ifs at hPQ
    · simp only [List.mem_singleton] at hPQ; subst hPQ
      refine ⟨?_, ?_⟩
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; rw [haVars]
      · intro p hp; exact absurd hp (List.not_mem_nil)
    · simp only [List.mem_singleton] at hPQ; subst hPQ
      refine ⟨?_, ?_⟩
      · intro p hp; exact absurd hp (List.not_mem_nil)
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; rw [haVars]
    · simp only [List.mem_singleton] at hPQ; subst hPQ
      refine ⟨?_, ?_⟩
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; rw [haVars]
      · intro p hp; exact absurd hp (List.not_mem_nil)
    · simp only [List.mem_singleton] at hPQ; subst hPQ
      refine ⟨?_, ?_⟩
      · intro p hp; exact absurd hp (List.not_mem_nil)
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; rw [haVars]
  | not Φ ih =>
    have hQF' : Φ.IsQuantifierFree := hQF
    intro PQ hPQ
    simp only [qfDNFAux] at hPQ
    have hfvEq : Formula.freeVars (Formula.not Φ) = Φ.freeVars := rfl
    rw [hfvEq]
    exact ih (!b) hQF' PQ hPQ
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    intro PQ hPQ
    simp only [qfDNFAux] at hPQ
    have hfvEq : Formula.freeVars (Formula.and Φ₁ Φ₂) = Φ₁.freeVars ∪ Φ₂.freeVars := rfl
    rw [hfvEq]
    split_ifs at hPQ
    · rw [List.mem_flatMap] at hPQ
      obtain ⟨PQ₁, hPQ₁, hPQ₂⟩ := hPQ
      rw [List.mem_map] at hPQ₂
      obtain ⟨PQ₂, hPQ₂, rfl⟩ := hPQ₂
      have ⟨h₁P, h₁Q⟩ := ih₁ true hQF₁ PQ₁ hPQ₁
      have ⟨h₂P, h₂Q⟩ := ih₂ true hQF₂ PQ₂ hPQ₂
      refine ⟨?_, ?_⟩
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact (h₁P p hp).trans Finset.subset_union_left
        · exact (h₂P p hp).trans Finset.subset_union_right
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact (h₁Q p hp).trans Finset.subset_union_left
        · exact (h₂Q p hp).trans Finset.subset_union_right
    · rw [List.mem_append] at hPQ
      rcases hPQ with hPQ | hPQ
      · have ⟨hP, hQ⟩ := ih₁ false hQF₁ PQ hPQ
        exact ⟨fun p hp => (hP p hp).trans Finset.subset_union_left,
               fun p hp => (hQ p hp).trans Finset.subset_union_left⟩
      · have ⟨hP, hQ⟩ := ih₂ false hQF₂ PQ hPQ
        exact ⟨fun p hp => (hP p hp).trans Finset.subset_union_right,
               fun p hp => (hQ p hp).trans Finset.subset_union_right⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    intro PQ hPQ
    simp only [qfDNFAux] at hPQ
    have hfvEq : Formula.freeVars (Formula.or Φ₁ Φ₂) = Φ₁.freeVars ∪ Φ₂.freeVars := rfl
    rw [hfvEq]
    split_ifs at hPQ
    · rw [List.mem_append] at hPQ
      rcases hPQ with hPQ | hPQ
      · have ⟨hP, hQ⟩ := ih₁ true hQF₁ PQ hPQ
        exact ⟨fun p hp => (hP p hp).trans Finset.subset_union_left,
               fun p hp => (hQ p hp).trans Finset.subset_union_left⟩
      · have ⟨hP, hQ⟩ := ih₂ true hQF₂ PQ hPQ
        exact ⟨fun p hp => (hP p hp).trans Finset.subset_union_right,
               fun p hp => (hQ p hp).trans Finset.subset_union_right⟩
    · rw [List.mem_flatMap] at hPQ
      obtain ⟨PQ₁, hPQ₁, hPQ₂⟩ := hPQ
      rw [List.mem_map] at hPQ₂
      obtain ⟨PQ₂, hPQ₂, rfl⟩ := hPQ₂
      have ⟨h₁P, h₁Q⟩ := ih₁ false hQF₁ PQ₁ hPQ₁
      have ⟨h₂P, h₂Q⟩ := ih₂ false hQF₂ PQ₂ hPQ₂
      refine ⟨?_, ?_⟩
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact (h₁P p hp).trans Finset.subset_union_left
        · exact (h₂P p hp).trans Finset.subset_union_right
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact (h₁Q p hp).trans Finset.subset_union_left
        · exact (h₂Q p hp).trans Finset.subset_union_right
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    intro PQ hPQ
    simp only [qfDNFAux] at hPQ
    have hfvEq : Formula.freeVars (Formula.implies Φ₁ Φ₂) =
        Φ₁.freeVars ∪ Φ₂.freeVars := rfl
    rw [hfvEq]
    split_ifs at hPQ
    · rw [List.mem_append] at hPQ
      rcases hPQ with hPQ | hPQ
      · have ⟨hP, hQ⟩ := ih₁ false hQF₁ PQ hPQ
        exact ⟨fun p hp => (hP p hp).trans Finset.subset_union_left,
               fun p hp => (hQ p hp).trans Finset.subset_union_left⟩
      · have ⟨hP, hQ⟩ := ih₂ true hQF₂ PQ hPQ
        exact ⟨fun p hp => (hP p hp).trans Finset.subset_union_right,
               fun p hp => (hQ p hp).trans Finset.subset_union_right⟩
    · rw [List.mem_flatMap] at hPQ
      obtain ⟨PQ₁, hPQ₁, hPQ₂⟩ := hPQ
      rw [List.mem_map] at hPQ₂
      obtain ⟨PQ₂, hPQ₂, rfl⟩ := hPQ₂
      have ⟨h₁P, h₁Q⟩ := ih₁ true hQF₁ PQ₁ hPQ₁
      have ⟨h₂P, h₂Q⟩ := ih₂ false hQF₂ PQ₂ hPQ₂
      refine ⟨?_, ?_⟩
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact (h₁P p hp).trans Finset.subset_union_left
        · exact (h₂P p hp).trans Finset.subset_union_right
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact (h₁Q p hp).trans Finset.subset_union_left
        · exact (h₂Q p hp).trans Finset.subset_union_right
  | exists_ _ _ _ => exact absurd hQF id
  | forall_ _ _ _ => exact absurd hQF id

/-- All polynomials appearing in `qfDNFAux b Φ`'s output pairs have
empty `vars`, when `Φ` is QF with empty `freeVars`. -/
theorem qfDNFAux_polys_vars_empty
    {σ : Type*} [DecidableEq σ]
    (b : Bool) {Φ : Formula σ (FieldAtom σ D)}
    (hQF : Φ.IsQuantifierFree) (hSent : Φ.freeVars = ∅) :
    ∀ PQ ∈ qfDNFAux b Φ,
      (∀ P ∈ PQ.1, P.vars = ∅) ∧ (∀ Q ∈ PQ.2, Q.vars = ∅) := by
  induction Φ generalizing b with
  | atom a =>
    intro PQ hPQ
    have haVars : a.poly.vars = ∅ := hSent
    simp only [qfDNFAux] at hPQ
    split_ifs at hPQ
    · simp only [List.mem_singleton] at hPQ; subst hPQ
      refine ⟨?_, ?_⟩
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact haVars
      · intro p hp; exact absurd hp (List.not_mem_nil)
    · simp only [List.mem_singleton] at hPQ; subst hPQ
      refine ⟨?_, ?_⟩
      · intro p hp; exact absurd hp (List.not_mem_nil)
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact haVars
    · simp only [List.mem_singleton] at hPQ; subst hPQ
      refine ⟨?_, ?_⟩
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact haVars
      · intro p hp; exact absurd hp (List.not_mem_nil)
    · simp only [List.mem_singleton] at hPQ; subst hPQ
      refine ⟨?_, ?_⟩
      · intro p hp; exact absurd hp (List.not_mem_nil)
      · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact haVars
  | not Φ ih =>
    have hSent' : Φ.freeVars = ∅ := hSent
    intro PQ hPQ
    simp only [qfDNFAux] at hPQ
    exact ih (!b) hQF hSent' PQ hPQ
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have hu : Φ₁.freeVars ∪ Φ₂.freeVars = ∅ := hSent
    have hSent₁ : Φ₁.freeVars = ∅ := (Finset.union_eq_empty.mp hu).1
    have hSent₂ : Φ₂.freeVars = ∅ := (Finset.union_eq_empty.mp hu).2
    intro PQ hPQ
    simp only [qfDNFAux] at hPQ
    split_ifs at hPQ
    · -- b = true: flatMap
      rw [List.mem_flatMap] at hPQ
      obtain ⟨PQ₁, hPQ₁, hPQ₂⟩ := hPQ
      rw [List.mem_map] at hPQ₂
      obtain ⟨PQ₂, hPQ₂, rfl⟩ := hPQ₂
      have ⟨h₁P, h₁Q⟩ := ih₁ true hQF₁ hSent₁ PQ₁ hPQ₁
      have ⟨h₂P, h₂Q⟩ := ih₂ true hQF₂ hSent₂ PQ₂ hPQ₂
      refine ⟨?_, ?_⟩ <;>
        intro p hp <;>
        rw [List.mem_append] at hp <;>
        rcases hp with hp | hp
      · exact h₁P p hp
      · exact h₂P p hp
      · exact h₁Q p hp
      · exact h₂Q p hp
    · -- b = false: append
      rw [List.mem_append] at hPQ
      rcases hPQ with hPQ | hPQ
      · exact ih₁ false hQF₁ hSent₁ PQ hPQ
      · exact ih₂ false hQF₂ hSent₂ PQ hPQ
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have hu : Φ₁.freeVars ∪ Φ₂.freeVars = ∅ := hSent
    have hSent₁ : Φ₁.freeVars = ∅ := (Finset.union_eq_empty.mp hu).1
    have hSent₂ : Φ₂.freeVars = ∅ := (Finset.union_eq_empty.mp hu).2
    intro PQ hPQ
    simp only [qfDNFAux] at hPQ
    split_ifs at hPQ
    · rw [List.mem_append] at hPQ
      rcases hPQ with hPQ | hPQ
      · exact ih₁ true hQF₁ hSent₁ PQ hPQ
      · exact ih₂ true hQF₂ hSent₂ PQ hPQ
    · rw [List.mem_flatMap] at hPQ
      obtain ⟨PQ₁, hPQ₁, hPQ₂⟩ := hPQ
      rw [List.mem_map] at hPQ₂
      obtain ⟨PQ₂, hPQ₂, rfl⟩ := hPQ₂
      have ⟨h₁P, h₁Q⟩ := ih₁ false hQF₁ hSent₁ PQ₁ hPQ₁
      have ⟨h₂P, h₂Q⟩ := ih₂ false hQF₂ hSent₂ PQ₂ hPQ₂
      refine ⟨?_, ?_⟩ <;>
        intro p hp <;>
        rw [List.mem_append] at hp <;>
        rcases hp with hp | hp
      · exact h₁P p hp
      · exact h₂P p hp
      · exact h₁Q p hp
      · exact h₂Q p hp
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨hQF₁, hQF₂⟩ := hQF
    have hu : Φ₁.freeVars ∪ Φ₂.freeVars = ∅ := hSent
    have hSent₁ : Φ₁.freeVars = ∅ := (Finset.union_eq_empty.mp hu).1
    have hSent₂ : Φ₂.freeVars = ∅ := (Finset.union_eq_empty.mp hu).2
    intro PQ hPQ
    simp only [qfDNFAux] at hPQ
    split_ifs at hPQ
    · -- b = true: append (qfDNFAux false Φ₁) (qfDNFAux true Φ₂)
      rw [List.mem_append] at hPQ
      rcases hPQ with hPQ | hPQ
      · exact ih₁ false hQF₁ hSent₁ PQ hPQ
      · exact ih₂ true hQF₂ hSent₂ PQ hPQ
    · rw [List.mem_flatMap] at hPQ
      obtain ⟨PQ₁, hPQ₁, hPQ₂⟩ := hPQ
      rw [List.mem_map] at hPQ₂
      obtain ⟨PQ₂, hPQ₂, rfl⟩ := hPQ₂
      have ⟨h₁P, h₁Q⟩ := ih₁ true hQF₁ hSent₁ PQ₁ hPQ₁
      have ⟨h₂P, h₂Q⟩ := ih₂ false hQF₂ hSent₂ PQ₂ hPQ₂
      refine ⟨?_, ?_⟩ <;>
        intro p hp <;>
        rw [List.mem_append] at hp <;>
        rcases hp with hp | hp
      · exact h₁P p hp
      · exact h₂P p hp
      · exact h₁Q p hp
      · exact h₂Q p hp
  | exists_ _ _ _ => exact absurd hQF id
  | forall_ _ _ _ => exact absurd hQF id

end QfDNFTracking

/-! ### Rename preserves `freeVars = ∅` -/

section RenameTracking

variable {D : Type*} [CommRing D]

theorem Formula.rename_freeVars_subset {σ τ : Type*}
    [DecidableEq σ] [DecidableEq τ]
    (f : σ → τ) (Φ : Formula σ (FieldAtom σ D)) :
    (Φ.rename f (FieldAtom.renameVars f)).freeVars ⊆
      Φ.freeVars.image f := by
  classical
  induction Φ with
  | atom a =>
    show ((Formula.atom (FieldAtom.renameVars f a)).freeVars) ⊆ _
    show (FieldAtom.renameVars f a).vars ⊆ _
    show (a.poly.rename f).vars ⊆ a.poly.vars.image f
    exact MvPolynomial.vars_rename f a.poly
  | not _ ih =>
    show (Formula.rename f (FieldAtom.renameVars f) _).freeVars ⊆ _
    show Formula.freeVars _ ⊆ _
    exact ih
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ Finset.image f (Φ₁.freeVars ∪ Φ₂.freeVars)
    rw [Finset.image_union]
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (ih₁ h)
    · exact Finset.mem_union_right _ (ih₂ h)
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ Finset.image f (Φ₁.freeVars ∪ Φ₂.freeVars)
    rw [Finset.image_union]
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (ih₁ h)
    · exact Finset.mem_union_right _ (ih₂ h)
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ Finset.image f (Φ₁.freeVars ∪ Φ₂.freeVars)
    rw [Finset.image_union]
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (ih₁ h)
    · exact Finset.mem_union_right _ (ih₂ h)
  | exists_ x Φ ih =>
    show Formula.freeVars _ \ {f x} ⊆ Finset.image f (Φ.freeVars \ {x})
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hy
    obtain ⟨hy_in, hy_ne⟩ := hy
    have := ih hy_in
    rw [Finset.mem_image] at this
    obtain ⟨z, hz_in, hz_eq⟩ := this
    rw [Finset.mem_image]
    refine ⟨z, ?_, hz_eq⟩
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨hz_in, ?_⟩
    intro h
    apply hy_ne
    rw [← hz_eq, h]
  | forall_ x Φ ih =>
    show Formula.freeVars _ \ {f x} ⊆ Finset.image f (Φ.freeVars \ {x})
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hy
    obtain ⟨hy_in, hy_ne⟩ := hy
    have := ih hy_in
    rw [Finset.mem_image] at this
    obtain ⟨z, hz_in, hz_eq⟩ := this
    rw [Finset.mem_image]
    refine ⟨z, ?_, hz_eq⟩
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨hz_in, ?_⟩
    intro h
    apply hy_ne
    rw [← hz_eq, h]

theorem Formula.rename_freeVars_empty {σ τ : Type*}
    [DecidableEq σ] [DecidableEq τ]
    (f : σ → τ) {Φ : Formula σ (FieldAtom σ D)}
    (hΦ : Φ.freeVars = ∅) :
    (Φ.rename f (FieldAtom.renameVars f)).freeVars = ∅ := by
  classical
  have hsub := Formula.rename_freeVars_subset f Φ
  rw [hΦ, Finset.image_empty] at hsub
  exact Finset.subset_empty.mp hsub

end RenameTracking

/-! ### Generalization: `vars ⊆ T` tracking

The goal of this section is to generalize the entire `PolyConst`-chain
to "coefficient vars ⊆ T" for an arbitrary `T : Finset (Fin k)`. The
key technical lemma is `splitLast_polyVarsSubset_of_vars_subset`:

> If `P.vars ⊆ insert (Fin.last k) (T.image Fin.castSucc)`, then every
> coefficient of `splitLast P` has `vars ⊆ T`.

We then show this property is preserved by the rest of the QE pipeline:
`pRemMv`, `Tru`, `TRems`, `pathLeafParent`, `posgcd`, `leafFormula`,
`degFormula`, `projBasic`. -/

section VarsSubsetTracking

variable {D : Type*} [CommRing D]

/-- `Q : Polynomial (MvPolynomial (Fin k) D)` has all coefficient
`vars ⊆ T`. -/
def PolyVarsSubset (T : Finset (Fin k))
    (Q : Polynomial (MvPolynomial (Fin k) D)) : Prop :=
  ∀ i, (Q.coeff i).vars ⊆ T

namespace PolyVarsSubset

variable {T : Finset (Fin k)}

theorem zero : PolyVarsSubset T (0 : Polynomial (MvPolynomial (Fin k) D)) := by
  intro i; simp

theorem one : PolyVarsSubset T (1 : Polynomial (MvPolynomial (Fin k) D)) := by
  classical
  intro i
  rw [Polynomial.coeff_one]
  split_ifs
  · rw [MvPolynomial.vars_one_empty]; exact Finset.empty_subset _
  · rw [MvPolynomial.vars_zero_empty]; exact Finset.empty_subset _

theorem C_const {c : MvPolynomial (Fin k) D} (hc : c.vars ⊆ T) :
    PolyVarsSubset T (Polynomial.C c) := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hc
  · rw [MvPolynomial.vars_zero_empty]; exact Finset.empty_subset _

theorem CC_of_D (d : D) :
    PolyVarsSubset T
      (Polynomial.C (MvPolynomial.C d : MvPolynomial (Fin k) D)) := by
  apply C_const
  rw [MvPolynomial.vars_C]
  exact Finset.empty_subset _

theorem C_X_castSucc {k : ℕ} {T : Finset (Fin k)} {j : Fin k} (hj : j ∈ T) :
    PolyVarsSubset T
      (Polynomial.C (MvPolynomial.X j : MvPolynomial (Fin k) D)) := by
  classical
  apply C_const
  by_cases hN : Nontrivial D
  · let := hN
    rw [MvPolynomial.vars_X]
    exact Finset.singleton_subset_iff.mpr hj
  · -- D is subsingleton, so MvPolynomial.X j = 0.
    have : ¬ Nontrivial D := hN
    rw [not_nontrivial_iff_subsingleton] at this
    have : Subsingleton (MvPolynomial (Fin k) D) := inferInstance
    have hzero : (MvPolynomial.X j : MvPolynomial (Fin k) D) = 0 :=
      Subsingleton.elim _ _
    rw [hzero, MvPolynomial.vars_zero_empty]
    exact Finset.empty_subset _

theorem X : PolyVarsSubset T (Polynomial.X : Polynomial (MvPolynomial (Fin k) D)) := by
  classical
  intro i
  rw [Polynomial.coeff_X]
  split_ifs
  · rw [MvPolynomial.vars_one_empty]; exact Finset.empty_subset _
  · rw [MvPolynomial.vars_zero_empty]; exact Finset.empty_subset _

private theorem vars_add_subset {p q : MvPolynomial (Fin k) D}
    (hp : p.vars ⊆ T) (hq : q.vars ⊆ T) : (p + q).vars ⊆ T := by
  classical
  intro x hx
  have hsub := MvPolynomial.vars_add_subset p q
  rcases Finset.mem_union.mp (hsub hx) with h | h
  · exact hp h
  · exact hq h

private theorem vars_neg_subset {p : MvPolynomial (Fin k) D}
    (hp : p.vars ⊆ T) : (-p).vars ⊆ T := by
  rwa [MvPolynomial.vars_neg]

private theorem vars_sub_subset {p q : MvPolynomial (Fin k) D}
    (hp : p.vars ⊆ T) (hq : q.vars ⊆ T) : (p - q).vars ⊆ T := by
  rw [sub_eq_add_neg]
  exact vars_add_subset hp (vars_neg_subset hq)

private theorem vars_mul_subset {p q : MvPolynomial (Fin k) D}
    (hp : p.vars ⊆ T) (hq : q.vars ⊆ T) : (p * q).vars ⊆ T := by
  classical
  intro x hx
  have hsub := MvPolynomial.vars_mul p q
  rcases Finset.mem_union.mp (hsub hx) with h | h
  · exact hp h
  · exact hq h

private theorem vars_pow_subset {p : MvPolynomial (Fin k) D}
    (hp : p.vars ⊆ T) (n : ℕ) : (p ^ n).vars ⊆ T := by
  induction n with
  | zero =>
    rw [pow_zero, MvPolynomial.vars_one_empty]; exact Finset.empty_subset _
  | succ n ih =>
    rw [pow_succ]
    exact vars_mul_subset ih hp

theorem add {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) (hQ : PolyVarsSubset T Q) :
    PolyVarsSubset T (P + Q) := by
  intro i
  rw [Polynomial.coeff_add]
  exact vars_add_subset (hP i) (hQ i)

theorem neg {P : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) : PolyVarsSubset T (-P) := by
  intro i
  rw [Polynomial.coeff_neg]
  exact vars_neg_subset (hP i)

theorem sub {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) (hQ : PolyVarsSubset T Q) :
    PolyVarsSubset T (P - Q) := by
  rw [sub_eq_add_neg]; exact add hP (neg hQ)

theorem mul {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) (hQ : PolyVarsSubset T Q) :
    PolyVarsSubset T (P * Q) := by
  classical
  intro i
  rw [Polynomial.coeff_mul]
  intro x hx
  have hsub :
      (∑ j ∈ Finset.antidiagonal i, P.coeff j.1 * Q.coeff j.2).vars ⊆
        (Finset.antidiagonal i).biUnion fun j =>
          (P.coeff j.1 * Q.coeff j.2).vars :=
    MvPolynomial.vars_sum_subset _ _
  have hxs := hsub hx
  rw [Finset.mem_biUnion] at hxs
  obtain ⟨j, _, hxj⟩ := hxs
  exact vars_mul_subset (hP _) (hQ _) hxj

theorem pow {P : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) (n : ℕ) : PolyVarsSubset T (P ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact one
  | succ n ih => rw [pow_succ]; exact mul ih hP

theorem prod {L : List (Polynomial (MvPolynomial (Fin k) D))}
    (hL : ∀ P ∈ L, PolyVarsSubset T P) : PolyVarsSubset T L.prod := by
  induction L with
  | nil => rw [List.prod_nil]; exact one
  | cons P rest ih =>
    rw [List.prod_cons]
    exact mul (hL P (by simp))
      (ih (fun Q hQ => hL Q (List.mem_cons_of_mem _ hQ)))

theorem leadingCoeff_vars_subset {P : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) : P.leadingCoeff.vars ⊆ T := by
  unfold Polynomial.leadingCoeff
  exact hP _

theorem of_polyConst {Q : Polynomial (MvPolynomial (Fin k) D)}
    (hQ : PolyConst Q) : PolyVarsSubset T Q := by
  intro i; rw [hQ i]; exact Finset.empty_subset _

end PolyVarsSubset

/-! ### `splitLast` preserves `vars ⊆ T` -/

section SplitLastVars

variable {D : Type*} [CommRing D]

/-- Helper: a monomial with support ⊆ insert (last k) (T.image castSucc)
maps via `splitLast` to a polynomial whose coefficients have `vars ⊆ T`. -/
private theorem splitLast_monomial_polyVarsSubset
    {T : Finset (Fin k)} {u : Fin (k+1) →₀ ℕ}
    (hu : u.support ⊆ insert (Fin.last k) (T.image Fin.castSucc)) (d : D) :
    PolyVarsSubset T (splitLast (MvPolynomial.monomial u d :
      MvPolynomial (Fin (k+1)) D)) := by
  classical
  -- Decompose u as (u (last k)) at last + finsum at castSucc indices.
  -- We'll express monomial u d as
  --   C d * X (last k) ^ (u (last k)) * ∏ j ∈ u.support \ {last k}, X j ^ (u j).
  -- For j ∈ u.support \ {last k}, we have j ∈ T.image castSucc (so j = castSucc j' for some j' ∈ T).
  -- splitLast turns each such X j into Polynomial.C (X j'), preserving the property.
  have hmono :
      (MvPolynomial.monomial u d : MvPolynomial (Fin (k+1)) D) =
        MvPolynomial.C d * u.prod (fun i n => MvPolynomial.X i ^ n) := by
    rw [MvPolynomial.monomial_eq]
  rw [hmono, map_mul, splitLast_C]
  -- Decompose u.prod over (last k) vs castSucc indices.
  -- Use that u.prod over a Finsupp is over its support.
  rw [Finsupp.prod]
  rw [map_prod]
  apply PolyVarsSubset.mul (PolyVarsSubset.CC_of_D d)
  -- Induct on the finset product.
  refine Finset.prod_induction _ _
    (fun A B hA hB => PolyVarsSubset.mul hA hB) PolyVarsSubset.one
    (fun i hi => ?_)
  rw [map_pow]
  apply PolyVarsSubset.pow
  -- splitLast (X i): either (last k) → X, or castSucc j → C (X j).
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | hlast
  · -- i = castSucc j; need j ∈ T.
    have hcs_mem : Fin.castSucc j ∈ insert (Fin.last k) (T.image Fin.castSucc) :=
      hu hi
    rw [Finset.mem_insert] at hcs_mem
    rcases hcs_mem with hl | himg
    · exfalso
      have hne : Fin.castSucc j ≠ Fin.last k :=
        Fin.castSucc_lt_last j |>.ne
      exact hne hl
    · rw [Finset.mem_image] at himg
      obtain ⟨j', hj'_mem, hj'_eq⟩ := himg
      have hjj' : j' = j := Fin.castSucc_injective _ hj'_eq
      subst hjj'
      rw [splitLast_X_castSucc]
      exact PolyVarsSubset.C_X_castSucc hj'_mem
  · subst hlast
    rw [splitLast_X_last]
    exact PolyVarsSubset.X

/-- **Key**: if `P.vars ⊆ insert (last k) (T.image castSucc)`, then every
coefficient of `splitLast P` has `vars ⊆ T`. -/
theorem splitLast_polyVarsSubset
    {T : Finset (Fin k)} {P : MvPolynomial (Fin (k+1)) D}
    (hP : P.vars ⊆ insert (Fin.last k) (T.image Fin.castSucc)) :
    PolyVarsSubset T (splitLast P) := by
  classical
  rw [MvPolynomial.as_sum P]
  rw [map_sum]
  refine Finset.sum_induction _ _ (fun A B hA hB => PolyVarsSubset.add hA hB)
    PolyVarsSubset.zero (fun v hv => ?_)
  apply splitLast_monomial_polyVarsSubset
  intro j hj
  apply hP
  rw [MvPolynomial.mem_vars_iff_mem_support]
  exact ⟨v, hv, hj⟩

end SplitLastVars

/-! ### `Tru` preserves `PolyVarsSubset` -/

section TruncateVars

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsDomain D] in
theorem PolyVarsSubset.truncate {T : Finset (Fin k)}
    {Q : Polynomial (MvPolynomial (Fin k) D)}
    (hQ : PolyVarsSubset T Q) (i : ℕ) :
    PolyVarsSubset T (truncate i Q) := by
  intro j
  rw [coeff_truncate]
  split_ifs
  · exact hQ j
  · rw [MvPolynomial.vars_zero_empty]; exact Finset.empty_subset _

omit [IsDomain D] in
theorem PolyVarsSubset.of_mem_Tru {T : Finset (Fin k)}
    {Q R : Polynomial (MvPolynomial (Fin k) D)}
    (hQ : PolyVarsSubset T Q) (hR : R ∈ Tru Q) : PolyVarsSubset T R := by
  by_cases hQ0 : Q = 0
  · subst hQ0; rw [Tru, ite_eq_left rfl] at hR; exact hR.elim
  rw [Tru, ite_eq_right hQ0] at hR
  split_ifs at hR with hbase
  · rw [Set.mem_singleton_iff] at hR; subst hR; exact hQ
  · rw [Set.mem_union, Set.mem_singleton_iff] at hR
    rcases hR with rfl | hR
    · exact hQ
    · exact PolyVarsSubset.of_mem_Tru (hQ.truncate _) hR
termination_by Q.natDegree
decreasing_by
  have hQpos : 0 < Q.natDegree := by
    push Not at hbase
    exact Nat.pos_of_ne_zero hbase.2
  have := natDegree_truncate_le (Q.natDegree - 1) Q
  omega

end TruncateVars

/-! ### `pRemMv` preserves `PolyVarsSubset` -/

section PRemVars

variable {D : Type*} [CommRing D] [IsDomain D]

/-- Strong-induction version of `PolyVarsSubset` preservation for the
`pRem_exists_aux` construction. -/
theorem pRem_exists_polyVarsSubset_aux {T : Finset (Fin k)}
    (Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0)
    (hQc : PolyVarsSubset T Q) :
    ∀ (p : ℕ) (P : Polynomial (MvPolynomial (Fin k) D)),
      P.natDegree < p → PolyVarsSubset T P →
    ∀ (n : ℕ),
      (if P.natDegree < Q.natDegree then 0
       else P.natDegree - Q.natDegree + 1) ≤ n →
    ∃ A R : Polynomial (MvPolynomial (Fin k) D),
      Polynomial.C (Q.leadingCoeff ^ n) * P = A * Q + R ∧
      R.degree < Q.degree ∧
      PolyVarsSubset T A ∧ PolyVarsSubset T R := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro P hPdeg hPc n hn
    by_cases hP : P = 0
    · refine ⟨0, 0, by simp [hP], ?_, .zero, .zero⟩
      rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
    by_cases hdeg : P.natDegree < Q.natDegree
    · refine ⟨0, Polynomial.C (Q.leadingCoeff ^ n) * P, by ring, ?_, .zero, ?_⟩
      · have hbn : (Q.leadingCoeff ^ n) ≠ 0 :=
          pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hQ)
        have hnat : (Polynomial.C (Q.leadingCoeff ^ n) * P).natDegree = P.natDegree :=
          Polynomial.natDegree_C_mul hbn
        exact Polynomial.degree_lt_degree (hnat ▸ hdeg)
      · exact PolyVarsSubset.mul
          (PolyVarsSubset.C_const
            (PolyVarsSubset.vars_pow_subset
              (PolyVarsSubset.leadingCoeff_vars_subset hQc) n)) hPc
    have hdeg' : Q.natDegree ≤ P.natDegree := Nat.not_lt.mp hdeg
    have ha_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hb_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    rw [ite_eq_right hdeg] at hn
    have hn1 : 1 ≤ n := by omega
    set P' : Polynomial (MvPolynomial (Fin k) D) :=
      Polynomial.C Q.leadingCoeff * P -
        Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree) * Q
      with hP'def
    have hP'c : PolyVarsSubset T P' := by
      apply PolyVarsSubset.sub
      · exact PolyVarsSubset.mul
          (PolyVarsSubset.C_const
            (PolyVarsSubset.leadingCoeff_vars_subset hQc)) hPc
      · exact PolyVarsSubset.mul
          (PolyVarsSubset.mul
            (PolyVarsSubset.C_const
              (PolyVarsSubset.leadingCoeff_vars_subset hPc))
            (PolyVarsSubset.pow PolyVarsSubset.X _)) hQc
    have hfund : Polynomial.C Q.leadingCoeff * P =
        Polynomial.C P.leadingCoeff *
          Polynomial.X ^ (P.natDegree - Q.natDegree) * Q + P' := by
      rw [hP'def]; ring
    obtain ⟨A', R', hAR', hdR', hA'c, hR'c⟩ :
        ∃ A' R' : Polynomial (MvPolynomial (Fin k) D),
          Polynomial.C (Q.leadingCoeff ^ (n - 1)) * P' = A' * Q + R' ∧
            R'.degree < Q.degree ∧ PolyVarsSubset T A' ∧ PolyVarsSubset T R' := by
      by_cases hP' : P' = 0
      · refine ⟨0, 0, by simp [hP'], ?_, .zero, .zero⟩
        rw [Polynomial.degree_zero]
        exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
      · have hsub : P.natDegree - Q.natDegree + Q.natDegree = P.natDegree :=
          Nat.sub_add_cancel hdeg'
        have hP'_natDeg : P'.natDegree < P.natDegree := by
          have hLdeg : (Polynomial.C Q.leadingCoeff * P).degree =
              (Polynomial.C P.leadingCoeff *
                Polynomial.X ^ (P.natDegree - Q.natDegree) * Q).degree := by
            rw [Polynomial.degree_C_mul hb_ne,
                mul_assoc,
                Polynomial.degree_C_mul ha_ne,
                Polynomial.degree_mul, Polynomial.degree_X_pow,
                Polynomial.degree_eq_natDegree hQ,
                Polynomial.degree_eq_natDegree hP]
            norm_cast
            omega
          have hLne : Polynomial.C Q.leadingCoeff * P ≠ 0 :=
            mul_ne_zero (fun h => hb_ne (Polynomial.C_eq_zero.mp h)) hP
          have hLeadEq : (Polynomial.C Q.leadingCoeff * P).leadingCoeff =
              (Polynomial.C P.leadingCoeff *
                Polynomial.X ^ (P.natDegree - Q.natDegree) * Q).leadingCoeff := by
            rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
                Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
                Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X_pow]
            ring
          have hP'_deg_lt : P'.degree < (Polynomial.C Q.leadingCoeff * P).degree :=
            Polynomial.degree_sub_lt_left hLdeg hLne hLeadEq
          rw [Polynomial.degree_C_mul hb_ne,
              Polynomial.degree_eq_natDegree hP',
              Polynomial.degree_eq_natDegree hP] at hP'_deg_lt
          exact_mod_cast hP'_deg_lt
        have hbound : (if P'.natDegree < Q.natDegree then 0
                       else P'.natDegree - Q.natDegree + 1) ≤ n - 1 := by
          split_ifs with h
          · omega
          · simp only [not_lt] at h
            omega
        exact ih P.natDegree hPdeg P' hP'_natDeg hP'c (n - 1) hbound
    refine ⟨A' + Polynomial.C (Q.leadingCoeff ^ (n - 1) * P.leadingCoeff) *
            Polynomial.X ^ (P.natDegree - Q.natDegree), R', ?_, hdR',
            ?_, hR'c⟩
    · have hbn : Q.leadingCoeff ^ n =
          Q.leadingCoeff ^ (n - 1) * Q.leadingCoeff := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]
      calc Polynomial.C (Q.leadingCoeff ^ n) * P
          = Polynomial.C (Q.leadingCoeff ^ (n - 1)) *
            (Polynomial.C Q.leadingCoeff * P) := by
            rw [hbn, Polynomial.C_mul]; ring
        _ = Polynomial.C (Q.leadingCoeff ^ (n - 1)) *
            (Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - Q.natDegree)
              * Q + P') := by rw [hfund]
        _ = (A' + Polynomial.C (Q.leadingCoeff ^ (n - 1) * P.leadingCoeff) *
              Polynomial.X ^ (P.natDegree - Q.natDegree)) * Q + R' := by
            rw [Polynomial.C_mul]
            linear_combination hAR'
    · apply PolyVarsSubset.add hA'c
      apply PolyVarsSubset.mul
      · apply PolyVarsSubset.C_const
        apply PolyVarsSubset.vars_mul_subset
        · exact PolyVarsSubset.vars_pow_subset
            (PolyVarsSubset.leadingCoeff_vars_subset hQc) _
        · exact PolyVarsSubset.leadingCoeff_vars_subset hPc
      · exact PolyVarsSubset.pow PolyVarsSubset.X _

theorem pRemMv_polyVarsSubset {T : Finset (Fin k)}
    {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) (hQ : PolyVarsSubset T Q) :
    PolyVarsSubset T (pRemMv P Q) := by
  unfold pRemMv
  split_ifs with hQ0
  · exact PolyVarsSubset.zero
  · set K := FractionRing (MvPolynomial (Fin k) D)
    have hbound : (if P.natDegree < Q.natDegree then 0
                   else P.natDegree - Q.natDegree + 1) ≤ pRemExp P Q := by
      split_ifs with h
      · exact Nat.zero_le _
      · exact pRemExp_ge P Q (Nat.not_lt.mp h)
    obtain ⟨A, R, hAR, hdR, hAc, hRc⟩ :=
      pRem_exists_polyVarsSubset_aux Q hQ0 hQ (P.natDegree + 1) P
        (Nat.lt_succ_self _) hP (pRemExp P Q) hbound
    set choosePRem :=
      (@PRem_descends (MvPolynomial (Fin k) D) _ _ K _ _ _ P Q hQ0).choose
    have hchoosePRem_eq :
        choosePRem.map (algebraMap (MvPolynomial (Fin k) D) K) = PRem K P Q :=
      (@PRem_descends (MvPolynomial (Fin k) D) _ _ K _ _ _ P Q hQ0).choose_spec
    suffices hch : choosePRem = R from by rw [hch]; exact hRc
    have hinj := IsFractionRing.injective (MvPolynomial (Fin k) D) K
    apply Polynomial.map_injective (algebraMap (MvPolynomial (Fin k) D) K) hinj
    rw [hchoosePRem_eq]
    have hmap := congrArg (Polynomial.map (algebraMap (MvPolynomial (Fin k) D) K)) hAR
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at hmap
    unfold PRem Rem
    simp only [Polynomial.map_mul, Polynomial.map_C]
    have hQmap_ne : Q.map (algebraMap (MvPolynomial (Fin k) D) K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinj).mpr hQ0
    have hdR_map : (R.map (algebraMap (MvPolynomial (Fin k) D) K)).degree <
        (Q.map (algebraMap (MvPolynomial (Fin k) D) K)).degree := by
      rwa [Polynomial.degree_map_eq_of_injective hinj,
           Polynomial.degree_map_eq_of_injective hinj Q]
    have hdvd : Q.map (algebraMap (MvPolynomial (Fin k) D) K) ∣
        (Polynomial.C ((algebraMap (MvPolynomial (Fin k) D) K)
          (Q.leadingCoeff ^ pRemExp P Q)) *
          P.map (algebraMap (MvPolynomial (Fin k) D) K)) -
          R.map (algebraMap (MvPolynomial (Fin k) D) K) :=
      ⟨A.map (algebraMap (MvPolynomial (Fin k) D) K), by linear_combination hmap⟩
    have hmod_sub :
        ((Polynomial.C ((algebraMap (MvPolynomial (Fin k) D) K)
          (Q.leadingCoeff ^ pRemExp P Q)) *
          P.map (algebraMap (MvPolynomial (Fin k) D) K)) -
          R.map (algebraMap (MvPolynomial (Fin k) D) K)) %
          Q.map (algebraMap (MvPolynomial (Fin k) D) K) = 0 :=
      EuclideanDomain.mod_eq_zero.mpr hdvd
    rw [Polynomial.sub_mod, sub_eq_zero] at hmod_sub
    rw [hmod_sub, (Polynomial.mod_eq_self_iff hQmap_ne).mpr hdR_map]

end PRemVars

/-! ### Path tracking through `TRems`, `pathLeafParent` (generalized) -/

section PathTrackingVars

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

theorem PolyVarsSubset.mkTRemsNode_subtree_root {T : Finset (Fin k)}
    {parentPol curPol : Polynomial (MvPolynomial (Fin k) D)}
    (_hp : PolyVarsSubset T parentPol) (hc : PolyVarsSubset T curPol) :
    PolyVarsSubset T (mkTRemsNode parentPol curPol).root := by
  unfold mkTRemsNode
  split_ifs
  · simpa [RoseTree.root] using hc
  · simpa [RoseTree.root] using hc

omit [IsDomain D] in
theorem polyVarsSubset_pathLeafParentAux {T : Finset (Fin k)}
    {cur : Polynomial (MvPolynomial (Fin k) D)} (hc : PolyVarsSubset T cur)
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : ∀ P ∈ path, PolyVarsSubset T P) :
    PolyVarsSubset T (pathLeafParentAux cur path) := by
  induction path generalizing cur with
  | nil => exact hc
  | cons q rest ih =>
    by_cases hq : q = 0
    · have heq : pathLeafParentAux cur (q :: rest) = cur := by
        simp [pathLeafParentAux, hq]
      rw [heq]; exact hc
    · have heq : pathLeafParentAux cur (q :: rest) = pathLeafParentAux q rest := by
        simp [pathLeafParentAux, hq]
      rw [heq]
      exact ih (hpath q (by simp)) (fun P hP => hpath P (by simp [hP]))

omit [IsDomain D] in
theorem polyVarsSubset_pathLeafParent {T : Finset (Fin k)}
    {P : Polynomial (MvPolynomial (Fin k) D)} (hP : PolyVarsSubset T P)
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : ∀ Q ∈ path, PolyVarsSubset T Q) :
    PolyVarsSubset T (pathLeafParent P path) := by
  induction path with
  | nil => exact hP
  | cons q rest _ =>
    by_cases hq : q = 0
    · have heq : pathLeafParent P (q :: rest) = P := by
        simp [pathLeafParent, hq]
      rw [heq]; exact hP
    · have heq : pathLeafParent P (q :: rest) = pathLeafParentAux q rest := by
        simp [pathLeafParent, hq]
      rw [heq]
      exact polyVarsSubset_pathLeafParentAux (hpath q (by simp))
        (fun Q hQ => hpath Q (List.mem_cons_of_mem _ hQ))

end PathTrackingVars

/-! ### TRems leafPaths are `PolyVarsSubset` -/

section TRemsTrackingVars

variable {D : Type*} [CommRing D] [IsDomain D]

theorem PolyVarsSubset.mkTRemsNode_all {T : Finset (Fin k)}
    {parentPol curPol : Polynomial (MvPolynomial (Fin k) D)}
    (hp : PolyVarsSubset T parentPol) (hc : PolyVarsSubset T curPol) :
    ∀ path ∈ (mkTRemsNode parentPol curPol).leafPaths,
      ∀ Q ∈ path, PolyVarsSubset T Q := by
  intro path hpath Q hQ
  by_cases hcur0 : curPol = 0
  · rw [mkTRemsNode, ite_eq_left hcur0] at hpath
    simp only [RoseTree.leafPaths, List.mem_singleton] at hpath
    subst hpath
    exact absurd hQ (List.not_mem_nil)
  · rw [mkTRemsNode, ite_eq_right hcur0] at hpath
    dsimp only at hpath
    set R := -(pRemMv parentPol curPol) with R_def
    have hRc : PolyVarsSubset T R := PolyVarsSubset.neg (pRemMv_polyVarsSubset hp hc)
    set cs := (Tru_finite R).toFinset.toList with cs_def
    set tru_trees := cs.attach.map (fun ⟨c, _⟩ => mkTRemsNode curPol c)
      with tt_def
    set ac := tru_trees ++ [RoseTree.node (0 : Polynomial (MvPolynomial (Fin k) D)) []]
      with ac_def
    have hac_ne : ac ≠ [] := by simp [ac_def]
    rw [leafPaths_node_ne_nil curPol ac hac_ne] at hpath
    simp only [List.mem_flatMap, List.mem_map] at hpath
    obtain ⟨child, hchild_mem, sp, hsp_mem, rfl⟩ := hpath
    rw [List.mem_cons] at hQ
    rw [ac_def, List.mem_append, List.mem_singleton] at hchild_mem
    rcases hQ with rfl | hQ
    · rcases hchild_mem with hchild_mem | rfl
      · rw [tt_def, List.mem_map] at hchild_mem
        obtain ⟨⟨c, hc_mem⟩, _, rfl⟩ := hchild_mem
        have hcc : PolyVarsSubset T c := by
          have hc_tru : c ∈ Tru R :=
            (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_mem)
          exact PolyVarsSubset.of_mem_Tru hRc hc_tru
        rw [mkTRemsNode_root]
        exact hcc
      · simp only [RoseTree.root]; exact PolyVarsSubset.zero
    · rcases hchild_mem with hchild_mem | rfl
      · rw [tt_def, List.mem_map] at hchild_mem
        obtain ⟨⟨c, hc_mem⟩, _, rfl⟩ := hchild_mem
        have hcc : PolyVarsSubset T c := by
          have hc_tru : c ∈ Tru R :=
            (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_mem)
          exact PolyVarsSubset.of_mem_Tru hRc hc_tru
        exact PolyVarsSubset.mkTRemsNode_all hc hcc sp hsp_mem Q hQ
      · simp only [RoseTree.leafPaths, List.mem_singleton] at hsp_mem
        subst hsp_mem; exact absurd hQ (List.not_mem_nil)
termination_by curPol.natDegree
decreasing_by
  have hmem_tru : c ∈ Tru R :=
    (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_mem)
  by_cases h4 : pRemMv parentPol curPol = 0
  · have hn0 : R = 0 :=
      show -(pRemMv parentPol curPol) = 0 by rw [h4, neg_zero]
    rw [hn0, Tru, ite_eq_left rfl] at hmem_tru; exact hmem_tru.elim
  · have h1 := natDegree_mem_Tru_le hmem_tru
    have h5 := Polynomial.natDegree_lt_natDegree h4
      (degree_pRemMv_lt parentPol curPol hcur0)
    have h6 : R.natDegree = (pRemMv parentPol curPol).natDegree :=
      Polynomial.natDegree_neg _
    omega

theorem PolyVarsSubset.TRems_leafPaths {T : Finset (Fin k)}
    {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) (hQ : PolyVarsSubset T Q) :
    ∀ path ∈ (TRems P Q).leafPaths, ∀ R ∈ path, PolyVarsSubset T R := by
  intro path hpath R hR
  rw [TRems] at hpath
  set cs := (Tru_finite Q).toFinset.toList with cs_def
  set tru_trees := cs.map (mkTRemsNode P) with tt_def
  set ac := tru_trees ++ [RoseTree.node (0 : Polynomial (MvPolynomial (Fin k) D)) []]
    with ac_def
  have hac_ne : ac ≠ [] := by simp [ac_def]
  rw [leafPaths_node_ne_nil P ac hac_ne] at hpath
  simp only [List.mem_flatMap, List.mem_map] at hpath
  obtain ⟨child, hchild_mem, sp, hsp_mem, rfl⟩ := hpath
  rw [List.mem_cons] at hR
  rw [ac_def, List.mem_append, List.mem_singleton] at hchild_mem
  rcases hR with rfl | hR
  · rcases hchild_mem with hchild_mem | rfl
    · rw [tt_def, List.mem_map] at hchild_mem
      obtain ⟨c, hc_mem, rfl⟩ := hchild_mem
      have hcc : PolyVarsSubset T c :=
        PolyVarsSubset.of_mem_Tru hQ
          ((Set.Finite.mem_toFinset _).mp ((Finset.mem_toList).mp hc_mem))
      rw [mkTRemsNode_root]
      exact hcc
    · simp only [RoseTree.root]; exact PolyVarsSubset.zero
  · rcases hchild_mem with hchild_mem | rfl
    · rw [tt_def, List.mem_map] at hchild_mem
      obtain ⟨c, hc_mem, rfl⟩ := hchild_mem
      have hcc : PolyVarsSubset T c :=
        PolyVarsSubset.of_mem_Tru hQ
          ((Set.Finite.mem_toFinset _).mp ((Finset.mem_toList).mp hc_mem))
      exact PolyVarsSubset.mkTRemsNode_all hP hcc sp hsp_mem R hR
    · simp only [RoseTree.leafPaths, List.mem_singleton] at hsp_mem
      subst hsp_mem; exact absurd hR (List.not_mem_nil)

end TRemsTrackingVars

/-! ### Formula-level: freeVars ⊆ T from PolyVarsSubset -/

section FormulaTrackingVars

open Classical

variable {D : Type*} [CommRing D]

theorem Formula.conjList_freeVars_subset
    {σ : Type*} [DecidableEq σ] {T : Finset σ}
    {Φs : List (Formula σ (FieldAtom σ D))}
    (h : ∀ Φ ∈ Φs, Φ.freeVars ⊆ T) :
    (Formula.conjList Φs).freeVars ⊆ T := by
  induction Φs with
  | nil =>
    show Formula.freeVars (Formula.trueFormula : Formula σ (FieldAtom σ D)) ⊆ T
    show (Formula.eq_zero (0 : MvPolynomial σ D)).freeVars ⊆ T
    show (Formula.atom (FieldAtom.eqZero 0)).freeVars ⊆ T
    intro x hx
    simp [Formula.freeVars, FieldAtom.vars, FieldAtom.eqZero] at hx
  | cons Φ rest ih =>
    show (Formula.and Φ (Formula.conjList rest)).freeVars ⊆ T
    show Φ.freeVars ∪ (Formula.conjList rest).freeVars ⊆ T
    apply Finset.union_subset (h Φ List.mem_cons_self)
    exact ih (fun Ψ hΨ => h Ψ (List.mem_cons_of_mem _ hΨ))

theorem Formula.disjList_freeVars_subset
    {σ : Type*} [DecidableEq σ] {T : Finset σ}
    {Φs : List (Formula σ (FieldAtom σ D))}
    (h : ∀ Φ ∈ Φs, Φ.freeVars ⊆ T) :
    (Formula.disjList Φs).freeVars ⊆ T := by
  induction Φs with
  | nil =>
    show Formula.freeVars (Formula.falseFormula : Formula σ (FieldAtom σ D)) ⊆ T
    show (Formula.ne_zero (0 : MvPolynomial σ D)).freeVars ⊆ T
    show (Formula.atom (FieldAtom.neZero 0)).freeVars ⊆ T
    intro x hx
    simp [Formula.freeVars, FieldAtom.vars, FieldAtom.neZero] at hx
  | cons Φ rest ih =>
    show (Formula.or Φ (Formula.disjList rest)).freeVars ⊆ T
    show Φ.freeVars ∪ (Formula.disjList rest).freeVars ⊆ T
    apply Finset.union_subset (h Φ List.mem_cons_self)
    exact ih (fun Ψ hΨ => h Ψ (List.mem_cons_of_mem _ hΨ))

theorem degFormula_freeVars_subset {T : Finset (Fin k)}
    {Q : Polynomial (MvPolynomial (Fin k) D)} (hQ : PolyVarsSubset T Q)
    (i : WithBot ℕ) :
    (degFormula Q i).freeVars ⊆ T := by
  cases i with
  | bot =>
    show (Formula.conjList ((List.range (Q.natDegree + 1)).map fun j =>
        Formula.eq_zero (Q.coeff j))).freeVars ⊆ T
    apply Formula.conjList_freeVars_subset
    intro Φ hΦ
    rw [List.mem_map] at hΦ
    obtain ⟨j, _, rfl⟩ := hΦ
    rw [Formula.eq_zero_freeVars]
    exact hQ j
  | coe n =>
    show (Formula.and (Formula.ne_zero (Q.coeff n))
      (Formula.conjList ((List.range (Q.natDegree - n)).map fun j =>
        Formula.eq_zero (Q.coeff (n + 1 + j))))).freeVars ⊆ T
    show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ T
    apply Finset.union_subset
    · rw [Formula.ne_zero_freeVars]; exact hQ n
    · apply Formula.conjList_freeVars_subset
      intro Φ hΦ
      rw [List.mem_map] at hΦ
      obtain ⟨j, _, rfl⟩ := hΦ
      rw [Formula.eq_zero_freeVars]
      exact hQ _

theorem degEqFormula_freeVars_subset {T : Finset (Fin k)}
    {Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)}
    (hQ₁ : PolyVarsSubset T Q₁) (hQ₂ : PolyVarsSubset T Q₂) :
    (degEqFormula Q₁ Q₂).freeVars ⊆ T := by
  unfold degEqFormula
  apply Formula.disjList_freeVars_subset
  intro Φ hΦ
  rw [List.mem_cons] at hΦ
  rcases hΦ with rfl | hΦ
  · show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ T
    apply Finset.union_subset
    · exact degFormula_freeVars_subset hQ₁ _
    · exact degFormula_freeVars_subset hQ₂ _
  · rw [List.mem_map] at hΦ
    obtain ⟨i, _, rfl⟩ := hΦ
    show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ T
    apply Finset.union_subset
    · exact degFormula_freeVars_subset hQ₁ _
    · exact degFormula_freeVars_subset hQ₂ _

theorem degNeqFormula_freeVars_subset {T : Finset (Fin k)}
    {Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)}
    (hQ₁ : PolyVarsSubset T Q₁) (hQ₂ : PolyVarsSubset T Q₂) :
    (degNeqFormula Q₁ Q₂).freeVars ⊆ T := by
  show (degEqFormula Q₁ Q₂).freeVars ⊆ T
  exact degEqFormula_freeVars_subset hQ₁ hQ₂

variable [IsDomain D]

theorem leafFormulaAux_freeVars_subset {T : Finset (Fin k)}
    {parent cur : Polynomial (MvPolynomial (Fin k) D)}
    (hp : PolyVarsSubset T parent) (hc : PolyVarsSubset T cur)
    {rest : List (Polynomial (MvPolynomial (Fin k) D))}
    (hrest : ∀ P ∈ rest, PolyVarsSubset T P) :
    (leafFormulaAux parent cur rest).freeVars ⊆ T := by
  induction rest generalizing parent cur with
  | nil =>
    show (degFormula (-(pRemMv parent cur)) ⊥).freeVars ⊆ T
    exact degFormula_freeVars_subset
      (PolyVarsSubset.neg (pRemMv_polyVarsSubset hp hc)) _
  | cons next rest' ih =>
    by_cases hnext : next = 0
    · have heq : leafFormulaAux parent cur (next :: rest') =
          degFormula (-(pRemMv parent cur)) ⊥ := by
        simp [leafFormulaAux, hnext]
      rw [heq]
      exact degFormula_freeVars_subset
        (PolyVarsSubset.neg (pRemMv_polyVarsSubset hp hc)) _
    · have heq : leafFormulaAux parent cur (next :: rest') =
          (degFormula (-(pRemMv parent cur)) (↑next.natDegree)).and
            (leafFormulaAux cur next rest') := by
        simp [leafFormulaAux, hnext]
      rw [heq]
      show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ T
      apply Finset.union_subset
      · exact degFormula_freeVars_subset
          (PolyVarsSubset.neg (pRemMv_polyVarsSubset hp hc)) _
      · exact ih hc (hrest next List.mem_cons_self)
          (fun P hP => hrest P (List.mem_cons_of_mem _ hP))

theorem leafFormula_freeVars_subset {T : Finset (Fin k)}
    {P Q : Polynomial (MvPolynomial (Fin k) D)}
    (hP : PolyVarsSubset T P) (hQ : PolyVarsSubset T Q)
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : ∀ R ∈ path, PolyVarsSubset T R) :
    (leafFormula P Q path).freeVars ⊆ T := by
  cases path with
  | nil =>
    show (degFormula Q ⊥).freeVars ⊆ T
    exact degFormula_freeVars_subset hQ _
  | cons q rest =>
    by_cases hq : q = 0
    · have heq : leafFormula P Q (q :: rest) = degFormula Q ⊥ := by
        simp [leafFormula, hq]
      rw [heq]
      exact degFormula_freeVars_subset hQ _
    · have heq : leafFormula P Q (q :: rest) =
          (degFormula Q (↑q.natDegree)).and (leafFormulaAux P q rest) := by
        simp [leafFormula, hq]
      rw [heq]
      show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ T
      apply Finset.union_subset
      · exact degFormula_freeVars_subset hQ _
      · exact leafFormulaAux_freeVars_subset hP (hpath q List.mem_cons_self)
          (fun R hR => hpath R (List.mem_cons_of_mem _ hR))

end FormulaTrackingVars

/-! ### `posgcd` preserves freeVars ⊆ T -/

section PosgcdTrackingVars

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

theorem posgcd_polyVarsSubset_and_freeVars_subset {T : Finset (Fin k)}
    {Ps : List (Polynomial (MvPolynomial (Fin k) D))}
    (hPs : ∀ P ∈ Ps, PolyVarsSubset T P) :
    ∀ GC ∈ posgcd Ps, PolyVarsSubset T GC.1 ∧ GC.2.freeVars ⊆ T := by
  induction Ps with
  | nil =>
    intro GC hmem
    simp only [posgcd, List.mem_singleton] at hmem
    subst hmem
    refine ⟨PolyVarsSubset.zero, ?_⟩
    show Formula.freeVars (Formula.trueFormula : Formula (Fin k) (FieldAtom (Fin k) D)) ⊆ T
    show (Formula.eq_zero (0 : MvPolynomial (Fin k) D)).freeVars ⊆ T
    show (Formula.atom (FieldAtom.eqZero 0)).freeVars ⊆ T
    intro x hx
    simp [Formula.freeVars, FieldAtom.vars, FieldAtom.eqZero] at hx
  | cons P rest ih =>
    intro GC hmem
    simp only [posgcd, List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨⟨Q, 𝒞⟩, hQC_mem, path, hpath, h_eq⟩ := hmem
    have hPc : PolyVarsSubset T P := hPs P List.mem_cons_self
    have hrestPs : ∀ R ∈ rest, PolyVarsSubset T R :=
      fun R hR => hPs R (List.mem_cons_of_mem _ hR)
    have ⟨hQc, hCfv⟩ := ih hrestPs (Q, 𝒞) hQC_mem
    have hpathPc : ∀ R ∈ path, PolyVarsSubset T R :=
      PolyVarsSubset.TRems_leafPaths hPc hQc path hpath
    refine ⟨?_, ?_⟩
    · rw [← h_eq]
      exact polyVarsSubset_pathLeafParent hPc hpathPc
    · rw [← h_eq]
      show (𝒞.and (leafFormula P Q path)).freeVars ⊆ T
      show 𝒞.freeVars ∪ (leafFormula P Q path).freeVars ⊆ T
      exact Finset.union_subset hCfv
        (leafFormula_freeVars_subset hPc hQc hpathPc)

end PosgcdTrackingVars

/-! ### `projBasic` preserves freeVars ⊆ T -/

section ProjBasicVars

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsDomain D] in
theorem map_splitLast_polyVarsSubset {T : Finset (Fin k)}
    {Ps : List (MvPolynomial (Fin (k+1)) D)}
    (hPs : ∀ P ∈ Ps, P.vars ⊆ insert (Fin.last k) (T.image Fin.castSucc)) :
    ∀ Q ∈ Ps.map splitLast, PolyVarsSubset T Q := by
  intro Q hQ
  rw [List.mem_map] at hQ
  obtain ⟨P, hP_mem, rfl⟩ := hQ
  exact splitLast_polyVarsSubset (hPs P hP_mem)

/-- **Generalized projBasic vars tracking**: `projBasic Ps Qs` has
`freeVars ⊆ T` when all input polynomials have
`vars ⊆ insert (Fin.last k) (T.image Fin.castSucc)`. -/
theorem projBasic_freeVars_subset {T : Finset (Fin k)}
    {Ps Qs : List (MvPolynomial (Fin (k+1)) D)}
    (hPs : ∀ P ∈ Ps, P.vars ⊆ insert (Fin.last k) (T.image Fin.castSucc))
    (hQs : ∀ Q ∈ Qs, Q.vars ⊆ insert (Fin.last k) (T.image Fin.castSucc)) :
    (projBasic Ps Qs).freeVars ⊆ T := by
  show (Formula.disjList _).freeVars ⊆ T
  apply Formula.disjList_freeVars_subset
  intro Φ hΦ
  simp only [List.mem_flatMap, List.mem_map, Prod.exists] at hΦ
  obtain ⟨G_1, C_1, h_mem_posgcd, path, hpath_mem, rfl⟩ := hΦ
  set Ps' : List (Polynomial (MvPolynomial (Fin k) D)) := Ps.map splitLast with Ps'_def
  set Qs' : List (Polynomial (MvPolynomial (Fin k) D)) := Qs.map splitLast with Qs'_def
  set d : ℕ := 1 + (Ps'.map Polynomial.natDegree).foldr max 0
  set extra : Polynomial (MvPolynomial (Fin k) D) := Qs'.prod ^ d
  have hPs'c : ∀ Q ∈ Ps', PolyVarsSubset T Q :=
    map_splitLast_polyVarsSubset hPs
  have hQs'c : ∀ Q ∈ Qs', PolyVarsSubset T Q :=
    map_splitLast_polyVarsSubset hQs
  have hextrac : PolyVarsSubset T extra :=
    PolyVarsSubset.pow (PolyVarsSubset.prod hQs'c) _
  have ⟨hG_1c, hC_1fv⟩ :=
    posgcd_polyVarsSubset_and_freeVars_subset hPs'c (G_1, C_1) h_mem_posgcd
  have hpath_PolyVarsSubset : ∀ R ∈ path, PolyVarsSubset T R :=
    PolyVarsSubset.TRems_leafPaths hextrac hG_1c path hpath_mem
  show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ T
  apply Finset.union_subset hC_1fv
  show Formula.freeVars _ ∪ Formula.freeVars _ ⊆ T
  apply Finset.union_subset
  · exact leafFormula_freeVars_subset hextrac hG_1c hpath_PolyVarsSubset
  · exact degNeqFormula_freeVars_subset
      (polyVarsSubset_pathLeafParent hextrac hpath_PolyVarsSubset) hG_1c

end ProjBasicVars

end VarsSubsetTracking

end Azurite.BPR

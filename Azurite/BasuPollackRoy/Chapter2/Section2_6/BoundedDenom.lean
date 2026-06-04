import Azurite.BasuPollackRoy.Chapter2.Section2_6.ConstPuiseux
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Lemma_2_95
import Azurite.BasuPollackRoy.Chapter2.Section2_6.OddMultiplicityRoot
import Azurite.BasuPollackRoy.Chapter2.Section2_6.RootSequence
import Mathlib.Algebra.Polynomial.Monic

/-! # BPR §2.6 — bounded denominators and the stabilized step

Two ingredients that keep the Newton–Puiseux recursion inside a fixed denominator lattice once the
multiplicity stabilizes:

* **bounded denominators** (`BoundedBy M`): a Puiseux series is a Laurent series in `ε^{1/M}`; the
  predicate is closed under the ring operations and `substPoly` (`boundedBy_substPoly`), and a
  polynomial's finitely many coefficients share one `M` (`exists_boundedBy`);
* **the stabilized step** (`stabilized_coeff_order`): when the multiplicity does not drop, the edge
  is the single segment `[0,r]`, `Q = c(X−x)^r`, and the exponent increment is a coefficient order
  `ξ = o(coeff (r−1))`.

Together (`stateSeq_boundedBy`, `stateSeq_xibeta_mem`) they bound the denominators of every `Pₙ`,
`ξₙ`, `βₙ` for `n` past the stabilization stage. -/

namespace Azurite.BPR

open Polynomial HahnSeries

variable {R : Type*} [Field R]

/-- `a`'s exponents lie in `(1/M)ℤ`: as a Hahn series it is a Laurent series in `ε^{1/M}`. -/
def BoundedBy (M : ℕ+) (a : PuiseuxSeries R) : Prop :=
  (a : HahnSeries ℚ R) ∈ puiseuxSubfield R M

theorem boundedBy_zero (M : ℕ+) : BoundedBy M (0 : PuiseuxSeries R) := by
  rw [BoundedBy, ZeroMemClass.coe_zero]; exact zero_mem _

theorem boundedBy_one (M : ℕ+) : BoundedBy M (1 : PuiseuxSeries R) := by
  rw [BoundedBy, OneMemClass.coe_one]; exact one_mem _

theorem BoundedBy.mul {M : ℕ+} {a b : PuiseuxSeries R} (ha : BoundedBy M a) (hb : BoundedBy M b) :
    BoundedBy M (a * b) := by rw [BoundedBy, Subfield.coe_mul]; exact mul_mem ha hb

theorem BoundedBy.add {M : ℕ+} {a b : PuiseuxSeries R} (ha : BoundedBy M a) (hb : BoundedBy M b) :
    BoundedBy M (a + b) := by rw [BoundedBy, Subfield.coe_add]; exact add_mem ha hb

theorem BoundedBy.sum {M : ℕ+} {ι : Type*} (s : Finset ι) {f : ι → PuiseuxSeries R}
    (hf : ∀ i ∈ s, BoundedBy M (f i)) : BoundedBy M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact boundedBy_zero M
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- A constant Puiseux series has exponent `0 ∈ (1/M)ℤ`, so it is bounded by any `M`. -/
theorem boundedBy_constPuiseux (M : ℕ+) (c : R) : BoundedBy M (constPuiseux c) := by
  rw [BoundedBy, coe_constPuiseux, puiseuxSubfield, RingHom.mem_fieldRange]
  refine ⟨HahnSeries.single 0 c, ?_⟩
  simp [puiseuxEmb_single, puiseuxExpHom_apply]

/-- `embDomain` along an order embedding `ℤ ↪o ℚ` maps the order to the order. -/
theorem order_embDomain {f : ℤ ↪o ℚ} {x : HahnSeries ℤ R} (hx : x ≠ 0) :
    (HahnSeries.embDomain f x).order = f x.order := by
  have hne : HahnSeries.embDomain f x ≠ 0 := by
    simpa using (HahnSeries.embDomain_injective (f := f)).ne hx
  have h := HahnSeries.orderTop_embDomain (f := f) (x := x)
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe] at h
  exact_mod_cast h

/-- The monomial `ε^γ` is bounded by `M` whenever `γ ∈ (1/M)ℤ`. -/
theorem boundedBy_puiseuxMonomial {M : ℕ+} {γ : ℚ} (n : ℤ) (hγ : γ = (n : ℚ) / (M : ℚ)) :
    BoundedBy M (puiseuxMonomial γ : PuiseuxSeries R) := by
  rw [BoundedBy, coe_puiseuxMonomial, puiseuxSubfield, RingHom.mem_fieldRange]
  refine ⟨HahnSeries.single n 1, ?_⟩
  rw [puiseuxEmb_single, hγ, puiseuxExpHom_apply]

/-- **Order extraction.** If `a ≠ 0` is bounded by `M`, then `M · o(a)` is an integer:
`o(a) ∈ (1/M)ℤ`. -/
theorem BoundedBy.order_mul_mem_int {M : ℕ+} {a : PuiseuxSeries R} (ha : BoundedBy M a)
    (h0 : a ≠ 0) : ∃ k : ℤ, HahnSeries.order (a : HahnSeries ℚ R) = (k : ℚ) / (M : ℚ) := by
  rw [BoundedBy, puiseuxSubfield, RingHom.mem_fieldRange] at ha
  obtain ⟨a', ha'⟩ := ha
  have hac : (a : HahnSeries ℚ R) ≠ 0 := by rw [Ne, ZeroMemClass.coe_eq_zero]; exact h0
  have ha'0 : a' ≠ 0 := fun h => by rw [h, map_zero] at ha'; exact hac ha'.symm
  refine ⟨a'.order, ?_⟩
  rw [← ha', puiseuxEmb, HahnSeries.embDomainRingHom_apply, order_embDomain ha'0]
  exact puiseuxExpHom_apply M a'.order

/-- If `a` is bounded by `M` and its order is the finite value `c`, then `c ∈ (1/M)ℤ`. -/
theorem boundedBy_puiseuxOrder_mem {M : ℕ+} {a : PuiseuxSeries R} (ha : BoundedBy M a) {c : ℚ}
    (hc : puiseuxOrder R a = (c : WithTop ℚ)) : ∃ k : ℤ, c = (k : ℚ) / (M : ℚ) := by
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [puiseuxOrder_zero] at hc; exact absurd hc.symm (by simp)
  obtain ⟨k, hk⟩ := ha.order_mul_mem_int ha0
  refine ⟨k, ?_⟩
  have hac : (a : HahnSeries ℚ R) ≠ 0 := by rw [Ne, ZeroMemClass.coe_eq_zero]; exact ha0
  have hpo : puiseuxOrder R a = ((HahnSeries.order (a : HahnSeries ℚ R) : ℚ) : WithTop ℚ) := by
    rw [puiseuxOrder, ← HahnSeries.order_eq_orderTop_of_ne_zero hac]
  rw [hpo] at hc
  rw [← hk]; exact_mod_cast hc.symm

/-- `BoundedBy` is monotone in the denominator: `q ∣ M` enlarges the lattice. -/
theorem BoundedBy.mono {q M : ℕ+} (h : q ∣ M) {a : PuiseuxSeries R} (ha : BoundedBy q a) :
    BoundedBy M a := puiseuxSubfield_mono R h ha

/-- **Every polynomial has a common denominator bound.** Its finitely many coefficients are Puiseux
series, each with some denominator; their product bounds them all. -/
theorem exists_boundedBy (P : Polynomial (PuiseuxSeries R)) :
    ∃ M : ℕ+, ∀ i, BoundedBy M (P.coeff i) := by
  classical
  have hq : ∀ i ∈ P.support, ∃ q : ℕ+, BoundedBy q (P.coeff i) := by
    intro i _
    have hmem := (P.coeff i).2
    rw [mem_puiseuxSeries_iff] at hmem
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩
  choose! q hq using hq
  refine ⟨∏ i ∈ P.support, q i, fun i => ?_⟩
  by_cases hi : i ∈ P.support
  · exact (hq i hi).mono (Finset.dvd_prod_of_mem q hi)
  · rw [Polynomial.mem_support_iff, not_not] at hi; rw [hi]; exact boundedBy_zero _

/-- **`substPoly` preserves `BoundedBy M`** when `ξ = a/M`, `β = b/M`. Each coefficient is a finite
sum of products `(P.coeff h) · ε^{hξ−β} · (constant)`, all bounded by `M`. -/
theorem boundedBy_substPoly {M : ℕ+} {P : Polynomial (PuiseuxSeries R)} {x : R} {ξ β : ℚ}
    {a b : ℤ} (hξ : ξ = (a : ℚ) / (M : ℚ)) (hβ : β = (b : ℚ) / (M : ℚ))
    (hP : ∀ i, BoundedBy M (P.coeff i)) (i : ℕ) :
    BoundedBy M ((substPoly P x ξ β).coeff i) := by
  rw [substPoly_coeff]
  apply BoundedBy.sum
  intro h _
  refine ((hP h).mul (boundedBy_puiseuxMonomial ((h : ℤ) * a - b) ?_)).mul
    (boundedBy_constPuiseux M _)
  rw [hξ, hβ]; push_cast; ring

/-- **The stabilized-step order identity.** If the edge `[A, B]` over `[0, r]` has
`rootMultiplicity x (charPoly P A B) = r` (multiplicity did not drop) with `x ≠ 0` and `r ≠ 0` in
`R`, then `o(P.coeff (r − 1)) = −newtonSlope A B` (`= ξ`). -/
theorem stabilized_coeff_order {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {x : R} {r : ℕ}
    (hABlt : A.1 < B.1) (hBr : B.1 ≤ r) (hx0 : x ≠ 0) (hrR : (r : R) ≠ 0)
    (hcolA : puiseuxOrder R (P.coeff A.1) = (A.2 : WithTop ℚ))
    (hcolB : puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ))
    (hbr : puiseuxOrder R (P.coeff r) = (0 : WithTop ℚ))
    (hr' : (charPoly P A B).rootMultiplicity x = r) :
    puiseuxOrder R (P.coeff (r - 1)) = (-(newtonSlope A B) : WithTop ℚ) := by
  classical
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hrR (by simp))
  have hQne : charPoly P A B ≠ 0 := charPoly_ne_zero hABlt hcolB
  -- single segment: A.1 = 0, B.1 = r
  have hspan : r ≤ B.1 - A.1 := by
    have h1 := rootMultiplicity_ne_zero_le_span hQne hx0
    rwa [charPoly_natDegree_eq hABlt hcolB, charPoly_natTrailingDegree_eq hABlt hcolA hcolB,
      hr'] at h1
  have hA1 : A.1 = 0 := by omega
  have hB1 : B.1 = r := by omega
  have hB2 : (B.2 : ℚ) = 0 := by
    have h := hcolB; rw [hB1, hbr] at h; exact_mod_cast h.symm
  have hdeg : (charPoly P A B).natDegree = r := by rw [charPoly_natDegree_eq hABlt hcolB, hB1]
  -- Q = c (X − x)^r ⇒ coeff (r−1) = c · (r • (−x)) ≠ 0
  have hnv : (charPoly P A B).nextCoeff = (charPoly P A B).leadingCoeff * (r • (-x)) := by
    conv_lhs => rw [eq_C_leadingCoeff_mul_X_sub_C_pow hQne hdeg hr', nextCoeff_C_mul,
      (monic_X_sub_C x).nextCoeff_pow r, nextCoeff_X_sub_C]
  have hcoeff : (charPoly P A B).coeff (r - 1) ≠ 0 := by
    have hcn : (charPoly P A B).coeff (r - 1) = (charPoly P A B).nextCoeff := by
      rw [nextCoeff_of_natDegree_pos (by rw [hdeg]; omega), hdeg]
    rw [hcn, hnv]
    refine mul_ne_zero (leadingCoeff_ne_zero.mpr hQne) ?_
    rw [nsmul_eq_mul]; exact mul_ne_zero hrR (neg_ne_zero.mpr hx0)
  -- column r−1 is on the edge
  have hcol : colOnLine P A B (r - 1) := by
    by_contra hn
    rw [charPoly_coeff, if_neg (fun hm => hn (Finset.mem_filter.mp hm).2)] at hcoeff
    exact hcoeff rfl
  have hcoleq : puiseuxOrder R (P.coeff (r - 1)) = (lineValue A B (r - 1) : WithTop ℚ) := hcol
  rw [hcoleq]; congr 1
  -- lineValue A B (r−1) = −newtonSlope A B
  have hms := newtonSlope_mul_sub (p := A) (q := B) hABlt.ne
  rw [hB1, hA1, hB2] at hms
  have hexp : newtonSlope A B * ((r : ℚ) - 1) = newtonSlope A B * (r : ℚ) - newtonSlope A B := by
    ring
  rw [lineValue, hA1, Nat.cast_sub hr1]
  push_cast
  push_cast at hms
  linarith [hms, hexp]

variable [IsRealClosed R]

/-- **Bounded denominators along the tail of the recursion.** There is a stage `N` (past which the
multiplicity is constant) and a single denominator `M` such that for all `n ≥ N`, every coefficient
of `Pₙ = (stateSeq s0 n).poly` is a Laurent series in `ε^{1/M}` (`BoundedBy M`). -/
theorem stateSeq_boundedBy (s0 : RecState R) :
    ∃ (N : ℕ) (M : ℕ+),
      (∀ n, N ≤ n → (stateSeq s0 n).mult = (stateSeq s0 N).mult) ∧
      ∀ n, N ≤ n → ∀ i, BoundedBy M ((stateSeq s0 n).poly.coeff i) := by
  obtain ⟨N, hN⟩ := stateSeq_mult_eventually_const s0
  obtain ⟨M, hM⟩ := exists_boundedBy ((stateSeq s0 N).poly)
  refine ⟨N, M, hN, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hM
  | succ n hn IH =>
    by_cases hbar : (stateSeq s0 n).poly.coeff 0 = 0
    · -- barrier: the step freezes the state, so the bound is inherited unchanged
      have hfreeze : stateSeq s0 (n + 1) = stateSeq s0 n := by
        show ((stateSeq s0 n).step).2.2.2 = stateSeq s0 n
        rw [RecState.step_barrier _ hbar]
      intro i; rw [hfreeze]; exact IH i
    · -- genuine step: a stabilized step keeps `ξ, β ∈ (1/M)ℤ`
      obtain ⟨sr, hstep⟩ := (stateSeq s0 n).step_spec hbar
      have hnext : stateSeq s0 (n + 1) = sr.next := by
        show ((stateSeq s0 n).step).2.2.2 = sr.next
        rw [hstep]
      have hrpos : (stateSeq s0 n).mult ≠ 0 := by
        obtain ⟨k, hk⟩ := (stateSeq s0 n).odd_mult; omega
      have hrR : ((stateSeq s0 n).mult : R) ≠ 0 := Nat.cast_ne_zero.mpr hrpos
      -- multiplicity did not drop, since it is constant from `N` on
      have hmult_eq : sr.next.mult = (stateSeq s0 n).mult := by
        rw [← hnext, hN (n + 1) (Nat.le_succ_of_le hn), ← hN n hn]
      have hr' : (charPoly (stateSeq s0 n).poly sr.edgeA sr.edgeB).rootMultiplicity sr.x
          = (stateSeq s0 n).mult := by rw [← sr.next_mult_eq, hmult_eq]
      -- `ξ` is literally `o(coeff (r−1))`
      have hξord : puiseuxOrder R ((stateSeq s0 n).poly.coeff ((stateSeq s0 n).mult - 1))
          = (sr.xi : WithTop ℚ) := by
        rw [stabilized_coeff_order sr.edge_lt sr.edge_le sr.x_ne hrR sr.colA sr.colB
          (stateSeq s0 n).coeff_mult_order hr', sr.xi_eq]
        norm_cast
      obtain ⟨k, hk⟩ := boundedBy_puiseuxOrder_mem (IH ((stateSeq s0 n).mult - 1)) hξord
      obtain ⟨kA, hkA⟩ := boundedBy_puiseuxOrder_mem (IH sr.edgeA.1) sr.colA
      have hβ : sr.beta = ((kA + (sr.edgeA.1 : ℤ) * k : ℤ) : ℚ) / (M : ℚ) := by
        rw [sr.beta_eq, hkA, hk]; push_cast; ring
      intro i
      rw [hnext, sr.next_poly]
      exact boundedBy_substPoly hk hβ IH i

/-- **The exponent and order increments share a fixed denominator past `N`.** For `n ≥ N`, both
`ξₙ = xiSeq s0 n` and `βₙ = betaSeq s0 n` lie in `(1/M)ℤ`. At a barrier step both are `0`; at a
genuine step `ξₙ = o(coeff (r−1)) ∈ (1/M)ℤ` (stabilized step) and `βₙ = edgeA.2 + edgeA.1·ξₙ`. -/
theorem stateSeq_xibeta_mem (s0 : RecState R) :
    ∃ (N : ℕ) (M : ℕ+), ∀ n, N ≤ n →
      (∃ k : ℤ, xiSeq s0 n = (k : ℚ) / (M : ℚ)) ∧
      (∃ k : ℤ, betaSeq s0 n = (k : ℚ) / (M : ℚ)) := by
  obtain ⟨N, M, hN, hbound⟩ := stateSeq_boundedBy s0
  refine ⟨N, M, fun n hn => ?_⟩
  by_cases hbar : (stateSeq s0 n).poly.coeff 0 = 0
  · -- barrier: both increments are `0`
    have hxi : xiSeq s0 n = 0 := by rw [xiSeq, RecState.step_barrier _ hbar]
    have hbeta : betaSeq s0 n = 0 := by rw [betaSeq, RecState.step_barrier _ hbar]
    exact ⟨⟨0, by rw [hxi]; simp⟩, ⟨0, by rw [hbeta]; simp⟩⟩
  · obtain ⟨sr, hstep⟩ := (stateSeq s0 n).step_spec hbar
    have hxi : xiSeq s0 n = sr.xi := by rw [xiSeq, hstep]
    have hbeta : betaSeq s0 n = sr.beta := by rw [betaSeq, hstep]
    have hnext : stateSeq s0 (n + 1) = sr.next := by
      show ((stateSeq s0 n).step).2.2.2 = sr.next
      rw [hstep]
    have hrpos : (stateSeq s0 n).mult ≠ 0 := by
      obtain ⟨k, hk⟩ := (stateSeq s0 n).odd_mult; omega
    have hrR : ((stateSeq s0 n).mult : R) ≠ 0 := Nat.cast_ne_zero.mpr hrpos
    have hmult_eq : sr.next.mult = (stateSeq s0 n).mult := by
      rw [← hnext, hN (n + 1) (Nat.le_succ_of_le hn), ← hN n hn]
    have hr' : (charPoly (stateSeq s0 n).poly sr.edgeA sr.edgeB).rootMultiplicity sr.x
        = (stateSeq s0 n).mult := by rw [← sr.next_mult_eq, hmult_eq]
    have hξord : puiseuxOrder R ((stateSeq s0 n).poly.coeff ((stateSeq s0 n).mult - 1))
        = (sr.xi : WithTop ℚ) := by
      rw [stabilized_coeff_order sr.edge_lt sr.edge_le sr.x_ne hrR sr.colA sr.colB
        (stateSeq s0 n).coeff_mult_order hr', sr.xi_eq]
      norm_cast
    obtain ⟨k, hk⟩ := boundedBy_puiseuxOrder_mem (hbound n hn ((stateSeq s0 n).mult - 1)) hξord
    obtain ⟨kA, hkA⟩ := boundedBy_puiseuxOrder_mem (hbound n hn sr.edgeA.1) sr.colA
    refine ⟨⟨k, by rw [hxi, hk]⟩, ⟨kA + (sr.edgeA.1 : ℤ) * k, ?_⟩⟩
    rw [hbeta, sr.beta_eq, hkA, hk]; push_cast; ring

end Azurite.BPR

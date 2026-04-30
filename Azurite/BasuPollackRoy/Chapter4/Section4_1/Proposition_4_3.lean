import Azurite.BasuPollackRoy.Chapter4.Section4_1.Notation_4_1
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Tactic.Ring

/-!
# BPR Proposition 4.3: Discriminant vanishing criterion

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

`Disc(P) = 0 ↔ deg(gcd(P, P')) > 0`. The forward implication is BPR's
"clear from the definition": `Disc(P) = ∏_{i > j} (x_i − x_j)^2` vanishes iff
two roots coincide (i.e. `P` has a multiple root in `C`). The remaining
equivalence — `P` has a multiple root in `C` iff `gcd(P, P')` is non-constant
— is the standard fact connecting separability and coprimality with the
derivative.

The Lean proof chains:
1. `disc P = 0 ↔ ¬ (P.aroots C).Nodup` via the off-diagonal multiset product.
2. `¬ (P.aroots C).Nodup ↔ ¬ P.Separable` via Mathlib's
   `Polynomial.nodup_aroots_iff_of_splits` (since `C` is algebraically closed).
3. `P.Separable` is definitionally `IsCoprime P P.derivative`.
4. `IsCoprime P P.derivative ↔ IsUnit (gcd P P')` via `EuclideanDomain.gcd_isUnit_iff`.
5. `IsUnit (gcd P P') ↔ (gcd P P').natDegree = 0` over a field, since
   `P` monic gives `gcd ≠ 0`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial
open scoped Classical

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- Count of `(a, b)` in the Cartesian product of multisets equals
    the product of individual counts. -/
lemma count_product_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Multiset α) (t : Multiset β) (a : α) (b : β) :
    (s ×ˢ t).count (a, b) = s.count a * t.count b := by
  induction s using Multiset.induction with
  | empty =>
    show Multiset.count (a, b) ((0 : Multiset α).bind (fun y => t.map fun z => (y, z))) = _
    simp
  | cons x s ih =>
    show Multiset.count (a, b) ((x ::ₘ s).bind fun y => t.map fun z => (y, z)) = _
    rw [Multiset.cons_bind, Multiset.count_add]
    show Multiset.count (a, b) (Multiset.map (fun z => (x, z)) t) +
         Multiset.count (a, b) (s ×ˢ t) = _
    rw [ih]
    by_cases hxa : x = a
    · subst hxa
      have hinj : Function.Injective (fun z : β => ((x, z) : α × β)) := by
        intros z₁ z₂ h; exact (Prod.mk.injEq x z₁ x z₂).mp h |>.2
      rw [Multiset.count_map_eq_count' _ _ hinj b, Multiset.count_cons_self]
      ring
    · have hzero : (Multiset.map (fun z : β => ((x, z) : α × β)) t).count (a, b) = 0 := by
        rw [Multiset.count_map, Multiset.card_eq_zero]
        apply Multiset.filter_eq_nil.mpr
        intros z _ hz
        exact hxa ((Prod.mk.injEq a b x z).mp hz).1.symm
      rw [hzero, Multiset.count_cons_of_ne (Ne.symm hxa)]
      ring

/-- The diagonal map `y ↦ (y, y)` is injective, so the count of `(a, a)`
    in `s.map (·, ·)` equals `s.count a`. -/
lemma count_diag_map {α : Type*} [DecidableEq α] (s : Multiset α) (a : α) :
    (s.map (fun y => ((y, y) : α × α))).count (a, a) = s.count a := by
  apply Multiset.count_map_eq_count' _ _ ?_ a
  intros x y h
  exact (Prod.mk.injEq x x y y).mp h |>.1

omit [IsAlgClosed C] in
/-- The off-diagonal product over `s ×ˢ s` vanishes iff `s` has a duplicate.
    This is the "clear from the definition" step in BPR's proof of
    Proposition 4.3: `Disc(P) = 0` iff `P` has a multiple root in `C`. -/
theorem offdiag_prod_eq_zero_iff (P : K[X]) :
    (((P.aroots C ×ˢ P.aroots C - (P.aroots C).map (fun a => (a, a))).map
        (fun ab : C × C => ab.1 - ab.2)).prod = 0)
      ↔ ¬(P.aroots C).Nodup := by
  set s := P.aroots C
  rw [Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, heq⟩
    simp only at heq
    rw [sub_eq_zero] at heq
    subst heq
    rw [← Multiset.one_le_count_iff_mem] at hmem
    rw [Multiset.count_sub, count_product_eq, count_diag_map] at hmem
    have h2 : 2 ≤ s.count a := by
      by_contra h
      push Not at h
      interval_cases (s.count a) <;> omega
    rw [Multiset.nodup_iff_count_le_one]
    push Not
    exact ⟨a, by omega⟩
  · intro hnotdup
    rw [Multiset.nodup_iff_count_le_one] at hnotdup
    push Not at hnotdup
    obtain ⟨a, ha⟩ := hnotdup
    refine ⟨(a, a), ?_, by simp⟩
    rw [← Multiset.one_le_count_iff_mem, Multiset.count_sub,
        count_product_eq, count_diag_map]
    have hge : 2 ≤ s.count a := ha
    have : 2 * s.count a ≤ s.count a * s.count a := Nat.mul_le_mul_right _ hge
    omega

/-- **BPR Proposition 4.3**. For a monic polynomial `P : K[X]`,
    `Disc(P) = 0` iff `gcd(P, P')` has positive degree.

    Per BPR: "It is clear from the definition that `Disc(P) = 0` iff `P` has a
    multiple root in `C`." The "multiple root iff `gcd(P, P')` is non-constant"
    half is the standard separability/coprimality bridge. -/
theorem disc_eq_zero_iff (P : K[X]) (hP : P.Monic) :
    (disc P : C) = 0 ↔ 0 < (EuclideanDomain.gcd P P.derivative).natDegree := by
  have hP_ne : P ≠ 0 := hP.ne_zero
  have hsplits : (P.map (algebraMap K C)).Splits := IsAlgClosed.splits _
  -- (1) sign factor is a unit, so disc P = 0 iff the off-diag product is 0.
  have step1 : (disc P : C) = 0 ↔ ((P.aroots C ×ˢ P.aroots C
      - (P.aroots C).map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod = 0 := by
    show ((-1 : C) ^ _ * _ = 0) ↔ _
    rw [mul_eq_zero]
    refine ⟨?_, fun hprod => Or.inr hprod⟩
    rintro (hsign | hprod)
    · exact absurd hsign (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    · exact hprod
  -- (2)+(3): off-diag = 0 ↔ aroots not Nodup ↔ ¬ Separable ↔ ¬ IsCoprime.
  rw [step1, offdiag_prod_eq_zero_iff,
      not_congr (Polynomial.nodup_aroots_iff_of_splits hP_ne hsplits)]
  show ¬IsCoprime P P.derivative ↔ _
  -- (4): IsCoprime ↔ IsUnit gcd over a Euclidean domain.
  rw [← EuclideanDomain.gcd_isUnit_iff]
  -- (5): IsUnit gcd ↔ natDegree gcd = 0 over a field, given gcd ≠ 0.
  refine ⟨fun hnu => ?_, fun hpos hu =>
    Nat.lt_irrefl 0 (Polynomial.natDegree_eq_zero_of_isUnit hu ▸ hpos)⟩
  by_contra hcon
  push Not at hcon
  apply hnu
  have hcon' : (EuclideanDomain.gcd P P.derivative).natDegree = 0 := Nat.le_zero.mp hcon
  have hgcd_ne : EuclideanDomain.gcd P P.derivative ≠ 0 := fun hzero =>
    hP_ne ((EuclideanDomain.gcd_eq_zero_iff).mp hzero).1
  rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hgcd_ne]
  exact_mod_cast hcon'

end Azurite.BPR.Chapter4

import Azurite.BasuPollackRoy.Chapter4.Section4_1.Notation_4_1
import Azurite.BasuPollackRoy.Chapter4.Section4_1.Proposition_4_3
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.IntervalCases

/-!
# BPR Remark 4.4: positivity for distinct real roots

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

When `P : R[X]` is monic with all roots in `R` (a linearly ordered field) and
distinct, `Disc(P) > 0`.

We capture this as a positivity statement on a *parallel* R-valued
discriminant `discR : R[X] → R`, defined by the same off-diagonal multiset
formula as `disc` but evaluated on `P.roots : Multiset R` instead of
`P.aroots C`. The proof of positivity exploits the squaring identity:
under the off-diagonal encoding, when the multiset of roots is `Nodup` we
have `discR P = Q^2` where `Q = ∏_{(a, b), a > b}(a − b)`. Distinct roots
make every factor of `Q` nonzero, so `Q ≠ 0` and `Q^2 > 0`.

The bridge `(algebraMap R C) (discR P) = disc P` (when `P` splits in `R`)
is deferred: it requires several multiset-vs-ringhom commutation lemmas
that are not currently in Mathlib (notably, `(s.map f) ×ˢ (t.map f) =
(s ×ˢ t).map (Prod.map f f)` and `(m - n).map f = m.map f - n.map f` for
injective `f`). Once we land that bridge, Remark 4.4 lifts to the
C-valued statement `disc P = (algebraMap R C) (positive R-element)`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

section RealSide
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The R-valued discriminant of a polynomial over a linearly ordered
    field, defined by the same off-diagonal formula as `disc` but
    evaluated on `P.roots : Multiset R`. When `P` splits in `R`, this
    equals `(algebraMap R C)⁻¹ (disc P)` (a connecting lemma whose proof
    is deferred). -/
noncomputable def discR (P : R[X]) : R :=
  let s := P.roots
  let p := s.card
  (-1 : R) ^ (p * (p - 1) / 2) *
    ((s ×ˢ s - s.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod

omit [Field R] [IsStrictOrderedRing R] in
/-- Partition lemma: when `s.Nodup`, the off-diagonal multiset
    `(s ×ˢ s) − Δ` decomposes into the strict-greater and strict-less
    parts of `s ×ˢ s`. -/
private lemma offdiag_eq_gt_plus_lt (s : Multiset R) (hs : s.Nodup) :
    s ×ˢ s - s.map (fun a => (a, a)) =
    (s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2) +
    (s ×ˢ s).filter (fun ab : R × R => ab.1 < ab.2) := by
  rw [Multiset.nodup_iff_count_le_one] at hs
  ext ⟨a, b⟩
  rw [Multiset.count_sub, Multiset.count_add,
      Multiset.count_filter, Multiset.count_filter,
      count_product_eq]
  by_cases hab : a = b
  · subst hab
    rw [count_diag_map]
    simp only [lt_irrefl, if_false, add_zero]
    have ha := hs a
    interval_cases (s.count a) <;> simp
  · have hdiag_zero : (s.map (fun y : R => (y, y))).count (a, b) = 0 := by
      rw [Multiset.count_map, Multiset.card_eq_zero]
      apply Multiset.filter_eq_nil.mpr
      intros z _ hz
      have heq := (Prod.mk.injEq a b z z).mp hz
      exact hab (heq.1.trans heq.2.symm)
    rw [hdiag_zero, Nat.sub_zero]
    rcases lt_trichotomy a b with hlt | heq | hgt
    · simp only [if_neg (asymm hlt), if_pos hlt, zero_add]
    · exact absurd heq hab
    · simp only [if_pos hgt, if_neg (asymm hgt), add_zero]

omit [Field R] [IsStrictOrderedRing R] in
/-- The strict-less part of `s ×ˢ s` is the strict-greater part with each
    pair swapped (the `Prod.swap` involution). -/
private lemma filter_lt_eq_filter_gt_swap (s : Multiset R) :
    (s ×ˢ s).filter (fun ab : R × R => ab.1 < ab.2) =
    ((s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2)).map Prod.swap := by
  have hinj : Function.Injective (Prod.swap : R × R → R × R) :=
    Function.LeftInverse.injective Prod.swap_swap
  ext ⟨x, y⟩
  rw [Multiset.count_filter,
      show ((x, y) : R × R) = Prod.swap (y, x) from rfl,
      Multiset.count_map_eq_count' _ _ hinj (y, x),
      Multiset.count_filter, count_product_eq, count_product_eq]
  by_cases hxy : x < y
  · simp [hxy, mul_comm]
  · simp [hxy]

omit [Field R] [IsStrictOrderedRing R] in
/-- When `s.Nodup`, the strict-greater part has cardinality `card·(card−1)/2`. -/
private lemma card_filter_gt_eq (s : Multiset R) (hs : s.Nodup) :
    ((s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2)).card =
    s.card * (s.card - 1) / 2 := by
  have hle : s.map (fun a : R => (a, a)) ≤ s ×ˢ s := by
    rw [Multiset.le_iff_count]
    intro p
    obtain ⟨a, b⟩ := p
    rw [count_product_eq]
    by_cases hab : a = b
    · subst hab
      rw [count_diag_map]
      nlinarith [Nat.zero_le (s.count a)]
    · have hzero : (s.map (fun y : R => (y, y))).count (a, b) = 0 := by
        rw [Multiset.count_map, Multiset.card_eq_zero]
        apply Multiset.filter_eq_nil.mpr
        intros z _ hz
        have heq := (Prod.mk.injEq a b z z).mp hz
        exact hab (heq.1.trans heq.2.symm)
      omega
  have hsub_card : (s ×ˢ s - s.map (fun a : R => (a, a))).card =
                   s.card * (s.card - 1) := by
    rw [Multiset.card_sub hle, Multiset.card_product, Multiset.card_map,
        Nat.mul_sub_one]
  have hcard_off : ((s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2)).card +
                   ((s ×ˢ s).filter (fun ab : R × R => ab.1 < ab.2)).card =
                   s.card * (s.card - 1) := by
    have h := offdiag_eq_gt_plus_lt s hs
    have hcard_eq : (s ×ˢ s - s.map (fun a => (a, a))).card =
        ((s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2) +
         (s ×ˢ s).filter (fun ab : R × R => ab.1 < ab.2)).card := by rw [h]
    rw [Multiset.card_add] at hcard_eq
    omega
  have hsymm : ((s ×ˢ s).filter (fun ab : R × R => ab.1 < ab.2)).card =
               ((s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2)).card := by
    rw [filter_lt_eq_filter_gt_swap, Multiset.card_map]
  omega

/-- The squaring identity: when `s.Nodup`, `discR`'s pre-image in `R`
    is a perfect square. With `Q := ∏_{(a, b) ∈ filter(>)}(a − b)`,
    we have `(-1)^N · off-diag-prod = Q^2`. -/
private lemma discR_aux_eq_sq (s : Multiset R) (hs : s.Nodup) :
    (-1 : R) ^ (s.card * (s.card - 1) / 2) *
      ((s ×ˢ s - s.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod =
    ((((s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2)).map
      (fun ab => ab.1 - ab.2)).prod) ^ 2 := by
  rw [offdiag_eq_gt_plus_lt s hs, Multiset.map_add, Multiset.prod_add,
      filter_lt_eq_filter_gt_swap, Multiset.map_map]
  have hfun : (fun ab : R × R => ab.1 - ab.2) ∘ Prod.swap =
              Neg.neg ∘ (fun ab : R × R => ab.1 - ab.2) := by
    funext ⟨a, b⟩; simp [Prod.swap]
  rw [hfun, ← Multiset.map_map, Multiset.prod_map_neg, Multiset.card_map,
      card_filter_gt_eq s hs]
  set N := s.card * (s.card - 1) / 2
  set Q := (((s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2)).map
            (fun ab : R × R => ab.1 - ab.2)).prod
  have hsq : (-1 : R) ^ N * (-1 : R) ^ N = 1 := by
    rw [← pow_add, show (N + N : ℕ) = 2 * N from by ring, pow_mul, neg_one_sq,
        one_pow]
  linear_combination (Q ^ 2) * hsq

/-- Distinct roots in `R` make the strict-greater product nonzero. -/
private lemma filter_gt_prod_ne_zero (s : Multiset R) (_hs : s.Nodup) :
    (((s ×ˢ s).filter (fun ab : R × R => ab.1 > ab.2)).map
      (fun ab => ab.1 - ab.2)).prod ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro hzero
  rw [Multiset.mem_map] at hzero
  obtain ⟨⟨a, b⟩, hmem, heq⟩ := hzero
  rw [Multiset.mem_filter] at hmem
  obtain ⟨_, hgt⟩ := hmem
  exact sub_ne_zero.mpr (ne_of_gt hgt) heq

/-- **BPR Remark 4.4 (R-valued form).** When `P : R[X]` is monic with all
    roots in the linearly ordered field `R` and distinct, the R-side
    discriminant is positive. -/
theorem discR_pos_of_distinct_roots (P : R[X]) (_hP : P.Monic)
    (hnodup : P.roots.Nodup) :
    0 < discR P := by
  unfold discR
  rw [discR_aux_eq_sq P.roots hnodup]
  exact sq_pos_of_ne_zero (filter_gt_prod_ne_zero P.roots hnodup)

end RealSide

section Bridge

/-- Multiset Cartesian product commutes with mapping a function on each
    component: `(s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g)`. -/
private lemma multiset_product_map {α α' β β' : Type*}
    (s : Multiset α) (t : Multiset β) (f : α → α') (g : β → β') :
    (s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g) := by
  show (s.map f).bind (fun a' => (t.map g).map fun b' => (a', b')) =
       (s.bind fun a => t.map fun b => (a, b)).map (Prod.map f g)
  rw [Multiset.bind_map, Multiset.map_bind]
  congr 1
  funext a
  rw [Multiset.map_map, Multiset.map_map]
  rfl

/-- Multiset subtraction commutes with mapping by an injective function:
    `(m - n).map f = m.map f - n.map f` when `f` is injective. -/
private lemma multiset_map_sub_of_injective {α β : Type*}
    [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (m n : Multiset α) :
    (m - n).map f = m.map f - n.map f := by
  ext y
  rw [Multiset.count_sub]
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [Multiset.count_map_eq_count' f _ hf x,
        Multiset.count_map_eq_count' f _ hf x,
        Multiset.count_map_eq_count' f _ hf x, Multiset.count_sub]
  · push Not at hy
    have h : ∀ s : Multiset α, (s.map f).count y = 0 := by
      intro s
      rw [Multiset.count_map, Multiset.card_eq_zero]
      apply Multiset.filter_eq_nil.mpr
      intros a _ heq
      exact hy a heq.symm
    rw [h, h, h]

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {C : Type*} [Field C] [Algebra R C] [IsAlgClosed C]

omit [IsStrictOrderedRing R] [IsAlgClosed C] in
/-- **Bridge.** When `P : R[X]` splits in `R`, the C-valued discriminant
    `disc P` is the image of the R-valued discriminant `discR P` under
    the embedding `R ↪ C`. -/
theorem disc_eq_algebraMap_discR (P : R[X]) (hsplits : P.Splits) :
    (disc P : C) = (algebraMap R C) (discR P) := by
  classical
  set f := algebraMap R C
  have hinj : Function.Injective f := RingHom.injective f
  have hinjP : Function.Injective (Prod.map f f) := hinj.prodMap hinj
  -- aroots in C = P.roots.map f
  have haroots_eq : P.aroots C = P.roots.map f :=
    hsplits.roots_map f
  -- Unfold disc and discR explicitly.
  show (-1 : C) ^ ((P.aroots C).card * ((P.aroots C).card - 1) / 2) *
        (((P.aroots C) ×ˢ (P.aroots C) - (P.aroots C).map (fun a => (a, a))).map
          (fun ab => ab.1 - ab.2)).prod
      = f ((-1 : R) ^ (P.roots.card * (P.roots.card - 1) / 2) *
        ((P.roots ×ˢ P.roots - P.roots.map (fun a => (a, a))).map
          (fun ab => ab.1 - ab.2)).prod)
  rw [haroots_eq, Multiset.card_map]
  -- Goal: (-1)^N * ((s_R.map f ×ˢ s_R.map f - (s_R.map f).map (·, ·)).map (·.1 - ·.2)).prod
  --     = f((-1)^N * ((s_R ×ˢ s_R - s_R.map (·, ·)).map (·.1 - ·.2)).prod)
  rw [map_mul, map_pow, map_multiset_prod]
  simp only [map_neg, map_one]
  -- Now both sides should be "f-image of R-side product"; close via `congr` + multiset commutations.
  congr 1
  rw [multiset_product_map P.roots P.roots f f]
  -- Convert (s_R.map f).map (·, ·) to (s_R.map (·, ·)).map (Prod.map f f)
  rw [show (P.roots.map f).map (fun a : C => (a, a))
        = (P.roots.map (fun a : R => (a, a))).map (Prod.map f f) from ?_]
  · rw [← multiset_map_sub_of_injective hinjP, Multiset.map_map, Multiset.map_map]
    -- Both sides are (m.map _).prod; show the two map functions agree.
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intros ab _
    obtain ⟨a, b⟩ := ab
    simp [Prod.map, map_sub]
  · rw [Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intros a _
    simp [Prod.map]

omit [IsAlgClosed C] in
/-- **BPR Remark 4.4.** When `P : R[X]` is monic with all roots in the
    linearly ordered field `R` and distinct, `Disc(P) > 0` --- precisely:
    `disc P` (in any algebraic closure `C`) equals `(algebraMap R C) d`
    for some positive `d : R`. -/
theorem disc_pos_of_real_distinct_roots (P : R[X]) (hP : P.Monic)
    (hsplits : P.Splits) (hnodup : P.roots.Nodup) :
    ∃ d : R, 0 < d ∧ (algebraMap R C) d = (disc P : C) :=
  ⟨discR P, discR_pos_of_distinct_roots P hP hnodup,
   (disc_eq_algebraMap_discR (C := C) P hsplits).symm⟩

end Bridge

end Azurite.BPR.Chapter4

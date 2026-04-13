import Azurite.AzPolynomial.TRems
import Azurite.AzPolynomial.Equiv.Tru
import Azurite.AzPolynomial.Equiv.PRem
import Azurite.AzPolynomial.Equiv.Neg

/-!
# Equivalence: `AzPolynomial.tremsLeafParents` ↔ BPR's `TRems` leaf parents

Shows that the leaf parents of the computable `tremsLeafParents` on
`AzPolynomial (AzMvPolynomial k D ord)` correspond exactly to the
leaf parents of the noncomputable `BPR.TRems` on
`Polynomial (MvPolynomial (Fin k) D)` under the `liftPoly` bridge.

The main results are:

* `liftPoly_pRem_eq_pRemMv` — the computable `pRem` matches the
  noncomputable `pRemMv` under `liftPoly`.
* `mem_tremsLeafParents_iff_isLeafParent` — a polynomial belongs to the
  computable leaf-parent list iff its `liftPoly` image is a leaf parent
  of the noncomputable tree.
-/

namespace Azurite

open AzMvPolynomial Polynomial

variable {k : ℕ} {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-! ### Bridge lemma: `liftPoly_neg` -/

@[simp] theorem liftPoly_neg (p : AzPolynomial (AzMvPolynomial k D ord)) :
    liftPoly (-p) = -(liftPoly p) := by
  simp only [liftPoly, AzPolynomial.toPoly_neg, Polynomial.map_neg]

/-! ### Bridge lemma: `liftPoly_pRem_eq_pRemMv` -/

private theorem toMvPolyHom_injective' :
    Function.Injective (AzMvPolynomial.toMvPolyHom (R := D) (n := k) (ord := ord)) :=
  fun _ _ h => toMvPoly_injective h

/-- `pRemExp` is preserved by `liftPoly` because `natDegree` is
preserved by injective `Polynomial.map`. -/
private theorem pRemExp_liftPoly
    (P Q : AzPolynomial (AzMvPolynomial k D ord)) :
    BPR.pRemExp (liftPoly P) (liftPoly Q) =
      BPR.pRemExp (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
  unfold BPR.pRemExp BPR.smallestEvenGe
  rw [liftPoly_natDegree, liftPoly_natDegree,
      AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]

/-- The computational `pRem` matches BPR's `pRemMv` under `liftPoly`:
for any `P Q : AzPolynomial (AzMvPolynomial k D ord)`,
`liftPoly (pRem P Q) = pRemMv (liftPoly P) (liftPoly Q)`. -/
theorem liftPoly_pRem_eq_pRemMv
    (P Q : AzPolynomial (AzMvPolynomial k D ord))
    (hQ : Q ≠ 0) :
    liftPoly (AzPolynomial.pRem P Q) =
      BPR.pRemMv (liftPoly P) (liftPoly Q) := by
  -- Both sides map to the same element under algebraMap, so equal by injectivity.
  set K' := FractionRing (MvPolynomial (Fin k) D)
  set ι : MvPolynomial (Fin k) D →+* K' := algebraMap _ K'
  set φ := AzMvPolynomial.toMvPolyHom (R := D) (n := k) (ord := ord)
  have hφ_inj := toMvPolyHom_injective' (D := D) (k := k) (ord := ord)
  have hι_inj := IsFractionRing.injective (MvPolynomial (Fin k) D) K'
  -- liftPoly Q ≠ 0, toPoly Q ≠ 0
  have hLQ_ne : liftPoly Q ≠ 0 := (liftPoly_eq_zero_iff Q).not.mpr hQ
  have hTQ_ne : AzPolynomial.toPoly Q ≠ 0 := by
    intro h; exact hQ (toPoly_inj.mp (by rw [h, toPoly_zero]))
  -- Step 1: Division equation in AzMvPoly[X]
  obtain ⟨A, hAR⟩ := AzPolynomial.toPoly_pRem_div_eq P Q hTQ_ne
  -- Step 2: Map through ι ∘ φ to K'[X]
  have hmap := congrArg (Polynomial.map (ι.comp φ)) hAR
  simp only [Polynomial.map_mul, Polynomial.map_add] at hmap
  -- Simplify coefficient: map (ι∘φ) (C(b^d)) = C(ι(lc(liftPoly Q)^d'))
  have hC_simp : Polynomial.map (ι.comp φ) (Polynomial.C (Q.leadingCoeff ^
      BPR.pRemExp (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q))) =
      Polynomial.C (ι ((liftPoly Q).leadingCoeff ^
        BPR.pRemExp (liftPoly P) (liftPoly Q))) := by
    rw [Polynomial.map_C, RingHom.comp_apply, map_pow, pRemExp_liftPoly]
    congr 3
    have := Polynomial.leadingCoeff_map_of_injective hφ_inj (AzPolynomial.toPoly Q)
    rw [leadingCoeff_toPoly] at this
    exact this.symm
  -- Convert map (ι∘φ) (toPoly r) to (liftPoly r).map ι
  have hcomp : ∀ r : AzPolynomial (AzMvPolynomial k D ord),
      Polynomial.map (ι.comp φ) (AzPolynomial.toPoly r) = (liftPoly r).map ι := by
    intro r; show _ = Polynomial.map ι (Polynomial.map φ (AzPolynomial.toPoly r))
    rw [Polynomial.map_map]
  rw [hC_simp, hcomp P, hcomp Q, hcomp (AzPolynomial.pRem P Q)] at hmap
  -- Step 3: Degree bound
  have hdeg : (liftPoly (AzPolynomial.pRem P Q)).degree <
      (liftPoly Q).degree := by
    show (Polynomial.map φ (AzPolynomial.toPoly (AzPolynomial.pRem P Q))).degree <
      (Polynomial.map φ (AzPolynomial.toPoly Q)).degree
    rw [Polynomial.degree_map_eq_of_injective hφ_inj,
        Polynomial.degree_map_eq_of_injective hφ_inj]
    exact AzPolynomial.degree_toPoly_pRem_lt P Q hTQ_ne
  have hdeg_ι : ((liftPoly (AzPolynomial.pRem P Q)).map ι).degree <
      ((liftPoly Q).map ι).degree := by
    rwa [Polynomial.degree_map_eq_of_injective hι_inj,
         Polynomial.degree_map_eq_of_injective hι_inj]
  -- Step 4: Uniqueness of Euclidean division in K'[X]
  have hLQ_map_ne : (liftPoly Q).map ι ≠ 0 :=
    (Polynomial.map_ne_zero_iff hι_inj).mpr hLQ_ne
  have hdvd : (liftPoly Q).map ι ∣
      (Polynomial.C (ι ((liftPoly Q).leadingCoeff ^
        BPR.pRemExp (liftPoly P) (liftPoly Q))) *
        (liftPoly P).map ι) -
      (liftPoly (AzPolynomial.pRem P Q)).map ι :=
    ⟨Polynomial.map (ι.comp φ) A, by linear_combination hmap⟩
  have hmod_sub :
      ((Polynomial.C (ι ((liftPoly Q).leadingCoeff ^
        BPR.pRemExp (liftPoly P) (liftPoly Q))) *
        (liftPoly P).map ι) -
        (liftPoly (AzPolynomial.pRem P Q)).map ι) %
          (liftPoly Q).map ι = 0 :=
    EuclideanDomain.mod_eq_zero.mpr hdvd
  rw [Polynomial.sub_mod, sub_eq_zero] at hmod_sub
  -- So (liftPoly(pRem P Q)).map ι = PRem K' (liftPoly P) (liftPoly Q)
  have hlift_spec : (liftPoly (AzPolynomial.pRem P Q)).map ι =
      BPR.PRem K' (liftPoly P) (liftPoly Q) := by
    -- Unfold PRem to Rem to explicit mod, then simplify map over product
    have heq : BPR.PRem K' (liftPoly P) (liftPoly Q) =
        (Polynomial.C (ι ((liftPoly Q).leadingCoeff ^
          BPR.pRemExp (liftPoly P) (liftPoly Q))) *
          (liftPoly P).map ι) % ((liftPoly Q).map ι) := by
      unfold BPR.PRem BPR.Rem
      simp only [Polynomial.map_mul, Polynomial.map_C]
      rfl
    rw [heq, hmod_sub, (Polynomial.mod_eq_self_iff hLQ_map_ne).mpr hdeg_ι]
  -- pRemMv satisfies the same spec
  have hpRemMv_spec := BPR.pRemMv_spec (liftPoly P) (liftPoly Q) hLQ_ne
  -- By injectivity of Polynomial.map ι
  exact Polynomial.map_injective ι hι_inj (by rw [hlift_spec, hpRemMv_spec])

/-! ### Helper: `tru` empty iff zero -/

theorem tru_eq_nil_iff
    (p : AzPolynomial (AzMvPolynomial k D ord)) :
    AzPolynomial.tru p = [] ↔ p = 0 := by
  constructor
  · intro h; rw [AzPolynomial.tru] at h
    by_contra hne
    simp only [beq_iff_eq, hne, ↓reduceIte, Bool.or_eq_true] at h
    split_ifs at h
  · intro h; subst h; rw [AzPolynomial.tru]; simp

omit [IsDomain D] in
private theorem Tru_eq_empty_iff
    (Q : Polynomial (MvPolynomial (Fin k) D)) :
    BPR.Tru Q = ∅ ↔ Q = 0 := by
  constructor
  · intro h; by_contra hne
    have : Q ∈ BPR.Tru Q := by
      rw [BPR.Tru, if_neg hne]
      split_ifs
      · exact Set.mem_singleton_iff.mpr rfl
      · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr rfl)
    rw [h] at this; exact this
  · rintro rfl; rw [BPR.Tru, if_pos rfl]

/-! ### Surjectivity: elements of `Tru(liftPoly p)` have preimages -/

private theorem Tru_liftPoly_subset_range
    (p : AzPolynomial (AzMvPolynomial k D ord)) :
    BPR.Tru (liftPoly p) ⊆
      Set.range (liftPoly (k := k) (D := D) (ord := ord)) := by
  suffices ∀ n, ∀ p : AzPolynomial (AzMvPolynomial k D ord),
      p.natDegree ≤ n →
      BPR.Tru (liftPoly p) ⊆ Set.range liftPoly from
    this p.natDegree p le_rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro p hpn x hx
  rw [BPR.Tru] at hx
  by_cases h0 : liftPoly p = 0
  · rw [if_pos h0] at hx; exact hx.elim
  · rw [if_neg h0] at hx
    by_cases hbase : (∃ d, (liftPoly p).leadingCoeff = MvPolynomial.C d) ∨
        (liftPoly p).natDegree = 0
    · rw [if_pos hbase, Set.mem_singleton_iff] at hx
      exact ⟨p, hx.symm⟩
    · rw [if_neg hbase, Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with rfl | hx
      · exact ⟨p, rfl⟩
      · rw [liftPoly_natDegree, ← liftPoly_truncate] at hx
        push Not at hbase
        have hpos : 0 < p.natDegree := by
          rw [← liftPoly_natDegree]; exact Nat.pos_of_ne_zero hbase.2
        have hle := AzPolynomial.natDegree_truncate_le (p.natDegree - 1) p
        exact ih _ (by omega) _ le_rfl hx

/-- Every element of `Tru (liftPoly p)` has a preimage in `tru p`. -/
private theorem exists_tru_preimage
    (p : AzPolynomial (AzMvPolynomial k D ord))
    (x : Polynomial (MvPolynomial (Fin k) D))
    (hx : x ∈ BPR.Tru (liftPoly p)) :
    ∃ q, q ∈ AzPolynomial.tru p ∧ liftPoly q = x := by
  obtain ⟨q, rfl⟩ := Tru_liftPoly_subset_range p hx
  exact ⟨q, (mem_tru_iff_mem_Tru p q).mpr hx, rfl⟩

/-! ### Inductive leaf predicate -/

/-- `IsLeafParentOfMkTRemsNode P Q q` means `q` is a nonzero node
(leaf parent) in some branch of the tree `BPR.mkTRemsNode P Q`.
Every nonzero node is a leaf parent because it has a `0`-sentinel child.
Two cases mirror the recursive structure of `mkTRemsLeafParentsAux`. -/
inductive BPR.IsLeafParentOfMkTRemsNode {k : ℕ} {D : Type _} [CommRing D]
    [IsDomain D] :
    Polynomial (MvPolynomial (Fin k) D) →
    Polynomial (MvPolynomial (Fin k) D) →
    Polynomial (MvPolynomial (Fin k) D) → Prop
  | self {P Q} (h : Q ≠ 0) :
      BPR.IsLeafParentOfMkTRemsNode P Q Q
  | child {P Q c q} (h : Q ≠ 0)
      (hc : c ∈ BPR.Tru (-(BPR.pRemMv P Q)))
      (hq : BPR.IsLeafParentOfMkTRemsNode Q c q) :
      BPR.IsLeafParentOfMkTRemsNode P Q q

/-! ### `mkTRemsLeafParentsAux` ↔ `IsLeafParentOfMkTRemsNode` -/

/-- Forward: membership in `mkTRemsLeafParentsAux` implies
`IsLeafParentOfMkTRemsNode`. -/
private theorem mkTRemsLeafParentsAux_to_isLeafParent
    (pp cc q : AzPolynomial (AzMvPolynomial k D ord))
    (hmem : q ∈ AzPolynomial.mkTRemsLeafParentsAux pp cc) :
    BPR.IsLeafParentOfMkTRemsNode (liftPoly pp) (liftPoly cc) (liftPoly q) := by
  suffices ∀ n, ∀ pp cc q : AzPolynomial (AzMvPolynomial k D ord),
      cc.natDegree ≤ n →
      q ∈ AzPolynomial.mkTRemsLeafParentsAux pp cc →
      BPR.IsLeafParentOfMkTRemsNode (liftPoly pp) (liftPoly cc) (liftPoly q) from
    this cc.natDegree pp cc q le_rfl hmem
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro pp cc q hcn hmem
  rw [AzPolynomial.mkTRemsLeafParentsAux] at hmem
  by_cases h0 : cc = 0
  · -- cc = 0: mkTRemsLeafParentsAux returns [], contradiction
    have : (cc == 0) = true := beq_iff_eq.mpr h0
    rw [dif_pos this] at hmem
    simp at hmem
  · -- cc ≠ 0
    have hbeq : ¬(cc == 0) = true := by simp [beq_iff_eq, h0]
    rw [dif_neg hbeq] at hmem; dsimp only at hmem
    -- hmem : q ∈ cc :: (tru ...).attach.flatMap (...)
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · -- q = cc: use .self
      exact .self ((liftPoly_eq_zero_iff _).not.mpr h0)
    · -- q ∈ flatMap: use .child
      simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists] at hmem
      obtain ⟨c, hcmem, hq⟩ := hmem
      have hlift_ne : liftPoly cc ≠ 0 := (liftPoly_eq_zero_iff _).not.mpr h0
      have hc_in_Tru : liftPoly c ∈
          BPR.Tru (-(BPR.pRemMv (liftPoly pp) (liftPoly cc))) := by
        rw [← liftPoly_pRem_eq_pRemMv _ _ h0, ← liftPoly_neg]
        exact (mem_tru_iff_mem_Tru _ c).mp hcmem
      have hlt : c.natDegree < cc.natDegree :=
        AzPolynomial.natDegree_child_lt_of_mem_tru_neg_pRem h0 hcmem
      exact .child hlift_ne hc_in_Tru (ih _ (by omega) cc c q le_rfl hq)

/-- Backward: `IsLeafParentOfMkTRemsNode` implies membership in
`mkTRemsLeafParentsAux`. Uses `generalize` to abstract `liftPoly`
applications before inducting on the predicate. -/
private theorem isLeafParent_to_mkTRemsLeafParentsAux
    (pp cc q : AzPolynomial (AzMvPolynomial k D ord))
    (hleaf : BPR.IsLeafParentOfMkTRemsNode (liftPoly pp) (liftPoly cc) (liftPoly q)) :
    q ∈ AzPolynomial.mkTRemsLeafParentsAux pp cc := by
  generalize hP : liftPoly pp = P at hleaf
  generalize hQ : liftPoly cc = Q at hleaf
  generalize hR : liftPoly q = R at hleaf
  induction hleaf generalizing pp cc q with
  | self h =>
    have hcc_ne : cc ≠ 0 := fun h0 => h (by rw [← hQ, h0, liftPoly_zero])
    have hqcc : q = cc := liftPoly_injective (by rw [hR, ← hQ])
    rw [hqcc]
    rw [AzPolynomial.mkTRemsLeafParentsAux]
    rw [dif_neg (by simp [beq_iff_eq, hcc_ne])]
    exact List.mem_cons_self ..
  | child h hc hq_inner ih =>
    have hcc_ne : cc ≠ 0 := fun h0 => h (by rw [← hQ, h0, liftPoly_zero])
    rw [← hP, ← hQ] at hc
    rw [← liftPoly_pRem_eq_pRemMv _ _ hcc_ne, ← liftPoly_neg] at hc
    obtain ⟨c_az, hc_tru, hc_eq⟩ := exists_tru_preimage _ _ hc
    have hq_mem := ih cc c_az q hQ hc_eq hR
    rw [AzPolynomial.mkTRemsLeafParentsAux]
    rw [dif_neg (by simp [beq_iff_eq, hcc_ne])]
    exact List.mem_cons_of_mem _ (by
      simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
      exact ⟨c_az, hc_tru, hq_mem⟩)

/-! ### Main equivalence: leaf parents -/

/-- A polynomial belongs to the computable `tremsLeafParents P Q` iff
it is either `P` itself (from the root-level 0-sentinel) or `liftPoly q`
is a leaf parent of the noncomputable subtree
`BPR.mkTRemsNode (liftPoly P) c` for some `c ∈ BPR.Tru (liftPoly Q)`.

This says the leaf parents of the computable `tremsLeafParents`
correspond exactly to those of the noncomputable `BPR.TRems` tree
under the `liftPoly` bridge. -/
theorem mem_tremsLeafParents_iff_isLeafParent
    (P Q q : AzPolynomial (AzMvPolynomial k D ord)) :
    q ∈ AzPolynomial.tremsLeafParents P Q ↔
      q = P ∨
      ∃ c ∈ BPR.Tru (liftPoly Q),
        BPR.IsLeafParentOfMkTRemsNode (liftPoly P) c (liftPoly q) := by
  -- tremsLeafParents P Q = P :: (tru Q).flatMap (mkTRemsLeafParentsAux P)
  simp only [AzPolynomial.tremsLeafParents, List.mem_cons, List.mem_flatMap]
  constructor
  · -- Forward
    rintro (rfl | ⟨c, hc_tru, hq_mem⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨liftPoly c,
        (mem_tru_iff_mem_Tru Q c).mp hc_tru,
        mkTRemsLeafParentsAux_to_isLeafParent P c q hq_mem⟩
  · -- Backward
    rintro (rfl | ⟨c', hc'_Tru, hleaf⟩)
    · exact Or.inl rfl
    · obtain ⟨c, hc_tru, hc_eq⟩ := exists_tru_preimage Q c' hc'_Tru
      rw [← hc_eq] at hleaf
      exact Or.inr ⟨c, hc_tru, isLeafParent_to_mkTRemsLeafParentsAux P c q hleaf⟩

end Azurite

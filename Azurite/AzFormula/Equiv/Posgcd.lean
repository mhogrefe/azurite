/-
  Equivalence between computable `azPosgcd` and BPR's noncomputable
  `posgcd` under the `liftPoly` bridge.

  The main result `azPosgcd_forward` shows that every element of the
  computable `azPosgcd` corresponds to an element of BPR's `posgcd`
  with the same lifted polynomial and the same realization.
-/
import Azurite.AzFormula.Posgcd
import Azurite.AzFormula.Equiv.LeafFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_3

namespace Azurite

open AzMvPolynomial BPR Polynomial

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-! ### Bridge lemmas for `pathLeafParent` -/

/-- The computable `azPathLeafParentAux` matches BPR's `pathLeafParentAux`
under the `liftPoly` bridge. -/
theorem liftPoly_azPathLeafParentAux
    (cur : AzPolynomial (AzMvPolynomial k D ord))
    (rest : List (AzPolynomial (AzMvPolynomial k D ord))) :
    liftPoly (azPathLeafParentAux cur rest) =
      BPR.pathLeafParentAux (liftPoly cur) (rest.map liftPoly) := by
  induction rest generalizing cur with
  | nil =>
    simp only [azPathLeafParentAux, BPR.pathLeafParentAux, List.map]
  | cons next rest' ih =>
    simp only [azPathLeafParentAux, List.map]
    by_cases h0 : next = 0
    · subst h0
      simp only [beq_self_eq_true, ↓reduceIte, liftPoly_zero, BPR.pathLeafParentAux]
    · have hbeq : ¬(next == 0) = true := by rwa [beq_iff_eq]
      rw [if_neg hbeq]
      have hlift_ne : liftPoly next ≠ 0 := (liftPoly_eq_zero_iff _).not.mpr h0
      simp only [BPR.pathLeafParentAux, if_neg hlift_ne]
      exact ih next

/-- The computable `azPathLeafParent` matches BPR's `pathLeafParent`
under the `liftPoly` bridge. -/
theorem liftPoly_azPathLeafParent
    (P : AzPolynomial (AzMvPolynomial k D ord))
    (path : List (AzPolynomial (AzMvPolynomial k D ord))) :
    liftPoly (azPathLeafParent P path) =
      BPR.pathLeafParent (liftPoly P) (path.map liftPoly) := by
  match path with
  | [] =>
    simp only [azPathLeafParent, BPR.pathLeafParent, List.map]
  | q :: rest =>
    simp only [azPathLeafParent, List.map]
    by_cases h0 : q = 0
    · subst h0
      simp only [beq_self_eq_true, ↓reduceIte, liftPoly_zero, BPR.pathLeafParent]
    · have hbeq : ¬(q == 0) = true := by rwa [beq_iff_eq]
      rw [if_neg hbeq]
      have hlift_ne : liftPoly q ≠ 0 := (liftPoly_eq_zero_iff _).not.mpr h0
      simp only [BPR.pathLeafParent, if_neg hlift_ne]
      exact liftPoly_azPathLeafParentAux q rest

/-! ### Tree-path bridge -/

/-- Elements of `tru p` are always nonzero. -/
private theorem ne_zero_of_mem_tru
    (p c : AzPolynomial (AzMvPolynomial k D ord))
    (hc : c ∈ AzPolynomial.tru p) : c ≠ 0 := by
  intro heq; rw [heq] at hc
  by_cases hp : p = 0
  · rw [hp, AzPolynomial.tru] at hc; simp at hc
  · have h1 := (mem_tru_iff_mem_Tru p 0).mp hc
    rw [liftPoly_zero] at h1
    exact BPR.zero_not_mem_Tru _ ((liftPoly_eq_zero_iff _).not.mpr hp) h1

/-- Extraction lemma: if `path ∈ (.node root cs).leafPaths` and `cs ≠ []`,
then `path` came from some child. -/
private theorem exists_child_of_mem_comp_leafPaths
    {α : Type*} (root : α) (cs : List (AzPolynomial.RoseTree α))
    (hcs : cs ≠ []) (path : List α)
    (hmem : path ∈ (AzPolynomial.RoseTree.node root cs).leafPaths) :
    ∃ child ∈ cs, ∃ sp ∈ child.leafPaths, path = child.root :: sp := by
  cases cs with
  | nil => exact absurd rfl hcs
  | cons _ _ =>
    simp only [AzPolynomial.RoseTree.leafPaths, List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨child, hchild, sp, hsp, rfl⟩ := hmem
    exact ⟨child, hchild, sp, hsp, rfl⟩

/-- The root of computable `mkTRemsNode` is `curPol`. -/
private theorem root_comp_mkTRemsNode
    (parentPol curPol : AzPolynomial (AzMvPolynomial k D ord)) :
    (AzPolynomial.mkTRemsNode parentPol curPol).root = curPol := by
  rw [AzPolynomial.mkTRemsNode]; split_ifs <;> rfl

/-- Each leaf path of the computable `tremsTree`, when mapped through
`liftPoly`, is a leaf path of BPR's `TRems`.

Both trees now have the same 0-sentinel structure, so no `++ [0]`
append is needed — the paths correspond directly. -/
theorem leafPaths_tremsTree_bridge
    (P Q : AzPolynomial (AzMvPolynomial k D ord))
    (path : List (AzPolynomial (AzMvPolynomial k D ord)))
    (hmem : path ∈ (AzPolynomial.tremsTree P Q).leafPaths) :
    path.map liftPoly ∈
      (BPR.TRems (liftPoly P) (liftPoly Q)).leafPaths := by
  unfold AzPolynomial.tremsTree at hmem
  -- Children are always non-empty due to the 0-sentinel
  have hne : (AzPolynomial.tru Q).map (AzPolynomial.mkTRemsNode P) ++
      [AzPolynomial.RoseTree.node 0 []] ≠ [] := by
    intro h; simp at h
  obtain ⟨st, hst_mem, sp, hsp_mem, rfl⟩ :=
    exists_child_of_mem_comp_leafPaths P _ hne path hmem
  -- st is either from a tru child or the 0-sentinel
  rw [List.mem_append] at hst_mem
  rcases hst_mem with hst_tru | hst_zero
  · -- st = mkTRemsNode P q for some q ∈ tru Q
    rw [List.mem_map] at hst_tru
    obtain ⟨q, hq_tru, rfl⟩ := hst_tru
    have hq_ne : q ≠ 0 := ne_zero_of_mem_tru Q q hq_tru
    rw [root_comp_mkTRemsNode]
    simp only [List.map_cons]
    -- liftPoly q ∈ Tru(liftPoly Q)
    have hq_Tru : liftPoly q ∈ BPR.Tru (liftPoly Q) :=
      (mem_tru_iff_mem_Tru Q q).mp hq_tru
    have hq_list : liftPoly q ∈ (BPR.Tru_finite (liftPoly Q)).toFinset.toList :=
      Finset.mem_toList.mpr ((Set.Finite.mem_toFinset _).mpr hq_Tru)
    have hst_bpr : BPR.mkTRemsNode (liftPoly P) (liftPoly q) ∈
        (BPR.Tru_finite (liftPoly Q)).toFinset.toList.map (BPR.mkTRemsNode (liftPoly P)) ++
          [.node 0 []] :=
      List.mem_append_left _ (List.mem_map.mpr ⟨liftPoly q, hq_list, rfl⟩)
    have hsp_bridge : sp.map liftPoly ∈
        (BPR.mkTRemsNode (liftPoly P) (liftPoly q)).leafPaths :=
      leafPaths_mkTRemsNode_bridge P q hq_ne sp hsp_mem
    have hroot : (BPR.mkTRemsNode (liftPoly P) (liftPoly q)).root = liftPoly q :=
      BPR.mkTRemsNode_root _ _
    have hmem_bpr := BPR.mem_leafPaths_of_child (liftPoly P)
      ((BPR.Tru_finite (liftPoly Q)).toFinset.toList.map (BPR.mkTRemsNode (liftPoly P)) ++
        [BPR.RoseTree.node 0 []])
      (BPR.mkTRemsNode (liftPoly P) (liftPoly q))
      hst_bpr (sp.map liftPoly) hsp_bridge
    rw [hroot] at hmem_bpr
    exact hmem_bpr
  · -- st = .node 0 [] (the 0-sentinel)
    rw [List.mem_singleton] at hst_zero
    rw [hst_zero] at hsp_mem ⊢
    simp only [AzPolynomial.RoseTree.leafPaths, List.mem_singleton] at hsp_mem
    rw [hsp_mem]
    simp only [AzPolynomial.RoseTree.root, List.map_cons, List.map_nil, liftPoly_zero]
    exact BPR.mem_leafPaths_zero _ _
where
  /-- Bridge for `mkTRemsNode` subtrees: each leaf path of the
  computable `mkTRemsNode`, mapped through `liftPoly`, is a leaf path
  of BPR's `mkTRemsNode`. -/
  leafPaths_mkTRemsNode_bridge
      (parentPol curPol : AzPolynomial (AzMvPolynomial k D ord))
      (hcur : curPol ≠ 0)
      (path : List (AzPolynomial (AzMvPolynomial k D ord)))
      (hmem : path ∈ (AzPolynomial.mkTRemsNode parentPol curPol).leafPaths) :
      path.map liftPoly ∈
        (BPR.mkTRemsNode (liftPoly parentPol) (liftPoly curPol)).leafPaths := by
    suffices ∀ n, ∀ pp cc : AzPolynomial (AzMvPolynomial k D ord),
        cc ≠ 0 → cc.natDegree ≤ n →
        ∀ path, path ∈ (AzPolynomial.mkTRemsNode pp cc).leafPaths →
        path.map liftPoly ∈
          (BPR.mkTRemsNode (liftPoly pp) (liftPoly cc)).leafPaths from
      this curPol.natDegree parentPol curPol hcur le_rfl path hmem
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro pp cc hcc hcn path hmem
    have hcc_beq : ¬(cc == 0) = true := by rwa [beq_iff_eq]
    rw [AzPolynomial.mkTRemsNode, dif_neg hcc_beq] at hmem
    dsimp only at hmem
    have hlcc : liftPoly cc ≠ 0 := (liftPoly_eq_zero_iff _).not.mpr hcc
    -- Children: (tru next).attach.map f ++ [.node 0 []]
    have hne : (AzPolynomial.tru (-(AzPolynomial.pRem pp cc))).attach.map
        (fun ⟨c, _⟩ => AzPolynomial.mkTRemsNode cc c) ++
        [AzPolynomial.RoseTree.node 0 []] ≠ [] := by
      intro h; simp at h
    obtain ⟨st, hst_mem, sp, hsp_mem, rfl⟩ :=
      exists_child_of_mem_comp_leafPaths cc _ hne path hmem
    rw [List.mem_append] at hst_mem
    rcases hst_mem with hst_tru | hst_zero
    · -- From a tru child
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hst_tru
      obtain ⟨c, hc_mem, rfl⟩ := hst_tru
      rw [root_comp_mkTRemsNode]
      simp only [List.map_cons]
      have hc_ne : c ≠ 0 := ne_zero_of_mem_tru _ c hc_mem
      have hc_lt : c.natDegree < cc.natDegree :=
        AzPolynomial.natDegree_child_lt_of_mem_tru_neg_pRem hcc hc_mem
      have hsp_bridge := ih _ (by omega) cc c hc_ne le_rfl sp hsp_mem
      have hc_Tru : liftPoly c ∈
          BPR.Tru (-(BPR.pRemMv (liftPoly pp) (liftPoly cc))) := by
        have := (mem_tru_iff_mem_Tru (-(AzPolynomial.pRem pp cc)) c).mp hc_mem
        rwa [liftPoly_neg, liftPoly_pRem_eq_pRemMv _ _ hcc] at this
      have hc_list : liftPoly c ∈
          (BPR.Tru_finite (-(BPR.pRemMv (liftPoly pp) (liftPoly cc)))).toFinset.toList :=
        Finset.mem_toList.mpr ((Set.Finite.mem_toFinset _).mpr hc_Tru)
      have hst_bpr : BPR.mkTRemsNode (liftPoly cc) (liftPoly c) ∈
          (BPR.Tru_finite (-(BPR.pRemMv (liftPoly pp) (liftPoly cc)))).toFinset.toList.attach.map
            (fun ⟨child, _⟩ => BPR.mkTRemsNode (liftPoly cc) child) ++
            [.node 0 []] :=
        List.mem_append_left _ (List.mem_map.mpr ⟨⟨liftPoly c, hc_list⟩, List.mem_attach _ _, rfl⟩)
      have hmem_bpr := BPR.mem_leafPaths_of_child (liftPoly cc)
        ((BPR.Tru_finite (-(BPR.pRemMv (liftPoly pp) (liftPoly cc)))).toFinset.toList.attach.map
          (fun ⟨child, _⟩ => BPR.mkTRemsNode (liftPoly cc) child) ++
          [BPR.RoseTree.node 0 []])
        (BPR.mkTRemsNode (liftPoly cc) (liftPoly c))
        hst_bpr (sp.map liftPoly) hsp_bridge
      rw [BPR.mkTRemsNode_root] at hmem_bpr
      rw [BPR.mkTRemsNode, if_neg hlcc]
      dsimp only
      exact hmem_bpr
    · -- From 0-sentinel
      rw [List.mem_singleton] at hst_zero
      rw [hst_zero] at hsp_mem ⊢
      simp only [AzPolynomial.RoseTree.leafPaths, List.mem_singleton] at hsp_mem
      rw [hsp_mem]
      simp only [AzPolynomial.RoseTree.root, List.map_cons, List.map_nil, liftPoly_zero]
      rw [BPR.mkTRemsNode, if_neg hlcc]
      dsimp only
      exact BPR.mem_leafPaths_zero _ _

/-! ### Reverse tree-path bridge -/

/-- Helper: constructing a path in a computable tree from a child and
sub-path.  Mirror of `exists_child_of_mem_comp_leafPaths`. -/
private theorem mem_comp_leafPaths_of_child
    {α : Type*} (root : α) (cs : List (AzPolynomial.RoseTree α))
    (hcs : cs ≠ [])
    (child : AzPolynomial.RoseTree α) (hchild : child ∈ cs)
    (sp : List α) (hsp : sp ∈ child.leafPaths) :
    (child.root :: sp) ∈ (AzPolynomial.RoseTree.node root cs).leafPaths := by
  cases cs with
  | nil => exact absurd rfl hcs
  | cons _ _ =>
    simp only [AzPolynomial.RoseTree.leafPaths, List.mem_flatMap, List.mem_map]
    exact ⟨child, hchild, sp, hsp, rfl⟩

/-- The 0-sentinel path `[0]` is always in the computable tree's
`leafPaths` when its children end with `.node 0 []`. -/
private theorem mem_comp_leafPaths_zero
    (root : AzPolynomial (AzMvPolynomial k D ord))
    (cs : List (AzPolynomial.RoseTree
      (AzPolynomial (AzMvPolynomial k D ord)))) :
    [0] ∈ (AzPolynomial.RoseTree.node root
      (cs ++ [.node 0 []])).leafPaths := by
  apply mem_comp_leafPaths_of_child root _ (by simp)
    (.node 0 []) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    [] (by simp [AzPolynomial.RoseTree.leafPaths])

/-- Reverse bridge for `mkTRemsNode` subtrees: each leaf path of
BPR's `mkTRemsNode`, when the arguments are in the image of `liftPoly`,
has a preimage in the computable `mkTRemsNode`. -/
private theorem leafPaths_mkTRemsNode_bridge_rev
    (parentPol curPol : AzPolynomial (AzMvPolynomial k D ord))
    (hcur : curPol ≠ 0)
    (path' : List (Polynomial (MvPolynomial (Fin k) D)))
    (hmem : path' ∈ (BPR.mkTRemsNode (liftPoly parentPol)
      (liftPoly curPol)).leafPaths) :
    ∃ path : List (AzPolynomial (AzMvPolynomial k D ord)),
      path ∈ (AzPolynomial.mkTRemsNode parentPol curPol).leafPaths ∧
      path.map liftPoly = path' := by
  suffices ∀ n, ∀ pp cc : AzPolynomial (AzMvPolynomial k D ord),
      cc ≠ 0 → cc.natDegree ≤ n →
      ∀ path', path' ∈ (BPR.mkTRemsNode (liftPoly pp)
        (liftPoly cc)).leafPaths →
      ∃ path, path ∈ (AzPolynomial.mkTRemsNode pp cc).leafPaths ∧
        path.map liftPoly = path' from
    this curPol.natDegree parentPol curPol hcur le_rfl path' hmem
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro pp cc hcc hcn path' hmem
  have hlcc : liftPoly cc ≠ 0 := (liftPoly_eq_zero_iff _).not.mpr hcc
  -- Unfold BPR mkTRemsNode
  rw [BPR.mkTRemsNode, if_neg hlcc] at hmem
  dsimp only at hmem
  -- BPR children are non-empty
  have bpr_hne :
      (BPR.Tru_finite (-(BPR.pRemMv (liftPoly pp) (liftPoly cc)))).toFinset.toList.attach.map
        (fun ⟨child, _⟩ => BPR.mkTRemsNode (liftPoly cc) child) ++
        [BPR.RoseTree.node 0 []] ≠ [] := by simp
  rw [BPR.leafPaths_node_ne_nil _ _ bpr_hne] at hmem
  simp only [List.mem_flatMap, List.mem_map] at hmem
  obtain ⟨bpr_child, hbc_mem, sp', hsp', rfl⟩ := hmem
  rw [List.mem_append] at hbc_mem
  rcases hbc_mem with hbc_tru | hbc_zero
  · -- From a Tru child
    simp only [List.mem_map, List.mem_attach, true_and,
      Subtype.exists] at hbc_tru
    obtain ⟨c, hc_mem, rfl⟩ := hbc_tru
    have hc_Tru : c ∈ BPR.Tru
        (-(BPR.pRemMv (liftPoly pp) (liftPoly cc))) :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_mem)
    -- Rewrite to liftPoly form
    rw [← liftPoly_pRem_eq_pRemMv _ _ hcc, ← liftPoly_neg] at hc_Tru
    obtain ⟨c_az, hc_tru, hc_eq⟩ :=
      exists_tru_preimage (-(AzPolynomial.pRem pp cc)) c hc_Tru
    have hc_ne : c_az ≠ 0 :=
      ne_zero_of_mem_tru _ c_az hc_tru
    have hc_lt : c_az.natDegree < cc.natDegree :=
      AzPolynomial.natDegree_child_lt_of_mem_tru_neg_pRem hcc hc_tru
    rw [← hc_eq] at hsp'
    obtain ⟨sp, hsp_mem, hsp_eq⟩ :=
      ih _ (by omega) cc c_az hc_ne le_rfl sp' hsp'
    refine ⟨c_az :: sp, ?_, ?_⟩
    · -- Membership in computable mkTRemsNode
      have hcc_beq : ¬(cc == 0) = true := by rwa [beq_iff_eq]
      rw [AzPolynomial.mkTRemsNode, dif_neg hcc_beq]
      dsimp only
      have hmem_child : AzPolynomial.mkTRemsNode cc c_az ∈
          (AzPolynomial.tru (-(AzPolynomial.pRem pp cc))).attach.map
            (fun ⟨child, _⟩ => AzPolynomial.mkTRemsNode cc child) ++
            [AzPolynomial.RoseTree.node 0 []] :=
        List.mem_append_left _ (List.mem_map.mpr
          ⟨⟨c_az, hc_tru⟩, List.mem_attach _ _, rfl⟩)
      have := mem_comp_leafPaths_of_child cc _ (by simp)
        (AzPolynomial.mkTRemsNode cc c_az) hmem_child sp hsp_mem
      rwa [root_comp_mkTRemsNode] at this
    · simp only [List.map_cons, hc_eq, hsp_eq,
        BPR.mkTRemsNode_root]
  · -- 0-sentinel
    rw [List.mem_singleton] at hbc_zero
    rw [hbc_zero] at hsp' ⊢
    simp only [BPR.RoseTree.leafPaths, List.mem_singleton] at hsp'
    rw [hsp']
    simp only [BPR.RoseTree.root]
    refine ⟨[0], ?_, by simp⟩
    have hcc_beq : ¬(cc == 0) = true := by rwa [beq_iff_eq]
    rw [AzPolynomial.mkTRemsNode, dif_neg hcc_beq]
    dsimp only
    exact mem_comp_leafPaths_zero cc _

/-- Reverse of `leafPaths_tremsTree_bridge`: each leaf path of BPR's
`TRems` has a preimage in the computable `tremsTree`. -/
theorem leafPaths_tremsTree_bridge_rev
    (P Q : AzPolynomial (AzMvPolynomial k D ord))
    (path' : List (Polynomial (MvPolynomial (Fin k) D)))
    (hmem : path' ∈
      (BPR.TRems (liftPoly P) (liftPoly Q)).leafPaths) :
    ∃ path : List (AzPolynomial (AzMvPolynomial k D ord)),
      path ∈ (AzPolynomial.tremsTree P Q).leafPaths ∧
      path.map liftPoly = path' := by
  unfold BPR.TRems at hmem
  have bpr_hne : (BPR.Tru_finite (liftPoly Q)).toFinset.toList.map
      (BPR.mkTRemsNode (liftPoly P)) ++
      [BPR.RoseTree.node 0 []] ≠ [] := by simp
  rw [BPR.leafPaths_node_ne_nil _ _ bpr_hne] at hmem
  simp only [List.mem_flatMap, List.mem_map] at hmem
  obtain ⟨bpr_child, hbc_mem, sp', hsp', rfl⟩ := hmem
  rw [List.mem_append] at hbc_mem
  rcases hbc_mem with hbc_tru | hbc_zero
  · -- From a Tru child
    rw [List.mem_map] at hbc_tru
    obtain ⟨c, hc_list, rfl⟩ := hbc_tru
    have hc_Tru : c ∈ BPR.Tru (liftPoly Q) :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_list)
    obtain ⟨q, hq_tru, hq_eq⟩ := exists_tru_preimage Q c hc_Tru
    have hq_ne : q ≠ 0 := ne_zero_of_mem_tru Q q hq_tru
    rw [← hq_eq] at hsp'
    obtain ⟨sp, hsp_mem, hsp_eq⟩ :=
      leafPaths_mkTRemsNode_bridge_rev P q hq_ne sp' hsp'
    refine ⟨q :: sp, ?_, ?_⟩
    · -- Membership in computable tree
      unfold AzPolynomial.tremsTree
      have hmem_child : AzPolynomial.mkTRemsNode P q ∈
          (AzPolynomial.tru Q).map (AzPolynomial.mkTRemsNode P) ++
            [AzPolynomial.RoseTree.node 0 []] :=
        List.mem_append_left _ (List.mem_map.mpr ⟨q, hq_tru, rfl⟩)
      have := mem_comp_leafPaths_of_child P _ (by simp)
        (AzPolynomial.mkTRemsNode P q) hmem_child sp hsp_mem
      rwa [root_comp_mkTRemsNode] at this
    · -- path.map liftPoly = bpr_child.root :: sp'
      simp only [List.map_cons, hq_eq, hsp_eq, BPR.mkTRemsNode_root]
  · -- 0-sentinel
    rw [List.mem_singleton] at hbc_zero
    rw [hbc_zero] at hsp' ⊢
    simp only [BPR.RoseTree.leafPaths, List.mem_singleton] at hsp'
    rw [hsp']
    simp only [BPR.RoseTree.root]
    exact ⟨[0], mem_comp_leafPaths_zero P
      ((AzPolynomial.tru Q).map (AzPolynomial.mkTRemsNode P)),
      by simp⟩

/-! ### Main theorems -/

variable {C : Type*} [Field C] [Algebra D C]

/-- Each element `(G, 𝒞)` of the computable `azPosgcd` corresponds to
an element `(G', 𝒞')` of BPR's `posgcd` with the same lifted
polynomial and the same realization. -/
theorem azPosgcd_forward
    (Ps : List (AzPolynomial (AzMvPolynomial k D ord)))
    (G : AzPolynomial (AzMvPolynomial k D ord))
    (𝒞 : Formula (Fin k) (AzFieldAtom k D ord))
    (hmem : (G, 𝒞) ∈ azPosgcd Ps) :
    ∃ (G' : Polynomial (MvPolynomial (Fin k) D))
      (𝒞' : Formula (Fin k) (FieldAtom (Fin k) D)),
      (G', 𝒞') ∈ BPR.posgcd (Ps.map liftPoly) ∧
      liftPoly G = G' ∧
      azRealization 𝒞 (C := C) = 𝒞'.realization := by
  induction Ps generalizing G 𝒞 with
  | nil =>
    simp only [azPosgcd, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    refine ⟨0, Formula.trueFormula, ?_, liftPoly_zero, ?_⟩
    · simp [BPR.posgcd]
    · simp
  | cons P rest ih =>
    simp only [azPosgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
    -- Decompose without rfl to preserve ih
    obtain ⟨⟨Q, C_q⟩, hQC_mem, path, hpath_mem, hG_eq, h𝒞_eq⟩ := hmem
    -- Apply IH before substituting G and 𝒞
    obtain ⟨Q', C', hQC'_mem, hQ_eq, hC_eq⟩ := ih Q C_q hQC_mem
    -- Now substitute
    subst hG_eq; subst h𝒞_eq
    set path' := path.map liftPoly
    have hpath'_mem : path' ∈ (BPR.TRems (liftPoly P) Q').leafPaths := by
      rw [← hQ_eq]; exact leafPaths_tremsTree_bridge P Q path hpath_mem
    refine ⟨BPR.pathLeafParent (liftPoly P) path',
            C'.and (BPR.leafFormula (liftPoly P) Q' path'), ?_, ?_, ?_⟩
    · -- Membership in BPR.posgcd
      simp only [List.map_cons, BPR.posgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨⟨Q', C'⟩, hQC'_mem, path', hpath'_mem, rfl, rfl⟩
    · -- liftPoly (azPathLeafParent P path) = pathLeafParent (liftPoly P) path'
      exact liftPoly_azPathLeafParent P path
    · -- azRealization (azSmartAnd C_q ...) = (C'.and ...).realization
      rw [azRealization_azSmartAnd, azRealization_azLeafFormula, hC_eq, ← hQ_eq,
          BPR.Formula.realization_and]

/-! ### Backward inclusion: `BPR.posgcd` into `azPosgcd` -/

/-- Each element `(G', 𝒞')` of BPR's `posgcd` corresponds to an element
`(G, 𝒞)` of the computable `azPosgcd` with the same lifted polynomial
and the same realization. Together with `azPosgcd_forward`, this shows
the two formulations are equivalent (up to realization). -/
theorem azPosgcd_backward
    (Ps : List (AzPolynomial (AzMvPolynomial k D ord)))
    (G' : Polynomial (MvPolynomial (Fin k) D))
    (𝒞' : Formula (Fin k) (FieldAtom (Fin k) D))
    (hmem : (G', 𝒞') ∈ BPR.posgcd (Ps.map liftPoly)) :
    ∃ (G : AzPolynomial (AzMvPolynomial k D ord))
      (𝒞 : Formula (Fin k) (AzFieldAtom k D ord)),
      (G, 𝒞) ∈ azPosgcd Ps ∧
      liftPoly G = G' ∧
      azRealization 𝒞 (C := C) = 𝒞'.realization := by
  induction Ps generalizing G' 𝒞' with
  | nil =>
    simp only [List.map_nil, BPR.posgcd, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨0, azTrueFormula,
      List.mem_singleton.mpr rfl, liftPoly_zero, by simp⟩
  | cons P rest ih =>
    simp only [List.map_cons, BPR.posgcd, List.mem_flatMap,
      List.mem_map, Prod.mk.injEq] at hmem
    obtain ⟨⟨Q', C'_sub⟩, hQC'_mem, path', hpath'_mem,
      hG'_eq, h𝒞'_eq⟩ := hmem
    -- Apply IH to get computable preimage of (Q', C'_sub)
    obtain ⟨Q, C_sub, hQC_mem, hQ_eq, hC_eq⟩ :=
      ih Q' C'_sub hQC'_mem
    -- Substitute G' and 𝒞' to expose the BPR constructions
    subst hG'_eq; subst h𝒞'_eq
    -- Get reverse leaf path bridge
    rw [← hQ_eq] at hpath'_mem
    obtain ⟨path, hpath_mem, hpath_eq⟩ :=
      leafPaths_tremsTree_bridge_rev P Q path' hpath'_mem
    refine ⟨azPathLeafParent P path,
            azSmartAnd C_sub (azLeafFormula P Q path), ?_, ?_, ?_⟩
    · -- Membership in azPosgcd
      simp only [azPosgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨⟨Q, C_sub⟩, hQC_mem, path, hpath_mem, rfl, rfl⟩
    · -- liftPoly G = G'
      rw [liftPoly_azPathLeafParent, hpath_eq]
    · -- azRealization 𝒞 = 𝒞'.realization
      rw [azRealization_azSmartAnd, azRealization_azLeafFormula,
          hC_eq, ← hQ_eq, hpath_eq, BPR.Formula.realization_and]

/-- Combined equivalence: a polynomial-realization pair `(G', S)` arises
from the computable `azPosgcd` iff it arises from BPR's `posgcd`. This
packages `azPosgcd_forward` and `azPosgcd_backward` into a single iff. -/
theorem mem_azPosgcd_image_iff
    (Ps : List (AzPolynomial (AzMvPolynomial k D ord)))
    (G' : Polynomial (MvPolynomial (Fin k) D))
    (S : Set (Fin k → C)) :
    (∃ (G : AzPolynomial (AzMvPolynomial k D ord))
       (𝒞 : Formula (Fin k) (AzFieldAtom k D ord)),
       (G, 𝒞) ∈ azPosgcd Ps ∧ liftPoly G = G' ∧
         azRealization 𝒞 (C := C) = S) ↔
    (∃ (𝒞' : Formula (Fin k) (FieldAtom (Fin k) D)),
       (G', 𝒞') ∈ BPR.posgcd (Ps.map liftPoly) ∧ 𝒞'.realization = S) := by
  constructor
  · rintro ⟨G, 𝒞, hmem, hG, hS⟩
    obtain ⟨G'', 𝒞', hmem', hG'', hR⟩ :=
      azPosgcd_forward (C := C) Ps G 𝒞 hmem
    refine ⟨𝒞', ?_, hR.symm.trans hS⟩
    rw [← hG, hG'']; exact hmem'
  · rintro ⟨𝒞', hmem', hS⟩
    obtain ⟨G, 𝒞, hmem, hG, hR⟩ :=
      azPosgcd_backward (C := C) Ps G' 𝒞' hmem'
    exact ⟨G, 𝒞, hmem, hG, hR.trans hS⟩

end Azurite

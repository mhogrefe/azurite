import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Azurite.BasuPollackRoy.Chapter1.Section1_3.DegFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_3.LeafFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SignedPseudoRemainder
import Azurite.BasuPollackRoy.Chapter1.Section1_3.TRems
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Tru
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Truncate

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ}

/-!
### Lemma 1.19: Partition and GCD properties of leaf formulas

BPR Lemma 1.19 states three things about the leaf formulas `C_L`:
1. The realizations `Reali(C_L)` partition `C^k`.
2. For `y ∈ Reali(C_L)`, the signed remainder sequence `SRemS(P_y, Q_y)`
   is proportional (up to squares) to the specialized node polynomials
   along the path `B_L`.
3. In particular, the leaf parent `Pol(p(L))_y` is `gcd(P_y, Q_y)`.

BPR states: "It is clear from the definitions, since the remainder and
pseudo-remainder of two polynomials in `C[X]` are equal up to a square."
-/

section Lemma_1_19

variable {D : Type*} [CommRing D] [IsDomain D]

open Classical

/-! #### Helper: Tru specialization -/

omit [IsDomain D] in
/-- For every `y ∈ C^k`, there exists `q ∈ Tru(Q)` such that `Q_y = q_y`
(i.e. they map to the same polynomial under specialization at `y`). -/
private theorem Tru_spec_exists
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0)
    (y : Fin k → C) :
    ∃ q ∈ Tru Q,
      Q.map (MvPolynomial.aeval y).toRingHom =
        q.map (MvPolynomial.aeval y).toRingHom := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  rw [Tru]; split_ifs with h0 hbase
  · exact absurd h0 hQ
  · exact ⟨Q, Set.mem_singleton_iff.mpr rfl, rfl⟩
  · -- Recursive case: Tru(Q) = {Q} ∪ Tru(truncate ...)
    push Not at hbase
    obtain ⟨hlc_nc, hnd_pos⟩ := hbase
    have hnd_pos' : 0 < Q.natDegree := Nat.pos_of_ne_zero hnd_pos
    by_cases hlc : φ Q.leadingCoeff = 0
    · -- Leading coeff vanishes at y → Q.map φ = (truncate ...).map φ
      set T := truncate (Q.natDegree - 1) Q
      have hmap_eq : Q.map φ = T.map φ := by
        ext j; simp only [Polynomial.coeff_map,
          show T = truncate (Q.natDegree - 1) Q from rfl, coeff_truncate]
        split_ifs with hj
        · rfl
        · push Not at hj
          have hle : Q.natDegree ≤ j := by omega
          rcases hle.eq_or_lt with rfl | hlt
          · simp only [Polynomial.leadingCoeff] at hlc; rw [hlc, map_zero]
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero]
      by_cases hT : T = 0
      · exact ⟨Q, Set.mem_union_left _ (Set.mem_singleton_iff.mpr rfl), rfl⟩
      · obtain ⟨q, hq_mem, hq_eq⟩ := Tru_spec_exists T hT y
        exact ⟨q, Set.mem_union_right _ hq_mem, hmap_eq.trans hq_eq⟩
    · exact ⟨Q, Set.mem_union_left _ (Set.mem_singleton_iff.mpr rfl), rfl⟩
termination_by Q.natDegree
decreasing_by
  show (truncate (Q.natDegree - 1) Q).natDegree < Q.natDegree
  have := natDegree_truncate_le (Q.natDegree - 1) Q; omega

/-! #### Tru degree-equality implies polynomial equality under specialization -/

omit [IsDomain D] in
/-- If `q ∈ Tru(R)` and the specialized degrees match, then the
specialized polynomials are equal: `R_y = q_y`. This is because
`q` is a truncation of `R` that removes only coefficients which
vanish at `y` (as forced by the degree equality). -/
private theorem Tru_degEq_imp_eq
    {C : Type*} [Field C] [Algebra D C]
    (R q : Polynomial (MvPolynomial (Fin k) D))
    (hq : q ∈ Tru R)
    (y : Fin k → C)
    (hdeg : (R.map (MvPolynomial.aeval y).toRingHom).degree =
            (q.map (MvPolynomial.aeval y).toRingHom).degree) :
    R.map (MvPolynomial.aeval y).toRingHom =
      q.map (MvPolynomial.aeval y).toRingHom := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  by_cases hR : R = 0
  · subst hR; rw [Tru, ite_eq_left rfl] at hq; exact hq.elim
  · rw [Tru, ite_eq_right hR] at hq
    by_cases hbase : (∃ d : D, R.leadingCoeff = MvPolynomial.C d) ∨ R.natDegree = 0
    · rw [ite_eq_left hbase, Set.mem_singleton_iff] at hq; subst hq; rfl
    · rw [ite_eq_right hbase, Set.mem_union, Set.mem_singleton_iff] at hq
      push Not at hbase
      obtain ⟨_, hnd_pos⟩ := hbase
      have hnd_pos' : 0 < R.natDegree := Nat.pos_of_ne_zero hnd_pos
      rcases hq with rfl | hq_trunc
      · -- q = R, trivial
        rfl
      · -- q ∈ Tru(truncate(R.natDegree - 1, R))
        set T := truncate (R.natDegree - 1) R
        -- Derive φ(R.leadingCoeff) = 0 from degree condition
        have hlc : φ R.leadingCoeff = 0 := by
          by_contra hlc_ne
          have hR_nd := Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hlc_ne
          have hq_nd : (q.map φ).natDegree ≤ R.natDegree - 1 :=
            le_trans Polynomial.natDegree_map_le
              (le_trans (natDegree_mem_Tru_le hq_trunc)
                (natDegree_truncate_le (R.natDegree - 1) R))
          have hRne : R.map φ ≠ 0 := by
            intro h; apply hlc_ne
            have : (R.map φ).coeff R.natDegree = 0 := by simp [h]
            rwa [Polynomial.coeff_map] at this
          have hR_deg : (R.map φ).degree = ↑R.natDegree := by
            rw [Polynomial.degree_eq_natDegree hRne, hR_nd]
          have hq_deg := hdeg.symm.trans hR_deg
          have := Polynomial.natDegree_eq_of_degree_eq_some hq_deg
          omega
        -- Show R.map φ = T.map φ
        have hR_eq_T : R.map φ = T.map φ := by
          ext j; simp only [Polynomial.coeff_map,
            show T = truncate (R.natDegree - 1) R from rfl, coeff_truncate]
          split_ifs with hj
          · rfl
          · push Not at hj
            have hle : R.natDegree ≤ j := by omega
            rcases hle.eq_or_lt with rfl | hlt
            · simp only [Polynomial.leadingCoeff] at hlc; rw [hlc, map_zero]
            · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero]
        -- IH: T.map φ = q.map φ
        have hdeg' : (T.map φ).degree = (q.map φ).degree := by
          rw [← hR_eq_T]; exact hdeg
        exact hR_eq_T.trans (Tru_degEq_imp_eq T q hq_trunc y hdeg')
termination_by R.natDegree
decreasing_by
  have := natDegree_truncate_le (R.natDegree - 1) R; omega

/-! #### Helpers for leafPaths membership -/

theorem mkTRemsNode_root
    (parent cur : Polynomial (MvPolynomial (Fin k) D)) :
    (mkTRemsNode parent cur).root = cur := by
  rw [mkTRemsNode]; split_ifs <;> rfl

omit [IsDomain D] in
private theorem Tru_nonempty_of_ne_zero
    (Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0) :
    Q ∈ Tru Q := by
  rw [Tru, ite_eq_right hQ]
  split_ifs
  · exact Set.mem_singleton_iff.mpr rfl
  · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr rfl)

omit [IsDomain D] in
theorem Tru_empty_of_eq_zero :
    Tru (0 : Polynomial (MvPolynomial (Fin k) D)) = ∅ := by
  rw [Tru, ite_eq_left rfl]

omit [IsDomain D] in
theorem zero_not_mem_Tru
    (Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0) :
    (0 : Polynomial (MvPolynomial (Fin k) D)) ∉ Tru Q := by
  rw [Tru, ite_eq_right hQ]; split_ifs with hbase
  · exact fun h => hQ (Set.mem_singleton_iff.mp h).symm
  · intro hmem
    rw [Set.mem_union, Set.mem_singleton_iff] at hmem
    rcases hmem with h | hmem
    · exact hQ h.symm
    · by_cases hT : truncate (Q.natDegree - 1) Q = 0
      · rw [hT, Tru_empty_of_eq_zero] at hmem; exact hmem.elim
      · exact absurd hmem (zero_not_mem_Tru _ hT)
termination_by Q.natDegree
decreasing_by
  push Not at hbase; obtain ⟨_, hnd⟩ := hbase
  have := natDegree_truncate_le (Q.natDegree - 1) Q
  omega

omit [IsDomain D] in
/-- Elements of `Tru Q` with the same `natDegree` are equal. This ensures
that at each level of `TRems`, different children correspond to different
degree values, enabling disjointness of leaf formulas. -/
private theorem Tru_natDegree_injective
    (Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0)
    {q₁ q₂ : Polynomial (MvPolynomial (Fin k) D)}
    (h₁ : q₁ ∈ Tru Q) (h₂ : q₂ ∈ Tru Q)
    (hnd : q₁.natDegree = q₂.natDegree) : q₁ = q₂ := by
  rw [Tru, ite_eq_right hQ] at h₁ h₂
  split_ifs at h₁ h₂ with hbase
  · rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂]
  · rw [Set.mem_union, Set.mem_singleton_iff] at h₁ h₂
    push Not at hbase; obtain ⟨_, hnd_pos⟩ := hbase
    have hnd_pos' : 0 < Q.natDegree := Nat.pos_of_ne_zero hnd_pos
    rcases h₁ with h₁_eq | h₁ <;> rcases h₂ with h₂_eq | h₂
    · rw [h₁_eq, h₂_eq]
    · exfalso; rw [h₁_eq] at hnd; have := natDegree_mem_Tru_le h₂
      have := natDegree_truncate_le (Q.natDegree - 1) Q; omega
    · exfalso; rw [h₂_eq] at hnd; have := natDegree_mem_Tru_le h₁
      have := natDegree_truncate_le (Q.natDegree - 1) Q; omega
    · by_cases hT : truncate (Q.natDegree - 1) Q = 0
      · rw [hT, Tru_empty_of_eq_zero] at h₁; exact h₁.elim
      · exact Tru_natDegree_injective _ hT h₁ h₂ hnd
termination_by Q.natDegree
decreasing_by
  have := natDegree_truncate_le (Q.natDegree - 1) Q; omega

/-! #### Helper: degree covering by Tru -/

omit [IsDomain D] in
/-- When `Q_y ≠ 0` and `algebraMap D C` is injective, the degree of `Q_y`
equals `↑(natDegree q)` for some `q ∈ Tru Q`. This is the key lemma
enabling the `degFormula`-based covering property. -/
theorem Tru_covers_degrees
    {C : Type*} [Field C] [Algebra D C]
    (hinj : Function.Injective (algebraMap D C))
    (Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0)
    (y : Fin k → C)
    (hQy : Q.map (MvPolynomial.aeval y).toRingHom ≠ 0) :
    ∃ q ∈ Tru Q,
      (Q.map (MvPolynomial.aeval y).toRingHom).degree = ↑q.natDegree := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  rw [Tru]; split_ifs with h0 hbase
  · exact absurd h0 hQ
  · -- Base case: lc constant or natDeg = 0 → lc doesn't vanish (by injectivity)
    refine ⟨Q, Set.mem_singleton_iff.mpr rfl, ?_⟩
    have hlc : φ Q.leadingCoeff ≠ 0 := by
      rcases hbase with ⟨d, hd⟩ | hnd
      · -- lc = C(d): φ(C d) = algebraMap D C d ≠ 0 by injectivity
        rw [hd]; intro hlc_zero
        have hd_ne : d ≠ 0 := by
          intro hd0
          exact (Polynomial.leadingCoeff_ne_zero.mpr hQ) (by rw [hd, hd0, map_zero])
        apply hd_ne; apply hinj; rw [map_zero]
        change (MvPolynomial.aeval y) (MvPolynomial.C d) = 0 at hlc_zero
        rwa [MvPolynomial.aeval_C] at hlc_zero
      · -- natDeg = 0: Q = C(Q.coeff 0), if φ(lc) = 0 then Q_y = 0
        intro hlc_zero; apply hQy
        have hQ_eq := Polynomial.eq_C_of_natDegree_eq_zero hnd
        have hcoeff : Q.coeff 0 = Q.leadingCoeff := by
          simp only [Polynomial.leadingCoeff, hnd]
        rw [hQ_eq, Polynomial.map_C, hcoeff, hlc_zero, Polynomial.C_0]
    rw [Polynomial.degree_eq_natDegree hQy,
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hlc]
  · -- Recursive case: lc non-constant, natDeg > 0
    push Not at hbase
    obtain ⟨hlc_nc, hnd_pos⟩ := hbase
    have hnd_pos' : 0 < Q.natDegree := Nat.pos_of_ne_zero hnd_pos
    by_cases hlc : φ Q.leadingCoeff = 0
    · -- lc vanishes at y: Q_y = truncate_y, recurse
      set T := truncate (Q.natDegree - 1) Q
      have hmap_eq : Q.map φ = T.map φ := by
        ext j; simp only [Polynomial.coeff_map,
          show T = truncate (Q.natDegree - 1) Q from rfl, coeff_truncate]
        split_ifs with hj
        · rfl
        · push Not at hj
          have hle : Q.natDegree ≤ j := by omega
          rcases hle.eq_or_lt with rfl | hlt
          · simp only [Polynomial.leadingCoeff] at hlc; rw [hlc, map_zero]
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero]
      have hT : T ≠ 0 := by
        intro h; exact hQy (by rw [hmap_eq, h, Polynomial.map_zero])
      have hTy : T.map φ ≠ 0 := by rwa [← hmap_eq]
      obtain ⟨q, hq_mem, hq_deg⟩ := Tru_covers_degrees hinj T hT y hTy
      exact ⟨q, Set.mem_union_right _ hq_mem, hmap_eq ▸ hq_deg⟩
    · -- lc doesn't vanish: deg(Q_y) = natDeg(Q)
      exact ⟨Q, Set.mem_union_left _ (Set.mem_singleton_iff.mpr rfl),
        by rw [Polynomial.degree_eq_natDegree hQy,
               Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hlc]⟩
termination_by Q.natDegree
decreasing_by
  show (truncate (Q.natDegree - 1) Q).natDegree < Q.natDegree
  have := natDegree_truncate_le (Q.natDegree - 1) Q; omega

/-! #### Helper: leafPaths membership -/

/-- If `child ∈ cs` (non-empty) and `path ∈ child.leafPaths`, then
`child.root :: path ∈ leafPaths (.node root cs)`. -/
theorem mem_leafPaths_of_child (root : α) (cs : List (RoseTree α))
    (child : RoseTree α) (hchild : child ∈ cs)
    (path : List α) (hpath : path ∈ child.leafPaths) :
    (child.root :: path) ∈ (RoseTree.node root cs).leafPaths := by
  cases cs with
  | nil => simp at hchild
  | cons _ _ =>
    simp only [RoseTree.leafPaths, List.mem_flatMap, List.mem_map]
    exact ⟨child, hchild, path, hpath, rfl⟩

omit [IsDomain D] in
/-- A path `[0]` is always in the leafPaths of a node whose children
include `RoseTree.node 0 []` (which it does after appending). -/
theorem mem_leafPaths_zero
    (root : Polynomial (MvPolynomial (Fin k) D))
    (cs : List (RoseTree (Polynomial (MvPolynomial (Fin k) D)))) :
    [0] ∈ (RoseTree.node root (cs ++ [.node 0 []])).leafPaths := by
  have hmem : RoseTree.node 0 ([] : List (RoseTree _)) ∈ cs ++ [.node 0 []] := by
    simp [List.mem_append]
  have h := mem_leafPaths_of_child root (cs ++ [.node 0 []])
    (.node 0 []) hmem [] (by simp [RoseTree.leafPaths])
  simpa [RoseTree.root] using h

/-! #### Helper: mkTRemsNode subtree covering -/

/-- The `leafFormulaAux` formulas for subtrees of `mkTRemsNode` cover
all of `C^k`. Requires `algebraMap D C` injective. -/
private theorem mkTRemsNode_covering
    {C : Type*} [Field C] [Algebra D C]
    (hinj : Function.Injective (algebraMap D C))
    (parent cur : Polynomial (MvPolynomial (Fin k) D))
    (y : Fin k → C) :
    ∃ subpath ∈ (mkTRemsNode parent cur).leafPaths,
      y ∈ (leafFormulaAux parent cur subpath).realization (C := C) := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  rw [mkTRemsNode]
  by_cases hcur : cur = 0
  · -- cur = 0: .node 0 [], leafPaths = [[]]
    rw [ite_eq_left hcur]
    exact ⟨[], by simp [RoseTree.leafPaths], by
      rw [leafFormulaAux, realization_degFormula, Set.mem_ofPred_eq,
          hcur, pRemMv, dite_eq_left rfl, neg_zero, Polynomial.map_zero, Polynomial.degree_zero]⟩
  · rw [ite_eq_right hcur]; dsimp only
    set R := -(pRemMv parent cur) with R_def
    set children := (Tru_finite R).toFinset.toList with children_def
    set tru_subtrees := children.attach.map (fun ⟨child, _⟩ => mkTRemsNode cur child)
      with tru_subtrees_def
    -- Split on whether R_y = 0
    by_cases hRy : R.map φ = 0
    · -- R_y = 0: use the 0 child, path = [0]
      refine ⟨[0], mem_leafPaths_zero cur tru_subtrees, ?_⟩
      have : leafFormulaAux parent cur [0] = degFormula (-(pRemMv parent cur)) ⊥ := by
        unfold leafFormulaAux; exact ite_eq_left rfl
      rw [this, realization_degFormula, Set.mem_ofPred_eq, Polynomial.degree_eq_bot]
      exact hRy
    · -- R_y ≠ 0: find matching Tru element
      have hR : R ≠ 0 := by intro h; exact hRy (h ▸ Polynomial.map_zero φ)
      obtain ⟨c, hc_tru, hc_deg⟩ := Tru_covers_degrees hinj R hR y hRy
      have hc_list : c ∈ children :=
        Finset.mem_toList.mpr ((Set.Finite.mem_toFinset _).mpr hc_tru)
      have hc_ne : c ≠ 0 := fun h => absurd (h ▸ hc_tru) (zero_not_mem_Tru R hR)
      -- c.natDegree < cur.natDegree for termination
      have hc_nd : c.natDegree < cur.natDegree := by
        have h1 := natDegree_mem_Tru_le hc_tru
        have h2 : R.natDegree < cur.natDegree :=
          Polynomial.natDegree_lt_natDegree hR (by
            rw [R_def, Polynomial.degree_neg]; exact degree_pRemMv_lt parent cur hcur)
        omega
      -- IH: find subpath in mkTRemsNode cur c
      obtain ⟨subpath, hsp_mem, hsp_real⟩ := mkTRemsNode_covering hinj cur c y
      -- The full path: c :: subpath
      refine ⟨c :: subpath, ?_, ?_⟩
      · -- c :: subpath ∈ leafPaths
        have hmem_cs : mkTRemsNode cur c ∈ tru_subtrees :=
          List.mem_map.mpr ⟨⟨c, hc_list⟩, List.mem_attach _ _, rfl⟩
        have h := mem_leafPaths_of_child cur (tru_subtrees ++ [.node 0 []])
          (mkTRemsNode cur c) (List.mem_append_left _ hmem_cs)
          subpath hsp_mem
        rwa [mkTRemsNode_root] at h
      · -- y ∈ realization of leafFormulaAux parent cur (c :: subpath)
        have : leafFormulaAux parent cur (c :: subpath) =
            (degFormula (-(pRemMv parent cur)) (↑c.natDegree)).and
              (leafFormulaAux cur c subpath) := by
          show (if c = 0 then _ else _) = _; exact ite_eq_right hc_ne
        rw [this, Formula.realization_and, Set.mem_inter_iff]
        exact ⟨by rw [realization_degFormula, Set.mem_ofPred_eq]; exact hc_deg, hsp_real⟩
termination_by cur.natDegree
decreasing_by exact hc_nd

/-- BPR Lemma 1.19 (i), covering: for every `y ∈ C^k`, some root-to-leaf
path in `TRems(P, Q)` has `y ∈ Reali(C_L)`. Requires `algebraMap D C`
injective. -/
theorem leafFormula_covering
    {C : Type*} [Field C] [Algebra D C]
    (hinj : Function.Injective (algebraMap D C))
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    (y : Fin k → C) :
    ∃ path ∈ (TRems P Q).leafPaths,
      y ∈ (leafFormula P Q path).realization (C := C) := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  unfold TRems
  set cs := (Tru_finite Q).toFinset.toList with cs_def
  -- Split on whether Q_y = 0
  by_cases hQy : Q.map φ = 0
  · -- Q_y = 0: use the 0 child, path = [0]
    refine ⟨[0], mem_leafPaths_zero P (cs.map (mkTRemsNode P)), ?_⟩
    have : leafFormula P Q [0] = degFormula Q ⊥ := by
      unfold leafFormula; exact ite_eq_left rfl
    rw [this, realization_degFormula, Set.mem_ofPred_eq, Polynomial.degree_eq_bot]
    exact hQy
  · -- Q_y ≠ 0: find matching Tru element
    have hQ : Q ≠ 0 := by intro h; exact hQy (h ▸ Polynomial.map_zero φ)
    obtain ⟨q, hq_tru, hq_deg⟩ := Tru_covers_degrees hinj Q hQ y hQy
    have hq_list : q ∈ cs :=
      Finset.mem_toList.mpr ((Set.Finite.mem_toFinset _).mpr hq_tru)
    have hq_ne : q ≠ 0 := fun h => absurd (h ▸ hq_tru) (zero_not_mem_Tru Q hQ)
    -- Use mkTRemsNode_covering for the subtree
    obtain ⟨subpath, hsp_mem, hsp_real⟩ := mkTRemsNode_covering hinj P q y
    -- Full path: q :: subpath
    refine ⟨q :: subpath, ?_, ?_⟩
    · -- q :: subpath ∈ leafPaths
      have hmem_cs : mkTRemsNode P q ∈ cs.map (mkTRemsNode P) :=
        List.mem_map.mpr ⟨q, hq_list, rfl⟩
      have h := mem_leafPaths_of_child P (cs.map (mkTRemsNode P) ++ [.node 0 []])
        (mkTRemsNode P q) (List.mem_append_left _ hmem_cs)
        subpath hsp_mem
      rwa [mkTRemsNode_root] at h
    · -- y ∈ realization of leafFormula P Q (q :: subpath)
      have : leafFormula P Q (q :: subpath) =
          (degFormula Q (↑q.natDegree)).and (leafFormulaAux P q subpath) := by
        show (if q = 0 then _ else _) = _; exact ite_eq_right hq_ne
      rw [this, Formula.realization_and, Set.mem_inter_iff]
      exact ⟨by rw [realization_degFormula, Set.mem_ofPred_eq]; exact hq_deg, hsp_real⟩

/-! #### Helper: leafPaths extraction -/

/-- For a rose tree node with non-empty children, `leafPaths` equals the
flatMap form. This lets us extract which child a path came from. -/
theorem leafPaths_node_ne_nil
    (root : α) (cs : List (RoseTree α)) (hcs : cs ≠ []) :
    (RoseTree.node root cs).leafPaths =
      cs.flatMap fun c => c.leafPaths.map (c.root :: ·) := by
  match cs with
  | [] => exact absurd rfl hcs
  | _ :: _ => simp only [RoseTree.leafPaths]

/-! #### Leaf formula: disjointness -/

/-- Two distinct leaf paths from `mkTRemsNode parent cur` produce
`leafFormulaAux` formulas with disjoint `C`-realizations. -/
private theorem mkTRemsNode_disjoint
    {C : Type*} [Field C] [Algebra D C]
    (parent cur : Polynomial (MvPolynomial (Fin k) D))
    {path1 path2 : List (Polynomial (MvPolynomial (Fin k) D))}
    (h1 : path1 ∈ (mkTRemsNode parent cur).leafPaths)
    (h2 : path2 ∈ (mkTRemsNode parent cur).leafPaths)
    (hne : path1 ≠ path2) :
    (leafFormulaAux parent cur path1).realization (C := C) ∩
      (leafFormulaAux parent cur path2).realization (C := C) = ∅ := by
  by_cases hcur : cur = 0
  · -- Only one leaf path
    rw [mkTRemsNode, ite_eq_left hcur] at h1 h2
    simp only [RoseTree.leafPaths, List.mem_singleton] at h1 h2
    exact absurd (h1 ▸ h2 ▸ rfl) hne
  · -- cur ≠ 0: unfold one level of mkTRemsNode
    rw [mkTRemsNode, ite_eq_right hcur] at h1 h2; dsimp only at h1 h2
    set R := -(pRemMv parent cur) with R_def
    set cs := (Tru_finite R).toFinset.toList with cs_def
    set tru_trees := cs.attach.map (fun ⟨c, _⟩ => mkTRemsNode cur c) with tt_def
    set ac := tru_trees ++ [RoseTree.node 0 []] with ac_def
    -- ac is non-empty (always has .node 0 [] at the end)
    have hac_ne : ac ≠ [] := by simp [ac_def]
    -- Extract child and subpath from leafPaths membership
    rw [leafPaths_node_ne_nil cur ac hac_ne] at h1 h2
    simp only [List.mem_flatMap, List.mem_map] at h1 h2
    obtain ⟨child1, hc1_mem, sp1, hsp1, heq1⟩ := h1
    obtain ⟨child2, hc2_mem, sp2, hsp2, heq2⟩ := h2
    -- pathᵢ = childᵢ.root :: spᵢ
    subst heq1; subst heq2
    -- Classify each child: from tru_trees or the explicit 0-leaf
    rw [ac_def, List.mem_append, List.mem_singleton] at hc1_mem hc2_mem
    rcases hc1_mem with hc1_tru | hc1_zero <;> rcases hc2_mem with hc2_tru | hc2_zero
    · -- Both children from tru_trees
      rw [tt_def, List.mem_map] at hc1_tru hc2_tru
      obtain ⟨⟨c1, hc1_cs⟩, _, hc1_eq⟩ := hc1_tru
      obtain ⟨⟨c2, hc2_cs⟩, _, hc2_eq⟩ := hc2_tru
      dsimp only at hc1_eq hc2_eq; subst hc1_eq; subst hc2_eq
      simp only [mkTRemsNode_root] at hne ⊢
      have hc1_tru : c1 ∈ Tru R :=
        (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc1_cs)
      have hc2_tru : c2 ∈ Tru R :=
        (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc2_cs)
      have hR_ne : R ≠ 0 := by
        intro h; rw [h, Tru_empty_of_eq_zero] at hc1_tru; exact hc1_tru.elim
      have hc1_ne : c1 ≠ 0 := fun h => absurd (h ▸ hc1_tru) (zero_not_mem_Tru R hR_ne)
      have hc2_ne : c2 ≠ 0 := fun h => absurd (h ▸ hc2_tru) (zero_not_mem_Tru R hR_ne)
      by_cases hc_eq : c1 = c2
      · -- Same child: recurse on subpaths
        subst hc_eq
        have hsp_ne : sp1 ≠ sp2 := fun h => hne (by rw [h])
        have heq1 : leafFormulaAux parent cur (c1 :: sp1) =
            (degFormula R (↑c1.natDegree)).and (leafFormulaAux cur c1 sp1) := by
          show (if c1 = 0 then _ else _) = _; exact ite_eq_right hc1_ne
        have heq2 : leafFormulaAux parent cur (c1 :: sp2) =
            (degFormula R (↑c1.natDegree)).and (leafFormulaAux cur c1 sp2) := by
          show (if c1 = 0 then _ else _) = _; exact ite_eq_right hc1_ne
        rw [heq1, heq2]
        -- (A.and B₁).realization ∩ (A.and B₂).realization = ∅ follows from B₁ ∩ B₂ = ∅
        have ih := mkTRemsNode_disjoint cur c1 hsp1 hsp2 hsp_ne (C := C)
        ext y; simp only [Formula.realization_and, Set.mem_inter_iff,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, hy1⟩, ⟨-, hy2⟩⟩
        have : y ∈ (leafFormulaAux cur c1 sp1).realization (C := C) ∩
            (leafFormulaAux cur c1 sp2).realization := ⟨hy1, hy2⟩
        rw [ih] at this; exact this
      · -- Different children: different natDegrees → disjoint
        have hnd_ne : c1.natDegree ≠ c2.natDegree := fun h =>
          hc_eq (Tru_natDegree_injective R hR_ne hc1_tru hc2_tru h)
        -- leafFormulaAux parent cur (cᵢ :: spᵢ) has realization
        -- ⊆ (degFormula R (↑cᵢ.natDegree)).realization
        have hsub1 : (leafFormulaAux parent cur (c1 :: sp1)).realization (C := C) ⊆
            (degFormula R (↑c1.natDegree)).realization := by
          simp only [leafFormulaAux, ite_eq_right hc1_ne, Formula.realization_and]
          exact Set.inter_subset_left
        have hsub2 : (leafFormulaAux parent cur (c2 :: sp2)).realization (C := C) ⊆
            (degFormula R (↑c2.natDegree)).realization := by
          simp only [leafFormulaAux, ite_eq_right hc2_ne, Formula.realization_and]
          exact Set.inter_subset_left
        have hdisj := degFormula_disjoint (C := C) R (↑c1.natDegree) (↑c2.natDegree)
          (by exact_mod_cast hnd_ne)
        ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        intro ⟨hy1, hy2⟩
        have : y ∈ (degFormula R (↑c1.natDegree)).realization (C := C) ∩
            (degFormula R (↑c2.natDegree)).realization := ⟨hsub1 hy1, hsub2 hy2⟩
        rw [hdisj] at this; exact this
    · -- child1 from tru, child2 = .node 0 []
      subst hc2_zero
      rw [tt_def, List.mem_map] at hc1_tru
      obtain ⟨⟨c1, hc1_cs⟩, _, hc1_eq⟩ := hc1_tru
      dsimp only at hc1_eq; subst hc1_eq
      simp only [mkTRemsNode_root] at hne ⊢
      simp only [RoseTree.root] at hne ⊢
      have hc1_tru : c1 ∈ Tru R :=
        (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc1_cs)
      have hR_ne : R ≠ 0 := by
        intro h; rw [h, Tru_empty_of_eq_zero] at hc1_tru; exact hc1_tru.elim
      have hc1_ne : c1 ≠ 0 := fun h => absurd (h ▸ hc1_tru) (zero_not_mem_Tru R hR_ne)
      -- child2 = .node 0 [], sp2 ∈ (.node 0 []).leafPaths = [[]], so sp2 = []
      simp only [RoseTree.leafPaths, List.mem_singleton] at hsp2
      subst hsp2
      -- leafFormulaAux parent cur (c1 :: sp1) ⊆ degFormula R (↑c1.natDegree)
      -- leafFormulaAux parent cur (0 :: []) = degFormula R ⊥
      have hsub1 : (leafFormulaAux parent cur (c1 :: sp1)).realization (C := C) ⊆
          (degFormula R (↑c1.natDegree)).realization := by
        simp only [leafFormulaAux, ite_eq_right hc1_ne, Formula.realization_and]
        exact Set.inter_subset_left
      have heq2 : (leafFormulaAux parent cur [0]).realization (C := C) =
          (degFormula R ⊥).realization := by
        simp [leafFormulaAux, ← R_def]
      rw [heq2]
      have hdisj := degFormula_disjoint (C := C) R (↑c1.natDegree) ⊥ (by simp)
      ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hy1, hy2⟩
      have : y ∈ (degFormula R (↑c1.natDegree)).realization (C := C) ∩
          (degFormula R ⊥).realization := ⟨hsub1 hy1, hy2⟩
      rw [hdisj] at this; exact this
    · -- child1 = .node 0 [], child2 from tru
      subst hc1_zero
      rw [tt_def, List.mem_map] at hc2_tru
      obtain ⟨⟨c2, hc2_cs⟩, _, hc2_eq⟩ := hc2_tru
      dsimp only at hc2_eq; subst hc2_eq
      simp only [mkTRemsNode_root] at hne ⊢
      simp only [RoseTree.root] at hne ⊢
      have hc2_tru : c2 ∈ Tru R :=
        (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc2_cs)
      have hR_ne : R ≠ 0 := by
        intro h; rw [h, Tru_empty_of_eq_zero] at hc2_tru; exact hc2_tru.elim
      have hc2_ne : c2 ≠ 0 := fun h => absurd (h ▸ hc2_tru) (zero_not_mem_Tru R hR_ne)
      simp only [RoseTree.leafPaths, List.mem_singleton] at hsp1
      subst hsp1
      have heq1 : (leafFormulaAux parent cur [0]).realization (C := C) =
          (degFormula R ⊥).realization := by
        simp [leafFormulaAux, ← R_def]
      have hsub2 : (leafFormulaAux parent cur (c2 :: sp2)).realization (C := C) ⊆
          (degFormula R (↑c2.natDegree)).realization := by
        simp only [leafFormulaAux, ite_eq_right hc2_ne, Formula.realization_and]
        exact Set.inter_subset_left
      rw [heq1]
      have hdisj := degFormula_disjoint (C := C) R ⊥ (↑c2.natDegree) (by simp)
      ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hy1, hy2⟩
      have : y ∈ (degFormula R ⊥).realization (C := C) ∩
          (degFormula R (↑c2.natDegree)).realization := ⟨hy1, hsub2 hy2⟩
      rw [hdisj] at this; exact this
    · -- Both = .node 0 []: same child, same path → contradiction
      subst hc1_zero; subst hc2_zero
      simp only [RoseTree.root, RoseTree.leafPaths, List.mem_singleton] at hsp1 hsp2 hne
      exact absurd (hsp1 ▸ hsp2 ▸ rfl) hne
termination_by cur.natDegree
decreasing_by
  -- c1 ∈ Tru(R), R = -(pRemMv parent cur), c1.natDegree < cur.natDegree
  have h1 := natDegree_mem_Tru_le hc1_tru
  have h2 : R.natDegree < cur.natDegree :=
    Polynomial.natDegree_lt_natDegree hR_ne (by
      rw [R_def, Polynomial.degree_neg]; exact degree_pRemMv_lt parent cur hcur)
  omega

/-- BPR Lemma 1.19 (i), disjointness: distinct leaf paths in `TRems(P, Q)`
produce `leafFormula` formulas with disjoint `C`-realizations. -/
theorem leafFormula_disjoint
    {C : Type*} [Field C] [Algebra D C]
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    {path1 path2 : List (Polynomial (MvPolynomial (Fin k) D))}
    (h1 : path1 ∈ (TRems P Q).leafPaths)
    (h2 : path2 ∈ (TRems P Q).leafPaths)
    (hne : path1 ≠ path2) :
    (leafFormula P Q path1).realization (C := C) ∩
      (leafFormula P Q path2).realization (C := C) = ∅ := by
  unfold TRems at h1 h2
  set cs := (Tru_finite Q).toFinset.toList with cs_def
  set tru_trees := cs.map (mkTRemsNode P) with tt_def
  set ac := tru_trees ++ [RoseTree.node 0 []] with ac_def
  have hac_ne : ac ≠ [] := by simp [ac_def]
  rw [leafPaths_node_ne_nil P ac hac_ne] at h1 h2
  simp only [List.mem_flatMap, List.mem_map] at h1 h2
  obtain ⟨child1, hc1_mem, sp1, hsp1, heq1⟩ := h1
  obtain ⟨child2, hc2_mem, sp2, hsp2, heq2⟩ := h2
  subst heq1; subst heq2
  rw [ac_def, List.mem_append, List.mem_singleton] at hc1_mem hc2_mem
  rcases hc1_mem with hc1_tru | hc1_zero <;> rcases hc2_mem with hc2_tru | hc2_zero
  · -- Both from tru_trees
    rw [tt_def, List.mem_map] at hc1_tru hc2_tru
    obtain ⟨q1, hq1_cs, rfl⟩ := hc1_tru
    obtain ⟨q2, hq2_cs, rfl⟩ := hc2_tru
    simp only [mkTRemsNode_root] at hne ⊢
    have hq1_tru : q1 ∈ Tru Q :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hq1_cs)
    have hq2_tru : q2 ∈ Tru Q :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hq2_cs)
    have hQ_ne : Q ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hq1_tru; exact hq1_tru.elim
    have hq1_ne : q1 ≠ 0 := fun h => absurd (h ▸ hq1_tru) (zero_not_mem_Tru Q hQ_ne)
    have hq2_ne : q2 ≠ 0 := fun h => absurd (h ▸ hq2_tru) (zero_not_mem_Tru Q hQ_ne)
    by_cases hq_eq : q1 = q2
    · -- Same q: leafFormula uses same degFormula Q prefix, disjointness from subtrees
      subst hq_eq
      have hsp_ne : sp1 ≠ sp2 := fun h => hne (by rw [h])
      simp only [leafFormula, ite_eq_right hq1_ne, Formula.realization_and]
      have ih := mkTRemsNode_disjoint P q1 hsp1 hsp2 hsp_ne (C := C)
      ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨⟨_, hy1⟩, ⟨_, hy2⟩⟩
      have : y ∈ (leafFormulaAux P q1 sp1).realization (C := C) ∩
          (leafFormulaAux P q1 sp2).realization := ⟨hy1, hy2⟩
      rw [ih] at this; exact this
    · -- Different q: different natDegrees → disjoint
      have hnd_ne : q1.natDegree ≠ q2.natDegree := fun h =>
        hq_eq (Tru_natDegree_injective Q hQ_ne hq1_tru hq2_tru h)
      have hsub1 : (leafFormula P Q (q1 :: sp1)).realization (C := C) ⊆
          (degFormula Q (↑q1.natDegree)).realization := by
        simp only [leafFormula, ite_eq_right hq1_ne, Formula.realization_and]
        exact Set.inter_subset_left
      have hsub2 : (leafFormula P Q (q2 :: sp2)).realization (C := C) ⊆
          (degFormula Q (↑q2.natDegree)).realization := by
        simp only [leafFormula, ite_eq_right hq2_ne, Formula.realization_and]
        exact Set.inter_subset_left
      have hdisj := degFormula_disjoint (C := C) Q (↑q1.natDegree) (↑q2.natDegree)
        (by exact_mod_cast hnd_ne)
      have hsub := Set.inter_subset_inter hsub1 hsub2
      rw [hdisj] at hsub
      exact Set.eq_empty_of_subset_empty hsub
  · -- child1 from tru, child2 = .node 0 []
    subst hc2_zero
    rw [tt_def, List.mem_map] at hc1_tru
    obtain ⟨q1, hq1_cs, rfl⟩ := hc1_tru
    simp only [mkTRemsNode_root] at hne ⊢
    simp only [RoseTree.root] at hne ⊢
    have hq1_tru : q1 ∈ Tru Q :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hq1_cs)
    have hQ_ne : Q ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hq1_tru; exact hq1_tru.elim
    have hq1_ne : q1 ≠ 0 := fun h => absurd (h ▸ hq1_tru) (zero_not_mem_Tru Q hQ_ne)
    simp only [RoseTree.leafPaths, List.mem_singleton] at hsp2; subst hsp2
    have hsub1 : (leafFormula P Q (q1 :: sp1)).realization (C := C) ⊆
        (degFormula Q (↑q1.natDegree)).realization := by
      simp only [leafFormula, ite_eq_right hq1_ne, Formula.realization_and]
      exact Set.inter_subset_left
    have heq2 : (leafFormula P Q [0]).realization (C := C) =
        (degFormula Q ⊥).realization := by
      simp [leafFormula]
    rw [heq2]
    have hdisj := degFormula_disjoint (C := C) Q (↑q1.natDegree) ⊥ (by simp)
    ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro ⟨hy1, hy2⟩
    have : y ∈ (degFormula Q (↑q1.natDegree)).realization (C := C) ∩
        (degFormula Q ⊥).realization := ⟨hsub1 hy1, hy2⟩
    rw [hdisj] at this; exact this
  · -- child1 = .node 0 [], child2 from tru
    subst hc1_zero
    rw [tt_def, List.mem_map] at hc2_tru
    obtain ⟨q2, hq2_cs, rfl⟩ := hc2_tru
    simp only [mkTRemsNode_root] at hne ⊢
    simp only [RoseTree.root] at hne ⊢
    have hq2_tru : q2 ∈ Tru Q :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hq2_cs)
    have hQ_ne : Q ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hq2_tru; exact hq2_tru.elim
    have hq2_ne : q2 ≠ 0 := fun h => absurd (h ▸ hq2_tru) (zero_not_mem_Tru Q hQ_ne)
    simp only [RoseTree.leafPaths, List.mem_singleton] at hsp1; subst hsp1
    have heq1 : (leafFormula P Q [0]).realization (C := C) =
        (degFormula Q ⊥).realization := by
      simp [leafFormula]
    have hsub2 : (leafFormula P Q (q2 :: sp2)).realization (C := C) ⊆
        (degFormula Q (↑q2.natDegree)).realization := by
      simp only [leafFormula, ite_eq_right hq2_ne, Formula.realization_and]
      exact Set.inter_subset_left
    rw [heq1]
    have hdisj := degFormula_disjoint (C := C) Q ⊥ (↑q2.natDegree) (by simp)
    ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro ⟨hy1, hy2⟩
    have : y ∈ (degFormula Q ⊥).realization (C := C) ∩
        (degFormula Q (↑q2.natDegree)).realization := ⟨hy1, hsub2 hy2⟩
    rw [hdisj] at this; exact this
  · -- Both = .node 0 []
    subst hc1_zero; subst hc2_zero
    simp only [RoseTree.root, RoseTree.leafPaths, List.mem_singleton] at hsp1 hsp2 hne
    exact absurd (hsp1 ▸ hsp2 ▸ rfl) hne

/-! #### Leaf formula: GCD -/

/-- The leaf parent of a sub-path in `leafFormulaAux`: the last nonzero
node before the terminal `0`. Returns `cur` when the remainder
vanishes (base case). -/
noncomputable def pathLeafParentAux
    (cur : Polynomial (MvPolynomial (Fin k) D)) :
    List (Polynomial (MvPolynomial (Fin k) D)) →
    Polynomial (MvPolynomial (Fin k) D)
  | [] => cur
  | next :: rest =>
    if next = 0 then cur
    else pathLeafParentAux next rest

/-- The leaf parent of a full path in `TRems(P, Q)`: the last nonzero
polynomial before the terminal `0` leaf. Returns `P` when `Q_y = 0`
(the path is `[0]`). -/
noncomputable def pathLeafParent
    (P : Polynomial (MvPolynomial (Fin k) D)) :
    List (Polynomial (MvPolynomial (Fin k) D)) →
    Polynomial (MvPolynomial (Fin k) D)
  | [] => P
  | q :: rest =>
    if q = 0 then P
    else pathLeafParentAux q rest

omit [IsDomain D] in
/-- Coefficients of a Tru element agree with the original polynomial
up to the Tru element's `natDegree`. -/
private theorem Tru_coeff_eq
    (R q : Polynomial (MvPolynomial (Fin k) D))
    (hq : q ∈ Tru R) (j : ℕ) (hj : j ≤ q.natDegree) :
    q.coeff j = R.coeff j := by
  by_cases hR : R = 0
  · subst hR; rw [Tru, ite_eq_left rfl] at hq; exact hq.elim
  · rw [Tru, ite_eq_right hR] at hq
    split_ifs at hq with hbase
    · rw [Set.mem_singleton_iff.mp hq]
    · rw [Set.mem_union, Set.mem_singleton_iff] at hq
      rcases hq with rfl | hq_trunc
      · rfl
      · have ih := Tru_coeff_eq (truncate (R.natDegree - 1) R) q hq_trunc j hj
        rw [ih, coeff_truncate, ite_eq_left (le_trans hj (le_trans
          (natDegree_mem_Tru_le hq_trunc) (natDegree_truncate_le _ _)))]
termination_by R.natDegree
decreasing_by
  push Not at hbase
  have := natDegree_truncate_le (R.natDegree - 1) R
  have := hbase.2; omega

omit [IsDomain D] in
/-- From `degFormula R (↑q.natDegree)` and `q ∈ Tru R`, the specialized
polynomials are equal and the leading coefficient doesn't vanish. -/
theorem degFormula_Tru_spec
    {C : Type*} [Field C] [Algebra D C]
    (R q : Polynomial (MvPolynomial (Fin k) D))
    (hq : q ∈ Tru R) (_hq_ne : q ≠ 0)
    (y : Fin k → C)
    (hy : y ∈ (degFormula R (↑q.natDegree)).realization (C := C)) :
    R.map (MvPolynomial.aeval y).toRingHom =
      q.map (MvPolynomial.aeval y).toRingHom ∧
    (MvPolynomial.aeval y).toRingHom q.leadingCoeff ≠ 0 := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  have hdeg_R : (R.map φ).degree = ↑q.natDegree := by
    simp only [realization_degFormula, Set.mem_ofPred_eq] at hy; exact hy
  have hlc_eq : q.leadingCoeff = R.coeff q.natDegree := by
    show q.coeff q.natDegree = R.coeff q.natDegree
    exact Tru_coeff_eq R q hq q.natDegree le_rfl
  have hlc : φ q.leadingCoeff ≠ 0 := by
    rw [hlc_eq]
    exact ((map_degree_eq_coe_iff φ R q.natDegree).mp hdeg_R).1
  have hq_map_ne : q.map φ ≠ 0 := by
    intro h; apply hlc
    have := congr_arg (fun p => Polynomial.coeff p q.natDegree) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
    exact this
  have hdeg_q : (q.map φ).degree = ↑q.natDegree := by
    rw [Polynomial.degree_eq_natDegree hq_map_ne,
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hlc]
  exact ⟨Tru_degEq_imp_eq R q hq y (by rw [hdeg_R, hdeg_q]), hlc⟩

omit [IsDomain D] in
/-- From `degFormula R ⊥`, the specialized polynomial vanishes. -/
private theorem degFormula_bot_spec
    {C : Type*} [Field C] [Algebra D C]
    (R : Polynomial (MvPolynomial (Fin k) D))
    (y : Fin k → C)
    (hy : y ∈ (degFormula R ⊥).realization (C := C)) :
    R.map (MvPolynomial.aeval y).toRingHom = 0 := by
  simp only [realization_degFormula, Set.mem_ofPred_eq] at hy
  exact Polynomial.degree_eq_bot.mp hy

/-- BPR Lemma 1.19 (iii), recursive case: for a valid sub-path in
`mkTRemsNode parent cur`, the leaf parent is a GCD of `parent_y`
and `cur_y`. -/
private theorem mkTRemsNode_gcd
    {C : Type*} [Field C] [Algebra D C]
    (parent cur : Polynomial (MvPolynomial (Fin k) D))
    (hcur : cur ≠ 0)
    {sp : List (Polynomial (MvPolynomial (Fin k) D))}
    (hsp : sp ∈ (mkTRemsNode parent cur).leafPaths)
    (y : Fin k → C)
    (hy : y ∈ (leafFormulaAux parent cur sp).realization (C := C))
    (hlc : (MvPolynomial.aeval y).toRingHom cur.leadingCoeff ≠ 0) :
    IsGCD ((pathLeafParentAux cur sp).map (MvPolynomial.aeval y).toRingHom)
      (parent.map (MvPolynomial.aeval y).toRingHom)
      (cur.map (MvPolynomial.aeval y).toRingHom) := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  set R := -(pRemMv parent cur) with R_def
  -- Pseudo-division identity
  obtain ⟨A, hA⟩ := pRemMv_pseudo_div parent cur hcur
  have hA_map := congrArg (Polynomial.map φ) hA
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at hA_map
  rw [map_pow φ] at hA_map
  have hc_pow : φ cur.leadingCoeff ^ pRemExp parent cur ≠ 0 :=
    pow_ne_zero _ hlc
  -- Unfold mkTRemsNode to get children structure
  rw [mkTRemsNode, ite_eq_right hcur] at hsp; dsimp only at hsp
  set cs := (Tru_finite R).toFinset.toList with cs_def
  set tru_trees := cs.attach.map (fun ⟨c, _⟩ => mkTRemsNode cur c) with tt_def
  set ac := tru_trees ++ [RoseTree.node 0 []] with ac_def
  have hac_ne : ac ≠ [] := by simp [ac_def]
  rw [leafPaths_node_ne_nil cur ac hac_ne] at hsp
  simp only [List.mem_flatMap, List.mem_map] at hsp
  obtain ⟨child, hc_mem, sp', hsp', hsp_eq⟩ := hsp
  subst hsp_eq
  rw [ac_def, List.mem_append, List.mem_singleton] at hc_mem
  rcases hc_mem with hc_tru | hc_zero
  · -- child from tru_trees: sp = [c, sp'] with c ∈ Tru R
    rw [tt_def, List.mem_map] at hc_tru
    obtain ⟨⟨c, hc_cs⟩, _, hc_eq⟩ := hc_tru
    dsimp only at hc_eq; subst hc_eq
    simp only [mkTRemsNode_root] at hy ⊢
    have hc_tru : c ∈ Tru R :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_cs)
    have hR_ne : R ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hc_tru; exact hc_tru.elim
    have hc_ne : c ≠ 0 := fun h => absurd (h ▸ hc_tru) (zero_not_mem_Tru R hR_ne)
    -- leafFormulaAux parent cur (c :: sp') = degFormula R (↑c.natDegree) ∧ ...
    simp only [leafFormulaAux, ite_eq_right hc_ne, Formula.realization_and] at hy
    obtain ⟨hy_deg, hy_rest⟩ := hy
    -- From degFormula: R_y = c_y and φ(c.leadingCoeff) ≠ 0
    obtain ⟨hRc, hlc_c⟩ := degFormula_Tru_spec R c hc_tru hc_ne y hy_deg
    -- IH: IsGCD (pathLeafParentAux c sp').map φ (cur.map φ) (c.map φ)
    have ih := mkTRemsNode_gcd cur c hc_ne hsp' y hy_rest hlc_c
    -- pathLeafParentAux cur (c :: sp') = pathLeafParentAux c sp'
    simp only [pathLeafParentAux, ite_eq_right hc_ne]
    -- Chain: rewrite c_y to R_y, then R_y to -(pRemMv parent cur)_y
    rw [← hRc] at ih
    have hR_eq : R.map φ = -(pRemMv parent cur).map φ := by
      rw [R_def, Polynomial.map_neg]
    rw [hR_eq] at ih
    exact (isGCD_of_pseudo_div hc_pow hA_map).mpr ih.of_neg_right
  · -- child = .node 0 []: sp = [0], remainder vanishes
    subst hc_zero
    simp only [RoseTree.leafPaths, List.mem_singleton] at hsp'
    subst hsp'
    -- leafFormulaAux parent cur [0] = degFormula R ⊥
    simp only [leafFormulaAux] at hy
    have hR_zero : R.map φ = 0 := degFormula_bot_spec R y hy
    have hpRem_zero : (pRemMv parent cur).map φ = 0 := by
      have : R.map φ = -(pRemMv parent cur).map φ := by rw [R_def, Polynomial.map_neg]
      rw [hR_zero] at this; exact neg_eq_zero.mp this.symm
    rw [hpRem_zero, add_zero] at hA_map
    -- pathLeafParentAux cur [0] = cur
    simp only [pathLeafParentAux]
    have hA_map' : Polynomial.C (φ cur.leadingCoeff ^ pRemExp parent cur) *
        parent.map φ = A.map φ * cur.map φ + 0 := by rw [add_zero]; exact hA_map
    exact (isGCD_of_pseudo_div hc_pow hA_map').mpr (isGCD_self_zero _)
termination_by cur.natDegree
decreasing_by
  exact lt_of_le_of_lt (natDegree_mem_Tru_le hc_tru)
    (Polynomial.natDegree_lt_natDegree hR_ne (by
      rw [Polynomial.degree_neg]; exact degree_pRemMv_lt parent cur hcur))

/-- BPR Lemma 1.19 (iii): for `y ∈ Reali(C_L)`, the leaf parent
`Pol(p(L))_y` is a GCD of `P_y` and `Q_y`. -/
theorem leafFormula_gcd
    {C : Type*} [Field C] [Algebra D C]
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : path ∈ (TRems P Q).leafPaths)
    (y : Fin k → C)
    (hy : y ∈ (leafFormula P Q path).realization (C := C)) :
    IsGCD ((pathLeafParent P path).map (MvPolynomial.aeval y).toRingHom)
      (P.map (MvPolynomial.aeval y).toRingHom)
      (Q.map (MvPolynomial.aeval y).toRingHom) := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  unfold TRems at hpath
  set cs := (Tru_finite Q).toFinset.toList with cs_def
  set tru_trees := cs.map (mkTRemsNode P) with tt_def
  set ac := tru_trees ++ [RoseTree.node 0 []] with ac_def
  have hac_ne : ac ≠ [] := by simp [ac_def]
  rw [leafPaths_node_ne_nil P ac hac_ne] at hpath
  simp only [List.mem_flatMap, List.mem_map] at hpath
  obtain ⟨child, hc_mem, sp, hsp, heq⟩ := hpath
  subst heq
  rw [ac_def, List.mem_append, List.mem_singleton] at hc_mem
  rcases hc_mem with hc_tru | hc_zero
  · -- child from tru_trees: path = [q, sp] with q ∈ Tru Q
    rw [tt_def, List.mem_map] at hc_tru
    obtain ⟨q, hq_cs, rfl⟩ := hc_tru
    simp only [mkTRemsNode_root] at hy ⊢
    have hq_tru : q ∈ Tru Q :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hq_cs)
    have hQ_ne : Q ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hq_tru; exact hq_tru.elim
    have hq_ne : q ≠ 0 := fun h => absurd (h ▸ hq_tru) (zero_not_mem_Tru Q hQ_ne)
    -- leafFormula P Q (q :: sp) = degFormula Q (↑q.natDegree) ∧ leafFormulaAux P q sp
    simp only [leafFormula, ite_eq_right hq_ne, Formula.realization_and] at hy
    obtain ⟨hy_deg, hy_rest⟩ := hy
    -- From degFormula: Q_y = q_y and φ(q.leadingCoeff) ≠ 0
    obtain ⟨hQq, hlc_q⟩ := degFormula_Tru_spec Q q hq_tru hq_ne y hy_deg
    -- By mkTRemsNode_gcd: IsGCD lp_y P_y q_y
    have ih := mkTRemsNode_gcd P q hq_ne hsp y hy_rest hlc_q
    -- pathLeafParent P (q :: sp) = pathLeafParentAux q sp
    simp only [pathLeafParent, ite_eq_right hq_ne]
    rw [hQq]
    exact ih
  · -- child = .node 0 []: path = [0], Q_y = 0
    subst hc_zero
    simp only [RoseTree.leafPaths, List.mem_singleton] at hsp
    subst hsp
    simp only [leafFormula] at hy
    have hQ_zero : Q.map φ = 0 := degFormula_bot_spec Q y hy
    simp only [pathLeafParent]
    rw [hQ_zero]
    exact isGCD_self_zero _

/-- For `y ∈ Reali(leafFormulaAux parent cur sp)`, every non-zero
polynomial along the sub-path `sp` has non-vanishing leading
coefficient at `y`. Mirrors `mkTRemsNode_gcd`: each `degFormula` on the
path pins a truncation `c ∈ Tru(R)`, and `degFormula_Tru_spec` gives
`φ(c.leadingCoeff) ≠ 0`. -/
theorem leafFormulaAux_lc_ne_zero
    {C : Type*} [Field C] [Algebra D C]
    (parent cur : Polynomial (MvPolynomial (Fin k) D)) (hcur : cur ≠ 0)
    {sp : List (Polynomial (MvPolynomial (Fin k) D))}
    (hsp : sp ∈ (mkTRemsNode parent cur).leafPaths)
    (y : Fin k → C)
    (hy : y ∈ (leafFormulaAux parent cur sp).realization (C := C)) :
    ∀ p ∈ sp, p ≠ 0 → (MvPolynomial.aeval y).toRingHom p.leadingCoeff ≠ 0 := by
  set R := -(pRemMv parent cur) with R_def
  rw [mkTRemsNode, ite_eq_right hcur] at hsp; dsimp only at hsp
  set cs := (Tru_finite R).toFinset.toList with cs_def
  set tru_trees := cs.attach.map (fun ⟨c, _⟩ => mkTRemsNode cur c) with tt_def
  set ac := tru_trees ++ [RoseTree.node 0 []] with ac_def
  have hac_ne : ac ≠ [] := by simp [ac_def]
  rw [leafPaths_node_ne_nil cur ac hac_ne] at hsp
  simp only [List.mem_flatMap, List.mem_map] at hsp
  obtain ⟨child, hc_mem, sp', hsp', hsp_eq⟩ := hsp
  subst hsp_eq
  rw [ac_def, List.mem_append, List.mem_singleton] at hc_mem
  rcases hc_mem with hc_tru | hc_zero
  · rw [tt_def, List.mem_map] at hc_tru
    obtain ⟨⟨c, hc_cs⟩, _, hc_eq⟩ := hc_tru
    dsimp only at hc_eq; subst hc_eq
    simp only [mkTRemsNode_root] at hy ⊢
    have hc_tru : c ∈ Tru R :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_cs)
    have hR_ne : R ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hc_tru; exact hc_tru.elim
    have hc_ne : c ≠ 0 := fun h => absurd (h ▸ hc_tru) (zero_not_mem_Tru R hR_ne)
    simp only [leafFormulaAux, ite_eq_right hc_ne, Formula.realization_and] at hy
    obtain ⟨hy_deg, hy_rest⟩ := hy
    obtain ⟨_, hlc_c⟩ := degFormula_Tru_spec R c hc_tru hc_ne y hy_deg
    have ih := leafFormulaAux_lc_ne_zero cur c hc_ne hsp' y hy_rest
    intro p hp hp0
    rcases List.mem_cons.mp hp with rfl | hp_sp'
    · exact hlc_c
    · exact ih p hp_sp' hp0
  · subst hc_zero
    simp only [RoseTree.leafPaths, List.mem_singleton] at hsp'
    subst hsp'
    intro p hp hp0
    rw [List.mem_singleton] at hp; subst hp; exact absurd rfl hp0
termination_by cur.natDegree
decreasing_by
  exact lt_of_le_of_lt (natDegree_mem_Tru_le hc_tru)
    (Polynomial.natDegree_lt_natDegree hR_ne (by
      rw [Polynomial.degree_neg]; exact degree_pRemMv_lt parent cur hcur))

/-- For `y ∈ Reali(leafFormula P Q path)`, every non-zero polynomial
along the leaf `path` has non-vanishing leading coefficient at `y`.
Mirrors `leafFormula_gcd`. -/
theorem leafFormula_path_lc_ne_zero
    {C : Type*} [Field C] [Algebra D C]
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : path ∈ (TRems P Q).leafPaths)
    (y : Fin k → C)
    (hy : y ∈ (leafFormula P Q path).realization (C := C)) :
    ∀ p ∈ path, p ≠ 0 → (MvPolynomial.aeval y).toRingHom p.leadingCoeff ≠ 0 := by
  unfold TRems at hpath
  set cs := (Tru_finite Q).toFinset.toList with cs_def
  set tru_trees := cs.map (mkTRemsNode P) with tt_def
  set ac := tru_trees ++ [RoseTree.node 0 []] with ac_def
  have hac_ne : ac ≠ [] := by simp [ac_def]
  rw [leafPaths_node_ne_nil P ac hac_ne] at hpath
  simp only [List.mem_flatMap, List.mem_map] at hpath
  obtain ⟨child, hc_mem, sp, hsp, heq⟩ := hpath
  subst heq
  rw [ac_def, List.mem_append, List.mem_singleton] at hc_mem
  rcases hc_mem with hc_tru | hc_zero
  · rw [tt_def, List.mem_map] at hc_tru
    obtain ⟨q, hq_cs, rfl⟩ := hc_tru
    simp only [mkTRemsNode_root] at hy ⊢
    have hq_tru : q ∈ Tru Q :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hq_cs)
    have hQ_ne : Q ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hq_tru; exact hq_tru.elim
    have hq_ne : q ≠ 0 := fun h => absurd (h ▸ hq_tru) (zero_not_mem_Tru Q hQ_ne)
    simp only [leafFormula, ite_eq_right hq_ne, Formula.realization_and] at hy
    obtain ⟨hy_deg, hy_rest⟩ := hy
    obtain ⟨_, hlc_q⟩ := degFormula_Tru_spec Q q hq_tru hq_ne y hy_deg
    have ih := leafFormulaAux_lc_ne_zero P q hq_ne hsp y hy_rest
    intro p hp hp0
    rcases List.mem_cons.mp hp with rfl | hp_sp
    · exact hlc_q
    · exact ih p hp_sp hp0
  · subst hc_zero
    simp only [RoseTree.leafPaths, List.mem_singleton] at hsp
    subst hsp
    intro p hp hp0
    rw [List.mem_singleton] at hp; subst hp; exact absurd rfl hp0

end Lemma_1_19

end Azurite.BPR

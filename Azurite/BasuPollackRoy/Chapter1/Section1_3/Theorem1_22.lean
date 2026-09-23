import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleQF
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_3
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Notation1_1
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14Corollaries
import Azurite.BasuPollackRoy.Chapter1.Section1_3.DegFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_3.LeafFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Lemma1_19
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Lemma1_20
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Posgcd
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SignedPseudoRemainder
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SplitLast
import Azurite.BasuPollackRoy.Chapter1.Section1_3.TRems

/-! # BPR Section 1.3 — Theorem 1.22: Projection theorem for constructible sets

BPR's projection theorem: the image of a constructible set in `C^{k+1}`
under the projection to `C^k` is constructible. Equivalently, the
theory of algebraically closed fields admits quantifier elimination.

The construction goes through `projBasic Ps Qs`: a quantifier-free
formula whose `C`-realization is the projection of a basic
constructible set cut out by `Ps` (equalities) and `Qs` (disequalities).
The general case follows by combining `projBasic` with the conj-form
decomposition (`exercise_1_3`).
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]




/-!
### The projection formula `projBasic`

Given families `𝒫, 𝒬 ⊂ D[Y₁, …, Y_k, X]`, the basic constructible
set `S = { (y, x) | ⋀ P ∈ 𝒫, P(y,x) = 0 ∧ ⋀ Q ∈ 𝒬, Q(y,x) ≠ 0 }`
projects to a subset `π(S) ⊂ C^k`. Its description as a quantifier-free
formula over `Fin k`-many variables is `projBasic 𝒫 𝒬`.

The construction mirrors the proof of Theorem 1.22:

1. Reinterpret `𝒫, 𝒬 ⊂ D[Y₁, …, Y_k, X]` as
   `𝒫', 𝒬' ⊂ D[Y₁, …, Y_k][X]` via `splitLast`.
2. Pick `d` strictly greater than the `X`-degrees of all `P ∈ 𝒫'`.
3. For each `(G₁, C₁) ∈ posgcd(𝒫')` — so `G₁_y` is a GCD of `𝒫'_y`
   whenever `y ∈ Reali(C₁)` — run `TRems(𝒬'.prod^d, G₁)` to obtain
   the gcd of `G₁_y` with `𝒬'_y.prod^d`.
4. The projection `π(S) ∩ Reali(C₁)` is characterised by
   `deg_X(G) ≠ deg_X(G₁)` (Lemma 1.14).

The resulting formula is a disjunction over all `(G₁, C₁)` and all
leaf paths.
-/

section ProjFormula

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

/-- The projection-of-basic formula: a quantifier-free formula whose
`C`-realization is the projection to `C^k` of the basic constructible
set `{ (y, x) | ⋀ P ∈ 𝒫, P(y,x) = 0 ∧ ⋀ Q ∈ 𝒬, Q(y,x) ≠ 0 }`.

See `realization_projBasic` for the correctness statement. -/
noncomputable def projBasic
    (Ps Qs : List (MvPolynomial (Fin (k+1)) D)) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  let Ps' : List (Polynomial (MvPolynomial (Fin k) D)) := Ps.map splitLast
  let Qs' : List (Polynomial (MvPolynomial (Fin k) D)) := Qs.map splitLast
  let d : ℕ := 1 + (Ps'.map Polynomial.natDegree).foldr max 0
  let extra : Polynomial (MvPolynomial (Fin k) D) := Qs'.prod ^ d
  Formula.disjList <|
    (posgcd Ps').flatMap fun QC₁ =>
      (TRems extra QC₁.1).leafPaths.map fun path =>
        QC₁.2.and
          ((leafFormula extra QC₁.1 path).and
            (degNeqFormula (pathLeafParent extra path) QC₁.1))

end ProjFormula

/-!
### Correctness of `projBasic`

`realization_projBasic` states that the realization of `projBasic Ps Qs`
agrees with the projection of the basic constructible set defined by
`Ps` (equalities) and `Qs` (disequalities).

The proof combines `posgcd_gcd` + `leafFormula_gcd` (identifying the
gcd structure) with `lemma_1_14` / `lemma_1_14_cor2` (characterising
when a fiber is nonempty).
-/

section ProjFormulaCorrectness

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsAlgClosed C] [IsDomain D] in
/-- Fiber-level version of the projection predicate: rewritten via
`splitLast` so that the variable `X` is explicit, and then mapped
through `aeval y` to land in `C[X]`. -/
private theorem exists_snoc_iff_exists_eval_splitLast [Algebra D C]
    (y : Fin k → C)
    (Ps Qs : List (MvPolynomial (Fin (k+1)) D)) :
    (∃ x : C, (∀ P ∈ Ps, MvPolynomial.aeval (Fin.snoc y x) P = 0) ∧
              (∀ Q ∈ Qs, MvPolynomial.aeval (Fin.snoc y x) Q ≠ 0)) ↔
    (∃ x : C,
      (∀ P' ∈ (Ps.map splitLast).map
          (Polynomial.map (MvPolynomial.aeval y).toRingHom),
        Polynomial.eval x P' = 0) ∧
      (∀ Q' ∈ (Qs.map splitLast).map
          (Polynomial.map (MvPolynomial.aeval y).toRingHom),
        Polynomial.eval x Q' ≠ 0)) := by
  simp only [List.forall_mem_map]
  constructor
  · rintro ⟨x, hP, hQ⟩
    refine ⟨x, ?_, ?_⟩
    · intro P hP_mem
      rw [← aeval_snoc_eq_eval_splitLast]; exact hP P hP_mem
    · intro Q hQ_mem
      rw [← aeval_snoc_eq_eval_splitLast]; exact hQ Q hQ_mem
  · rintro ⟨x, hP, hQ⟩
    refine ⟨x, ?_, ?_⟩
    · intro P hP_mem
      rw [aeval_snoc_eq_eval_splitLast]; exact hP P hP_mem
    · intro Q hQ_mem
      rw [aeval_snoc_eq_eval_splitLast]; exact hQ Q hQ_mem

omit [IsAlgClosed C] in
/-- A GCD of `G` with `0` is associated with `G`. -/
private theorem IsGCD.eq_zero_left_iff {G P Q : Polynomial C}
    (h : IsGCD G P Q) (hQ : Q = 0) : G = 0 ↔ P = 0 := by
  subst hQ
  constructor
  · intro hG
    rw [hG] at h
    exact zero_dvd_iff.mp h.1
  · intro hP
    subst hP
    exact zero_dvd_iff.mp (h.2.2 0 (dvd_refl _) (dvd_refl _))

omit [IsAlgClosed C] in
/-- An `IsListGCD` of a family is zero iff every element of the family
is zero. -/
private theorem IsListGCD.eq_zero_iff {G : Polynomial C}
    {Ps : List (Polynomial C)} (h : IsListGCD G Ps) :
    G = 0 ↔ ∀ P ∈ Ps, P = 0 := by
  constructor
  · intro hG P hP
    have := h.1 P hP
    rw [hG] at this
    exact zero_dvd_iff.mp this
  · intro hAll
    exact zero_dvd_iff.mp (h.2 0 (fun P hP => (hAll P hP).symm ▸ dvd_refl 0))

omit [IsAlgClosed C] in
/-- Two `IsListGCD`s of the same family are associated (differ by a
unit). -/
private theorem IsListGCD.associated {G G' : Polynomial C}
    {Ps : List (Polynomial C)} (h : IsListGCD G Ps) (h' : IsListGCD G' Ps) :
    Associated G G' :=
  associated_of_dvd_dvd (h'.2 G h.1) (h.2 G' h'.1)

omit [IsAlgClosed C] in
/-- Two `IsGCD`s of the same pair are associated. -/
private theorem IsGCD.associated {G G' P Q : Polynomial C}
    (h : IsGCD G P Q) (h' : IsGCD G' P Q) : Associated G G' :=
  associated_of_dvd_dvd (h'.2.2 G h.1 h.2.1) (h.2.2 G' h'.1 h'.2.1)

omit [IsAlgClosed C] [IsDomain D] in
/-- Fold bound: each element of `Ps'` has natDegree strictly less than
`1 + foldr max 0 (Ps'.map natDegree)`. -/
theorem natDegree_lt_foldr_succ
    (Ps' : List (Polynomial (MvPolynomial (Fin k) D))) :
    ∀ P' ∈ Ps', P'.natDegree < 1 + (Ps'.map Polynomial.natDegree).foldr max 0 := by
  intro P' hP'
  have h : P'.natDegree ≤ (Ps'.map Polynomial.natDegree).foldr max 0 := by
    induction Ps' with
    | nil => simp at hP'
    | cons Q rest ih =>
      simp only [List.mem_cons] at hP'
      simp only [List.map_cons, List.foldr_cons]
      rcases hP' with rfl | hP'
      · exact le_max_left _ _
      · exact le_trans (ih hP') (le_max_right _ _)
  omega

omit [IsDomain D] in
/-- Key technical iff: given `G_1` a list-gcd of `Ps'_y` and `G` a
gcd of `extra_y = Qs'.prod^d_y` and `G_1_y`, with `d` strictly greater
than the `X`-degree of every `P ∈ Ps'`, the existence of a common
root of `Ps'_y` avoiding the zeros of `Qs'_y` is equivalent to
`deg G_y ≠ deg G_1_y`. -/
theorem fiber_iff_degree_ne
    [Algebra D C]
    (Ps' Qs' : List (Polynomial (MvPolynomial (Fin k) D)))
    (d : ℕ) (hd : ∀ P' ∈ Ps', P'.natDegree < d) (hd_pos : 0 < d)
    {G G_1 : Polynomial (MvPolynomial (Fin k) D)}
    (y : Fin k → C)
    (h_G_1 : IsListGCD (G_1.map (MvPolynomial.aeval y).toRingHom)
              (Ps'.map (Polynomial.map (MvPolynomial.aeval y).toRingHom)))
    (h_G : IsGCD (G.map (MvPolynomial.aeval y).toRingHom)
            ((Qs'.prod ^ d).map (MvPolynomial.aeval y).toRingHom)
            (G_1.map (MvPolynomial.aeval y).toRingHom)) :
    (∃ x : C,
      (∀ P' ∈ Ps'.map (Polynomial.map (MvPolynomial.aeval y).toRingHom),
        Polynomial.eval x P' = 0) ∧
      (∀ Q' ∈ Qs'.map (Polynomial.map (MvPolynomial.aeval y).toRingHom),
        Polynomial.eval x Q' ≠ 0)) ↔
    (G.map (MvPolynomial.aeval y).toRingHom).degree ≠
      (G_1.map (MvPolynomial.aeval y).toRingHom).degree := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom
  set Ps_s := Ps'.map (Polynomial.map φ) with hPs_s
  set Qs_s := Qs'.map (Polynomial.map φ) with hQs_s
  set Gs := G.map φ with hGs
  set G_1s := G_1.map φ with hG_1s
  -- `(Qs'.prod^d).map φ = Qs_s.prod^d`
  have hextra_eq : (Qs'.prod ^ d).map φ = Qs_s.prod ^ d := by
    rw [Polynomial.map_pow]; congr 1
    rw [hQs_s, ← Polynomial.map_list_prod]
  rw [hextra_eq] at h_G
  by_cases hG_1s_zero : G_1s = 0
  · -- Case B: G_1s = 0, so all Ps_s are zero
    have hPs_all_zero : ∀ P ∈ Ps_s, P = 0 := (IsListGCD.eq_zero_iff h_G_1).mp hG_1s_zero
    have hG_deg : Gs.degree ≠ G_1s.degree ↔ Gs ≠ 0 := by
      rw [hG_1s_zero, Polynomial.degree_zero]
      exact ⟨fun h hz => h (hz ▸ rfl), fun h hz =>
        h (Polynomial.degree_eq_bot.mp hz)⟩
    rw [hG_deg]
    have hGs_assoc : Associated Gs (Qs_s.prod ^ d) := by
      refine (IsGCD.associated h_G ?_)
      refine ⟨dvd_refl _, ?_, ?_⟩
      · rw [hG_1s_zero]; exact dvd_zero _
      · intro D hD _; exact hD
    have hGs_iff : Gs ≠ 0 ↔ Qs_s.prod ^ d ≠ 0 := by
      constructor
      · intro h hz
        exact h (hGs_assoc.eq_zero_iff.mpr hz)
      · intro h hz
        exact h (hGs_assoc.symm.eq_zero_iff.mpr hz)
    rw [hGs_iff]
    have hQs_iff : Qs_s.prod ^ d ≠ 0 ↔ Qs_s.prod ≠ 0 := by
      constructor
      · intro h hz; exact h (by rw [hz, zero_pow hd_pos.ne'])
      · intro h hz; exact h (pow_eq_zero_iff hd_pos.ne' |>.mp hz)
    rw [hQs_iff]
    constructor
    · rintro ⟨x, _hP, hQ⟩ hprod
      -- Qs_s.prod = 0: pick any Q_s whose product is 0 — must have some Q_s with eval x Q_s = 0
      -- Actually simpler: if prod = 0, then eval x prod = 0, but prod = ∏ Q, so eval x Q = 0 for some Q
      have heval : (Polynomial.eval x Qs_s.prod) = 0 := by rw [hprod]; simp
      rw [Polynomial.eval_list_prod] at heval
      have hmem := List.prod_eq_zero_iff.mp heval
      simp only [List.mem_map] at hmem
      obtain ⟨v, hv_mem, hv_zero⟩ := hmem
      exact hQ v hv_mem hv_zero
    · intro hprod
      have hQ_prod_ne : Qs_s.prod ≠ 0 := hprod
      have hdeg : 0 ≤ Qs_s.prod.degree := by
        rw [Polynomial.degree_eq_natDegree hQ_prod_ne]
        exact Nat.cast_nonneg _
      have := (lemma_1_14_cor2 (C := C) (K := C) Qs_s).mpr hdeg
      obtain ⟨x, hx⟩ := this
      refine ⟨x, ?_, ?_⟩
      · intro P hP
        rw [hPs_all_zero P hP]; simp
      · intro Q hQ
        have := hx Q hQ
        rwa [Polynomial.coe_aeval_eq_eval] at this
  · -- Case A: G_1s ≠ 0, apply lemma_1_14
    -- Step 1: listGcd Ps_s ~ G_1s, so natDegree(listGcd Ps_s) = natDegree G_1s
    have h_listGcd : IsListGCD (listGcd Ps_s) Ps_s := listGcd_isListGCD Ps_s
    have h_listGcd_assoc : Associated (listGcd Ps_s) G_1s :=
      IsListGCD.associated h_listGcd h_G_1
    have h_listGcd_ne : listGcd Ps_s ≠ 0 := by
      intro hz
      exact hG_1s_zero (h_listGcd_assoc.symm.eq_zero_iff.mpr hz)
    have h_listGcd_natDegree : (listGcd Ps_s).natDegree = G_1s.natDegree :=
      Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated h_listGcd_assoc)
    -- Step 2: G_1s.natDegree < d
    have h_G_1s_natDegree_lt : G_1s.natDegree < d := by
      -- G_1s divides some nonzero P ∈ Ps_s (since not all are zero)
      have hsome : ∃ P ∈ Ps_s, P ≠ 0 := by
        by_contra hall
        exact hG_1s_zero ((IsListGCD.eq_zero_iff h_G_1).mpr fun P hP => by
          by_contra hne; exact hall ⟨P, hP, hne⟩)
      obtain ⟨P, hP_mem, hP_ne⟩ := hsome
      have hG_1s_dvd_P : G_1s ∣ P := h_G_1.1 P hP_mem
      have hG_1s_le : G_1s.natDegree ≤ P.natDegree :=
        Polynomial.natDegree_le_of_dvd hG_1s_dvd_P hP_ne
      -- P = P'.map φ for some P' ∈ Ps', with P'.natDegree < d
      simp only [hPs_s, List.mem_map] at hP_mem
      obtain ⟨P', hP'_mem, hP_eq⟩ := hP_mem
      have hP_le : P.natDegree ≤ P'.natDegree := by
        rw [← hP_eq]; exact Polynomial.natDegree_map_le
      have hP'_lt : P'.natDegree < d := hd P' hP'_mem
      omega
    -- Step 3: apply lemma_1_14
    have hlem := lemma_1_14 (C := C) (K := C) Ps_s Qs_s h_listGcd_ne
      (d := d) (by rw [h_listGcd_natDegree]; exact h_G_1s_natDegree_lt)
    -- Step 4: translate aeval → eval on C[X]
    have hlem_eval : (∃ x : C,
        (∀ P ∈ Ps_s, Polynomial.eval x P = 0) ∧
        (∀ Q ∈ Qs_s, Polynomial.eval x Q ≠ 0)) ↔
        (gcd (listGcd Ps_s) (Qs_s.prod ^ d)).natDegree ≠ (listGcd Ps_s).natDegree := by
      rw [← hlem]
      simp only [Polynomial.coe_aeval_eq_eval]
    rw [hlem_eval]
    -- Step 5: translate (listGcd Ps_s).natDegree → G_1s.natDegree
    rw [h_listGcd_natDegree]
    -- Step 6: gcd(listGcd Ps_s, Qs_s.prod^d) has same natDegree as Gs
    have hgcd_isGCD : IsGCD (gcd (listGcd Ps_s) (Qs_s.prod ^ d)) (Qs_s.prod ^ d) (listGcd Ps_s) := by
      refine ⟨gcd_dvd_right _ _, gcd_dvd_left _ _, fun E hE1 hE2 => ?_⟩
      exact dvd_gcd hE2 hE1
    -- Relate (gcd (listGcd Ps_s) (Qs_s.prod ^ d)) to Gs via IsGCD
    have hG_listGcd : IsGCD Gs (Qs_s.prod ^ d) (listGcd Ps_s) := by
      refine ⟨h_G.1, ?_, ?_⟩
      · exact h_G.2.1.trans h_listGcd_assoc.symm.dvd
      · intro E hE1 hE2
        have : E ∣ G_1s := (h_listGcd_assoc.dvd_iff_dvd_right).mp hE2
        exact h_G.2.2 E hE1 this
    have hGs_gcd_assoc : Associated Gs (gcd (listGcd Ps_s) (Qs_s.prod ^ d)) :=
      IsGCD.associated hG_listGcd hgcd_isGCD
    have hGs_gcd_nd : Gs.natDegree =
        (gcd (listGcd Ps_s) (Qs_s.prod ^ d)).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated hGs_gcd_assoc)
    rw [← hGs_gcd_nd]
    -- Step 7: Gs ≠ 0 (divides G_1s ≠ 0), so degree = natDegree
    have hGs_ne : Gs ≠ 0 := by
      intro hz
      have : Gs ∣ G_1s := h_G.2.1
      rw [hz] at this
      exact hG_1s_zero (zero_dvd_iff.mp this)
    rw [Polynomial.degree_eq_natDegree hGs_ne, Polynomial.degree_eq_natDegree hG_1s_zero]
    exact ⟨fun h => fun heq => h (by exact_mod_cast heq),
           fun h => fun heq => h (by exact_mod_cast heq)⟩

/-- **Correctness of `projBasic`.** Its realization is precisely the
projection of the basic constructible set defined by `Ps` (equalities)
and `Qs` (disequalities). -/
theorem realization_projBasic
    [Algebra D C] (hinj : Function.Injective (algebraMap D C))
    (Ps Qs : List (MvPolynomial (Fin (k+1)) D)) :
    (projBasic Ps Qs).realization (C := C) =
      { y | ∃ x : C, (∀ P ∈ Ps, MvPolynomial.aeval (Fin.snoc y x) P = 0) ∧
                     (∀ Q ∈ Qs, MvPolynomial.aeval (Fin.snoc y x) Q ≠ 0) } := by
  set Ps' : List (Polynomial (MvPolynomial (Fin k) D)) := Ps.map splitLast with Ps'_def
  set Qs' : List (Polynomial (MvPolynomial (Fin k) D)) := Qs.map splitLast with Qs'_def
  set d : ℕ := 1 + (Ps'.map Polynomial.natDegree).foldr max 0 with d_def
  have hd_pos : 0 < d := by rw [d_def]; omega
  set extra : Polynomial (MvPolynomial (Fin k) D) := Qs'.prod ^ d with extra_def
  have hproj_eq : projBasic Ps Qs =
    Formula.disjList ((posgcd Ps').flatMap fun QC₁ =>
      (TRems extra QC₁.1).leafPaths.map fun path =>
        QC₁.2.and ((leafFormula extra QC₁.1 path).and
          (degNeqFormula (pathLeafParent extra path) QC₁.1))) := rfl
  rw [hproj_eq, Formula.realization_disjList]
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [exists_snoc_iff_exists_eval_splitLast y Ps Qs]
  constructor
  · rintro ⟨Φ, hΦ_mem, hy_Φ⟩
    simp only [List.mem_flatMap, List.mem_map, Prod.exists] at hΦ_mem
    obtain ⟨G_1, C_1, h_mem_posgcd, path, hpath_mem, hΦ_eq⟩ := hΦ_mem
    subst hΦ_eq
    simp only [Formula.realization_and, Set.mem_inter_iff,
      realization_degNeqFormula, Set.mem_ofPred_eq] at hy_Φ
    obtain ⟨hy_C_1, hy_leaf, hy_deg⟩ := hy_Φ
    have h_G_1_isListGCD := posgcd_gcd Ps' h_mem_posgcd y hy_C_1
    have h_G_isGCD := leafFormula_gcd extra G_1 hpath_mem y hy_leaf
    exact (fiber_iff_degree_ne Ps' Qs' d (natDegree_lt_foldr_succ Ps')
      hd_pos y h_G_1_isListGCD h_G_isGCD).mpr hy_deg
  · rintro ⟨x, hP, hQ⟩
    obtain ⟨G_1, C_1, h_mem_posgcd, hy_C_1⟩ := posgcd_covering hinj Ps' y
    obtain ⟨path, hpath_mem, hy_leaf⟩ := leafFormula_covering hinj extra G_1 y
    have h_G_1_isListGCD := posgcd_gcd Ps' h_mem_posgcd y hy_C_1
    have h_G_isGCD := leafFormula_gcd extra G_1 hpath_mem y hy_leaf
    have h_deg := (fiber_iff_degree_ne Ps' Qs' d (natDegree_lt_foldr_succ Ps')
      hd_pos y h_G_1_isListGCD h_G_isGCD).mp ⟨x, hP, hQ⟩
    refine ⟨C_1.and ((leafFormula extra G_1 path).and
              (degNeqFormula (pathLeafParent extra path) G_1)), ?_, ?_⟩
    · simp only [List.mem_flatMap, List.mem_map, Prod.exists]
      exact ⟨G_1, C_1, h_mem_posgcd, path, hpath_mem, rfl⟩
    · simp only [Formula.realization_and, Set.mem_inter_iff,
        realization_degNeqFormula, Set.mem_ofPred_eq]
      exact ⟨hy_C_1, hy_leaf, h_deg⟩

end ProjFormulaCorrectness

/-!
### Theorem 1.22: Projection theorem for constructible sets

BPR Theorem 1.22: the image of a constructible set in `C^{k+1}` under
the projection to `C^k` is constructible.

The proof combines `realization_projBasic` (the basic case) with
`exercise_1_3` (every constructible set is a finite union of basic
constructibles) and a structural decomposition of basic constructible
sets as `Zer F \ ⋃ⱼ Zer Gⱼ`.
-/

section QuantifierFree

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsAlgClosed C] [IsDomain D] in
/-- A conjunction of quantifier-free formulas is quantifier-free. -/
theorem Formula.conjList_isQF
    {σ : Type*} (Φs : List (Formula σ (FieldAtom σ D)))
    (h : ∀ Φ ∈ Φs, Φ.IsQuantifierFree) :
    (Formula.conjList Φs).IsQuantifierFree := by
  induction Φs with
  | nil => trivial
  | cons Φ rest ih =>
    exact ⟨h Φ List.mem_cons_self,
      ih (fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))⟩

omit [IsAlgClosed C] [IsDomain D] in
/-- A disjunction of quantifier-free formulas is quantifier-free. -/
theorem Formula.disjList_isQF
    {σ : Type*} (Φs : List (Formula σ (FieldAtom σ D)))
    (h : ∀ Φ ∈ Φs, Φ.IsQuantifierFree) :
    (Formula.disjList Φs).IsQuantifierFree := by
  induction Φs with
  | nil => trivial
  | cons Φ rest ih =>
    exact ⟨h Φ List.mem_cons_self,
      ih (fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))⟩

omit [IsAlgClosed C] [IsDomain D] in
theorem degFormula_isQF
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i : WithBot ℕ) :
    (degFormula Q i).IsQuantifierFree := by
  cases i with
  | bot =>
    apply Formula.conjList_isQF
    intro Φ hΦ
    simp only [List.mem_map] at hΦ
    obtain ⟨j, _, rfl⟩ := hΦ
    trivial
  | coe n =>
    refine ⟨trivial, ?_⟩
    apply Formula.conjList_isQF
    intro Φ hΦ
    simp only [List.mem_map] at hΦ
    obtain ⟨j, _, rfl⟩ := hΦ
    trivial

omit [IsAlgClosed C] [IsDomain D] in
theorem degEqFormula_isQF
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    (degEqFormula Q₁ Q₂).IsQuantifierFree := by
  apply Formula.disjList_isQF
  intro Φ hΦ
  simp only [List.mem_cons, List.mem_map] at hΦ
  rcases hΦ with rfl | ⟨i, _, rfl⟩
  · exact ⟨degFormula_isQF Q₁ ⊥, degFormula_isQF Q₂ ⊥⟩
  · exact ⟨degFormula_isQF Q₁ (some i), degFormula_isQF Q₂ (some i)⟩

omit [IsAlgClosed C] [IsDomain D] in
theorem degNeqFormula_isQF
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    (degNeqFormula Q₁ Q₂).IsQuantifierFree :=
  degEqFormula_isQF Q₁ Q₂

omit [IsAlgClosed C] in
theorem leafFormulaAux_isQF
    (parent cur : Polynomial (MvPolynomial (Fin k) D))
    (rest : List (Polynomial (MvPolynomial (Fin k) D))) :
    (leafFormulaAux parent cur rest).IsQuantifierFree := by
  induction rest generalizing parent cur with
  | nil => exact degFormula_isQF _ _
  | cons q rest ih =>
    simp only [leafFormulaAux]
    split_ifs
    · exact degFormula_isQF _ _
    · exact ⟨degFormula_isQF _ _, ih cur q⟩

omit [IsAlgClosed C] in
theorem leafFormula_isQF
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D))) :
    (leafFormula P Q path).IsQuantifierFree := by
  cases path with
  | nil =>
    show (degFormula Q ⊥).IsQuantifierFree
    exact degFormula_isQF Q ⊥
  | cons q rest =>
    simp only [leafFormula]
    split_ifs
    · exact degFormula_isQF Q ⊥
    · exact ⟨degFormula_isQF Q _, leafFormulaAux_isQF _ _ _⟩

omit [IsAlgClosed C] in
/-- Every formula `𝒞` appearing in a pair of `posgcd Ps` is quantifier-free. -/
theorem posgcd_snd_isQF
    (Ps : List (Polynomial (MvPolynomial (Fin k) D)))
    {G : Polynomial (MvPolynomial (Fin k) D)}
    {𝒞 : Formula (Fin k) (FieldAtom (Fin k) D)}
    (hmem : (G, 𝒞) ∈ posgcd Ps) : 𝒞.IsQuantifierFree := by
  induction Ps generalizing G 𝒞 with
  | nil =>
    simp only [posgcd, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨_, rfl⟩ := hmem
    trivial
  | cons P rest ih =>
    simp only [posgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
    obtain ⟨⟨Q, C_q⟩, hQC_mem, path, _, _, hC_eq⟩ := hmem
    subst hC_eq
    exact ⟨ih hQC_mem, leafFormula_isQF _ _ _⟩

omit [IsAlgClosed C] in
/-- `projBasic Ps Qs` is quantifier-free. -/
theorem projBasic_isQF
    (Ps Qs : List (MvPolynomial (Fin (k+1)) D)) :
    (projBasic Ps Qs).IsQuantifierFree := by
  apply Formula.disjList_isQF
  intro Φ hΦ
  simp only [List.mem_flatMap, List.mem_map, Prod.exists] at hΦ
  obtain ⟨G_1, C_1, hmem, path, _, rfl⟩ := hΦ
  exact ⟨posgcd_snd_isQF _ hmem,
    leafFormula_isQF _ _ _, degNeqFormula_isQF _ _⟩

end QuantifierFree

/-!
### Theorem 1.22: the basic case

If `Ps, Qs ⊂ C[Y₁, …, Y_k, X]`, then the projection to `C^k` of the
basic constructible set
`{ z ∈ C^{k+1} | ⋀ P ∈ Ps, P(z) = 0 ∧ ⋀ Q ∈ Qs, Q(z) ≠ 0 }`
is constructible.
-/

/-- BPR Theorem 1.22 (basic case): the projection of a basic constructible
set cut out by `Ps` (equalities) and `Qs` (disequalities) is constructible. -/
theorem theorem_1_22_basic
    (Ps Qs : List (MvPolynomial (Fin (k+1)) C)) :
    IsConstructibleSet
      { y : Fin k → C | ∃ x : C,
          (∀ P ∈ Ps, MvPolynomial.aeval (Fin.snoc y x) P = 0) ∧
          (∀ Q ∈ Qs, MvPolynomial.aeval (Fin.snoc y x) Q ≠ 0) } := by
  have hinj : Function.Injective (algebraMap C C) := fun _ _ h => h
  rw [← realization_projBasic (D := C) hinj Ps Qs]
  exact qf_realizable_isConstructible (projBasic_isQF Ps Qs)

/-!
### Theorem 1.22: the general case

By `exercise_1_3`, every constructible set is a finite union of basic
constructible sets. A basic constructible set further decomposes as a
finite union of *conj-form* sets — sets cut out by a conjunction of
equalities and inequalities, exactly the shape of `theorem_1_22_basic`.
Since projection commutes with union and finite unions of constructibles
are constructible, the general projection theorem follows.
-/

omit [Field C] [IsAlgClosed C] in
/-- Projection commutes with union of sets. -/
theorem proj_set_union (S T : Set (Fin (k+1) → C)) :
    { y : Fin k → C | ∃ x : C, Fin.snoc y x ∈ S ∪ T } =
      { y | ∃ x, Fin.snoc y x ∈ S } ∪ { y | ∃ x, Fin.snoc y x ∈ T } := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨x, hx | hx⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨x, Or.inl hx⟩
    · exact ⟨x, Or.inr hx⟩

/-- A set `V ⊂ C^{k+1}` is a finite union of BPR conj-form sets: each
summand is cut out by a list `Ps` of equalities and a list `Qs` of
inequalities. -/
inductive IsFinUnionConjForm : Set (Fin (k+1) → C) → Prop where
  | conj (Ps Qs : List (MvPolynomial (Fin (k+1)) C)) :
      IsFinUnionConjForm
        { z | (∀ P ∈ Ps, MvPolynomial.aeval z P = 0) ∧
              (∀ Q ∈ Qs, MvPolynomial.aeval z Q ≠ 0) }
  | union {V W} : IsFinUnionConjForm V → IsFinUnionConjForm W →
      IsFinUnionConjForm (V ∪ W)

namespace IsFinUnionConjForm

omit [IsAlgClosed C] in
/-- The empty set is conj-form (use `Qs = [0]`: `0 ≠ 0` is false). -/
theorem empty : IsFinUnionConjForm (∅ : Set (Fin (k+1) → C)) := by
  have h : IsFinUnionConjForm
      { z : Fin (k+1) → C | (∀ P ∈ ([] : List (MvPolynomial (Fin (k+1)) C)),
                              MvPolynomial.aeval z P = 0) ∧
                            (∀ Q ∈ [(0 : MvPolynomial (Fin (k+1)) C)],
                              MvPolynomial.aeval z Q ≠ 0) } := .conj [] [0]
  convert h using 1
  ext z
  simp

omit [IsAlgClosed C] in
/-- A conj-form intersected with a finite union of conj-forms is a finite
union of conj-forms. -/
theorem conj_inter (Ps Qs : List (MvPolynomial (Fin (k+1)) C))
    {V : Set (Fin (k+1) → C)} (hV : IsFinUnionConjForm V) :
    IsFinUnionConjForm
      ({ z | (∀ P ∈ Ps, MvPolynomial.aeval z P = 0) ∧
             (∀ Q ∈ Qs, MvPolynomial.aeval z Q ≠ 0) } ∩ V) := by
  induction hV with
  | conj Ps' Qs' =>
    have h : IsFinUnionConjForm
        { z : Fin (k+1) → C | (∀ P ∈ Ps ++ Ps', MvPolynomial.aeval z P = 0) ∧
                              (∀ Q ∈ Qs ++ Qs', MvPolynomial.aeval z Q ≠ 0) } :=
      .conj (Ps ++ Ps') (Qs ++ Qs')
    convert h using 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_append]
    constructor
    · rintro ⟨⟨hP, hQ⟩, hP', hQ'⟩
      refine ⟨fun P hP_ => ?_, fun Q hQ_ => ?_⟩
      · rcases hP_ with hmem | hmem
        · exact hP P hmem
        · exact hP' P hmem
      · rcases hQ_ with hmem | hmem
        · exact hQ Q hmem
        · exact hQ' Q hmem
    · rintro ⟨hP, hQ⟩
      refine ⟨⟨fun P hP_ => hP P (Or.inl hP_),
               fun Q hQ_ => hQ Q (Or.inl hQ_)⟩,
              fun P hP_ => hP P (Or.inr hP_),
              fun Q hQ_ => hQ Q (Or.inr hQ_)⟩
  | union _ _ ih₁ ih₂ =>
    rw [Set.inter_union_distrib_left]
    exact .union ih₁ ih₂

omit [IsAlgClosed C] in
/-- Intersection closure. -/
theorem inter {V W : Set (Fin (k+1) → C)}
    (hV : IsFinUnionConjForm V) (hW : IsFinUnionConjForm W) :
    IsFinUnionConjForm (V ∩ W) := by
  induction hV with
  | conj Ps Qs => exact conj_inter Ps Qs hW
  | union _ _ ih₁ ih₂ =>
    rw [Set.union_inter_distrib_right]
    exact .union ih₁ ih₂

omit [IsAlgClosed C] in
/-- Helper: `{z | ∃ P ∈ l, aeval z P ≠ 0}` is a finite union of conj-forms. -/
theorem exists_ne_zero_of_list
    (l : List (MvPolynomial (Fin (k+1)) C)) :
    IsFinUnionConjForm
      { z : Fin (k+1) → C | ∃ P ∈ l, MvPolynomial.aeval z P ≠ 0 } := by
  induction l with
  | nil =>
    have heq : { z : Fin (k+1) → C |
                  ∃ P ∈ ([] : List (MvPolynomial (Fin (k+1)) C)),
                  MvPolynomial.aeval z P ≠ 0 } = ∅ := by
      ext z; simp
    rw [heq]; exact empty
  | cons head rest ih =>
    have heq : { z : Fin (k+1) → C | ∃ P ∈ head :: rest,
                  MvPolynomial.aeval z P ≠ 0 } =
          { z | MvPolynomial.aeval z head ≠ 0 } ∪
          { z | ∃ P ∈ rest, MvPolynomial.aeval z P ≠ 0 } := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_union, List.mem_cons]
      constructor
      · rintro ⟨P, hmem | hmem, hne⟩
        · exact Or.inl (hmem ▸ hne)
        · exact Or.inr ⟨P, hmem, hne⟩
      · rintro (hne | ⟨P, hmem, hne⟩)
        · exact ⟨head, Or.inl rfl, hne⟩
        · exact ⟨P, Or.inr hmem, hne⟩
    rw [heq]
    refine .union ?_ ih
    have hshape : { z : Fin (k+1) → C | MvPolynomial.aeval z head ≠ 0 } =
        { z | (∀ P ∈ ([] : List (MvPolynomial (Fin (k+1)) C)),
               MvPolynomial.aeval z P = 0) ∧
              (∀ Q ∈ [head], MvPolynomial.aeval z Q ≠ 0) } := by
      ext z
      simp
    rw [hshape]
    exact .conj [] [head]

end IsFinUnionConjForm

omit [IsAlgClosed C] in
/-- Every algebraic set is a finite union of conj-forms (a single one). -/
theorem IsAlgebraicSet.isFinUnionConjForm
    {V : Set (Fin (k+1) → C)} (hV : IsAlgebraicSet V) :
    IsFinUnionConjForm V := by
  obtain ⟨finset, hV⟩ := hV
  subst hV
  have hshape : (Zer finset : Set (Fin (k+1) → C)) =
      { z | (∀ P ∈ finset.toList, MvPolynomial.aeval z P = 0) ∧
            (∀ Q ∈ ([] : List (MvPolynomial (Fin (k+1)) C)),
              MvPolynomial.aeval z Q ≠ 0) } := by
    ext z
    simp only [Zer, Set.mem_ofPred_eq, Finset.mem_toList, List.not_mem_nil,
               false_implies, implies_true, and_true,
               MvPolynomial.aeval_eq_eval]
  rw [hshape]
  exact .conj finset.toList []

omit [IsAlgClosed C] in
/-- The complement of an algebraic set is a finite union of conj-forms. -/
theorem IsAlgebraicSet.compl_isFinUnionConjForm
    {V : Set (Fin (k+1) → C)} (hV : IsAlgebraicSet V) :
    IsFinUnionConjForm Vᶜ := by
  obtain ⟨finset, hV⟩ := hV
  subst hV
  have hshape : (Zer finset : Set (Fin (k+1) → C))ᶜ =
      { z | ∃ P ∈ finset.toList, MvPolynomial.aeval z P ≠ 0 } := by
    ext z
    simp only [Zer, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall,
               Finset.mem_toList, MvPolynomial.aeval_eq_eval, exists_prop]
  rw [hshape]
  exact IsFinUnionConjForm.exists_ne_zero_of_list _

omit [IsAlgClosed C] in
/-- Every basic constructible set is a finite union of conj-forms. -/
theorem IsBasicConstructibleSet.isFinUnionConjForm
    {V : Set (Fin (k+1) → C)} (hV : IsBasicConstructibleSet V) :
    IsFinUnionConjForm V := by
  induction hV with
  | algebraic hA => exact hA.isFinUnionConjForm
  | compl_algebraic hA => exact hA.compl_isFinUnionConjForm
  | inter _ _ ih₁ ih₂ => exact ih₁.inter ih₂

/-- The projection of a finite union of conj-form sets is constructible. -/
theorem IsFinUnionConjForm.proj_isConstructible
    {V : Set (Fin (k+1) → C)} (hV : IsFinUnionConjForm V) :
    IsConstructibleSet
      { y : Fin k → C | ∃ x : C, Fin.snoc y x ∈ V } := by
  induction hV with
  | conj Ps Qs => exact theorem_1_22_basic Ps Qs
  | union _ _ ih₁ ih₂ =>
    rw [proj_set_union]
    exact ih₁.union ih₂

/-- BPR Theorem 1.22 (general case): the projection to `C^k` of any
constructible subset of `C^{k+1}` is constructible. -/
theorem theorem_1_22
    {S : Set (Fin (k+1) → C)} (hS : IsConstructibleSet S) :
    IsConstructibleSet
      { y : Fin k → C | ∃ x : C, Fin.snoc y x ∈ S } := by
  have hfu := exercise_1_3 hS
  clear hS
  induction hfu with
  | basic hbc => exact hbc.isFinUnionConjForm.proj_isConstructible
  | union _ _ ih₁ ih₂ =>
    rw [proj_set_union]
    exact ih₁.union ih₂


end Azurite.BPR

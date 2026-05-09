import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.LinearCombination
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SignedPseudoRemainder
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Tru
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Truncate

/-! # BPR Section 1.3 — Tree of possible signed pseudo-remainder sequences `TRems(P, Q)`

The **tree of possible signed pseudo-remainder sequences** of two
polynomials `P, Q ∈ D[Y₁, …, Y_k][X]`, denoted `TRems(P, Q)`, is
a (rose) tree defined as follows:

* The **root** contains `P`.
* The **children of the root** are labelled by the elements of `Tru(Q)`.
* Each node `N` stores a polynomial `Pol(N) ∈ D[Y₁, …, Y_k][X]`.
* `N` is a **leaf** (no children) when `Pol(N) = 0`.
* If `N` is not a leaf, the children of `N` are labelled by the
  truncations of `−PRem(Pol(p(N)), Pol(N))`, where `p(N)` is
  `N`'s parent.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D]

/-- Rose tree: a node labelled by `α` with a list of subtrees. -/
inductive RoseTree (α : Type*) where
  | node : α → List (RoseTree α) → RoseTree α

/-- The label at the root of a `RoseTree`. -/
def RoseTree.root : RoseTree α → α
  | .node a _ => a

/-- All root-to-leaf paths in a `RoseTree`, represented as lists of
node labels from the root's immediate child down to the leaf.
A leaf (no children) produces the single empty path `[]`.
A branching node distributes paths through each child subtree. -/
def RoseTree.leafPaths : RoseTree α → List (List α)
  | .node _ [] => [[]]
  | .node _ cs => cs.flatMap fun c =>
      c.leafPaths.map (c.root :: ·)

section TRems

open Classical

omit [IsDomain D] in
/-- `Tru Q` is always a finite set. -/
theorem Tru_finite (Q : Polynomial (MvPolynomial (Fin k) D)) :
    (Tru Q).Finite := by
  rw [Tru]
  split_ifs
  · exact Set.finite_empty
  · exact Set.finite_singleton _
  · exact (Set.finite_singleton _).union (Tru_finite _)
termination_by Q.natDegree
decreasing_by
  show (truncate (Q.natDegree - 1) Q).natDegree < Q.natDegree
  have hQpos : 0 < Q.natDegree := by
    rename_i _ hb
    push Not at hb
    exact Nat.pos_of_ne_zero hb.2
  have h := natDegree_truncate_le (Q.natDegree - 1) Q
  omega

omit [IsDomain D] in
/-- Elements of `Tru Q` have `natDegree ≤ Q.natDegree`. -/
theorem natDegree_mem_Tru_le {Q Q' : Polynomial (MvPolynomial (Fin k) D)}
    (hQ' : Q' ∈ Tru Q) : Q'.natDegree ≤ Q.natDegree := by
  by_cases h0 : Q = 0
  · subst h0; rw [Tru, if_pos rfl] at hQ'; exact hQ'.elim
  · rw [Tru, if_neg h0] at hQ'
    by_cases hbase : (∃ d : D, Q.leadingCoeff = MvPolynomial.C d) ∨ Q.natDegree = 0
    · rw [if_pos hbase, Set.mem_singleton_iff] at hQ'; subst hQ'; exact le_refl _
    · rw [if_neg hbase, Set.mem_union, Set.mem_singleton_iff] at hQ'
      rcases hQ' with rfl | hQ'
      · exact le_refl _
      · have := natDegree_mem_Tru_le hQ'
        have := natDegree_truncate_le (Q.natDegree - 1) Q
        omega
termination_by Q.natDegree
decreasing_by
  show (truncate (Q.natDegree - 1) Q).natDegree < Q.natDegree
  have hQpos : 0 < Q.natDegree := by
    push Not at hbase; exact Nat.pos_of_ne_zero hbase.2
  have := natDegree_truncate_le (Q.natDegree - 1) Q; omega

/-- The signed pseudo-remainder of `P` and `Q` in `D[Y₁,…,Y_k][X]`,
descended from the fraction field. Returns `0` when `Q = 0`. -/
noncomputable def pRemMv
    (P Q : Polynomial (MvPolynomial (Fin k) D)) :
    Polynomial (MvPolynomial (Fin k) D) :=
  if hQ : Q = 0 then 0
  else (@PRem_descends (MvPolynomial (Fin k) D) _ _
    (FractionRing (MvPolynomial (Fin k) D)) _ _ _ P Q hQ).choose

/-- The descended `pRemMv` maps to `PRem` under `algebraMap`. -/
theorem pRemMv_spec
    (P Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0) :
    (pRemMv P Q).map (algebraMap (MvPolynomial (Fin k) D)
      (FractionRing (MvPolynomial (Fin k) D))) =
      PRem (FractionRing (MvPolynomial (Fin k) D)) P Q := by
  unfold pRemMv; rw [dif_neg hQ]
  exact (@PRem_descends (MvPolynomial (Fin k) D) _ _
    (FractionRing (MvPolynomial (Fin k) D)) _ _ _ P Q hQ).choose_spec

/-- The descended pseudo-remainder has degree strictly less than the
divisor when the divisor is nonzero. -/
theorem degree_pRemMv_lt
    (P Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0) :
    (pRemMv P Q).degree < Q.degree := by
  unfold pRemMv; rw [dif_neg hQ]
  have hinj := IsFractionRing.injective (MvPolynomial (Fin k) D)
    (FractionRing (MvPolynomial (Fin k) D))
  have hspec := (@PRem_descends (MvPolynomial (Fin k) D) _ _
    (FractionRing (MvPolynomial (Fin k) D)) _ _ _ P Q hQ).choose_spec
  rw [← Polynomial.degree_map_eq_of_injective hinj,
      ← Polynomial.degree_map_eq_of_injective hinj Q, hspec]
  exact @degree_pRem_lt (MvPolynomial (Fin k) D) _
    (FractionRing (MvPolynomial (Fin k) D)) _ _ _ P Q hQ

/-- Pseudo-division identity in `D[Y₁,…,Yₖ][X]`:
`C(b_q^d) · P = A · Q + pRemMv(P, Q)` for some `A`. -/
theorem pRemMv_pseudo_div
    (P Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0) :
    ∃ A : Polynomial (MvPolynomial (Fin k) D),
      Polynomial.C (Q.leadingCoeff ^ pRemExp P Q) * P =
        A * Q + pRemMv P Q := by
  set K := FractionRing (MvPolynomial (Fin k) D)
  have hinj := IsFractionRing.injective (MvPolynomial (Fin k) D) K
  have hbound : (if P.natDegree < Q.natDegree then 0
                 else P.natDegree - Q.natDegree + 1) ≤ pRemExp P Q := by
    split_ifs with h
    · exact Nat.zero_le _
    · exact pRemExp_ge P Q (Nat.not_lt.mp h)
  obtain ⟨A, R, hAR, hdR⟩ :=
    pRem_exists_aux Q hQ (P.natDegree + 1) P (Nat.lt_succ_self _)
      (pRemExp P Q) hbound
  -- Show R = pRemMv P Q: both map to PRem K P Q under algebraMap
  suffices R = pRemMv P Q by rw [← this]; exact ⟨A, hAR⟩
  apply Polynomial.map_injective (algebraMap (MvPolynomial (Fin k) D) K) hinj
  rw [pRemMv_spec P Q hQ]
  -- Show R.map = PRem K P Q by Euclidean division uniqueness
  have hmap := congrArg (Polynomial.map (algebraMap (MvPolynomial (Fin k) D) K)) hAR
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at hmap
  unfold PRem Rem
  simp only [Polynomial.map_mul, Polynomial.map_C]
  have hQmap_ne : Q.map (algebraMap (MvPolynomial (Fin k) D) K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hQ
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

/-- Build the subtree of `TRems` rooted at `curPol`, whose parent
holds `parentPol`. Terminates because `natDegree` strictly decreases
through `PRem` and `Tru`.

Every non-zero node has an explicit `0` child (leaf) appended after
the `Tru` children.  This matches BPR's tree structure where every
branch eventually ends at a node with `Pol(N) = 0`. -/
noncomputable def mkTRemsNode
    (parentPol curPol : Polynomial (MvPolynomial (Fin k) D)) :
    RoseTree (Polynomial (MvPolynomial (Fin k) D)) :=
  if curPol = 0 then .node curPol []
  else
    let next := -(pRemMv parentPol curPol)
    let children := (Tru_finite next).toFinset.toList
    .node curPol (children.attach.map (fun ⟨child, _hmem⟩ =>
      mkTRemsNode curPol child) ++ [.node 0 []])
termination_by curPol.natDegree
decreasing_by
  rename_i h_ne
  have hmem_tru : child ∈ Tru next :=
    (Set.Finite.mem_toFinset _).mp ((Finset.mem_toList).mp _hmem)
  by_cases h4 : pRemMv parentPol curPol = 0
  · -- next = 0 ⇒ Tru next = ∅, contradicting hmem_tru
    have hn0 : next = 0 := show -(pRemMv parentPol curPol) = 0 by rw [h4, neg_zero]
    rw [hn0, Tru, if_pos rfl] at hmem_tru; exact hmem_tru.elim
  · have h1 := natDegree_mem_Tru_le hmem_tru
    have h5 := Polynomial.natDegree_lt_natDegree h4
      (degree_pRemMv_lt parentPol curPol h_ne)
    have h6 : next.natDegree = (pRemMv parentPol curPol).natDegree :=
      Polynomial.natDegree_neg _
    omega

/-- BPR's **tree of possible signed pseudo-remainder sequences**
`TRems(P, Q)` for `P, Q ∈ D[Y₁, …, Y_k][X]`.

The root contains `P`; its children are the elements of `Tru(Q)`
(each expanded into subtrees) followed by an explicit `0` leaf.
Each deeper level unfolds via `Tru(−PRem(…))`. A node whose
polynomial is `0` is a leaf (no children). -/
noncomputable def TRems
    (P Q : Polynomial (MvPolynomial (Fin k) D)) :
    RoseTree (Polynomial (MvPolynomial (Fin k) D)) :=
  .node P ((Tru_finite Q).toFinset.toList.map (mkTRemsNode P) ++ [.node 0 []])

end TRems

/-!
### Example 1.17

For `P = X⁴ + aX² + bX + c` and `Q = 4X³ + 2aX + b` (the derivative
of `P`), the tree `TRems(P, Q)` has 10 nodes and 4 leaves.
The computable version `Azurite.AzPolynomial.tremsTree` reproduces
this example with every node verified by `#guard` tests in
`Azurite/AzPolynomial/TRems.lean`.
-/

end Azurite.BPR

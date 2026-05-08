import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial
import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleQF
import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleSets
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Definitions
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Example1_2
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_1
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_2
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_3
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_4
import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Notation1_1
import Azurite.BasuPollackRoy.Chapter1.Section1_1.PrenexNormalForm
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization
import Azurite.BasuPollackRoy.Chapter1.Section1_1.RealizationInvariance
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Sentences
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Coprime
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Corollary1_6
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_7
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_10
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_13
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Divisor
import Azurite.BasuPollackRoy.Chapter1.Section1_2.EuclideanDivision
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_5
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_6
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_7
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lcm
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14Corollaries
import Azurite.BasuPollackRoy.Chapter1.Section1_2.PolynomialBasics
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_5
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_8
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_9
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_12
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Remark1_4
import Azurite.BasuPollackRoy.Chapter1.Section1_2.RootCharacterizations
import Azurite.BasuPollackRoy.Chapter1.Section1_2.SRemSTermination
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Fiber
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Projection
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SignedPseudoRemainder
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Specialize
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SplitLast
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Tru
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Truncate

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 1: Algebraically Closed Fields
## Section 1.3: Projection Theorem for Constructible Sets

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

### Overview

The goal of this section is the **projection theorem**: the image of
a constructible set under a coordinate projection is again
constructible. Equivalently, the theory of algebraically closed
fields admits quantifier elimination.

A basic constructible set `S ⊂ C^{k+1}` can be described as

  S = { z ∈ C^{k+1} | ⋀_{P ∈ 𝓟} P(z) = 0 ∧ ⋀_{Q ∈ 𝓠} Q(z) ≠ 0}

with `𝓟, 𝓠` finite subsets of `C[Y₁, …, Y_k, X]`, and its projection
`π(S)` — obtained by forgetting the last coordinate — is

  π(S) = { y ∈ C^k | ∃ x ∈ C, ⋀_{P ∈ 𝓟} P(y, x) = 0 ∧
                              ⋀_{Q ∈ 𝓠} Q(y, x) ≠ 0}.

We consider the polynomials in `𝓟` and `𝓠` as polynomials in the
single variable `X` with the variables `(Y₁, …, Y_k)` appearing as
parameters. For a specialization of `Y` to `y = (y₁, …, y_k) ∈ C^k`,
we write `P_y(X)` for `P(y₁, …, y_k, X)`. Hence,

  π(S) = { y ∈ C^k | ∃ x ∈ C, ⋀_{P ∈ 𝓟} P_y(x) = 0 ∧
                              ⋀_{Q ∈ 𝓠} Q_y(x) ≠ 0}.

### Representation via `Formula`

Following Section 1.1, a constructible set is represented as (the
`C`-realization of) a `Formula` over `Fin (k+1)`-many variables with
atoms of the form `P = 0` or `P ≠ 0` (`FieldAtom`). A *basic*
constructible set, as above, corresponds to a basic formula — a
conjunction of atoms in the sense of `Formula.IsBasicFormula`.

With this representation, the projection `π` is naturally defined
for any formula `Φ` in `Fin (k+1)`-many variables, producing a
subset of `C^k`: `y ∈ π(Φ)` iff some extension `(y, x) ∈ C^{k+1}`
satisfies `Φ`.

### Convention on the variable order

We order the `k+1` variables as `(Y₁, …, Y_k, X)` — the last
variable `X` is the one that gets eliminated by `π`. In Lean we use
`Fin (k+1)`, identifying:

* `Fin.castSucc i` (for `i : Fin k`) with the parameter `Y_{i+1}`;
* `Fin.last k` with the eliminated variable `X`.

Given `y : Fin k → C` and `x : C`, the concatenation `Fin.snoc y x`
is the assignment `z : Fin (k+1) → C` with
`z (Fin.castSucc i) = y i` and `z (Fin.last k) = x`.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

/-! Note: `specialize`, `splitLast`, `proj`, `fiber`, the signed
pseudo-remainder `PRem` (with its descent), and the truncations
`truncate`/`Tru` are defined in
`Azurite.BasuPollackRoy.Chapter1.Section1_3.{Specialize,SplitLast,Projection,Fiber,SignedPseudoRemainder,Truncate,Tru}`. -/

variable {D : Type*} [CommRing D] [IsDomain D]
variable {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]

/-!
### Tree of possible signed pseudo-remainder sequences `TRems(P, Q)`

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

/-!
### Example 1.21

For the same polynomials `P` and `P'` as in Example 1.17,
`Posgcd({P, P'})` has 9 elements `(Gᵢ, Cᵢ)`. The `Gᵢ` are the
leaf parents of `TRems(P, P')` (i.e. the last nonzero polynomial on
each root-to-leaf path), and each `Cᵢ` is a conjunction of degree
formulas specifying when `gcd(P_y, P'_y) = (Gᵢ)_y`.

The computable version `Azurite.azPosgcd` reproduces all 9 elements
with every `G`-component and formula-simplification property verified
by `#guard` tests in `Azurite/AzFormula/Posgcd.lean`.
-/

/-!
### Notation 1.18: Degree as a formula

For `Q ∈ D[Y₁, …, Y_k][X]`, the **degree formula** `degFormula Q i`
is a quantifier-free formula in the variables `Y₁, …, Y_k` whose
`C`-realization is the set of `y ∈ C^k` such that the specialized
polynomial `Q_y(X)` has degree `i` (where `i ∈ WithBot ℕ`, with
`⊥` representing degree `−∞`, i.e. `Q_y = 0`).

Concretely:
- `degFormula Q ⊥` is the conjunction `⋀_{j=0}^{natDeg Q} (coeff Q j = 0)`.
- `degFormula Q (some n)` is `coeff Q n ≠ 0 ∧ ⋀_{j=n+1}^{natDeg Q} (coeff Q j = 0)`.
- `degEqFormula Q₁ Q₂` is `⋁_i (degFormula Q₁ i ∧ degFormula Q₂ i)`.
-/

section DegFormula

variable {D : Type*} [CommRing D] [IsDomain D]
omit [IsDomain D]

/-- BPR Notation 1.18: `deg_X(Q) = i` as a formula in `Fin k` variables.

For `Q ∈ D[Y₁,…,Yₖ][X]`:
- `i = ⊥` means all coefficients vanish (degree = −∞, i.e., `Q_y = 0`)
- `i = some n` means `coeff Q n ≠ 0` and all higher coefficients vanish -/
noncomputable def degFormula
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i : WithBot ℕ) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  match i with
  | ⊥ => Formula.conjList ((List.range (Q.natDegree + 1)).map fun j =>
      Formula.eq_zero (Q.coeff j))
  | some n => .and
      (Formula.ne_zero (Q.coeff n))
      (Formula.conjList ((List.range (Q.natDegree - n)).map fun j =>
        Formula.eq_zero (Q.coeff (n + 1 + j))))

/-- BPR Notation 1.18: `deg_X(Q₁) = deg_X(Q₂)` as a formula.

This is the finite disjunction over all possible degree values
`i ∈ {⊥, 0, 1, …, max(natDeg Q₁, natDeg Q₂)}` of
`degFormula Q₁ i ∧ degFormula Q₂ i`. -/
noncomputable def degEqFormula
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  let m := max Q₁.natDegree Q₂.natDegree
  Formula.disjList (
    ((degFormula Q₁ ⊥).and (degFormula Q₂ ⊥)) ::
    (List.range (m + 1)).map fun i =>
      (degFormula Q₁ (some i)).and (degFormula Q₂ (some i)))

/-- The negation of `degEqFormula`: `deg_X(Q₁_y) ≠ deg_X(Q₂_y)`. -/
noncomputable def degNeqFormula
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  .not (degEqFormula Q₁ Q₂)

/-! #### Degree characterization lemma -/

private theorem degree_eq_coe_iff
    {R : Type*} [Semiring R] (p : Polynomial R) (n : ℕ) :
    p.degree = ↑n ↔ p.coeff n ≠ 0 ∧ ∀ m, n < m → p.coeff m = 0 := by
  constructor
  · intro h
    exact ⟨by rw [← Polynomial.natDegree_eq_of_degree_eq_some h]
              exact Polynomial.leadingCoeff_ne_zero.mpr (by intro h0; simp [h0] at h),
           fun m hm => (Polynomial.degree_le_iff_coeff_zero p n).mp (le_of_eq h) m
              (by exact_mod_cast hm)⟩
  · intro ⟨hne, hhi⟩
    exact le_antisymm
      ((Polynomial.degree_le_iff_coeff_zero p n).mpr
        fun m hm => hhi m (by exact_mod_cast hm))
      (Polynomial.le_degree_of_ne_zero hne)

/-- Coefficients above `natDegree` vanish: a convenient shorthand. -/
private theorem coeff_eq_zero_of_natDegree_lt
    {R : Type*} [Semiring R] (Q : Polynomial R) {n : ℕ}
    (h : Q.natDegree < n) : Q.coeff n = 0 := by
  have := Polynomial.degree_le_natDegree (p := Q)
  exact (Polynomial.degree_le_iff_coeff_zero Q Q.natDegree).mp this n
    (by exact_mod_cast h)

/-! #### Helper: coefficient vanishing above `natDegree` under ring homs -/

private theorem map_eq_zero_iff
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (Q : Polynomial R) :
    Q.map f = 0 ↔ ∀ n ≤ Q.natDegree, f (Q.coeff n) = 0 := by
  constructor
  · intro h n _
    have := congr_arg (fun p => Polynomial.coeff p n) h
    simp [Polynomial.coeff_map] at this
    exact this
  · intro h
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hn : n ≤ Q.natDegree
    · exact h n hn
    · have : Q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt Q (by omega)
      simp [this]

private theorem map_degree_eq_coe_iff
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (Q : Polynomial R) (n : ℕ) :
    (Q.map f).degree = ↑n ↔
      f (Q.coeff n) ≠ 0 ∧ ∀ m, n < m → m ≤ Q.natDegree → f (Q.coeff m) = 0 := by
  rw [degree_eq_coe_iff]
  simp only [Polynomial.coeff_map]
  constructor
  · exact fun ⟨hne, hhi⟩ => ⟨hne, fun m hm _ => hhi m hm⟩
  · intro ⟨hne, hhi⟩
    exact ⟨hne, fun m hm => by
      by_cases hm' : m ≤ Q.natDegree
      · exact hhi m hm hm'
      · have : Q.coeff m = 0 := coeff_eq_zero_of_natDegree_lt Q (by omega)
        simp [this]⟩

/-! #### Realization of `degFormula` -/

/-- The realization of `degFormula Q i` is the set of `y ∈ C^k` where
the specialized polynomial `Q.map (aeval y)` has degree `i`.

This is the formal counterpart of BPR's claim that `Reali(deg_X(Q) = i)`
partitions `C^k` according to the degree of `Q_y`. -/
theorem realization_degFormula
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i : WithBot ℕ) :
    (degFormula Q i).realization (C := C) =
      { y | (Q.map (MvPolynomial.aeval y).toRingHom).degree = i } := by
  match i with
  | ⊥ =>
    ext y
    simp only [degFormula, Formula.realization_conjList, Set.mem_setOf_eq,
      List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Formula.realization_eq_zero]
    rw [Polynomial.degree_eq_bot, map_eq_zero_iff]
    constructor
    · exact fun h n hn => h n (by omega)
    · exact fun h n hn => h n (by omega)
  | some n =>
    ext y
    simp only [degFormula, Formula.realization_and, Formula.realization_ne_zero,
      Formula.realization_conjList, Set.mem_inter_iff, Set.mem_setOf_eq,
      List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Formula.realization_eq_zero]
    rw [show (some n : WithBot ℕ) = (↑n : WithBot ℕ) from rfl,
        map_degree_eq_coe_iff]
    constructor
    · intro ⟨hne, hhi⟩
      exact ⟨hne, fun m hm hm' => by
        have hlt : m - (n + 1) < Q.natDegree - n := by omega
        have := hhi (m - (n + 1)) hlt
        rwa [show n + 1 + (m - (n + 1)) = m by omega] at this⟩
    · intro ⟨hne, hhi⟩
      exact ⟨hne, fun j hj => hhi (n + 1 + j) (by omega) (by omega)⟩

/-- The realization of `degEqFormula Q₁ Q₂` is the set of `y ∈ C^k`
where `Q₁_y` and `Q₂_y` have the same degree. -/
theorem realization_degEqFormula
    {C : Type*} [Field C] [Algebra D C]
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    (degEqFormula Q₁ Q₂).realization (C := C) =
      { y | (Q₁.map (MvPolynomial.aeval y).toRingHom).degree =
            (Q₂.map (MvPolynomial.aeval y).toRingHom).degree } := by
  ext y
  simp only [degEqFormula, Formula.realization_disjList, Set.mem_setOf_eq,
    List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, rfl | ⟨i, _, rfl⟩, hmem⟩ <;>
    simp only [Formula.realization_and, Set.mem_inter_iff,
      realization_degFormula, Set.mem_setOf_eq] at hmem <;>
    exact hmem.1.trans hmem.2.symm
  · intro h
    match hd : (Q₁.map (MvPolynomial.aeval y).toRingHom).degree with
    | ⊥ =>
      refine ⟨_, Or.inl rfl, ?_⟩
      simp only [Formula.realization_and, Set.mem_inter_iff,
        realization_degFormula, Set.mem_setOf_eq]
      exact ⟨hd, h.symm.trans hd⟩
    | some n =>
      refine ⟨_, Or.inr ⟨n, ?_, rfl⟩, ?_⟩
      · simp only [Nat.lt_succ_iff]
        have hnd := Polynomial.natDegree_eq_of_degree_eq_some hd
        have hle : (Q₁.map (MvPolynomial.aeval y).toRingHom).natDegree ≤ Q₁.natDegree :=
          Polynomial.natDegree_map_le
        exact le_trans (by omega : n ≤ Q₁.natDegree) (le_max_left _ _)
      · simp only [Formula.realization_and, Set.mem_inter_iff,
          realization_degFormula, Set.mem_setOf_eq]
        exact ⟨hd, h.symm.trans hd⟩

/-- The realization of `degNeqFormula Q₁ Q₂` is the set of `y ∈ C^k`
where `Q₁_y` and `Q₂_y` have distinct degrees. -/
theorem realization_degNeqFormula
    {C : Type*} [Field C] [Algebra D C]
    (Q₁ Q₂ : Polynomial (MvPolynomial (Fin k) D)) :
    (degNeqFormula Q₁ Q₂).realization (C := C) =
      { y | (Q₁.map (MvPolynomial.aeval y).toRingHom).degree ≠
            (Q₂.map (MvPolynomial.aeval y).toRingHom).degree } := by
  simp only [degNeqFormula, Formula.realization, realization_degEqFormula]
  ext y; simp [Set.mem_compl_iff, Set.mem_setOf_eq]

/-! #### Partition property -/

/-- The `degFormula` family partitions `C^k`: every `y` satisfies
exactly one `degFormula Q i`. (Covering part.) -/
theorem degFormula_covering
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (y : Fin k → C) :
    ∃ i : WithBot ℕ, y ∈ (degFormula Q i).realization (C := C) := by
  simp only [realization_degFormula, Set.mem_setOf_eq]
  exact ⟨_, rfl⟩

/-- The `degFormula` family partitions `C^k`: distinct degree values
give disjoint realizations. (Disjointness part.) -/
theorem degFormula_disjoint
    {C : Type*} [Field C] [Algebra D C]
    (Q : Polynomial (MvPolynomial (Fin k) D)) (i j : WithBot ℕ) (hij : i ≠ j) :
    (degFormula Q i).realization (C := C) ∩
      (degFormula Q j).realization (C := C) = ∅ := by
  simp only [realization_degFormula]
  ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro h; rw [h]; exact hij

end DegFormula

/-!
### The leaf formula C_L

Given a leaf `L` of `TRems(P, Q)`, let `B_L` be the unique path from the
root `R` to `L`. Every path ends with the `0` polynomial (the explicit
leaf). For each non-leaf node `N` on `B_L`, let `c(N)` be the unique
child of `N` in `B_L`. The **leaf formula** `C_L` is
```
  deg_X(Q) = natDeg(Pol(c(R)))
  ∧ ⋀_{N ∈ B_L, N ≠ R, c(N) ≠ 0}
      deg_X(−PRem(Pol(p(N)), Pol(N))) = natDeg(Pol(c(N)))
  ∧ deg_X(−PRem(Pol(p(L)), Pol(L's parent))) = ⊥
```
where the last conjunct says the remainder at the leaf vanishes.

We represent the path as a list of node polynomials (excluding the root `P`),
so a path `[q₁, q₂, …, qₘ, 0]` encodes:
- `q₁` is a child of the root (an element of `Tru(Q)` or `0`),
- `qᵢ₊₁` is a child of `qᵢ` (an element of `Tru(−PRem(p(qᵢ), qᵢ))` or `0`),
- `0` at the end is the explicit leaf (with `Pol = 0`).

Using `degFormula R (↑n)` (which pins the degree of `R_y` to exactly `n`)
instead of `degEqFormula R next` ensures disjointness across branches,
since the `degFormula` family partitions `C^k` by `degFormula_disjoint`.
-/

section LeafFormula

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

/-- Auxiliary: conjoin `degFormula` instances along the interior of the path.
`parent` and `cur` are consecutive nodes; `rest` is the remainder of the path.
When `next = 0` (the explicit leaf), use `degFormula R ⊥` (remainder vanishes).
When `next ≠ 0`, use `degFormula R (↑next.natDegree)` and recurse. -/
noncomputable def leafFormulaAux
    (parent cur : Polynomial (MvPolynomial (Fin k) D))
    (rest : List (Polynomial (MvPolynomial (Fin k) D))) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  match rest with
  | [] => degFormula (-(pRemMv parent cur)) ⊥
  | next :: rest' =>
    if next = 0 then
      degFormula (-(pRemMv parent cur)) ⊥
    else
      (degFormula (-(pRemMv parent cur)) (↑next.natDegree)).and
        (leafFormulaAux cur next rest')

/-- BPR's leaf formula `C_L` for a root-to-leaf path in `TRems(P, Q)`.

`path` is the list of node polynomials on the path **after the root**
(i.e., starting from a child of `P`). With the explicit `0` leaf,
every valid path is non-empty and ends with `0`. When the first element
is `0`, the formula is just `degFormula Q ⊥` (i.e. `Q_y = 0`). -/
noncomputable def leafFormula
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D))) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  match path with
  | [] => degFormula Q ⊥
  | q :: rest =>
    if q = 0 then degFormula Q ⊥
    else (degFormula Q (↑q.natDegree)).and (leafFormulaAux P q rest)

end LeafFormula

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
  · subst hR; rw [Tru, if_pos rfl] at hq; exact hq.elim
  · rw [Tru, if_neg hR] at hq
    by_cases hbase : (∃ d : D, R.leadingCoeff = MvPolynomial.C d) ∨ R.natDegree = 0
    · rw [if_pos hbase, Set.mem_singleton_iff] at hq; subst hq; rfl
    · rw [if_neg hbase, Set.mem_union, Set.mem_singleton_iff] at hq
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
  rw [Tru, if_neg hQ]
  split_ifs
  · exact Set.mem_singleton_iff.mpr rfl
  · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr rfl)

omit [IsDomain D] in
theorem Tru_empty_of_eq_zero :
    Tru (0 : Polynomial (MvPolynomial (Fin k) D)) = ∅ := by
  rw [Tru, if_pos rfl]

omit [IsDomain D] in
theorem zero_not_mem_Tru
    (Q : Polynomial (MvPolynomial (Fin k) D)) (hQ : Q ≠ 0) :
    (0 : Polynomial (MvPolynomial (Fin k) D)) ∉ Tru Q := by
  rw [Tru, if_neg hQ]; split_ifs with hbase
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
  rw [Tru, if_neg hQ] at h₁ h₂
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
private theorem Tru_covers_degrees
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
    rw [if_pos hcur]
    exact ⟨[], by simp [RoseTree.leafPaths], by
      rw [leafFormulaAux, realization_degFormula, Set.mem_setOf_eq,
          hcur, pRemMv, dif_pos rfl, neg_zero, Polynomial.map_zero, Polynomial.degree_zero]⟩
  · rw [if_neg hcur]; dsimp only
    set R := -(pRemMv parent cur) with R_def
    set children := (Tru_finite R).toFinset.toList with children_def
    set tru_subtrees := children.attach.map (fun ⟨child, _⟩ => mkTRemsNode cur child)
      with tru_subtrees_def
    -- Split on whether R_y = 0
    by_cases hRy : R.map φ = 0
    · -- R_y = 0: use the 0 child, path = [0]
      refine ⟨[0], mem_leafPaths_zero cur tru_subtrees, ?_⟩
      have : leafFormulaAux parent cur [0] = degFormula (-(pRemMv parent cur)) ⊥ := by
        unfold leafFormulaAux; exact if_pos rfl
      rw [this, realization_degFormula, Set.mem_setOf_eq, Polynomial.degree_eq_bot]
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
          show (if c = 0 then _ else _) = _; exact if_neg hc_ne
        rw [this, Formula.realization_and, Set.mem_inter_iff]
        exact ⟨by rw [realization_degFormula, Set.mem_setOf_eq]; exact hc_deg, hsp_real⟩
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
      unfold leafFormula; exact if_pos rfl
    rw [this, realization_degFormula, Set.mem_setOf_eq, Polynomial.degree_eq_bot]
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
        show (if q = 0 then _ else _) = _; exact if_neg hq_ne
      rw [this, Formula.realization_and, Set.mem_inter_iff]
      exact ⟨by rw [realization_degFormula, Set.mem_setOf_eq]; exact hq_deg, hsp_real⟩

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
    rw [mkTRemsNode, if_pos hcur] at h1 h2
    simp only [RoseTree.leafPaths, List.mem_singleton] at h1 h2
    exact absurd (h1 ▸ h2 ▸ rfl) hne
  · -- cur ≠ 0: unfold one level of mkTRemsNode
    rw [mkTRemsNode, if_neg hcur] at h1 h2; dsimp only at h1 h2
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
          show (if c1 = 0 then _ else _) = _; exact if_neg hc1_ne
        have heq2 : leafFormulaAux parent cur (c1 :: sp2) =
            (degFormula R (↑c1.natDegree)).and (leafFormulaAux cur c1 sp2) := by
          show (if c1 = 0 then _ else _) = _; exact if_neg hc1_ne
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
          simp only [leafFormulaAux, if_neg hc1_ne, Formula.realization_and]
          exact Set.inter_subset_left
        have hsub2 : (leafFormulaAux parent cur (c2 :: sp2)).realization (C := C) ⊆
            (degFormula R (↑c2.natDegree)).realization := by
          simp only [leafFormulaAux, if_neg hc2_ne, Formula.realization_and]
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
        simp only [leafFormulaAux, if_neg hc1_ne, Formula.realization_and]
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
        simp only [leafFormulaAux, if_neg hc2_ne, Formula.realization_and]
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
      simp only [leafFormula, if_neg hq1_ne, Formula.realization_and]
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
        simp only [leafFormula, if_neg hq1_ne, Formula.realization_and]
        exact Set.inter_subset_left
      have hsub2 : (leafFormula P Q (q2 :: sp2)).realization (C := C) ⊆
          (degFormula Q (↑q2.natDegree)).realization := by
        simp only [leafFormula, if_neg hq2_ne, Formula.realization_and]
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
      simp only [leafFormula, if_neg hq1_ne, Formula.realization_and]
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
      simp only [leafFormula, if_neg hq2_ne, Formula.realization_and]
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
  · subst hR; rw [Tru, if_pos rfl] at hq; exact hq.elim
  · rw [Tru, if_neg hR] at hq
    split_ifs at hq with hbase
    · rw [Set.mem_singleton_iff.mp hq]
    · rw [Set.mem_union, Set.mem_singleton_iff] at hq
      rcases hq with rfl | hq_trunc
      · rfl
      · have ih := Tru_coeff_eq (truncate (R.natDegree - 1) R) q hq_trunc j hj
        rw [ih, coeff_truncate, if_pos (le_trans hj (le_trans
          (natDegree_mem_Tru_le hq_trunc) (natDegree_truncate_le _ _)))]
termination_by R.natDegree
decreasing_by
  push Not at hbase
  have := natDegree_truncate_le (R.natDegree - 1) R
  have := hbase.2; omega

omit [IsDomain D] in
/-- From `degFormula R (↑q.natDegree)` and `q ∈ Tru R`, the specialized
polynomials are equal and the leading coefficient doesn't vanish. -/
private theorem degFormula_Tru_spec
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
    simp only [realization_degFormula, Set.mem_setOf_eq] at hy; exact hy
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
  simp only [realization_degFormula, Set.mem_setOf_eq] at hy
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
  rw [mkTRemsNode, if_neg hcur] at hsp; dsimp only at hsp
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
    simp only [leafFormulaAux, if_neg hc_ne, Formula.realization_and] at hy
    obtain ⟨hy_deg, hy_rest⟩ := hy
    -- From degFormula: R_y = c_y and φ(c.leadingCoeff) ≠ 0
    obtain ⟨hRc, hlc_c⟩ := degFormula_Tru_spec R c hc_tru hc_ne y hy_deg
    -- IH: IsGCD (pathLeafParentAux c sp').map φ (cur.map φ) (c.map φ)
    have ih := mkTRemsNode_gcd cur c hc_ne hsp' y hy_rest hlc_c
    -- pathLeafParentAux cur (c :: sp') = pathLeafParentAux c sp'
    simp only [pathLeafParentAux, if_neg hc_ne]
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
    simp only [leafFormula, if_neg hq_ne, Formula.realization_and] at hy
    obtain ⟨hy_deg, hy_rest⟩ := hy
    -- From degFormula: Q_y = q_y and φ(q.leadingCoeff) ≠ 0
    obtain ⟨hQq, hlc_q⟩ := degFormula_Tru_spec Q q hq_tru hq_ne y hy_deg
    -- By mkTRemsNode_gcd: IsGCD lp_y P_y q_y
    have ih := mkTRemsNode_gcd P q hq_ne hsp y hy_rest hlc_q
    -- pathLeafParent P (q :: sp) = pathLeafParentAux q sp
    simp only [pathLeafParent, if_neg hq_ne]
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

end Lemma_1_19

/-! ### Append-0 invariance

BPR's tree `TRems(P, Q)` always appends an explicit `0` leaf, so every
leaf path ends with `0`.  The computable tree omits this sentinel.  The
following lemmas show that `pathLeafParent(Aux)` and `leafFormula(Aux)`
are invariant under appending `0` to a path, bridging the two
representations. -/

section AppendZero

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsDomain D] in
theorem pathLeafParentAux_append_zero
    (cur : Polynomial (MvPolynomial (Fin k) D))
    (rest : List (Polynomial (MvPolynomial (Fin k) D))) :
    pathLeafParentAux cur (rest ++ [0]) = pathLeafParentAux cur rest := by
  induction rest generalizing cur with
  | nil => simp [pathLeafParentAux]
  | cons next rest' ih =>
    simp only [List.cons_append, pathLeafParentAux]
    split_ifs with h
    · rfl
    · exact ih next

omit [IsDomain D] in
theorem pathLeafParent_append_zero
    (P : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D))) :
    pathLeafParent P (path ++ [0]) = pathLeafParent P path := by
  match path with
  | [] => simp [pathLeafParent]
  | q :: rest =>
    simp only [List.cons_append, pathLeafParent]
    split_ifs with h
    · rfl
    · exact pathLeafParentAux_append_zero q rest

theorem leafFormulaAux_append_zero
    (parent cur : Polynomial (MvPolynomial (Fin k) D))
    (rest : List (Polynomial (MvPolynomial (Fin k) D))) :
    leafFormulaAux parent cur (rest ++ [0]) = leafFormulaAux parent cur rest := by
  induction rest generalizing parent cur with
  | nil => simp [leafFormulaAux]
  | cons next rest' ih =>
    simp only [List.cons_append, leafFormulaAux]
    split_ifs with h
    · rfl
    · congr 1; exact ih cur next

theorem leafFormula_append_zero
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D))) :
    leafFormula P Q (path ++ [0]) = leafFormula P Q path := by
  match path with
  | [] => simp [leafFormula]
  | q :: rest =>
    simp only [List.cons_append, leafFormula]
    split_ifs with h
    · rfl
    · congr 1; exact leafFormulaAux_append_zero P q rest

end AppendZero

/-!
### Definition 1.20: Set of possible greatest common divisors

The *set of possible greatest common divisors* of a finite family
`𝒫 ⊂ D[Y₁, …, Y_k][X]` is a finite list of pairs `(G, 𝒞)` where
`G ∈ D[Y₁, …, Y_k][X]` and `𝒞` is a formula, such that for each pair,
`y ∈ Reali(𝒞)` implies `gcd(𝒫_y) = G_y`.

Defined recursively:
- `posgcd(∅) = {(0, True)}`
- `posgcd(𝒫 ∪ {P}) = {(Pol(p(L)), 𝒞 ∧ 𝒞_L) | (Q, 𝒞) ∈ posgcd(𝒫),
   L leaf of TRems(P, Q)}`
-/

section PosGcd

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

/-- BPR Definition 1.20: the set of possible greatest common divisors
of a finite family `𝒫 ⊂ D[Y₁, …, Yₖ][X]`.

Each element is a pair `(G, 𝒞)` where `G` is a polynomial and `𝒞`
is a formula such that `y ∈ Reali(𝒞)` implies `gcd(𝒫_y) = G_y`. -/
noncomputable def posgcd :
    List (Polynomial (MvPolynomial (Fin k) D)) →
    List (Polynomial (MvPolynomial (Fin k) D) ×
      Formula (Fin k) (FieldAtom (Fin k) D))
  | [] => [(0, Formula.trueFormula)]
  | P :: rest =>
    (posgcd rest).flatMap fun (Q, C) =>
      (TRems P Q).leafPaths.map fun path =>
        (pathLeafParent P path, C.and (leafFormula P Q path))

end PosGcd

/-!
### Correctness of `posgcd`

For every `(G, 𝒞) ∈ posgcd(Ps)`:

* `posgcd_gcd`: if `y ∈ Reali(𝒞)`, then `G_y` is a GCD of `Ps_y`;
* `posgcd_covering`: every `y ∈ C^k` lies in `Reali(𝒞)` for some
  `(G, 𝒞) ∈ posgcd(Ps)` — assuming `algebraMap D C` is injective.

These are the two properties that make `posgcd` behave like a finite
case-splitting computation of the family GCD. They lift the single-pair
statements `leafFormula_gcd` (Lemma 1.19(iii)) and `leafFormula_covering`
from a single `TRems(P, Q)` tree to the iterated construction.
-/

section PosgcdCorrectness

open Classical

variable {D : Type*} [CommRing D] [IsDomain D]

omit [IsAlgClosed C] in
/-- Correctness of `posgcd` (gcd half): for each `(G, 𝒞) ∈ posgcd(Ps)`
and every `y ∈ Reali(𝒞)`, the specialization `G_y` is a GCD of the
family `Ps_y` of specialized polynomials. -/
theorem posgcd_gcd
    [Algebra D C]
    (Ps : List (Polynomial (MvPolynomial (Fin k) D)))
    {G : Polynomial (MvPolynomial (Fin k) D)}
    {𝒞 : Formula (Fin k) (FieldAtom (Fin k) D)}
    (hmem : (G, 𝒞) ∈ posgcd Ps)
    (y : Fin k → C)
    (hy : y ∈ 𝒞.realization (C := C)) :
    IsListGCD (G.map (MvPolynomial.aeval y).toRingHom)
      (Ps.map (Polynomial.map (MvPolynomial.aeval y).toRingHom)) := by
  induction Ps generalizing G 𝒞 with
  | nil =>
    simp only [posgcd, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨by simp, fun _ _ => by simp⟩
  | cons P rest ih =>
    simp only [posgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
    obtain ⟨⟨Q, C_q⟩, hQC_mem, path, hpath_mem, hG_eq, h𝒞_eq⟩ := hmem
    subst hG_eq; subst h𝒞_eq
    simp only [Formula.realization_and, Set.mem_inter_iff] at hy
    obtain ⟨hy_C, hy_leaf⟩ := hy
    have ih' := ih hQC_mem hy_C
    have hgcd := leafFormula_gcd P Q hpath_mem y hy_leaf
    set φ := (MvPolynomial.aeval (R := D) y).toRingHom
    refine ⟨?_, ?_⟩
    · intro P' hP'
      simp only [List.map_cons, List.mem_cons] at hP'
      rcases hP' with rfl | hP'
      · exact hgcd.1
      · exact dvd_trans hgcd.2.1 (ih'.1 _ hP')
    · intro E hE
      simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at hE
      obtain ⟨hE_P, hE_rest⟩ := hE
      have hE_Q : E ∣ Q.map φ := ih'.2 E hE_rest
      exact hgcd.2.2 E hE_P hE_Q

omit [IsAlgClosed C] in
/-- Correctness of `posgcd` (covering half): every `y ∈ C^k` is in
`Reali(𝒞)` for some `(G, 𝒞) ∈ posgcd(Ps)`. Requires `algebraMap D C`
injective (to invoke `leafFormula_covering`). -/
theorem posgcd_covering
    [Algebra D C]
    (hinj : Function.Injective (algebraMap D C))
    (Ps : List (Polynomial (MvPolynomial (Fin k) D)))
    (y : Fin k → C) :
    ∃ G 𝒞, (G, 𝒞) ∈ posgcd Ps ∧ y ∈ 𝒞.realization (C := C) := by
  induction Ps with
  | nil =>
    refine ⟨0, Formula.trueFormula, ?_, ?_⟩
    · simp [posgcd]
    · simp [Formula.trueFormula]
  | cons P rest ih =>
    obtain ⟨Q, C_q, hQC_mem, hy_C⟩ := ih
    obtain ⟨path, hpath_mem, hy_leaf⟩ := leafFormula_covering hinj P Q y
    refine ⟨pathLeafParent P path, C_q.and (leafFormula P Q path), ?_, ?_⟩
    · simp only [posgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
      exact ⟨⟨Q, C_q⟩, hQC_mem, path, hpath_mem, rfl, rfl⟩
    · simp only [Formula.realization_and, Set.mem_inter_iff]
      exact ⟨hy_C, hy_leaf⟩

end PosgcdCorrectness

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
  simp only [Set.mem_setOf_eq]
  rw [exists_snoc_iff_exists_eval_splitLast y Ps Qs]
  constructor
  · rintro ⟨Φ, hΦ_mem, hy_Φ⟩
    simp only [List.mem_flatMap, List.mem_map, Prod.exists] at hΦ_mem
    obtain ⟨G_1, C_1, h_mem_posgcd, path, hpath_mem, hΦ_eq⟩ := hΦ_mem
    subst hΦ_eq
    simp only [Formula.realization_and, Set.mem_inter_iff,
      realization_degNeqFormula, Set.mem_setOf_eq] at hy_Φ
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
        realization_degNeqFormula, Set.mem_setOf_eq]
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
  simp only [Set.mem_setOf_eq, Set.mem_union]
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
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_append]
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
      simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_cons]
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
    simp only [Zer, Set.mem_setOf_eq, Finset.mem_toList, List.not_mem_nil,
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
    simp only [Zer, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall,
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

/-!
### Exercise 1.9

Find the conditions on `(a, b, c)` for:
(a) `P = aX² + bX + c` and `P' = 2aX + b` to have a common root; and
(b) `P = aX² + bX + c` to have a root which is not a root of `P'`.

Both conditions are computed by the concrete projection algorithm
`Azurite.azProjectQFAt`, which eliminates the variable `X` (represented
as `d`) from a quantifier-free formula. The resulting quantifier-free
formulas in `(a, b, c)` are verified by `#guard` tests in
`Azurite/AzFormula/ProjBasic.lean`:

- (a) projects `d` from `a*d² + b*d + c = 0 ∧ 2*a*d + b = 0`.
- (b) projects `d` from `a*d² + b*d + c = 0 ∧ 2*a*d + b ≠ 0`.
-/

end Azurite.BPR

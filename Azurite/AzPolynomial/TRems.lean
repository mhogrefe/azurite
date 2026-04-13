import Azurite.AzPolynomial.Tru
import Azurite.AzPolynomial.PRem
import Azurite.AzPolynomial.Equiv.PRem
import Azurite.AzPolynomial.Equiv.Algebra

/-!
# Tree of possible signed pseudo-remainder sequences `TRems(P, Q)`

Computable version of BPR's `TRems(P, Q)` for
`P, Q ∈ D[Y₁, …, Y_k][X]`, represented as
`AzPolynomial (AzMvPolynomial k D ord)`.

Two functions are provided:

* `tremsTree P Q` — builds the full `RoseTree`, useful for debugging.
* `tremsLeafParents P Q` — returns only the leaf-parent polynomials, which is the
  information needed by later algorithms.
-/

namespace Azurite.AzPolynomial

open AzMvPolynomial

variable {k : ℕ} {D : Type _} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-! ### Rose tree -/

/-- Rose tree: a node labelled by `α` with a list of subtrees. -/
inductive RoseTree (α : Type*) where
  | node : α → List (RoseTree α) → RoseTree α

/-- The label at the root of a `RoseTree`. -/
def RoseTree.root : RoseTree α → α
  | .node a _ => a

/-- The children of a `RoseTree` node. -/
def RoseTree.children : RoseTree α → List (RoseTree α)
  | .node _ cs => cs

/-- Collect all leaf labels (nodes with no children). -/
def RoseTree.leaves : RoseTree α → List α
  | .node a [] => [a]
  | .node _ cs => cs.flatMap RoseTree.leaves

/-! ### Supporting lemmas for termination -/

private theorem natDegree_neg (p : AzPolynomial (AzMvPolynomial k D ord)) :
    (-p).natDegree = p.natDegree := by
  simp only [natDegree]
  congr 1
  show (-p).coeffs.size = p.coeffs.size
  change (mapZeroInjective _ _ p).coeffs.size = p.coeffs.size
  simp [mapZeroInjective]

private theorem natDegree_pRem_lt
    (P Q : AzPolynomial (AzMvPolynomial k D ord))
    (hQ : Q ≠ 0) (hR : pRem P Q ≠ 0) :
    (pRem P Q).natDegree < Q.natDegree := by
  have hQP : AzPolynomial.toPoly Q ≠ 0 := by
    intro h; exact hQ (toPoly_inj.mp (by rw [h, toPoly_zero]))
  have hRP : AzPolynomial.toPoly (pRem P Q) ≠ 0 := by
    intro h; exact hR (toPoly_inj.mp (by rw [h, toPoly_zero]))
  have hdeg := degree_toPoly_pRem_lt P Q hQP
  have := Polynomial.natDegree_lt_natDegree hRP hdeg
  rwa [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly] at this

private theorem natDegree_mem_tru_le
    (p : AzPolynomial (AzMvPolynomial k D ord))
    (child : AzPolynomial (AzMvPolynomial k D ord))
    (hmem : child ∈ tru p) : child.natDegree ≤ p.natDegree := by
  unfold tru at hmem
  split_ifs at hmem with h0 hbase
  · simp at hmem
  · rw [List.mem_singleton.mp hmem]
  · rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact le_refl _
    · have ih := natDegree_mem_tru_le _ child hmem
      have := natDegree_truncate_le (p.natDegree - 1) p
      omega
termination_by p.natDegree
decreasing_by
  have hQpos : 0 < p.natDegree := by
    simp only [Bool.or_eq_true, beq_iff_eq] at *
    omega
  have h := natDegree_truncate_le (p.natDegree - 1) p
  omega

/-- Shared termination argument for `mkTRemsNode` and `mkTRemsLeafParentsAux`. -/
theorem natDegree_child_lt_of_mem_tru_neg_pRem
    {parentPol curPol child : AzPolynomial (AzMvPolynomial k D ord)}
    (h_ne : curPol ≠ 0)
    (hmem : child ∈ tru (-(pRem parentPol curPol))) :
    child.natDegree < curPol.natDegree := by
  by_cases h4 : pRem parentPol curPol = 0
  · -- pRem = 0 ⇒ tru(-0) = tru 0 = [], contradicting hmem
    rw [h4, neg_zero] at hmem; unfold tru at hmem; simp at hmem
  · have h1 := natDegree_mem_tru_le _ child hmem
    have h5 := natDegree_pRem_lt parentPol curPol h_ne h4
    have h6 : (-(pRem parentPol curPol)).natDegree =
        (pRem parentPol curPol).natDegree := natDegree_neg _
    omega

/-! ### Building the tree -/

/-- Build the subtree of `TRems` rooted at `curPol`, whose parent
holds `parentPol`. Terminates because `natDegree` strictly decreases
through `pRem` and `tru`. -/
private def mkTRemsNode
    (parentPol curPol : AzPolynomial (AzMvPolynomial k D ord)) :
    RoseTree (AzPolynomial (AzMvPolynomial k D ord)) :=
  if _h : curPol == 0 then .node curPol []
  else
    let next := -(pRem parentPol curPol)
    let children := tru next
    .node curPol (children.attach.map fun ⟨child, _hmem⟩ =>
      mkTRemsNode curPol child)
termination_by curPol.natDegree
decreasing_by
  simp only [beq_iff_eq] at _h
  exact natDegree_child_lt_of_mem_tru_neg_pRem _h _hmem

/-- BPR's **tree of possible signed pseudo-remainder sequences**
`TRems(P, Q)` — full tree, useful for debugging.

The root contains `P`; its children are the elements of `tru(Q)`;
each deeper level unfolds via `tru(−pRem(…))`. A node whose
polynomial is `0` is a leaf. -/
def tremsTree
    (P Q : AzPolynomial (AzMvPolynomial k D ord)) :
    RoseTree (AzPolynomial (AzMvPolynomial k D ord)) :=
  .node P ((tru Q).map (mkTRemsNode P))

/-- Collect the **leaf-parent polynomials** of `TRems(P, Q)`:
the last nonzero polynomial in each branch. In BPR's terminology
a leaf has `Pol(N) = 0`; this function returns `Pol(p(L))`, the
parent of each such leaf. More efficient than building the full
tree when only the leaf parents are needed. -/
def mkTRemsLeafParentsAux
    (parentPol curPol : AzPolynomial (AzMvPolynomial k D ord)) :
    List (AzPolynomial (AzMvPolynomial k D ord)) :=
  if _h : curPol == 0 then [curPol]
  else
    let next := -(pRem parentPol curPol)
    let children := tru next
    match children with
    | [] => [curPol]
    | _ => children.attach.flatMap fun ⟨child, _hmem⟩ =>
        mkTRemsLeafParentsAux curPol child
termination_by curPol.natDegree
decreasing_by
  simp only [beq_iff_eq] at _h
  exact natDegree_child_lt_of_mem_tru_neg_pRem _h _hmem

/-- The **leaf-parent polynomials** of `TRems(P, Q)`: the last nonzero
polynomial in each branch. In BPR a leaf has `Pol(N) = 0`; this
returns `Pol(p(L))` for each leaf `L`. -/
def tremsLeafParents
    (P Q : AzPolynomial (AzMvPolynomial k D ord)) :
    List (AzPolynomial (AzMvPolynomial k D ord)) :=
  (tru Q).flatMap (mkTRemsLeafParentsAux P)

/-! ### Tests -/

section Tests

private abbrev MvInt3 := AzMvPolynomial 3 ℤ .Degrevlex
private instance : Fact (3 ≤ 26) := ⟨by omega⟩
private def p (s : String) : AzPolynomial MvInt3 :=
  (AzPolynomial.parseStrMvCoeffWith (AbcVar 3) (n := 3) (R := ℤ)
    (ord := .Degrevlex) s).getD 0
private def s (q : AzPolynomial MvInt3) : String :=
  q.toStrMvCoeffWith (AbcVar 3)

-- Q = 0: tru(0) = [], so tremsLeafParents has no branches
#guard tremsLeafParents (p "x+(a)") (p "0") == []

-- Q = 0: tree root is P with no children
#guard (tremsTree (p "x+(a)") (p "0")).root == p "x+(a)"
#guard (tremsTree (p "x+(a)") (p "0")).children.length == 0

-- Q is a nonzero constant: tru(Q) = [Q], pRem(P, Q) = 0,
-- so the Q-node has no further children ⇒ leaf is Q itself.
#guard (tremsLeafParents (p "x+(a)") (p "(1)")).map s == ["(1)"]

-- P = x^2+(b), Q = x+(a): leading coeff of Q is constant (1),
-- so tru(Q) = [Q]. One branch, pRem = (a^2+b), which has degree 0.
-- Then pRem(Q, -(a^2+b)) = 0 ⇒ leaf.
#guard (tremsLeafParents (p "x^2+(b)") (p "x+(a)")).length == 1

-- Non-constant leading coefficient: tru branches.
-- tru((a)*x+(b)) = [(a)*x+(b), (b)]  →  two branches
#guard (tru (p "(a)*x+(b)")).map s == ["(a)*x+(b)", "(b)"]

-- Full tree structure: root label
#guard (tremsTree (p "(a)*x^2+(b)*x+(1)") (p "(a)*x+(b)")).root
  == p "(a)*x^2+(b)*x+(1)"

-- Number of children of root = length of tru(Q)
#guard (tremsTree (p "(a)*x^2+(b)*x+(1)") (p "(a)*x+(b)")).children.length == 2

/-! #### BPR Example 1.17

`P = X⁴ + aX² + bX + c`, `Q = 4X³ + 2aX + b` (the derivative of `P`).

The tree `TRems(P, Q)` has the structure:
```
P ─── Q ─┬─ (−8a)X² + (−12b)X + (−16c)
         │   ├─ (−128a³ − 576b² + 512ac)X + (−64a²b − 768bc)
         │   │   └─ −65536a⁵b² + 262144a⁶c − … [LEAF]
         │   └─ (−64a²b − 768bc) [LEAF]
         ├─ (−12b)X + (−16c)
         │   └─ −20736b⁵ + 55296ab³c + 196608bc³ [LEAF]
         └─ (−16c) [LEAF]
```
Four leaves correspond to the four possible signed pseudo-remainder
sequences, branching at each level where the leading coefficient of a
truncation is non-constant.
-/

-- Helper: follow a path through the tree
private def nodeAt (t : RoseTree (AzPolynomial MvInt3)) : List Nat → AzPolynomial MvInt3
  | [] => t.root
  | i :: rest => nodeAt (t.children.getD i (.node 0 [])) rest

private def childCount (t : RoseTree (AzPolynomial MvInt3)) : List Nat → Nat
  | [] => t.children.length
  | i :: rest => childCount (t.children.getD i (.node 0 [])) rest

private def ex117tree :=
  tremsTree (p "x^4+(a)*x^2+(b)*x+(c)") (p "(4)*x^3+(2*a)*x+(b)")

-- Root: P
#guard s (nodeAt ex117tree []) == "x^4+(a)*x^2+(b)*x+(c)"
#guard childCount ex117tree [] == 1

-- Level 1: Q (leading coeff 4 is constant, so tru(Q) = [Q])
#guard s (nodeAt ex117tree [0]) == "(4)*x^3+(2*a)*x+(b)"
#guard childCount ex117tree [0] == 3

-- Level 2: tru(−pRem(P, Q)) — leading coeff (−8a) is non-constant,
-- so tru produces three truncations (degree 2, 1, 0).
#guard s (nodeAt ex117tree [0, 0]) ==
  "(-8*a)*x^2+(-12*b)*x+(-16*c)"
#guard s (nodeAt ex117tree [0, 1]) ==
  "(-12*b)*x+(-16*c)"
#guard s (nodeAt ex117tree [0, 2]) ==
  "(-16*c)"
#guard childCount ex117tree [0, 0] == 2
#guard childCount ex117tree [0, 1] == 1
#guard childCount ex117tree [0, 2] == 0   -- LEAF

-- Level 3 from [0,0]: tru(−pRem(Q, (−8a)X²+…)) —
-- leading coeff (−128a³ − 576b² + 512ac) is non-constant, two truncations.
#guard s (nodeAt ex117tree [0, 0, 0]) ==
  "(-128*a^3-576*b^2+512*a*c)*x+(-64*a^2*b-768*b*c)"
#guard s (nodeAt ex117tree [0, 0, 1]) ==
  "(-64*a^2*b-768*b*c)"
#guard childCount ex117tree [0, 0, 0] == 1
#guard childCount ex117tree [0, 0, 1] == 0   -- LEAF

-- Level 3 from [0,1]: −pRem(Q, (−12b)X+(−16c)) is degree 0 → one truncation.
#guard s (nodeAt ex117tree [0, 1, 0]) ==
  "(-20736*b^5+55296*a*b^3*c+196608*b*c^3)"
#guard childCount ex117tree [0, 1, 0] == 0   -- LEAF

-- Level 4: the deepest leaf.
#guard s (nodeAt ex117tree [0, 0, 0, 0]) ==
  "(-65536*a^5*b^2+262144*a^6*c-442368*a^2*b^4+2359296*a^3*b^2*c-2097152*a^4*c^2+4194304*a^2*c^3)"
#guard childCount ex117tree [0, 0, 0, 0] == 0   -- LEAF

-- All four leaf parents, collected by tremsLeafParents
#guard (tremsLeafParents (p "x^4+(a)*x^2+(b)*x+(c)")
    (p "(4)*x^3+(2*a)*x+(b)")).map s ==
  [ "(-65536*a^5*b^2+262144*a^6*c-442368*a^2*b^4+2359296*a^3*b^2*c-2097152*a^4*c^2+4194304*a^2*c^3)",
    "(-64*a^2*b-768*b*c)",
    "(-20736*b^5+55296*a*b^3*c+196608*b*c^3)",
    "(-16*c)" ]

end Tests

end Azurite.AzPolynomial

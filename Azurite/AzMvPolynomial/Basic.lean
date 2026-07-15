/-
  Multivariate polynomials (Fin-indexed).  The math core fixes the variable
  type to `Fin n`; no `Var` / `LinearOrder σ` typeclass is referenced.
-/
import Azurite.AzMvPolynomial.Monomial
import Azurite.AzMvPolynomial.MonicMonomialOrder

namespace Azurite

open MonicMonomial Monomial

/-- A multivariate polynomial over `Fin n`: a sorted array of
    `Monomial n R ord`.  The monic parts of the monomials are required
    to be in strictly descending order (which implies they are distinct).
    An empty array represents the zero polynomial. -/
structure AzMvPolynomial (n : ℕ) (R : Type _) [Semiring R]
    (ord : MonomialOrder := .Degrevlex) where
  /-- The array of monomials, sorted so that leading terms come first. -/
  terms : Array (Monomial n R ord)
  /-- All pairs of monic parts are strictly decreasing (descending order). -/
  sorted : terms.toList.Pairwise (fun a b => a.monic > b.monic)

instance {R : Type _} [Semiring R] [DecidableEq R] {n : ℕ} {ord : MonomialOrder} :
    DecidableEq (AzMvPolynomial n R ord) :=
  fun a b => by
    have : DecidableEq (Array (Monomial n R ord)) := inferInstance
    cases a; cases b
    simp only [AzMvPolynomial.mk.injEq]
    exact this _ _

namespace AzMvPolynomial

variable {R : Type _} [Semiring R] {n : ℕ} {ord : MonomialOrder}

/-- The zero polynomial (empty term list). -/
def zero : AzMvPolynomial n R ord := ⟨#[], List.Pairwise.nil⟩

instance : Zero (AzMvPolynomial n R ord) := ⟨zero⟩

/-- A polynomial is zero iff its term array is empty. -/
@[simp] theorem zero_terms : (0 : AzMvPolynomial n R ord).terms = #[] := rfl

/-- Number of terms in the polynomial. -/
def numTerms (p : AzMvPolynomial n R ord) : ℕ := p.terms.size

/-- The leading monomial (largest monic part), if the polynomial is nonzero. -/
def leadTerm (p : AzMvPolynomial n R ord) : Option (Monomial n R ord) :=
  p.terms[0]?

/-- The leading monic monomial, if the polynomial is nonzero. -/
def leadMonic (p : AzMvPolynomial n R ord) : Option (MonicMonomial n ord) :=
  p.leadTerm.map Monomial.monic

/-- The leading coefficient, if the polynomial is nonzero. -/
def leadCoeff (p : AzMvPolynomial n R ord) : Option {c : R // c ≠ 0} :=
  p.leadTerm.map Monomial.coeff

/-- Construct a polynomial from a single monomial. -/
def ofMonomial (m : Monomial n R ord) : AzMvPolynomial n R ord :=
  ⟨#[m], List.pairwise_singleton _ _⟩

/-- The constant polynomial `1`.  Returns `0` when `1 = 0` in the
    coefficient ring (trivial ring). -/
def one [DecidableEq R] : AzMvPolynomial n R ord :=
  if h : (1 : R) = 0 then 0
  else ofMonomial (Monomial.one h)

instance [DecidableEq R] : One (AzMvPolynomial n R ord) := ⟨one⟩

/-- Constructs a constant polynomial with value `c`.
    Returns `0` when `c = 0`. -/
def C [DecidableEq R] (c : R) : AzMvPolynomial n R ord :=
  if h : c = 0 then 0
  else ofMonomial ⟨⟨c, h⟩, MonicMonomial.one⟩

/-- The polynomial consisting of a single variable `i : Fin n`.
    Returns `0` when `1 = 0` in the trivial ring. -/
def X [DecidableEq R] (i : Fin n) : AzMvPolynomial n R ord :=
  if h : (1 : R) = 0 then 0
  else ofMonomial ⟨⟨1, h⟩, MonicMonomial.ofVar i⟩

/-- The total degree of the polynomial (maximum total degree among its terms),
    or 0 for the zero polynomial. -/
def totalDegree (p : AzMvPolynomial n R ord) : ℕ :=
  p.terms.foldl (fun acc m => max acc m.totalDegree) 0

/-- A multivariate polynomial is *constant* when it is either zero or a
    single term whose monic monomial is `1` (all exponents zero).
    Equivalently, it lies in the image of `C : R → AzMvPolynomial n R`. -/
def isConstant (p : AzMvPolynomial n R ord) : Bool :=
  match p.terms.toList with
  | [] => true
  | [m] => m.monic == MonicMonomial.one
  | _ :: _ :: _ => false

/-! ### withOrder: changing the monomial ordering -/

private theorem pairwise_gt_of_pairwise_ge_nodup
    {l : List (Monomial n R ord)}
    (hp : l.Pairwise (fun a b => a.monic ≥ b.monic))
    (hnd : l.Pairwise (fun a b => a.monic ≠ b.monic)) :
    l.Pairwise (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp hnd ⊢
    exact ⟨fun b hb => lt_of_le_of_ne (hp.1 b hb) (Ne.symm (hnd.1 b hb)),
           ih hp.2 hnd.2⟩

/-- Comparator for sorting monomials in descending order by monic part
    (greater or equal). Uses the computable `compareExponents`. -/
def monicGeq {ord : MonomialOrder}
    (a b : Monomial n R ord) : Bool :=
  !(MonomialOrder.compareExponents ord a.monic.exponents b.monic.exponents == Ordering.lt)

theorem monicGeq_iff_ge {ord : MonomialOrder}
    (a b : Monomial n R ord) :
    monicGeq a b = true ↔ a.monic ≥ b.monic := by
  unfold monicGeq
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq, ge_iff_le]
  constructor
  · intro h; by_contra hlt; exact h (not_le.mp hlt)
  · intro h hlt; exact absurd hlt (not_lt.mpr h)

theorem monicGeq_trans {ord : MonomialOrder}
    (a b c : Monomial n R ord) :
    monicGeq a b = true → monicGeq b c = true → monicGeq a c = true := by
  rw [monicGeq_iff_ge, monicGeq_iff_ge, monicGeq_iff_ge]
  exact fun hab hbc => le_trans hbc hab

theorem monicGeq_total {ord : MonomialOrder}
    (a b : Monomial n R ord) :
    (monicGeq a b || monicGeq b a) = true := by
  simp only [Bool.or_eq_true, monicGeq_iff_ge]
  exact le_total b.monic a.monic

private theorem withOrder_monic_ne_of_perm
    (p : AzMvPolynomial n R ord) (ord' : MonomialOrder)
    (l : List (Monomial n R ord'))
    (hperm : l.Perm (p.terms.toList.map (fun m => m.withOrder ord'))) :
    l.Pairwise (fun a b => a.monic ≠ b.monic) := by
  apply List.Pairwise.perm _ hperm.symm (fun h => Ne.symm h)
  rw [List.pairwise_map]
  exact p.sorted.imp (fun {a b} hab heq => by
    apply ne_of_gt hab
    simp only [Monomial.withOrder, MonicMonomial.withOrder] at heq
    exact MonicMonomial.ext (MonicMonomial.mk.inj heq))

/-- Convert a polynomial to use a different monomial ordering.
    If the order is unchanged, this is the identity.
    Otherwise, terms are re-sorted in descending order under the new ordering
    using O(n log n) merge sort. -/
def withOrder (p : AzMvPolynomial n R ord) (ord' : MonomialOrder) :
    AzMvPolynomial n R ord' :=
  if h : ord = ord' then
    h ▸ p
  else
    let mapped := p.terms.toList.map (fun m => m.withOrder ord')
    let sorted := mapped.mergeSort monicGeq
    ⟨sorted.toArray, by
      rw [List.toList_toArray]
      have hperm : sorted.Perm mapped := List.mergeSort_perm mapped monicGeq
      have hge : sorted.Pairwise (fun a b => a.monic ≥ b.monic) :=
        (List.pairwise_mergeSort monicGeq_trans monicGeq_total mapped).imp
          (fun h => (monicGeq_iff_ge _ _).mp h)
      exact pairwise_gt_of_pairwise_ge_nodup hge
        (withOrder_monic_ne_of_perm p ord' sorted hperm)⟩

/-- Construct a polynomial from an array of monomials with pairwise-distinct
    monic parts. The monomials are sorted into descending order automatically.
    The distinctness proof can typically be discharged with `by decide`. -/
def ofMonomials (ms : Array (Monomial n R ord))
    (hdistinct : ms.toList.Pairwise (fun a b => a.monic ≠ b.monic)) :
    AzMvPolynomial n R ord :=
  let sorted := ms.toList.mergeSort monicGeq
  ⟨sorted.toArray, by
    rw [List.toList_toArray]
    have hperm : sorted.Perm ms.toList := List.mergeSort_perm ms.toList monicGeq
    have hge : sorted.Pairwise (fun a b => a.monic ≥ b.monic) :=
      (List.pairwise_mergeSort monicGeq_trans monicGeq_total ms.toList).imp
        (fun h => (monicGeq_iff_ge _ _).mp h)
    have hne : sorted.Pairwise (fun a b => a.monic ≠ b.monic) :=
      hdistinct.perm hperm.symm (fun h => Ne.symm h)
    exact pairwise_gt_of_pairwise_ge_nodup hge hne⟩

/-- Check that adjacent elements in a sorted list have distinct monic parts.
    This is O(n), vs O(n²) for `Pairwise`. -/
def adjacentDistinct : List (Monomial n R ord) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a.monic != b.monic && adjacentDistinct (b :: rest)

theorem pairwise_gt_of_ge_adjacent_ne
    {l : List (Monomial n R ord)}
    (hge : l.Pairwise (fun a b => a.monic ≥ b.monic))
    (hadj : adjacentDistinct l = true) :
    l.Pairwise (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hge ⊢
    have htail_adj : adjacentDistinct t = true := by
      match t, hadj with
      | [], _ => rfl
      | [_], _ => rfl
      | _ :: _ :: _, hadj' =>
        simp only [adjacentDistinct, Bool.and_eq_true] at hadj' ⊢
        exact hadj'.2
    have htail_gt := ih hge.2 htail_adj
    constructor
    · intro b hb
      match t, hge, hadj, htail_gt with
      | [], _, _, _ => exact absurd hb (by simp)
      | c :: rest, ⟨hrel, _⟩, hadj', htail_gt' =>
        simp only [adjacentDistinct, Bool.and_eq_true, bne_iff_ne, ne_eq] at hadj'
        have hac_gt : a.monic > c.monic :=
          lt_of_le_of_ne (hrel c (List.mem_cons_self ..)) (Ne.symm hadj'.1)
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hac_gt
        · have hcb : c.monic ≥ b.monic := by
            rw [List.pairwise_cons] at htail_gt'
            exact le_of_lt (htail_gt'.1 b hb')
          exact lt_of_le_of_lt hcb hac_gt
    · exact htail_gt

/-- Construct a polynomial from an array of monomials, sorting and checking
    for duplicate monic parts in O(n log n) time.
    Returns `none` if two monomials share the same monic part. -/
def ofMonomials? (ms : Array (Monomial n R ord)) :
    Option (AzMvPolynomial n R ord) :=
  let sorted := ms.toList.mergeSort monicGeq
  if hadj : adjacentDistinct sorted then
    some ⟨sorted.toArray, by
      rw [List.toList_toArray]
      have hge : sorted.Pairwise (fun a b => a.monic ≥ b.monic) :=
        (List.pairwise_mergeSort monicGeq_trans monicGeq_total ms.toList).imp
          (fun h => (monicGeq_iff_ge _ _).mp h)
      exact pairwise_gt_of_ge_adjacent_ne hge hadj⟩
  else none

end AzMvPolynomial

end Azurite

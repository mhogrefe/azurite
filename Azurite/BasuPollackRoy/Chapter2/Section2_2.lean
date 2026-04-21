import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.Basic
import Mathlib.Data.Sign.Basic

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 2: Real Closed Fields
## Section 2.2: Real Root Counting

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

## Notation 2.32 (Sign variations)

The number of sign variations `Var(a)` in a sequence `a = a₀, …, aₚ` of
elements of `R ∖ {0}` is defined by induction on `p`:

- `Var(a₀) = 0`,
- `Var(a₀, …, aₚ) = Var(a₁, …, aₚ) + 1` if `a₀ · a₁ < 0`,
- `Var(a₀, …, aₚ) = Var(a₁, …, aₚ)`     if `a₀ · a₁ > 0`.

This definition extends to any finite sequence `a` of elements of `R` by
considering the finite sequence `b` obtained by dropping the zeros from `a`
and setting `Var(a) := Var(b)`, with `Var(∅) = 0`.

We formalise `a` as a `List R`. The helper `varNonzero` implements the
pairwise recursion over a list whose zeros have already been dropped, and
`Var` is the extension to arbitrary lists, obtained by filtering out zeros.

## `Var(P)` and `pos(P)` for a univariate polynomial

For `P = aₚ Xᵖ + ⋯ + a₀ ∈ R[X]`, BPR writes `Var(P)` for the number of sign
variations in the coefficient sequence `a₀, …, aₚ` and `pos(P)` for the
number of positive real roots of `P`, counted with multiplicity.

## Notation 2.34 (Sign variations in a sequence of polynomials at `a`)

Let `P = P₀, …, P_d` be a sequence of polynomials in `R[X]` and let
`a ∈ R ∪ {−∞, +∞}`. The number of sign variations of `P` at `a`, denoted
`Var(P; a)`, is `Var(P₀(a), …, P_d(a))`. At `a = ±∞` the signs to consider
are those of the leading monomials (Proposition 2.4): for `x → +∞` the sign
of `P_i(x)` stabilises to `sign(leadingCoeff P_i)`, and for `x → −∞` to
`sign((−1)^(natDegree P_i) · leadingCoeff P_i)`.

## `Var(P; a, b)` and `num(P; (a, b])`

For `a, b ∈ R ∪ {−∞, +∞}`:
- `Var(P; a, b) = Var(P; a) − Var(P; b)` is the change in sign-variation
  count between the two endpoints (an integer, since `Var(P; a)` may be
  less than `Var(P; b)`).
- `num(P; (a, b])` is the number of roots of `P` in the half-open interval
  `(a, b]`, counted with multiplicity.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*}

/-- Count of sign variations in a list, realised by iterating over adjacent
    pairs. Intended to be applied to a list whose zeros have been removed;
    `Var` handles zero-dropping and calls this. -/
def varNonzero [Mul R] [Zero R] [LT R] [DecidableLT R] : List R → ℕ
  | []            => 0
  | [_]           => 0
  | a :: b :: rest =>
      (if a * b < 0 then 1 else 0) + varNonzero (b :: rest)

/-- **BPR Notation 2.32.** The number of sign variations `Var(a)` in a
    finite sequence `a` of elements of an ordered ring `R`. Zeros are
    dropped from `a` before counting adjacent pairs of opposite signs. -/
def Var [Mul R] [Zero R] [DecidableEq R] [LT R] [DecidableLT R]
    (a : List R) : ℕ :=
  varNonzero (a.filter (· ≠ 0))

section

variable [Mul R] [Zero R] [LT R] [DecidableLT R]

@[simp] lemma varNonzero_nil : varNonzero ([] : List R) = 0 := rfl

@[simp] lemma varNonzero_singleton (a : R) : varNonzero [a] = 0 := rfl

lemma varNonzero_cons_cons (a b : R) (rest : List R) :
    varNonzero (a :: b :: rest) =
      (if a * b < 0 then 1 else 0) + varNonzero (b :: rest) := rfl

end

section

variable [Mul R] [Zero R] [DecidableEq R] [LT R] [DecidableLT R]

@[simp] lemma Var_nil : Var ([] : List R) = 0 := rfl

lemma Var_eq_varNonzero_filter (a : List R) :
    Var a = varNonzero (a.filter (· ≠ 0)) := rfl

/-- If every element of `a` is nonzero, then filtering zeros is a no-op and
    `Var a` agrees with the pairwise count `varNonzero a`. -/
lemma Var_of_forall_ne_zero {a : List R} (h : ∀ x ∈ a, x ≠ 0) :
    Var a = varNonzero a := by
  unfold Var
  congr 1
  exact List.filter_eq_self.mpr (fun x hx => by simpa using h x hx)

end

section

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `varNonzero` vanishes on a list whose entries are all nonneg: every
    adjacent product is nonneg, so no sign variation ever triggers. -/
lemma varNonzero_eq_zero_of_forall_nonneg :
    ∀ {l : List R}, (∀ x ∈ l, 0 ≤ x) → varNonzero l = 0
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
      rw [varNonzero_cons_cons]
      have ha := h a (List.mem_cons_self)
      have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hab : ¬ a * b < 0 := not_lt.mpr (mul_nonneg ha hb)
      rw [if_neg hab, zero_add]
      exact varNonzero_eq_zero_of_forall_nonneg
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `varNonzero` vanishes on a list whose entries are all nonpos. -/
lemma varNonzero_eq_zero_of_forall_nonpos :
    ∀ {l : List R}, (∀ x ∈ l, x ≤ 0) → varNonzero l = 0
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
      rw [varNonzero_cons_cons]
      have ha := h a (List.mem_cons_self)
      have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hab : ¬ a * b < 0 := not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos ha hb)
      rw [if_neg hab, zero_add]
      exact varNonzero_eq_zero_of_forall_nonpos
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `Var` vanishes on a list whose entries are all nonneg. -/
lemma Var_eq_zero_of_forall_nonneg {l : List R} (h : ∀ x ∈ l, 0 ≤ x) :
    Var l = 0 := by
  unfold Var
  exact varNonzero_eq_zero_of_forall_nonneg
    (fun x hx => h x (List.mem_of_mem_filter hx))

/-- `Var` vanishes on a list whose entries are all nonpos. -/
lemma Var_eq_zero_of_forall_nonpos {l : List R} (h : ∀ x ∈ l, x ≤ 0) :
    Var l = 0 := by
  unfold Var
  exact varNonzero_eq_zero_of_forall_nonpos
    (fun x hx => h x (List.mem_of_mem_filter hx))

omit [IsStrictOrderedRing R] in
/-- Prepending a zero to a list does not change its variation count. -/
@[simp] lemma Var_zero_cons (l : List R) : Var ((0 : R) :: l) = Var l := by
  unfold Var
  rw [List.filter_cons]
  simp

end

section

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If two lists of nonzero elements have pointwise matching signs, their
    `varNonzero` counts agree. The `a * b < 0` comparison depends only on
    `sign a * sign b` (via `sign_mul`), so sign-map equality is enough. -/
lemma varNonzero_congr_sign : ∀ {l₁ l₂ : List R},
    l₁.map SignType.sign = l₂.map SignType.sign →
    varNonzero l₁ = varNonzero l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons => simp at h
  | cons a rest₁ ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp at h
    | cons a' rest₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨ha, hrest⟩ := h
      cases rest₁ with
      | nil =>
        cases rest₂ with
        | nil => rfl
        | cons => simp at hrest
      | cons b rest₁' =>
        cases rest₂ with
        | nil => simp at hrest
        | cons b' rest₂' =>
          simp only [List.map_cons, List.cons.injEq] at hrest
          obtain ⟨hb, hrest'⟩ := hrest
          rw [varNonzero_cons_cons, varNonzero_cons_cons]
          have h_iff : (a * b < 0) ↔ (a' * b' < 0) := by
            have hs : SignType.sign (a * b) = SignType.sign (a' * b') := by
              rw [sign_mul, sign_mul, ha, hb]
            refine ⟨fun hab => ?_, fun hab => ?_⟩
            · rw [sign_eq_neg_one_iff.mpr hab] at hs
              exact sign_eq_neg_one_iff.mp hs.symm
            · rw [sign_eq_neg_one_iff.mpr hab] at hs
              exact sign_eq_neg_one_iff.mp hs
          have hif_eq : (if a * b < 0 then (1 : ℕ) else 0) =
              (if a' * b' < 0 then 1 else 0) := by
            by_cases hab : a * b < 0
            · rw [if_pos hab, if_pos (h_iff.mp hab)]
            · rw [if_neg hab, if_neg (fun hc => hab (h_iff.mpr hc))]
          rw [hif_eq]
          congr 1
          apply ih
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨hb, hrest'⟩

/-- `Var` is invariant under operations that preserve the sign pattern of
    the list. -/
lemma Var_congr_sign {l₁ l₂ : List R}
    (h : l₁.map SignType.sign = l₂.map SignType.sign) :
    Var l₁ = Var l₂ := by
  unfold Var
  apply varNonzero_congr_sign
  -- Goal: (l₁.filter (· ≠ 0)).map sign = (l₂.filter (· ≠ 0)).map sign
  -- Strategy: show this equals (l_i.map sign).filter (· ≠ 0), then use h.
  have key : ∀ (l : List R),
      (l.filter (· ≠ 0)).map SignType.sign =
      (l.map SignType.sign).filter (· ≠ 0) := by
    intro l
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x _
    simp only [Function.comp_apply, decide_not, sign_eq_zero_iff]
  rw [key, key, h]

end

/-! ### Worked example (BPR p. 43)

`Var(1, −1, 2, 0, 0, 3, 4, −5, −2, 0, 3) = 4`: after dropping zeros the
subsequence is `1, −1, 2, 3, 4, −5, −2, 3`, whose sign-change pairs are
`(1, −1)`, `(−1, 2)`, `(4, −5)`, `(−2, 3)`. -/

example : Var ([1, -1, 2, 0, 0, 3, 4, -5, -2, 0, 3] : List Int) = 4 := by decide

/-! ## `Var(P)` and `pos(P)` for a univariate polynomial -/

/-- **BPR notation.** For `P = aₚ Xᵖ + ⋯ + a₀ ∈ R[X]`, `Var(P)` is the
    number of sign variations in the coefficient sequence `a₀, …, aₚ`. -/
noncomputable def varPoly [Semiring R] [LinearOrder R] (P : R[X]) : ℕ :=
  Var ((List.range (P.natDegree + 1)).map P.coeff)

/-- **BPR notation.** For `P ∈ R[X]`, `pos(P)` is the number of positive
    real roots of `P`, counted with multiplicity. (Follows Mathlib's
    convention `Polynomial.roots 0 = ∅`, so `pos(0) = 0`.) -/
noncomputable def posRoots [CommRing R] [IsDomain R] [LinearOrder R]
    (P : R[X]) : ℕ :=
  Multiset.card (P.roots.filter (0 < ·))

/-! ## Notation 2.34: Sign variations of a polynomial sequence at a point -/

/-- An element of `R ∪ {−∞, +∞}`, used as the evaluation point for
    `varAt` (BPR Notation 2.34). -/
inductive ExtendedPoint (R : Type*)
  | finite (a : R) : ExtendedPoint R
  | posInf : ExtendedPoint R
  | negInf : ExtendedPoint R
  deriving DecidableEq

namespace ExtendedPoint

/-- Evaluation of `P ∈ R[X]` at an extended point.

    At a finite `a` this is `P(a)`. At `±∞` it returns a representative
    whose sign agrees with the sign of `P(x)` for `|x|` sufficiently large,
    by Proposition 2.4:

    - at `+∞`, `sign(P(x)) = sign(aₚ · x^p) = sign(aₚ)` for `x → +∞`, so
      return `leadingCoeff P`;
    - at `−∞`, `sign(P(x)) = sign(aₚ · x^p) = sign((−1)^p · aₚ)` for
      `x → −∞`, so return `(−1)^(natDegree P) · leadingCoeff P`.

    For `P = 0` the return value is `0`, matching `sign(0) = 0`. -/
noncomputable def evalPoly [Ring R] (P : R[X]) : ExtendedPoint R → R
  | .finite a => P.eval a
  | .posInf   => P.leadingCoeff
  | .negInf   => (-1) ^ P.natDegree * P.leadingCoeff

end ExtendedPoint

/-- **BPR Notation 2.34.** The number of sign variations of a sequence of
    polynomials `P = P₀, …, P_d` at a point `a ∈ R ∪ {−∞, +∞}`,
    `Var(P; a) = Var(P₀(a), …, P_d(a))`, where at `a = ±∞` the signs to
    consider are those of the leading monomials (Proposition 2.4). -/
noncomputable def varAt [Ring R] [LinearOrder R]
    (P : List R[X]) (a : ExtendedPoint R) : ℕ :=
  Var (P.map (ExtendedPoint.evalPoly · a))

section

variable [Ring R] [LinearOrder R]

lemma varAt_finite (P : List R[X]) (a : R) :
    varAt P (ExtendedPoint.finite a) = Var (P.map (fun Q => Q.eval a)) := rfl

lemma varAt_posInf (P : List R[X]) :
    varAt P ExtendedPoint.posInf = Var (P.map Polynomial.leadingCoeff) := rfl

lemma varAt_negInf (P : List R[X]) :
    varAt P ExtendedPoint.negInf =
      Var (P.map (fun Q => (-1) ^ Q.natDegree * Q.leadingCoeff)) := rfl

@[simp] lemma varAt_nil (a : ExtendedPoint R) : varAt ([] : List R[X]) a = 0 := rfl

end

/-! ### Worked example (BPR Notation 2.34)

`Var(X⁵, X² − 1, 0, X² − 1, X + 2, 1; 1) = 0`: evaluating at `1` gives the
sequence `1, 0, 0, 0, 3, 1`; dropping zeros yields `1, 3, 1`, with no sign
changes. -/

example :
    varAt ([X ^ 5, X ^ 2 - 1, 0, X ^ 2 - 1, X + 2, 1] : List ℤ[X])
      (ExtendedPoint.finite 1) = 0 := by
  simp [varAt_finite, Var, varNonzero]

/-! ## `Var(P; a, b)` and `num(P; (a, b])` -/

/-- **BPR notation.** `Var(P; a, b) = Var(P; a) − Var(P; b)`, the change in
    sign-variation count of a polynomial sequence `P` between two extended
    points `a, b ∈ R ∪ {−∞, +∞}`. Takes values in `ℤ` because the two
    `varAt` counts need not be comparable in general. -/
noncomputable def varBetween [Ring R] [LinearOrder R]
    (P : List R[X]) (a b : ExtendedPoint R) : ℤ :=
  (varAt P a : ℤ) - (varAt P b : ℤ)

/-- **BPR notation.** `num(P; (a, b])` is the number of roots of `P` in the
    half-open interval `(a, b] ⊆ R`, counted with multiplicity, where
    `a, b : ExtendedPoint R`. Conventions:

    - `a = +∞` or `b = −∞` gives the empty interval, so `0`;
    - `a = −∞, b = +∞` covers all of `R`, so the total root count of `P`;
    - finite `a, b` use `{r | a < r ∧ r ≤ b}`;
    - `a = finite a', b = +∞` uses `{r | a' < r}`;
    - `a = −∞, b = finite b'` uses `{r | r ≤ b'}`. -/
noncomputable def numRoots [CommRing R] [IsDomain R] [LinearOrder R]
    (P : R[X]) : ExtendedPoint R → ExtendedPoint R → ℕ
  | .posInf,   _           => 0
  | .negInf,   .negInf     => 0
  | .finite _, .negInf     => 0
  | .negInf,   .posInf     => Multiset.card P.roots
  | .finite a, .posInf     => Multiset.card (P.roots.filter (a < ·))
  | .negInf,   .finite b   => Multiset.card (P.roots.filter (· ≤ b))
  | .finite a, .finite b   =>
      Multiset.card (P.roots.filter (fun r => a < r ∧ r ≤ b))

end Azurite.BPR

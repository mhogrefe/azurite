import Azurite.BasuPollackRoy.Chapter1.Section1_3.SplitLast
import Azurite.BasuPollackRoy.Chapter1.Section1_3.TRems
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Theorem1_22
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Remark_2_51
import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicQF
import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# BPR Theorem 2.62 — Fibre Formula Construction

This file builds the QF formula `fiberFormula_high P` whose realisation
equals the fibre-non-empty set `{y | ∃ x : R, aeval (Fin.snoc y x) P = 0}`,
and proves its correctness — the multivariate Sturm-Tarski heart of BPR's
Theorem 2.62.

Structure:

* **Sturm sign-change combinatorics**: the abstract `varAtSigns`,
  `varAtNegInfWithDegrees`, `sturmCount`, `goodSignPattern`.
* **Enumeration**: `allSignPatterns`, `goodRootLeafPatterns` (over the
  root truncations `Tru(splitLast P)` × `TRems` leaves × sign patterns).
* **Sign-condition formula** per leaf path: `sturmLeafSignFormula`.
* **Assembly**: `fiberFormula_high` and `fiberFormula_high_isQF`.
* **Correctness**: `fiberFormula_high_realization`, via the
  combinatorial-to-actual bridge `sturmCount_eq_actual_varAt_diff`
  (`PosAssoc` positive-scalar association + the `mkTRemsNode_sturm_posAssoc`
  pointwise correspondence).
-/

namespace Azurite.BPR

/-! ### Sturm sign-change combinatorics

Each leaf path of `TRems(P̃, ∂P̃/∂X)` (over a root truncation `P̃`)
encodes a scenario for the actual degrees and leading coefficients of
the Sturm sequence of `P_y` as `y` varies. The number of sign changes
depends only on:
* the **sign pattern** of the leading coefficients (a list of
  `SignType`s), and
* the **natDegrees** of the Sturm sequence elements.

We define the abstract sign-change count `varAtSigns`
(`varAt(+∞)` on the sign pattern alone), the parity-adjusted count
`varAtNegInfWithDegrees` (`varAt(-∞)`, each sign flipped by `(-1)^d_i`),
the resulting `sturmCount`, and the `goodSignPattern` predicate.
-/

/-- The number of sign changes in a list of `SignType`s, ignoring
zero entries. This is the abstract analogue of `varAt` at `+∞`. -/
def varAtSigns : List SignType → ℕ
  | [] => 0
  | [_] => 0
  | s :: t :: rest =>
      if s = 0 then varAtSigns (t :: rest)
      else if t = 0 then varAtSigns (s :: rest)
      else if s = t then varAtSigns (t :: rest)
      else 1 + varAtSigns (t :: rest)

@[simp] theorem varAtSigns_nil : varAtSigns [] = 0 := by
  unfold varAtSigns; rfl

@[simp] theorem varAtSigns_singleton (s : SignType) :
    varAtSigns [s] = 0 := by
  unfold varAtSigns; rfl

theorem varAtSigns_cons_cons (s t : SignType) (rest : List SignType) :
    varAtSigns (s :: t :: rest) =
      if s = 0 then varAtSigns (t :: rest)
      else if t = 0 then varAtSigns (s :: rest)
      else if s = t then varAtSigns (t :: rest)
      else 1 + varAtSigns (t :: rest) := by
  rw [varAtSigns]

/-- Prepending a zero does not change the sign-variation count. -/
theorem varAtSigns_zero_cons (L : List SignType) :
    varAtSigns (0 :: L) = varAtSigns L := by
  cases L with
  | nil => simp
  | cons t rest => rw [varAtSigns_cons_cons, ite_eq_left rfl]

/-- `varAtSigns` depends only on the list with zeros removed: the
recursion skips zeros inline, so filtering them out first is a no-op. -/
theorem varAtSigns_filter_ne_zero : ∀ (L : List SignType),
    varAtSigns (L.filter (· ≠ 0)) = varAtSigns L
  | [] => rfl
  | [s] => by
      rcases eq_or_ne s 0 with hs | hs
      · subst hs; simp
      · rw [List.filter_cons_of_pos (by simpa using hs)]; rfl
  | s :: t :: rest => by
      rcases eq_or_ne s 0 with hs | hs
      · -- s = 0: dropped by filter, skipped by varAtSigns.
        subst hs
        rw [List.filter_cons_of_neg (by simp), varAtSigns_zero_cons]
        exact varAtSigns_filter_ne_zero (t :: rest)
      · -- s ≠ 0: kept; recurse on the shorter `s :: rest` or `t :: rest`.
        rw [List.filter_cons_of_pos (by simpa using hs)]
        rcases eq_or_ne t 0 with ht | ht
        · subst ht
          rw [List.filter_cons_of_neg (by simp), varAtSigns_cons_cons,
              ite_eq_right hs, ite_eq_left rfl,
              ← List.filter_cons_of_pos (a := s) (by simpa using hs)]
          exact varAtSigns_filter_ne_zero (s :: rest)
        · rw [List.filter_cons_of_pos (by simpa using ht), varAtSigns_cons_cons,
              varAtSigns_cons_cons, ite_eq_right hs, ite_eq_right hs, ite_eq_right ht, ite_eq_right ht,
              ← List.filter_cons_of_pos (a := t) (by simpa using ht),
              varAtSigns_filter_ne_zero (t :: rest)]
  termination_by L => L.length

/-- Appending trailing zeros does not change the sign-variation count. -/
theorem varAtSigns_append_replicate_zero (L : List SignType) (n : ℕ) :
    varAtSigns (L ++ List.replicate n 0) = varAtSigns L := by
  rw [← varAtSigns_filter_ne_zero (L ++ List.replicate n 0),
      ← varAtSigns_filter_ne_zero L, List.filter_append,
      show (List.replicate n (0 : SignType)).filter (· ≠ 0) = [] from ?_,
      List.append_nil]
  rw [List.filter_eq_nil_iff]
  intro x hx
  rw [List.eq_of_mem_replicate hx]
  simp

/-- Apply parity adjustment to a sign: even degree → unchanged,
odd degree → negate. This is the sign of `(-1)^d * s`. -/
def signWithParity (s : SignType) (d : ℕ) : SignType :=
  if d % 2 = 0 then s else -s

@[simp] theorem signWithParity_zero (s : SignType) :
    signWithParity s 0 = s := rfl

@[simp] theorem signWithParity_pos_even (s : SignType) (n : ℕ) :
    signWithParity s (2 * n) = s := by
  simp [signWithParity, Nat.mul_mod_right]

@[simp] theorem signWithParity_pos_odd (s : SignType) (n : ℕ) :
    signWithParity s (2 * n + 1) = -s := by
  simp [signWithParity]

/-- The number of sign changes at `-∞`, given a sign pattern of leading
coefficients and the corresponding natDegrees. Each entry of the sign
pattern is flipped by `(-1)^{d_i}` before counting. -/
def varAtNegInfWithDegrees (pattern : List SignType) (degrees : List ℕ) : ℕ :=
  varAtSigns ((pattern.zip degrees).map (fun sd => signWithParity sd.1 sd.2))

@[simp] theorem varAtNegInfWithDegrees_nil_left (degrees : List ℕ) :
    varAtNegInfWithDegrees [] degrees = 0 := by
  simp [varAtNegInfWithDegrees]

@[simp] theorem varAtNegInfWithDegrees_nil_right (pattern : List SignType) :
    varAtNegInfWithDegrees pattern [] = 0 := by
  simp [varAtNegInfWithDegrees]

/-- The Sturm count for a sign pattern and a list of natDegrees:
`varAt(-∞) - varAt(+∞)`. By Sturm's Theorem 2.50 and Remark 2.51, this
equals the number of distinct real roots of any polynomial having the
prescribed sign-pattern-and-degree scenario, and is positive iff such a
polynomial has at least one real root. -/
def sturmCount (pattern : List SignType) (degrees : List ℕ) : ℤ :=
  (varAtNegInfWithDegrees pattern degrees : ℤ) - (varAtSigns pattern : ℤ)

/-- A sign pattern (paired with a degree list) is *good* if its Sturm
count is positive -- i.e., a Sturm sequence realising this
sign-and-degree scenario corresponds to a polynomial with at least one
real root. -/
def goodSignPattern (pattern : List SignType) (degrees : List ℕ) : Prop :=
  0 < sturmCount pattern degrees

instance (pattern : List SignType) (degrees : List ℕ) :
    Decidable (goodSignPattern pattern degrees) := by
  unfold goodSignPattern; infer_instance

/-! ### Enumeration of sign patterns (light combinatorics)

We enumerate all `{+, 0, -}^n` sign patterns of length `n`. We use the
full three-valued alphabet (rather than just the two non-zero signs)
because a `TRems` leaf path ends with the explicit `0` polynomial,
whose leading coefficient has sign `0`. Since `varAtSigns` ignores
zeros, including the zero sign is harmless for the Sturm count, and it
spares us proving that path elements are non-vanishing. -/

/-- All `{+, 0, -}^n` sign patterns of length `n`. -/
def allSignPatterns : ℕ → List (List SignType)
  | 0 => [[]]
  | n + 1 =>
      (allSignPatterns n).flatMap fun p =>
        [.pos :: p, .zero :: p, .neg :: p]

@[simp] theorem allSignPatterns_zero :
    allSignPatterns 0 = [[]] := rfl

theorem mem_allSignPatterns_iff {n : ℕ} {p : List SignType} :
    p ∈ allSignPatterns n ↔ p.length = n := by
  induction n generalizing p with
  | zero =>
    constructor
    · intro hp
      simp [allSignPatterns] at hp
      subst hp; simp
    · intro hlen
      have : p = [] := List.length_eq_zero_iff.mp hlen
      subst this; simp [allSignPatterns]
  | succ n ih =>
    simp only [allSignPatterns, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨q, hq_mem, rfl | rfl | rfl⟩ <;>
        rw [ih] at hq_mem <;> simp [hq_mem]
    · intro hlen
      cases p with
      | nil => simp at hlen
      | cons head tail =>
        refine ⟨tail, ih.mpr (by simpa using hlen), ?_⟩
        rcases head with _ | _ | _
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl

/-! ### Good root-truncation/leaf/sign triples

For `P_split = splitLast P`, `goodRootLeafPatterns P_split` enumerates
the triples `(P̃, path, sigPat)` where:
* `P̃ ∈ Tru P_split` is a truncation of `P_split` — encoding a possible
  actual degree of the specialised polynomial `P_y` (when the top
  coefficients of `P_split` vanish at `y`, `P_y` drops to a lower
  degree captured by some truncation `P̃`);
* `path` is a root-to-leaf path of `TRems P̃ P̃'` (`P̃' = P̃.derivative`)
  — encoding the degrees of the signed remainder sequence; and
* `sigPat` is a `{+, -}^(P̃ :: path).length` assignment, *good* in the
  Sturm sense for the natDegrees of `P̃ :: path`.

The root `P̃` is prepended to `path` throughout because the Sturm
sign-change count of `SRemS(P_y, P_y')` begins with `P_y` itself
(BPR Example 2.63: the sequence has degrees `4, 3, 2, 1, 0` starting
at `deg P`, not `deg P'`).
-/

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D]

/-- The list of `(root-truncation, leaf-path, sign-pattern)` triples
for the parametrised Sturm-Tarski analysis of `P_split`. See the
section comment for the meaning of each component. -/
noncomputable def goodRootLeafPatterns
    (P_split : Polynomial (MvPolynomial (Fin k) D)) :
    List (Polynomial (MvPolynomial (Fin k) D) ×
          List (Polynomial (MvPolynomial (Fin k) D)) × List SignType) :=
  (Tru_finite P_split).toFinset.toList.flatMap fun Ptil =>
    (TRems Ptil Ptil.derivative).leafPaths.flatMap fun path =>
      let degrees := (Ptil :: path).map Polynomial.natDegree
      ((allSignPatterns (Ptil :: path).length).filter
        (fun pat => decide (goodSignPattern pat degrees))).map
        (fun pat => (Ptil, path, pat))

theorem mem_goodRootLeafPatterns_iff
    {P_split : Polynomial (MvPolynomial (Fin k) D)}
    {Ptil : Polynomial (MvPolynomial (Fin k) D)}
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    {pat : List SignType} :
    (Ptil, path, pat) ∈ goodRootLeafPatterns P_split ↔
      Ptil ∈ Tru P_split ∧
      path ∈ (TRems Ptil Ptil.derivative).leafPaths ∧
      pat ∈ allSignPatterns (Ptil :: path).length ∧
      goodSignPattern pat ((Ptil :: path).map Polynomial.natDegree) := by
  simp only [goodRootLeafPatterns, List.mem_flatMap, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Prod.mk.injEq,
    Finset.mem_toList, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨Ptil', hPtil'_mem, path', hpath'_mem, pat',
        ⟨hpat'_mem, hpat'_good⟩, hPtil_eq, hpath_eq, hpat_eq⟩
    subst hPtil_eq; subst hpath_eq; subst hpat_eq
    exact ⟨hPtil'_mem, hpath'_mem, hpat'_mem, hpat'_good⟩
  · rintro ⟨hPtil_mem, hpath_mem, hpat_mem, hpat_good⟩
    exact ⟨Ptil, hPtil_mem, path, hpath_mem, pat,
      ⟨hpat_mem, hpat_good⟩, rfl, rfl, rfl⟩

/-! ### Sign-condition formula for a leaf path

For a `TRems` leaf `path` and a sign pattern `signPattern` of the
same length, the formula `sturmLeafSignFormula path signPattern`
asserts that each polynomial in `path` has its leading X-coefficient
(a `MvPolynomial (Fin k) D`) evaluate to the specified sign at `y`.
This is the per-leaf sign-condition cell.
-/

/-- The sign-condition formula for a TRems leaf path, asserting that
each polynomial's leading X-coefficient has the prescribed sign. -/
noncomputable def Formula.sturmLeafSignFormula
    (path : List (Polynomial (MvPolynomial (Fin k) D)))
    (signPattern : List SignType) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  signCondFormula (path.map Polynomial.leadingCoeff |>.zip signPattern)

omit [IsDomain D] in
theorem Formula.sturmLeafSignFormula_isQF
    (path : List (Polynomial (MvPolynomial (Fin k) D)))
    (signPattern : List SignType) :
    (Formula.sturmLeafSignFormula path signPattern).IsQuantifierFree :=
  Formula.signCondFormula_isQF _

section SturmLeafSignFormulaRealization

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R]

omit [IsDomain D] in
theorem Formula.realization_sturmLeafSignFormula
    (path : List (Polynomial (MvPolynomial (Fin k) D)))
    (signPattern : List SignType) :
    (Formula.sturmLeafSignFormula path signPattern).realization (C := R) =
      { y : Fin k → R | ∀ ps ∈ (path.map Polynomial.leadingCoeff).zip signPattern,
          SignType.sign (MvPolynomial.aeval y ps.1) = ps.2 } :=
  Formula.signCondFormula_realization _

end SturmLeafSignFormulaRealization

/-! ### Assembly: `fiberFormula_high`

The fibre-non-empty QF formula is the disjunction of:
* the `P_y = 0` locus `degFormula P_split ⊥` (where *every* `x` is a
  root, so the fibre is non-empty), and
* over each `(P̃, path, sigPat) ∈ goodRootLeafPatterns P_split`, the
  conjunction of:
  - `degFormula P_split (↑P̃.natDegree)` — `P_y` has actual degree
    `deg P̃` (so `P_y = P̃_y`, by `degFormula_Tru_spec`);
  - the Chapter 1 `leafFormula P̃ P̃' path` — the signed remainder
    sequence has the degrees encoded by `path`; both translated from
    `FieldAtom` to `OrderedFieldAtom` via `FieldAtom.toOrderedFieldAtom`;
  - the `sturmLeafSignFormula (P̃ :: path) sigPat` — the leading
    coefficients of the *full* sequence `P̃ :: path` have signs
    `sigPat`.
-/

/-- The fibre-non-empty QF formula. Defined unconditionally. -/
noncomputable def fiberFormula_high (P : MvPolynomial (Fin (k+1)) D) :
    Formula (Fin k) (OrderedFieldAtom (Fin k) D) :=
  let P_split := splitLast P
  Formula.disjListO (
    ((degFormula P_split ⊥).mapAtom FieldAtom.toOrderedFieldAtom) ::
    (goodRootLeafPatterns P_split).map fun t =>
      (((degFormula P_split (↑t.1.natDegree)).and
          (leafFormula t.1 t.1.derivative t.2.1)).mapAtom
            FieldAtom.toOrderedFieldAtom).and
        (Formula.sturmLeafSignFormula (t.1 :: t.2.1) t.2.2)
  )

theorem fiberFormula_high_isQF (P : MvPolynomial (Fin (k+1)) D) :
    (fiberFormula_high P).IsQuantifierFree := by
  apply Formula.disjListO_isQF
  intro Φ hΦ
  simp only [List.mem_cons, List.mem_map] at hΦ
  rcases hΦ with rfl | ⟨⟨Ptil, path, sigPat⟩, _, rfl⟩
  · rw [Formula.mapAtom_isQF]; exact degFormula_isQF _ _
  · refine ⟨?_, Formula.sturmLeafSignFormula_isQF _ _⟩
    rw [Formula.mapAtom_isQF]
    exact ⟨degFormula_isQF _ _, leafFormula_isQF _ _ _⟩

/-! ### Correctness

The realisation of `fiberFormula_high P` equals the fibre-non-empty set
`{y | ∃ x : R, aeval (Fin.snoc y x) P = 0}`. This is the substantive
Sturm-Tarski content of BPR's Theorem 2.62 proof.

The argument:

1. **Root truncation + leaf covering**: for any `y` with `P_y ≠ 0`,
   `Tru_covers_degrees` finds the truncation `P̃ ∈ Tru(splitLast P)`
   pinning `P_y`'s actual degree, and `leafFormula_covering` a path of
   `TRems(P̃, P̃')` identifying the Sturm-sequence degrees.
2. **Sign pattern**: along that path, the leading X-coefficients have
   definite signs at `y` — the pattern `sigPat`.
3. **Combinatorial Sturm count = actual count**: the abstract
   `sturmCount sigPat degrees` equals the actual `varAt(SRemS)`
   sign-change difference at `±∞` (`sturmCount_eq_actual_varAt_diff`).
4. **Remark 2.51 connection**: `∃ real root iff that difference > 0`,
   i.e. the triple is in `goodRootLeafPatterns`.
5. **Final assembly**: `realization_disjListO` and the per-disjunct
   realisation equalities, with the `P_y = 0` locus as the head
   disjunct. -/

section FiberFormulaHighRealization

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R] [IsRealClosed R]

omit [Algebra D R] [IsDomain D] in
/-- An `IsRealClosed` field has the intermediate value property, by BPR
Theorem 2.11 ((a) ⇒ (b) via `isAlgClosed_Ri`, then (b) ⇒ (c) via
`theorem_2_11_b_c`). This lets Theorem 2.62 assume `[IsRealClosed R]`
directly instead of carrying an explicit IVP hypothesis. -/
theorem hasIVP_of_isRealClosed :
    Azurite.BPR.HasIntermediateValueProperty R := by
  have : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  exact Theorem2_11.theorem_2_11_b_c

/-- Helper: `(l.map f).zip (l.map g) = l.map (fun a => (f a, g a))`. -/
private theorem zip_map_map_diag {α β γ : Type*}
    (l : List α) (f : α → β) (g : α → γ) :
    (l.map f).zip (l.map g) = l.map (fun a => (f a, g a)) := by
  induction l with
  | nil => rfl
  | cons head tail ih => simp [List.zip_cons_cons, ih]

omit [IsDomain D] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Helper: the existential `∃ x : R, aeval (Fin.snoc y x) P = 0` is
equivalent to the existence of a real root of the univariate
specialisation `P_y(X) := (splitLast P).map (aeval y)`. Direct
application of `aeval_snoc_eq_eval_splitLast`. -/
theorem exists_aeval_snoc_iff_exists_isRoot_specialized
    (P : MvPolynomial (Fin (k+1)) D) (y : Fin k → R) :
    (∃ x : R, MvPolynomial.aeval (Fin.snoc y x) P = 0) ↔
    (∃ x : R,
      ((splitLast P).map (MvPolynomial.aeval y).toRingHom).IsRoot x) := by
  refine ⟨fun ⟨x, hx⟩ => ⟨x, ?_⟩, fun ⟨x, hx⟩ => ⟨x, ?_⟩⟩
  · show ((splitLast P).map _).eval x = 0
    rw [← aeval_snoc_eq_eval_splitLast]; exact hx
  · rw [aeval_snoc_eq_eval_splitLast]; exact hx

/-! ### Sign-arithmetic helpers for the Sturm bridge.

These pure sign-arithmetic facts connect the abstract `signWithParity`
to the actual `(-1)^d * c` computation used in `ExtendedPoint.evalPoly`
at `-∞`. -/

omit [IsRealClosed R] [Algebra D R] [IsDomain D] in
/-- The sign of `(-1)^d * c` matches the parity-adjusted sign of `c`. -/
private theorem sign_neg_one_pow_mul (d : ℕ) (c : R) :
    SignType.sign ((-1 : R) ^ d * c) = signWithParity (SignType.sign c) d := by
  rw [sign_mul, sign_pow, sign_neg neg_one_lt_zero, signWithParity]
  split_ifs with h
  · have h_even : Even d := Nat.even_iff.mpr h
    rw [h_even.neg_one_pow, one_mul]
  · have h_odd : Odd d := Nat.odd_iff.mpr (by omega)
    rw [h_odd.neg_one_pow, neg_one_mul]

omit [IsRealClosed R] [Algebra D R] [IsDomain D] in
/-- For nonzero `a, b`, the product is negative iff their signs differ. -/
private theorem mul_neg_iff_sign_ne {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b < 0 ↔ SignType.sign a ≠ SignType.sign b := by
  rw [← sign_eq_neg_one_iff, sign_mul]
  have hsa : SignType.sign a ≠ 0 := sign_ne_zero.mpr ha
  have hsb : SignType.sign b ≠ 0 := sign_ne_zero.mpr hb
  revert hsa hsb
  generalize SignType.sign a = sa
  generalize SignType.sign b = sb
  revert sa sb
  decide

omit [IsRealClosed R] [Algebra D R] [IsDomain D] [IsStrictOrderedRing R] in
/-- Removing a zero that immediately follows a list element does not
change the variation count. -/
private theorem Var_cons_zero_cons (a : R) (l : List R) :
    Var (a :: (0 : R) :: l) = Var (a :: l) := by
  unfold Var
  congr 1
  simp [List.filter_cons]

omit [IsRealClosed R] [Algebra D R] [IsDomain D] [IsStrictOrderedRing R] in
/-- The `varNonzero` recurrence for `Var` when the first two entries are
nonzero. -/
private theorem Var_cons_cons_of_ne (a b : R) (rest : List R)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Var (a :: b :: rest) = (if a * b < 0 then 1 else 0) + Var (b :: rest) := by
  unfold Var
  rw [List.filter_cons_of_pos (by simpa using ha),
      List.filter_cons_of_pos (by simpa using hb), varNonzero_cons_cons,
      ← List.filter_cons_of_pos (a := b) (by simpa using hb)]

omit [IsRealClosed R] [Algebra D R] [IsDomain D] in
/-- **Sign-counting bridge.** `Var` of a list of `R`-values equals the
abstract `varAtSigns` of the list of their signs. Both count adjacent
sign changes after dropping zeros; this matches them structurally. -/
theorem Var_eq_varAtSigns_map_sign : ∀ (L : List R),
    Var L = varAtSigns (L.map SignType.sign)
  | [] => by simp
  | [a] => by
      rw [List.map_cons, List.map_nil, varAtSigns_singleton]
      unfold Var
      rcases eq_or_ne a 0 with h | h
      · subst h; simp
      · rw [List.filter_cons_of_pos (by simpa using h)]; rfl
  | a :: b :: rest => by
      rw [List.map_cons, List.map_cons, varAtSigns_cons_cons]
      by_cases ha : a = 0
      · -- a = 0: skip it.
        subst ha
        rw [ite_eq_left sign_zero, Var_zero_cons, ← List.map_cons]
        exact Var_eq_varAtSigns_map_sign (b :: rest)
      · have ha' : SignType.sign a ≠ 0 := sign_ne_zero.mpr ha
        rw [ite_eq_right ha']
        by_cases hb : b = 0
        · -- b = 0: skip it.
          subst hb
          rw [ite_eq_left sign_zero, Var_cons_zero_cons, ← List.map_cons]
          exact Var_eq_varAtSigns_map_sign (a :: rest)
        · have hb' : SignType.sign b ≠ 0 := sign_ne_zero.mpr hb
          rw [ite_eq_right hb', Var_cons_cons_of_ne a b rest ha hb]
          by_cases hsab : SignType.sign a = SignType.sign b
          · -- same sign: no variation.
            rw [ite_eq_left hsab,
              ite_eq_right (fun h => (mul_neg_iff_sign_ne ha hb).mp h hsab),
              zero_add, ← List.map_cons]
            exact Var_eq_varAtSigns_map_sign (b :: rest)
          · -- opposite sign: one variation.
            rw [ite_eq_right hsab,
              ite_eq_left ((mul_neg_iff_sign_ne ha hb).mpr hsab),
              ← List.map_cons]
            congr 1
            exact Var_eq_varAtSigns_map_sign (b :: rest)
  termination_by L => L.length

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- `varAt _ +∞` rewritten as an abstract `varAtSigns` over the
leading-coefficient signs. (`evalPoly · posInf` is `leadingCoeff`.) -/
private theorem varAt_posInf_eq_varAtSigns (L : List (Polynomial R)) :
    varAt L ExtendedPoint.posInf
      = varAtSigns (L.map (fun Q => SignType.sign Q.leadingCoeff)) := by
  rw [varAt_posInf, Var_eq_varAtSigns_map_sign, List.map_map]
  rfl

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- `varAt _ -∞` rewritten as an abstract `varAtSigns` over the
parity-adjusted leading-coefficient signs. (`evalPoly · negInf` is
`(-1)^natDegree · leadingCoeff`, whose sign is `signWithParity` of the
leading-coefficient sign by `sign_neg_one_pow_mul`.) -/
private theorem varAt_negInf_eq_varAtSigns (L : List (Polynomial R)) :
    varAt L ExtendedPoint.negInf
      = varAtSigns (L.map (fun Q =>
          signWithParity (SignType.sign Q.leadingCoeff) Q.natDegree)) := by
  rw [varAt_negInf, Var_eq_varAtSigns_map_sign, List.map_map]
  congr 1
  apply List.map_congr_left
  intro Q _
  exact sign_neg_one_pow_mul Q.natDegree Q.leadingCoeff

/-! ### `PosAssoc`: positive-scalar association

Two polynomials related by a *positive* scalar multiple agree in
`natDegree` and leading-coefficient sign, hence have the same
`evalPoly` sign at every `ExtendedPoint` — all that `varAt` sees. This
is the bridge from the even-`pRemExp` pseudo-remainders (which are
positive multiples of the true signed remainders) to the actual
`SRemS` sequence. -/

omit [IsDomain D] [IsRealClosed R] [Algebra D R] [IsStrictOrderedRing R] [LinearOrder R] in
/-- Scaling the dividend by a constant scales the remainder. -/
private theorem C_mul_mod (c : R) (P Q : Polynomial R) :
    (Polynomial.C c * P) % Q = Polynomial.C c * (P % Q) := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hsub : P - P % Q = Q * (P / Q) :=
    (eq_sub_of_add_eq (EuclideanDomain.div_add_mod P Q)).symm
  have hdvd : Q ∣ (Polynomial.C c * P - Polynomial.C c * (P % Q)) := by
    rw [← mul_sub, hsub]; exact (dvd_mul_right Q _).mul_left _
  rw [Polynomial.mod_eq_of_dvd_sub hdvd]
  exact (Polynomial.mod_eq_self_iff hQ).mpr (by
    rw [Polynomial.degree_C_mul hc]; exact Polynomial.degree_mod_lt _ hQ)

omit [IsDomain D] [IsRealClosed R] [Algebra D R] [IsStrictOrderedRing R] [LinearOrder R] in
/-- Scaling the divisor by a non-zero constant leaves the remainder
unchanged. -/
private theorem mod_C_mul (c : R) (hc : c ≠ 0) (P Q : Polynomial R) :
    P % (Polynomial.C c * Q) = P % Q := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  have hCQ : Polynomial.C c * Q ≠ 0 :=
    mul_ne_zero (by rwa [Ne, Polynomial.C_eq_zero]) hQ
  have hdeg : (P % (Polynomial.C c * Q)).degree < Q.degree := by
    have := Polynomial.degree_mod_lt P hCQ
    rwa [Polynomial.degree_C_mul hc] at this
  have hsub : P - P % (Polynomial.C c * Q)
      = (Polynomial.C c * Q) * (P / (Polynomial.C c * Q)) :=
    (eq_sub_of_add_eq (EuclideanDomain.div_add_mod P (Polynomial.C c * Q))).symm
  have hdvd : Q ∣ (P - P % (Polynomial.C c * Q)) := by
    rw [hsub]; exact (dvd_mul_left Q _).mul_right _
  rw [Polynomial.mod_eq_of_dvd_sub hdvd, (Polynomial.mod_eq_self_iff hQ).mpr hdeg]

/-- `a` is a positive scalar multiple of `b`. -/
private def PosAssoc (a b : Polynomial R) : Prop :=
  ∃ c : R, 0 < c ∧ a = Polynomial.C c * b

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- `PosAssoc` is reflexive (scale by `1`). -/
private theorem PosAssoc.refl (a : Polynomial R) : PosAssoc a a :=
  ⟨1, one_pos, by rw [Polynomial.C_1, one_mul]⟩

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- `PosAssoc` is symmetric (scale by `c⁻¹`). -/
private theorem PosAssoc.symm {a b : Polynomial R} (h : PosAssoc a b) : PosAssoc b a := by
  obtain ⟨c, hc, hab⟩ := h
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  rw [hab, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (ne_of_gt hc),
      Polynomial.C_1, one_mul]

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- `PosAssoc` is transitive (multiply the scalars). -/
private theorem PosAssoc.trans {a b c : Polynomial R}
    (h₁ : PosAssoc a b) (h₂ : PosAssoc b c) : PosAssoc a c := by
  obtain ⟨k₁, hk₁, rfl⟩ := h₁
  obtain ⟨k₂, hk₂, rfl⟩ := h₂
  exact ⟨k₁ * k₂, mul_pos hk₁ hk₂, by rw [Polynomial.C_mul, mul_assoc]⟩

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- Scaling the second polynomial of a signed remainder sequence by a
positive constant gives a sequence of positive-scalar associates. The
scalars alternate (`1, c, 1, c, …`) but are always positive; for `varAt`
purposes only positivity matters. -/
private theorem SRemS_posAssoc_smul_right (c : R) (hc : 0 < c) (Q S : Polynomial R) :
    ∀ i, PosAssoc (SRemS Q (Polynomial.C c * S) i) (SRemS Q S i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => exact PosAssoc.refl Q
    | 1 => exact ⟨c, hc, by rw [SRemS_snd, SRemS_snd]⟩
    | (j + 2) =>
      obtain ⟨kj, hkj, hkje⟩ := ih j (by omega)
      obtain ⟨kj1, hkj1, hkj1e⟩ := ih (j + 1) (by omega)
      by_cases hSj1 : SRemS Q S (j + 1) = 0
      · have hCj1 : SRemS Q (Polynomial.C c * S) (j + 1) = 0 := by
          rw [hkj1e, hSj1, mul_zero]
        rw [SRemS_zero_ge Q (Polynomial.C c * S) j hCj1 (j + 2) (by omega),
            SRemS_zero_ge Q S j hSj1 (j + 2) (by omega)]
        exact PosAssoc.refl 0
      · have hCj1 : SRemS Q (Polynomial.C c * S) (j + 1) ≠ 0 := by
          rw [hkj1e]
          exact mul_ne_zero (Polynomial.C_ne_zero.mpr (ne_of_gt hkj1)) hSj1
        refine ⟨kj, hkj, ?_⟩
        rw [SRemS_ss _ _ _ hCj1, hkje, hkj1e, C_mul_mod,
            mod_C_mul _ (ne_of_gt hkj1), SRemS_ss _ _ _ hSj1, mul_neg]

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- Scaling the first polynomial of a signed remainder sequence by a
positive constant gives a sequence of positive-scalar associates. -/
private theorem SRemS_posAssoc_smul_left (c : R) (hc : 0 < c) (Q S : Polynomial R) :
    ∀ i, PosAssoc (SRemS (Polynomial.C c * Q) S i) (SRemS Q S i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => exact ⟨c, hc, by rw [SRemS_fst, SRemS_fst]⟩
    | 1 => exact PosAssoc.refl S
    | (j + 2) =>
      obtain ⟨kj, hkj, hkje⟩ := ih j (by omega)
      obtain ⟨kj1, hkj1, hkj1e⟩ := ih (j + 1) (by omega)
      by_cases hSj1 : SRemS Q S (j + 1) = 0
      · have hCj1 : SRemS (Polynomial.C c * Q) S (j + 1) = 0 := by
          rw [hkj1e, hSj1, mul_zero]
        rw [SRemS_zero_ge (Polynomial.C c * Q) S j hCj1 (j + 2) (by omega),
            SRemS_zero_ge Q S j hSj1 (j + 2) (by omega)]
        exact PosAssoc.refl 0
      · have hCj1 : SRemS (Polynomial.C c * Q) S (j + 1) ≠ 0 := by
          rw [hkj1e]
          exact mul_ne_zero (Polynomial.C_ne_zero.mpr (ne_of_gt hkj1)) hSj1
        refine ⟨kj, hkj, ?_⟩
        rw [SRemS_ss _ _ _ hCj1, hkje, hkj1e, C_mul_mod,
            mod_C_mul _ (ne_of_gt hkj1), SRemS_ss _ _ _ hSj1, mul_neg]

omit [IsRealClosed R] [LinearOrder R] [IsStrictOrderedRing R] in
/-- The specialised signed pseudo-remainder is a `C(lc^d)`-multiple of the
true remainder: `(pRemMv parent cur)_y = C(φ(lc cur)^d) · (parent_y % cur_y)`,
where `d = pRemExp parent cur` is even. -/
private theorem pRemMv_map_eq
    (parent cur : Polynomial (MvPolynomial (Fin k) D)) (hcur : cur ≠ 0)
    (y : Fin k → R)
    (hlc : (MvPolynomial.aeval y).toRingHom cur.leadingCoeff ≠ 0) :
    (pRemMv parent cur).map (MvPolynomial.aeval y).toRingHom
      = Polynomial.C
          ((MvPolynomial.aeval y).toRingHom cur.leadingCoeff ^ pRemExp parent cur)
        * (parent.map (MvPolynomial.aeval y).toRingHom %
           cur.map (MvPolynomial.aeval y).toRingHom) := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom with hφ
  obtain ⟨A, hA⟩ := pRemMv_pseudo_div parent cur hcur
  have hAmap := congrArg (Polynomial.map φ) hA
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C] at hAmap
  rw [map_pow φ] at hAmap
  have hcur_y : cur.map φ ≠ 0 := by
    intro h
    apply hlc
    have hc : φ cur.leadingCoeff = (cur.map φ).coeff cur.natDegree :=
      (Polynomial.coeff_map φ cur.natDegree).symm
    rw [hc, h, Polynomial.coeff_zero]
  have hdeg : ((pRemMv parent cur).map φ).degree < (cur.map φ).degree :=
    calc ((pRemMv parent cur).map φ).degree
        ≤ (pRemMv parent cur).degree := Polynomial.degree_map_le
      _ < cur.degree := degree_pRemMv_lt parent cur hcur
      _ = (cur.map φ).degree :=
          (Polynomial.degree_map_eq_of_leadingCoeff_ne_zero φ hlc).symm
  have hdvd : cur.map φ ∣
      (Polynomial.C (φ cur.leadingCoeff ^ pRemExp parent cur) * parent.map φ
        - (pRemMv parent cur).map φ) := by
    have heq : Polynomial.C (φ cur.leadingCoeff ^ pRemExp parent cur) * parent.map φ
        - (pRemMv parent cur).map φ = A.map φ * cur.map φ := by
      rw [hAmap]; ring
    rw [heq]; exact dvd_mul_left _ _
  rw [← C_mul_mod, Polynomial.mod_eq_of_dvd_sub hdvd,
      (Polynomial.mod_eq_self_iff hcur_y).mpr hdeg]

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- A positive scalar multiple has the same `evalPoly` sign at every
extended point: `evalPoly (C c * b) pt = c · evalPoly b pt`. -/
private theorem PosAssoc.evalPoly_sign_eq {a b : Polynomial R}
    (h : PosAssoc a b) (pt : ExtendedPoint R) :
    SignType.sign (ExtendedPoint.evalPoly a pt) =
      SignType.sign (ExtendedPoint.evalPoly b pt) := by
  obtain ⟨c, hc, rfl⟩ := h
  have key : ExtendedPoint.evalPoly (Polynomial.C c * b) pt =
      c * ExtendedPoint.evalPoly b pt := by
    cases pt with
    | posInf =>
        simp only [ExtendedPoint.evalPoly, Polynomial.leadingCoeff_mul,
          Polynomial.leadingCoeff_C]
    | negInf =>
        simp only [ExtendedPoint.evalPoly, Polynomial.natDegree_C_mul (ne_of_gt hc),
          Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
        ring
    | finite x =>
        simp only [ExtendedPoint.evalPoly, Polynomial.eval_mul, Polynomial.eval_C]
  rw [key, sign_mul, sign_pos hc, one_mul]

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- `varAt` is invariant under elementwise positive-scalar association:
positive scalars preserve every leading-coefficient/evaluation sign, so
the sign-variation count is unchanged. -/
private theorem varAt_eq_of_forall₂_posAssoc {L₁ L₂ : List (Polynomial R)}
    (h : List.Forall₂ PosAssoc L₁ L₂) (pt : ExtendedPoint R) :
    varAt L₁ pt = varAt L₂ pt := by
  have hmap : L₁.map (fun Q => SignType.sign (ExtendedPoint.evalPoly Q pt))
      = L₂.map (fun Q => SignType.sign (ExtendedPoint.evalPoly Q pt)) := by
    induction h with
    | nil => rfl
    | cons hab _ ih =>
        rw [List.map_cons, List.map_cons, hab.evalPoly_sign_eq pt, ih]
  unfold varAt
  apply Var_congr_sign
  rw [List.map_map, List.map_map]
  exact hmap

omit [IsDomain D] [IsRealClosed R] [Algebra D R] [IsStrictOrderedRing R] in
/-- Trailing zero polynomials do not change `varAt` (their `evalPoly` is
`0`, which `Var` ignores). -/
private theorem varAt_append_replicate_zero (L : List (Polynomial R)) (n : ℕ)
    (pt : ExtendedPoint R) :
    varAt (L ++ List.replicate n 0) pt = varAt L pt := by
  unfold varAt Var
  rw [List.map_append, List.filter_append,
      show ((List.replicate n (0 : Polynomial R)).map
            (ExtendedPoint.evalPoly · pt)).filter (· ≠ 0) = [] from ?_,
      List.append_nil]
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨Q, hQ, rfl⟩ := hx
  rw [List.eq_of_mem_replicate hQ]
  cases pt <;> simp [ExtendedPoint.evalPoly]

omit [IsRealClosed R] in
/-- **Core Sturm correspondence (leafFormulaAux level).** Mirrors
`mkTRemsNode_gcd`: along a sub-path `sp` of `mkTRemsNode parent cur`,
the specialised sequence `(cur :: sp).map φ` is pointwise a
positive-scalar associate of the signed remainder sequence
`SRemS(cur_y, -(parent_y % cur_y))`. -/
private theorem mkTRemsNode_sturm_posAssoc
    (parent cur : Polynomial (MvPolynomial (Fin k) D)) (hcur : cur ≠ 0)
    {sp : List (Polynomial (MvPolynomial (Fin k) D))}
    (hsp : sp ∈ (mkTRemsNode parent cur).leafPaths)
    (y : Fin k → R)
    (hy : y ∈ (leafFormulaAux parent cur sp).realization (C := R))
    (hlc : (MvPolynomial.aeval y).toRingHom cur.leadingCoeff ≠ 0) :
    ∀ i, PosAssoc
      (SRemS (cur.map (MvPolynomial.aeval y).toRingHom)
        (-(parent.map (MvPolynomial.aeval y).toRingHom %
            cur.map (MvPolynomial.aeval y).toRingHom)) i)
      (((cur :: sp).map (Polynomial.map (MvPolynomial.aeval y).toRingHom)).getD i 0) := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom with hφ
  set Rp := -(pRemMv parent cur) with Rp_def
  rw [mkTRemsNode, ite_eq_right hcur] at hsp; dsimp only at hsp
  set cs := (Tru_finite Rp).toFinset.toList with cs_def
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
    have hc_tru : c ∈ Tru Rp :=
      (Set.Finite.mem_toFinset _).mp (Finset.mem_toList.mp hc_cs)
    have hRp_ne : Rp ≠ 0 := by
      intro h; rw [h, Tru_empty_of_eq_zero] at hc_tru; exact hc_tru.elim
    have hc_ne : c ≠ 0 := fun h => absurd (h ▸ hc_tru) (zero_not_mem_Tru Rp hRp_ne)
    simp only [leafFormulaAux, ite_eq_right hc_ne, Formula.realization_and] at hy
    obtain ⟨hy_deg, hy_rest⟩ := hy
    obtain ⟨hRc, hlc_c⟩ := degFormula_Tru_spec Rp c hc_tru hc_ne y hy_deg
    have hK : (0 : R) < φ cur.leadingCoeff ^ pRemExp parent cur :=
      Even.pow_pos (pRemExp_even parent cur) hlc
    have hcmap : c.map φ = Polynomial.C (φ cur.leadingCoeff ^ pRemExp parent cur)
        * (-(parent.map φ % cur.map φ)) := by
      rw [← hRc, Rp_def, Polynomial.map_neg, pRemMv_map_eq parent cur hcur y hlc, mul_neg]
    have hcy_ne : c.map φ ≠ 0 := by
      intro h
      apply hlc_c
      have hcoeff : φ c.leadingCoeff = (c.map φ).coeff c.natDegree :=
        (Polynomial.coeff_map φ c.natDegree).symm
      rw [hcoeff, h, Polynomial.coeff_zero]
    have hB_ne : -(parent.map φ % cur.map φ) ≠ 0 :=
      fun hB0 => hcy_ne (by rw [hcmap, hB0, mul_zero])
    have IH := mkTRemsNode_sturm_posAssoc cur c hc_ne hsp' y hy_rest hlc_c
    intro i
    rcases i with _ | n
    · exact PosAssoc.refl _
    · rw [List.map_cons, List.getD_cons_succ, SRemS_succ _ _ hB_ne n]
      refine PosAssoc.trans (SRemS_posAssoc_smul_left _ hK _ _ n).symm ?_
      have ih_n := IH n
      rw [hcmap, mod_C_mul _ (ne_of_gt hK)] at ih_n
      exact ih_n
  · subst hc_zero
    simp only [RoseTree.leafPaths, List.mem_singleton] at hsp'
    subst hsp'
    simp only [RoseTree.root] at hy ⊢
    simp only [leafFormulaAux, ↓reduceIte] at hy
    have hRp_zero : Rp.map φ = 0 := by
      rw [realization_degFormula, Set.mem_ofPred_eq, Polynomial.degree_eq_bot] at hy; exact hy
    have hB0 : -(parent.map φ % cur.map φ) = 0 := by
      have hpRem0 : (pRemMv parent cur).map φ = 0 := by
        have hRn : Rp.map φ = -(pRemMv parent cur).map φ := by
          rw [Rp_def, Polynomial.map_neg]
        rw [hRp_zero] at hRn
        exact neg_eq_zero.mp hRn.symm
      rw [pRemMv_map_eq parent cur hcur y hlc, mul_eq_zero] at hpRem0
      rcases hpRem0 with h | h
      · exact absurd h (Polynomial.C_ne_zero.mpr (pow_ne_zero _ hlc))
      · rw [h, neg_zero]
    intro i
    rcases i with _ | n
    · exact PosAssoc.refl _
    · rw [hB0, SRemS_zero_ge (cur.map φ) 0 0 (by rw [SRemS_snd]) (n + 1) (by omega)]
      simp only [List.map_cons, List.map_nil, Polynomial.map_zero, List.getD_cons_succ]
      rw [show ([(0 : Polynomial R)].getD n 0) = 0 from by cases n <;> rfl]
      exact PosAssoc.refl 0
termination_by cur.natDegree
decreasing_by
  exact lt_of_le_of_lt (natDegree_mem_Tru_le hc_tru)
    (Polynomial.natDegree_lt_natDegree hRp_ne (by
      rw [Polynomial.degree_neg]; exact degree_pRemMv_lt parent cur hcur))

omit [IsRealClosed R] in
/-- **Top-level Sturm correspondence.** For a leaf `path` of `TRems P Q`,
the specialised sequence `(P :: path).map φ` is pointwise a
positive-scalar associate of the signed remainder sequence
`SRemS(P_y, Q_y)`. Mirrors `leafFormula_gcd`. -/
private theorem leafFormula_sturm_posAssoc
    (P Q : Polynomial (MvPolynomial (Fin k) D))
    {path : List (Polynomial (MvPolynomial (Fin k) D))}
    (hpath : path ∈ (TRems P Q).leafPaths)
    (y : Fin k → R)
    (hy : y ∈ (leafFormula P Q path).realization (C := R)) :
    ∀ i, PosAssoc
      (SRemS (P.map (MvPolynomial.aeval y).toRingHom)
        (Q.map (MvPolynomial.aeval y).toRingHom) i)
      (((P :: path).map (Polynomial.map (MvPolynomial.aeval y).toRingHom)).getD i 0) := by
  set φ := (MvPolynomial.aeval (R := D) y).toRingHom with hφ
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
    obtain ⟨hQq, hlc_q⟩ := degFormula_Tru_spec Q q hq_tru hq_ne y hy_deg
    have hQy_ne : Q.map φ ≠ 0 := by
      rw [hQq]
      intro h
      apply hlc_q
      have hcoeff : φ q.leadingCoeff = (q.map φ).coeff q.natDegree :=
        (Polynomial.coeff_map φ q.natDegree).symm
      rw [hcoeff, h, Polynomial.coeff_zero]
    have IH := mkTRemsNode_sturm_posAssoc P q hq_ne hsp y hy_rest hlc_q
    intro i
    rcases i with _ | n
    · exact PosAssoc.refl _
    · rw [List.map_cons, List.getD_cons_succ, SRemS_succ _ _ hQy_ne n, hQq]
      exact IH n
  · subst hc_zero
    simp only [RoseTree.leafPaths, List.mem_singleton] at hsp
    subst hsp
    simp only [RoseTree.root] at hy ⊢
    simp only [leafFormula, ↓reduceIte] at hy
    have hQy0 : Q.map φ = 0 := by
      rw [realization_degFormula, Set.mem_ofPred_eq, Polynomial.degree_eq_bot] at hy; exact hy
    intro i
    rcases i with _ | n
    · exact PosAssoc.refl _
    · rw [hQy0, SRemS_zero_ge (P.map φ) 0 0 (by rw [SRemS_snd]) (n + 1) (by omega)]
      simp only [List.map_cons, List.map_nil, Polynomial.map_zero, List.getD_cons_succ]
      rw [show ([(0 : Polynomial R)].getD n 0) = 0 from by cases n <;> rfl]
      exact PosAssoc.refl 0

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- `varAt` as an abstract `varAtSigns` over the `evalPoly`-signs at `pt`. -/
private theorem varAt_eq_varAtSigns (L : List (Polynomial R)) (pt : ExtendedPoint R) :
    varAt L pt = varAtSigns (L.map (fun Q => SignType.sign (ExtendedPoint.evalPoly Q pt))) := by
  rw [varAt, Var_eq_varAtSigns_map_sign, List.map_map]; rfl

/-- Two lists with equal `getD`-extension (default `0`) have equal
zero-filtered forms. -/
private theorem filter_eq_of_getD : ∀ (M₁ M₂ : List SignType),
    (∀ i, M₁.getD i 0 = M₂.getD i 0) →
    M₁.filter (· ≠ 0) = M₂.filter (· ≠ 0)
  | [], [], _ => rfl
  | [], b :: M₂', h => by
      have hb : b = 0 := by have := h 0; simpa using this.symm
      subst hb
      rw [List.filter_cons_of_neg (by simp)]
      exact filter_eq_of_getD [] M₂' (fun i => by have := h (i + 1); simpa using this)
  | a :: M₁', [], h => by
      have ha : a = 0 := by have := h 0; simpa using this
      subst ha
      rw [List.filter_cons_of_neg (by simp)]
      exact filter_eq_of_getD M₁' [] (fun i => by have := h (i + 1); simpa using this)
  | a :: M₁', b :: M₂', h => by
      have hab : a = b := by have := h 0; simpa using this
      subst hab
      have hrec : M₁'.filter (· ≠ 0) = M₂'.filter (· ≠ 0) :=
        filter_eq_of_getD M₁' M₂' (fun i => by have := h (i + 1); simpa using this)
      by_cases ha : a = 0
      · subst ha
        rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_neg (by simp), hrec]
      · rw [List.filter_cons_of_pos (by simpa using ha),
            List.filter_cons_of_pos (by simpa using ha), hrec]
  termination_by M₁ M₂ => M₁.length + M₂.length

/-- `varAtSigns` depends only on the `getD`-extension of the list (i.e. it
is invariant under appending/removing trailing zeros). -/
private theorem varAtSigns_eq_of_getD {M₁ M₂ : List SignType}
    (h : ∀ i, M₁.getD i 0 = M₂.getD i 0) : varAtSigns M₁ = varAtSigns M₂ := by
  rw [← varAtSigns_filter_ne_zero M₁, ← varAtSigns_filter_ne_zero M₂,
      filter_eq_of_getD M₁ M₂ h]

omit [IsDomain D] [IsRealClosed R] [Algebra D R] in
/-- If two polynomial lists are pointwise positive-scalar associates (via
`getD`, default `0`), their `varAt`s agree. -/
private theorem varAt_eq_of_pointwise_posAssoc (L₁ L₂ : List (Polynomial R))
    (pt : ExtendedPoint R) (h : ∀ i, PosAssoc (L₁.getD i 0) (L₂.getD i 0)) :
    varAt L₁ pt = varAt L₂ pt := by
  rw [varAt_eq_varAtSigns, varAt_eq_varAtSigns]
  apply varAtSigns_eq_of_getD
  intro i
  have hmap : ∀ (L : List (Polynomial R)),
      (L.map (fun Q => SignType.sign (ExtendedPoint.evalPoly Q pt))).getD i 0
        = SignType.sign (ExtendedPoint.evalPoly (L.getD i 0) pt) := by
    intro L
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases L[i]? with
    | none =>
        simp only [Option.map_none, Option.getD_none]
        cases pt <;> simp [ExtendedPoint.evalPoly]
    | some a => simp
  rw [hmap, hmap, (h i).evalPoly_sign_eq pt]

omit [IsDomain D] [IsRealClosed R] [Algebra D R] [IsStrictOrderedRing R] in
/-- The signed remainder sequence vanishes once the index exceeds
`Q.natDegree + 1` (the degrees strictly decrease). -/
private theorem SRemS_eq_zero_of_natDegree_lt (P Q : Polynomial R) (hP : P ≠ 0)
    (j : ℕ) (hj : Q.natDegree + 2 ≤ j) : SRemS P Q j = 0 := by
  by_contra hne
  have hall : ∀ i, i ≤ j → SRemS P Q i ≠ 0 := by
    intro i hij hz
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hP (by simpa using hz)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      exact hne (SRemS_zero_ge P Q m hz j (by omega))
  have h_le : ∀ k, k + 1 ≤ j → (SRemS P Q (k + 1)).natDegree + k ≤ Q.natDegree := by
    intro k
    induction k with
    | zero => intro _; simp [SRemS_snd]
    | succ n ih =>
      intro hk
      have hstep : (SRemS P Q (n + 1 + 1)).natDegree < (SRemS P Q (n + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree (hall (n + 1 + 1) (by omega))
          (degree_SRemS_lt P Q n (hall (n + 1) (by omega)))
      have := ih (by omega)
      omega
  have hfin := h_le (j - 1) (by omega)
  rw [show j - 1 + 1 = j from by omega] at hfin
  omega

omit [IsDomain D] [IsRealClosed R] [Algebra D R] [LinearOrder R] [IsStrictOrderedRing R] in
/-- The `getD` of a `SRemSList` is the corresponding `SRemS` value (or `0`
out of range). -/
private theorem SRemSList_getD (P Q : Polynomial R) (N i : ℕ) :
    (SRemSList P Q N).getD i 0 = if i < N then SRemS P Q i else 0 := by
  unfold SRemSList
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < N
  · rw [List.getElem?_range h, Option.map_some, Option.getD_some, ite_eq_left h]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega),
        Option.map_none, Option.getD_none, ite_eq_right h]

omit [IsDomain D] [IsRealClosed R] in
/-- If `y` satisfies `sturmLeafSignFormula seq sigPat` and `sigPat` has
the same length as `seq`, then `sigPat` is exactly the list of actual
leading-coefficient signs of `seq` at `y`. -/
private theorem sturmLeafSignFormula_sigPat_eq
    (seq : List (Polynomial (MvPolynomial (Fin k) D))) (sigPat : List SignType)
    (hlen : sigPat.length = seq.length) (y : Fin k → R)
    (h : y ∈ (Formula.sturmLeafSignFormula seq sigPat).realization (C := R)) :
    sigPat = seq.map (fun p => SignType.sign (MvPolynomial.aeval y p.leadingCoeff)) := by
  rw [Formula.realization_sturmLeafSignFormula, Set.mem_ofPred_eq] at h
  apply List.ext_getElem
  · rw [List.length_map]; exact hlen
  · intro i hi _
    rw [List.getElem_map]
    have hmem := h _ (List.getElem_mem (n := i)
      (h := by rw [List.length_zip, List.length_map, hlen, min_self]; omega))
    rw [List.getElem_zip, List.getElem_map] at hmem
    exact hmem.symm

omit [IsRealClosed R] in
/-- **Generalized combinatorial-to-actual Sturm-count bridge.** Identical to
`sturmCount_eq_actual_varAt_diff` but with the second Sturm argument an
*arbitrary* polynomial `S` (over `D[Y]`) in place of the hardcoded
`Ptil.derivative`. The leaf path now ranges over `TRems Ptil S`, and the
conclusion concerns the actual sign-change difference of `SRemS(P_y, S_y)`
where `S_y = S.map φ`. (`leafFormula_sturm_posAssoc` is already generic in the
second argument, so the proof is the `.derivative` one with the single
`derivative_map` step removed — `S_y` is the second argument directly.)

This is the Sturm–Tarski engine for BPR Theorem 2.76: taking
`S = Ptil.derivative * 𝒫` (with `𝒫` a product of powers of the family `𝒬`)
makes `S_y = P_y' · 𝒬_y^α`, so by Theorem 2.61 the difference is the
parametrized Tarski query `TaQ(𝒬_y^α, P_y)`. -/
theorem sturmCount_eq_actual_varAt_diff_gen
    (Ptil S : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D)))
    (sigPat : List SignType)
    (h_path : path ∈ (TRems Ptil S).leafPaths)
    (h_sigPat : sigPat ∈ allSignPatterns (Ptil :: path).length)
    (y : Fin k → R)
    (h_leaf : y ∈ (leafFormula Ptil S path).realization (C := R))
    (h_sign : y ∈ (Formula.sturmLeafSignFormula (Ptil :: path) sigPat).realization
                    (C := R))
    (hlc : MvPolynomial.aeval y Ptil.leadingCoeff ≠ 0) :
    let P_y := Ptil.map (MvPolynomial.aeval y).toRingHom;
    let S_y := S.map (MvPolynomial.aeval y).toRingHom;
    (sturmCount sigPat ((Ptil :: path).map Polynomial.natDegree) : ℤ) =
      ((varAt (SRemSList P_y S_y (S_y.natDegree + 2))
            (.negInf : ExtendedPoint R) : ℤ) -
        (varAt (SRemSList P_y S_y (S_y.natDegree + 2))
            (.posInf : ExtendedPoint R) : ℤ)) := by
  intro P_y S_y
  set φ : MvPolynomial (Fin k) D →+* R := (MvPolynomial.aeval y).toRingHom with hφ
  -- (1) `sigPat` is the actual leading-coefficient sign vector at `y`.
  have hlen : sigPat.length = (Ptil :: path).length := by
    rw [mem_allSignPatterns_iff] at h_sigPat; exact h_sigPat
  have hsigPat : sigPat =
      (Ptil :: path).map (fun p => SignType.sign (MvPolynomial.aeval y p.leadingCoeff)) :=
    sturmLeafSignFormula_sigPat_eq _ _ hlen y h_sign
  -- (2) Degree/sign preservation under specialisation.
  have hpres : ∀ p ∈ (Ptil :: path), p ≠ 0 →
      MvPolynomial.aeval y p.leadingCoeff ≠ 0 := by
    intro p hp hp0
    rcases List.mem_cons.mp hp with rfl | hp_path
    · exact hlc
    · exact leafFormula_path_lc_ne_zero Ptil S h_path y h_leaf p hp_path hp0
  have hpres_full : ∀ p ∈ (Ptil :: path),
      SignType.sign (MvPolynomial.aeval y p.leadingCoeff) =
        SignType.sign (p.map φ).leadingCoeff ∧
      p.natDegree = (p.map φ).natDegree := by
    intro p hp
    rcases eq_or_ne p 0 with rfl | hp0
    · refine ⟨?_, ?_⟩ <;> simp [hφ]
    · have hne : φ p.leadingCoeff ≠ 0 := hpres p hp hp0
      have hnd : (p.map φ).natDegree = p.natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hne
      have hlc_eq : (p.map φ).leadingCoeff = MvPolynomial.aeval y p.leadingCoeff := by
        unfold Polynomial.leadingCoeff
        rw [hnd, Polynomial.coeff_map]; rfl
      exact ⟨by rw [hlc_eq], hnd.symm⟩
  -- (3) The specialised path sequence and the actual `SRemS(P_y, S_y)` have
  --     equal `varAt` (pointwise positive-scalar associates modulo trailing 0s).
  have hcorr : ∀ pt : ExtendedPoint R,
      varAt (SRemSList P_y S_y (S_y.natDegree + 2)) pt
        = varAt ((Ptil :: path).map (Polynomial.map φ)) pt := by
    have hP_y_ne : P_y ≠ 0 := by
      have hc : P_y.coeff Ptil.natDegree = MvPolynomial.aeval y Ptil.leadingCoeff := by
        show (Ptil.map φ).coeff Ptil.natDegree = _
        rw [Polynomial.coeff_map]; rfl
      intro h
      rw [h, Polynomial.coeff_zero] at hc
      exact hlc hc.symm
    have hpw := leafFormula_sturm_posAssoc Ptil S h_path y h_leaf
    intro pt
    apply varAt_eq_of_pointwise_posAssoc
    intro i
    rw [SRemSList_getD]
    by_cases hiN : i < S_y.natDegree + 2
    · rw [ite_eq_left hiN]; exact hpw i
    · rw [ite_eq_right hiN]
      have hSRemS0 : SRemS P_y S_y i = 0 :=
        SRemS_eq_zero_of_natDegree_lt P_y S_y hP_y_ne i (by omega)
      have hL2 : ((Ptil :: path).map (Polynomial.map φ)).getD i 0 = 0 := by
        have hp := hpw i
        rw [hSRemS0] at hp
        obtain ⟨c, hc, hce⟩ := hp
        rcases mul_eq_zero.mp hce.symm with h | h
        · exact absurd h (Polynomial.C_ne_zero.mpr (ne_of_gt hc))
        · exact h
      rw [hL2]; exact PosAssoc.refl 0
  -- Assemble: replace `SRemSList` by the path, convert to `varAtSigns`, match.
  simp only [hcorr]
  rw [varAt_negInf_eq_varAtSigns, varAt_posInf_eq_varAtSigns]
  simp only [sturmCount, varAtNegInfWithDegrees]
  have hB : varAtSigns sigPat =
      varAtSigns (((Ptil :: path).map (Polynomial.map φ)).map
        (fun Q => SignType.sign Q.leadingCoeff)) := by
    rw [hsigPat]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    exact (hpres_full p hp).1
  have hA : varAtSigns ((sigPat.zip ((Ptil :: path).map Polynomial.natDegree)).map
        (fun sd => signWithParity sd.1 sd.2)) =
      varAtSigns (((Ptil :: path).map (Polynomial.map φ)).map
        (fun Q => signWithParity (SignType.sign Q.leadingCoeff) Q.natDegree)) := by
    rw [hsigPat, zip_map_map_diag]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    obtain ⟨hs, hd⟩ := hpres_full p hp
    simp only [Function.comp_apply]
    rw [hs, hd]
  rw [hA, hB]

omit [IsRealClosed R] in
/-- **Combinatorial-to-actual Sturm-count bridge**. On a
`y` satisfying a root truncation's `degFormula`, the leaf path's
`leafFormula`, and the full sequence's `sturmLeafSignFormula`, the
abstract `sturmCount sigPat ((Ptil :: path).map natDegree)` equals the
actual sign-change difference of the Sturm sequence `SRemS(P_y, P_y')`
at `±∞`, where `P_y = Ptil_y`. This is the substantive content of
BPR's Theorem 2.62 proof, matching the per-leaf "n" entries of
Example 2.63.

The argument: by the even exponent in `pRemExp`, each specialised TRems
pseudo-remainder `(-pRemMv ·).map φ` is a *positive* scalar multiple of
the corresponding signed remainder `SRemS`, so signs, degrees, and
leading-coefficient signs all agree (`Var_congr_sign`). The full
sequence `Ptil :: path` (with `Ptil` the root) corresponds to the
nonzero terms of `SRemS(P_y, P_y')`, and the trailing `0` of `path`
matches the trailing zeros of `SRemSList` (both ignored by
`varAtSigns`). Then `varAt(·) posInf = varAtSigns sigPat` and
`varAt(·) negInf = varAtNegInfWithDegrees sigPat degrees` via
`Var_eq_varAtSigns_map_sign` and `sign_neg_one_pow_mul`. -/
theorem sturmCount_eq_actual_varAt_diff
    (Ptil : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D)))
    (sigPat : List SignType)
    (h_path : path ∈ (TRems Ptil Ptil.derivative).leafPaths)
    (h_sigPat : sigPat ∈ allSignPatterns (Ptil :: path).length)
    (y : Fin k → R)
    (h_leaf : y ∈ (leafFormula Ptil Ptil.derivative path).realization (C := R))
    (h_sign : y ∈ (Formula.sturmLeafSignFormula (Ptil :: path) sigPat).realization
                    (C := R))
    (hlc : MvPolynomial.aeval y Ptil.leadingCoeff ≠ 0) :
    let P_y := Ptil.map (MvPolynomial.aeval y).toRingHom;
    (sturmCount sigPat ((Ptil :: path).map Polynomial.natDegree) : ℤ) =
      ((varAt (SRemSList P_y P_y.derivative
            (P_y.derivative.natDegree + 2))
            (.negInf : ExtendedPoint R) : ℤ) -
        (varAt (SRemSList P_y P_y.derivative
            (P_y.derivative.natDegree + 2))
            (.posInf : ExtendedPoint R) : ℤ)) := by
  intro P_y
  -- `Ptil.derivative` is the special case `S = Ptil.derivative` of the
  -- generalized bridge: `P_y.derivative = (Ptil.derivative).map φ` by
  -- `derivative_map`, so the two conclusions coincide.
  have hderiv : P_y.derivative
      = Ptil.derivative.map (MvPolynomial.aeval y).toRingHom :=
    Polynomial.derivative_map Ptil _
  rw [hderiv]
  exact sturmCount_eq_actual_varAt_diff_gen Ptil Ptil.derivative path sigPat
    h_path h_sigPat y h_leaf h_sign hlc

/-- **Per-triple Sturm-Tarski bridge**. Given a root truncation
`Ptil ∈ Tru (splitLast P)` and a `y` pinning `P_y` to degree
`Ptil.natDegree` (so `P_y = Ptil_y ≠ 0`), satisfying the leaf path's
`leafFormula` and the full sequence's `sturmLeafSignFormula sigPat`,
the fibre `Z_y = {x | P_y(x) = 0}` is non-empty iff `sigPat` is good
(positive abstract Sturm count for `(Ptil :: path)`'s natDegrees).

The proof (from BPR Example 2.63):

1. `degFormula_Tru_spec` gives `P_y = Ptil_y` and `lc(Ptil)_y ≠ 0`,
   so `P_y ≠ 0`.
2. `aeval_snoc_eq_eval_splitLast` converts to "∃ x, P_y.IsRoot x".
3. Remark 2.51 converts root-existence to
   `0 < varAt(SRemS) at -∞ - varAt at +∞`.
4. `sturmCount_eq_actual_varAt_diff` ties the actual varAt diff to the
   abstract `sturmCount sigPat`, matching the
   "n ≥ 1 ↔ goodSignPattern" criterion. -/
theorem sturm_iff_root_for_root_path_sigPat
    (P : MvPolynomial (Fin (k+1)) D)
    (_hinj : Function.Injective (algebraMap D R))
    (Ptil : Polynomial (MvPolynomial (Fin k) D))
    (path : List (Polynomial (MvPolynomial (Fin k) D)))
    (sigPat : List SignType)
    (h_Ptil : Ptil ∈ Tru (splitLast P))
    (h_path : path ∈ (TRems Ptil Ptil.derivative).leafPaths)
    (h_sigPat : sigPat ∈ allSignPatterns (Ptil :: path).length)
    (y : Fin k → R)
    (h_deg : y ∈ (degFormula (splitLast P) (↑Ptil.natDegree)).realization (C := R))
    (h_leaf : y ∈ (leafFormula Ptil Ptil.derivative path).realization (C := R))
    (h_sign : y ∈ (Formula.sturmLeafSignFormula (Ptil :: path) sigPat).realization
                    (C := R)) :
    (∃ x : R, MvPolynomial.aeval (Fin.snoc y x) P = 0) ↔
      goodSignPattern sigPat ((Ptil :: path).map Polynomial.natDegree) := by
  -- Tru never contains 0, and is empty if splitLast P = 0.
  have hsplit_ne : splitLast P ≠ 0 := by
    rintro h; rw [h, Tru_empty_of_eq_zero] at h_Ptil; exact h_Ptil
  have hPtil_ne : Ptil ≠ 0 := fun h => zero_not_mem_Tru _ hsplit_ne (h ▸ h_Ptil)
  -- Step 1: P_y = Ptil_y, with nonvanishing leading coefficient.
  obtain ⟨hP_y_eq, hlc⟩ :=
    degFormula_Tru_spec (splitLast P) Ptil h_Ptil hPtil_ne y h_deg
  -- Step 2: Convert to univariate root-existence on P_y = Ptil_y.
  rw [exists_aeval_snoc_iff_exists_isRoot_specialized, hP_y_eq]
  set P_y : Polynomial R := Ptil.map (MvPolynomial.aeval y).toRingHom with hP_y_def
  have hP_y_ne : P_y ≠ 0 := by
    rw [hP_y_def]; intro h; apply hlc
    have := congr_arg (fun p => Polynomial.coeff p Ptil.natDegree) h
    simpa [Polynomial.coeff_map] using this
  -- Step 3+4: Remark 2.51, then the abstract bridge.
  rw [remark_2_51 hasIVP_of_isRealClosed P_y hP_y_ne,
      ← sturmCount_eq_actual_varAt_diff Ptil path sigPat h_path h_sigPat
        y h_leaf h_sign hlc]
  -- Step 5: goodSignPattern is `0 < sturmCount` by definition.
  rfl

theorem fiber_nonempty_iff_some_good_disjunct
    (P : MvPolynomial (Fin (k+1)) D)
    (hinj : Function.Injective (algebraMap D R))
    (y : Fin k → R) :
    (∃ x : R, MvPolynomial.aeval (Fin.snoc y x) P = 0) ↔
    (y ∈ (degFormula (splitLast P) ⊥).realization (C := R) ∨
     ∃ (Ptil : Polynomial (MvPolynomial (Fin k) D))
       (path : List (Polynomial (MvPolynomial (Fin k) D)))
       (sigPat : List SignType),
        (Ptil, path, sigPat) ∈ goodRootLeafPatterns (splitLast P) ∧
        y ∈ (degFormula (splitLast P) (↑Ptil.natDegree)).realization (C := R) ∧
        y ∈ (leafFormula Ptil Ptil.derivative path).realization (C := R) ∧
        y ∈ (Formula.sturmLeafSignFormula (Ptil :: path) sigPat).realization
              (C := R)) := by
  constructor
  · -- Forward: ∃ x → P_y = 0 ∨ ∃ good triple.
    intro h_exists
    by_cases hP_y0 : (splitLast P).map (MvPolynomial.aeval y).toRingHom = 0
    · left
      rw [realization_degFormula, Set.mem_ofPred_eq, Polynomial.degree_eq_bot]
      exact hP_y0
    · right
      have hsplit_ne : splitLast P ≠ 0 :=
        fun h => hP_y0 (by rw [h, Polynomial.map_zero])
      -- Find the truncation Ptil ∈ Tru with deg P_y = deg Ptil.
      obtain ⟨Ptil, hPtil_mem, hPtil_deg⟩ :=
        Tru_covers_degrees hinj (splitLast P) hsplit_ne y hP_y0
      have h_deg : y ∈ (degFormula (splitLast P) (↑Ptil.natDegree)).realization
          (C := R) := by
        rw [realization_degFormula, Set.mem_ofPred_eq]; exact hPtil_deg
      -- Find a TRems(Ptil, Ptil') leaf path covering y.
      obtain ⟨path, h_path, h_leaf⟩ :=
        leafFormula_covering hinj Ptil Ptil.derivative y
      -- Construct sigPat = actual signs of (Ptil :: path)'s leading coeffs.
      set sigPat : List SignType :=
        (Ptil :: path).map
          (fun p => SignType.sign (MvPolynomial.aeval y p.leadingCoeff))
        with sigPat_def
      have h_sigPat : sigPat ∈ allSignPatterns (Ptil :: path).length := by
        rw [mem_allSignPatterns_iff, sigPat_def, List.length_map]
      have h_sign : y ∈ (Formula.sturmLeafSignFormula (Ptil :: path)
          sigPat).realization (C := R) := by
        rw [Formula.realization_sturmLeafSignFormula]
        simp only [Set.mem_ofPred_eq]
        intro ps hps
        rw [sigPat_def, zip_map_map_diag, List.mem_map] at hps
        obtain ⟨p, _, rfl⟩ := hps
        rfl
      have h_good : goodSignPattern sigPat ((Ptil :: path).map Polynomial.natDegree) :=
        (sturm_iff_root_for_root_path_sigPat P hinj Ptil path sigPat
          hPtil_mem h_path h_sigPat y h_deg h_leaf h_sign).mp h_exists
      exact ⟨Ptil, path, sigPat,
        mem_goodRootLeafPatterns_iff.mpr ⟨hPtil_mem, h_path, h_sigPat, h_good⟩,
        h_deg, h_leaf, h_sign⟩
  · -- Backward.
    rintro (h_bot | ⟨Ptil, path, sigPat, h_mem, h_deg, h_leaf, h_sign⟩)
    · -- P_y = 0: any x is a root.
      rw [realization_degFormula, Set.mem_ofPred_eq, Polynomial.degree_eq_bot] at h_bot
      rw [exists_aeval_snoc_iff_exists_isRoot_specialized]
      exact ⟨0, by rw [h_bot]; simp [Polynomial.IsRoot]⟩
    · obtain ⟨hPtil_mem, h_path, h_sigPat, h_good⟩ :=
        mem_goodRootLeafPatterns_iff.mp h_mem
      exact (sturm_iff_root_for_root_path_sigPat P hinj Ptil path sigPat
        hPtil_mem h_path h_sigPat y h_deg h_leaf h_sign).mpr h_good

/-- The fibre-non-empty QF formula `fiberFormula_high P` realises to the
fibre-non-empty set.

The proof unfolds the `disjListO`-of-`cons` form: the head disjunct is
the `P_y = 0` locus `degFormula P_split ⊥`, and the tail disjuncts range
over `goodRootLeafPatterns`. It reduces to the combinatorial statement
`fiber_nonempty_iff_some_good_disjunct`, whose Sturm-Tarski content is
the bridge `sturmCount_eq_actual_varAt_diff`. -/
theorem fiberFormula_high_realization
    (P : MvPolynomial (Fin (k+1)) D)
    (hinj : Function.Injective (algebraMap D R)) :
    (fiberFormula_high P).realization (C := R) =
      {y : Fin k → R |
        ∃ x : R, MvPolynomial.aeval (Fin.snoc y x) P = 0} := by
  ext y
  rw [Set.mem_ofPred_eq, fiber_nonempty_iff_some_good_disjunct P hinj y]
  unfold fiberFormula_high
  rw [Formula.realization_disjListO, Set.mem_ofPred_eq]
  simp only [List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨Φ, hΦ_mem, hy_in⟩
    rcases hΦ_mem with rfl | ⟨⟨Ptil, path, sigPat⟩, h_mem, rfl⟩
    · -- Head disjunct: the P_y = 0 locus.
      left
      rwa [Formula.realization_mapAtom_toOrderedFieldAtom] at hy_in
    · -- A good triple disjunct.
      right
      simp only [Formula.realization_and, Set.mem_inter_iff,
        Formula.realization_mapAtom_toOrderedFieldAtom] at hy_in
      obtain ⟨⟨h_deg, h_leaf⟩, h_sign⟩ := hy_in
      exact ⟨Ptil, path, sigPat, h_mem, h_deg, h_leaf, h_sign⟩
  · rintro (h_bot | ⟨Ptil, path, sigPat, h_mem, h_deg, h_leaf, h_sign⟩)
    · refine ⟨_, Or.inl rfl, ?_⟩
      rwa [Formula.realization_mapAtom_toOrderedFieldAtom]
    · refine ⟨_, Or.inr ⟨(Ptil, path, sigPat), h_mem, rfl⟩, ?_⟩
      simp only [Formula.realization_and, Set.mem_inter_iff,
        Formula.realization_mapAtom_toOrderedFieldAtom]
      exact ⟨⟨h_deg, h_leaf⟩, h_sign⟩

end FiberFormulaHighRealization

end Azurite.BPR

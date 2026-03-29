/-
  Monomials (coefficient × monic monomial) for multivariate polynomials.
-/
import Azurite.AzMvPolynomial.MonicMonomial
import Azurite.AzMvPolynomial.MonicMonomialProofs
import Azurite.AzPolynomial.StringLemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.TakeDrop

namespace Azurite
open AzPolynomial

instance : DecidablePred isPolySyntaxChar := fun c =>
  if h : (c.toNat ≥ '0'.toNat ∧ c.toNat ≤ '9'.toNat) ∨ c = '+' ∨ c = '-' ∨ c = '*' ∨ c = '^'
  then isTrue h else isFalse h

/-- A character used in polynomial syntax that must not appear in coefficient
    representations: `+`, `*`, `^`. (Digits and `-` are allowed.) -/
def isCoeffSyntaxChar (c : Char) : Prop :=
  c = '+' ∨ c = '*' ∨ c = '^'

/-- Typeclass for coefficient types that can be serialized/deserialized as character
    sequences. Unlike `ParsableVar`, this does not extend `Var`, and `-` is permitted
    as the first character of the representation (to support negative coefficients). -/
class ParsableCoeff (R : Type _) [Semiring R] where
  one_ne_zero : (1 : R) ≠ 0
  toChars : R → List Char
  parseChars : List Char → Option R
  parse_toChars : ∀ r : R, parseChars (toChars r) = some r
  toChars_nonempty : ∀ r : R, toChars r ≠ []
  /-- No coefficient-syntax character (`+`, `*`, `^`) occurs anywhere. -/
  toChars_no_syntax : ∀ r : R, ∀ c ∈ toChars r, ¬ isCoeffSyntaxChar c
  /-- `-` may only occur as the very first character. -/
  toChars_no_minus_tail : ∀ r : R, ∀ c ∈ (toChars r).tail, c ≠ '-'
  /-- The first character is a poly-syntax character (digit or `-`). -/
  toChars_head_is_syntax : ∀ r : R, ∃ h : toChars r ≠ [], isPolySyntaxChar ((toChars r).head h)
  /-- An optional representation of `-1`, used for displaying `-x` instead of `-1*x`. -/
  negOne : Option {c : R // c ≠ 0 ∧ c ≠ 1} := none
  /-- If `toChars r` starts with `-`, then the tail is nonempty and its head is
      a poly-syntax character (a digit). This ensures the parser can distinguish
      `-3*x` (coefficient) from `-x` (negOne). -/
  toChars_minus_next_syntax : ∀ r : R, ∀ h : toChars r ≠ [],
    (toChars r).head h = '-' →
    (toChars r).tail ≠ [] ∧ ∀ h2, isPolySyntaxChar ((toChars r).tail.head h2)

/-- A monomial: a nonzero coefficient of type `R` paired with a monic monomial.
    The coefficient is stored as a subtype `{c : R // c ≠ 0}` to ensure
    that zero monomials are unrepresentable. -/
structure Monomial (σ : Type _) {n : ℕ} [LinearOrder σ] [Var σ n]
    (R : Type _) [Semiring R] (ord : MonomialOrder := .Degrevlex) where
  coeff : {c : R // c ≠ 0}
  monic : MonicMonomial σ ord

instance {R : Type _} [Semiring R] [DecidableEq R] {σ : Type _} {n : ℕ}
    [LinearOrder σ] [Var σ n] {ord : MonomialOrder} :
    DecidableEq (Monomial σ R ord) :=
  fun a b => by
    cases a; cases b
    simp only [Monomial.mk.injEq]
    exact instDecidableAnd

namespace Monomial

variable {R : Type _} [Semiring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- The identity monomial with coefficient `1` and all exponents zero. -/
def one [One R] (h : (1 : R) ≠ 0) : Monomial σ R ord :=
  ⟨⟨1, h⟩, MonicMonomial.one⟩

/-- Negate a monomial by negating its coefficient. -/
def neg [Neg R] (hne : ∀ c : R, c ≠ 0 → -c ≠ 0) (m : Monomial σ R ord) : Monomial σ R ord :=
  ⟨⟨-m.coeff.val, hne m.coeff.val m.coeff.property⟩, m.monic⟩

/-- `Neg` instance for `Monomial` when the coefficient type is a `Ring`. -/
instance {R : Type _} [Ring R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder} : Neg (Monomial σ R ord) where
  neg m := ⟨⟨-m.coeff.val, neg_ne_zero.mpr m.coeff.property⟩, m.monic⟩

/-- Convert a monomial to use a different monomial ordering. -/
def withOrder (m : Monomial σ R ord) (ord' : MonomialOrder) : Monomial σ R ord' :=
  ⟨m.coeff, m.monic.withOrder ord'⟩

@[simp] theorem coeff_withOrder (m : Monomial σ R ord) (ord' : MonomialOrder) :
    (m.withOrder ord').coeff = m.coeff := rfl

/-- The total degree of a monomial (sum of all exponents in the monic part). -/
def totalDegree (m : Monomial σ R ord) : ℕ :=
  m.monic.totalDegree

/-- Evaluate a monomial at a point given by `f : σ → R`.
    Computes `coeff * ∏ i, f(var_i) ^ exp_i`. -/
def eval [CommMonoidWithZero R] (m : Monomial σ R ord) (f : σ → R) : R :=
  m.coeff.val * m.monic.eval f

/-- Rename variables via a map `f : σ₁ → σ₂`. -/
def rename {σ₂ : Type _} {n₂ : ℕ} [LinearOrder σ₂] [v₂ : Var σ₂ n₂]
    (m : Monomial σ R ord) (f : σ → σ₂)
    (ord₂ : MonomialOrder := ord) : Monomial σ₂ R ord₂ :=
  ⟨m.coeff, m.monic.rename f ord₂⟩

/-- Evaluating a renamed monomial equals evaluating the original with a composed assignment. -/
theorem eval_rename {σ₂ : Type _} {n₂ : ℕ} [LinearOrder σ₂] [v₂ : Var σ₂ n₂]
    [CommMonoidWithZero R]
    (m : Monomial σ R ord) (f : σ → σ₂) (g : σ₂ → R) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).eval (n := n₂) g = m.eval (g ∘ f) := by
  simp only [eval, rename, MonicMonomial.eval_rename]

/-- Evaluating the negation of a monomial gives the negation of its evaluation. -/
theorem eval_neg {R : Type _} [CommRing R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder} (m : Monomial σ R ord) (f : σ → R) :
    (-m).eval f = -(m.eval f) := by
  simp only [eval, Neg.neg, neg_mul]


/-- Multiply two monomials (multiply coefficients, multiply monic parts). -/
def mul [NoZeroDivisors R] (a b : Monomial σ R ord) : Monomial σ R ord :=
  ⟨⟨a.coeff.val * b.coeff.val, mul_ne_zero a.coeff.property b.coeff.property⟩,
   a.monic * b.monic⟩

instance [NoZeroDivisors R] : Mul (Monomial σ R ord) := ⟨mul⟩

/-- Evaluating a product of monomials equals the product of their evaluations. -/
theorem eval_mul {R : Type _} [CommSemiring R] [NoZeroDivisors R]
    {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}
    (a b : Monomial σ R ord) (f : σ → R) :
    (a * b).eval f = a.eval f * b.eval f := by
  simp only [eval]
  simp only [show (a * b).coeff.val = a.coeff.val * b.coeff.val from rfl,
             show (a * b).monic = a.monic * b.monic from rfl]
  simp only [MonicMonomial.eval, MonicMonomial.mul_exponents,
             Fin.getElem_fin, Vector.getElem_ofFn, pow_add]
  rw [Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

instance [Nontrivial R] : One (Monomial σ R ord) :=
  ⟨⟨⟨1, one_ne_zero⟩, MonicMonomial.one⟩⟩

@[ext] theorem ext' (a b : Monomial σ R ord)
    (hc : a.coeff.val = b.coeff.val) (hm : a.monic = b.monic) : a = b := by
  rcases a with ⟨ac, am⟩; rcases b with ⟨bc, bm⟩
  simp only at hc hm
  subst hm; congr 1; exact Subtype.ext hc

section CommMonoidInstance

set_option linter.unusedSectionVars false in
@[simp] theorem mul_coeff_val [NoZeroDivisors R] (a b : Monomial σ R ord) :
    (a * b).coeff.val = a.coeff.val * b.coeff.val := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem mul_monic [NoZeroDivisors R] (a b : Monomial σ R ord) :
    (a * b).monic = a.monic * b.monic := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem one_coeff_val [Nontrivial R] : (1 : Monomial σ R ord).coeff.val = 1 := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem one_monic [Nontrivial R] : (1 : Monomial σ R ord).monic = 1 := rfl

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

omit [Nontrivial R] in
theorem mul_assoc (a b c : Monomial σ R ord) : a * b * c = a * (b * c) := by
  apply ext' <;> simp [_root_.mul_assoc]

theorem one_mul (a : Monomial σ R ord) : 1 * a = a := by
  apply ext' <;> simp

theorem mul_one (a : Monomial σ R ord) : a * 1 = a := by
  apply ext' <;> simp

omit [Nontrivial R] in
theorem mul_comm (a b : Monomial σ R ord) : a * b = b * a := by
  apply ext' <;> simp [_root_.mul_comm]

instance : CommMonoid (Monomial σ R ord) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

end CommMonoidInstance

/-- Convert a monomial to a list of characters.
    - If the monic part is `1`, return the coefficient representation.
    - If the coefficient is `1`, return the monic monomial representation.
    - Otherwise, join the two with `*`. -/
def toChars [DecidableEq R] [ParsableCoeff R] [pv : ParsableVar σ n]
    (m : Monomial σ R ord) : List Char :=
  if m.monic = 1 then
    ParsableCoeff.toChars m.coeff.val
  else if m.coeff.val = 1 then
    m.monic.toChars
  else match ParsableCoeff.negOne (R := R) with
    | some ⟨c, _⟩ =>
      if m.coeff.val = c then '-' :: m.monic.toChars
      else ParsableCoeff.toChars m.coeff.val ++ ['*'] ++ m.monic.toChars
    | none => ParsableCoeff.toChars m.coeff.val ++ ['*'] ++ m.monic.toChars

/-- Parse a character list into a `Monomial`.
    Uses the first character to distinguish:
    - Lowercase letter → starts a monic monomial (coefficient is implicitly `1`).
    - Otherwise → starts a coefficient. A `*` separator, if present, separates
      the coefficient from the monic monomial part. -/
def parse [DecidableEq R] [ParsableCoeff R] [pv : ParsableVar σ n]
    (cs : List Char) : Option (Monomial σ R ord) :=
  match cs with
  | [] => none
  | c :: rest =>
    if decide (¬ isPolySyntaxChar c) then
      -- Starts with non-syntax char: parse as monic monomial, coeff = 1
      (MonicMonomial.parse (ord := ord) cs).map (fun m => ⟨⟨1, ParsableCoeff.one_ne_zero⟩, m⟩)
    else if _ : c = '-' then
      match rest with
      | c' :: _ =>
        if decide (¬ isPolySyntaxChar c') then
          -- '-' followed by non-syntax char: coefficient is negOne
          match ParsableCoeff.negOne (R := R) with
          | some ⟨negOneVal, hne, _⟩ =>
            (MonicMonomial.parse (ord := ord) rest).map
              (fun m => ⟨⟨negOneVal, hne⟩, m⟩)
          | none => none
        else
          -- '-' followed by syntax char: fall through to span-based parsing
          let (coeffPart, rest') := cs.span (· != '*')
          match rest' with
          | [] =>
            (ParsableCoeff.parseChars coeffPart).bind (fun c =>
              if hc : c = 0 then none else some ⟨⟨c, hc⟩, 1⟩)
          | '*' :: monicPart =>
            (ParsableCoeff.parseChars coeffPart).bind (fun c =>
              if hc : c = 0 then none
              else (MonicMonomial.parse (ord := ord) monicPart).map
                (fun m => ⟨⟨c, hc⟩, m⟩))
          | _ => none
      | [] =>
        -- Just '-': try as coefficient
        let (coeffPart, rest') := cs.span (· != '*')
        match rest' with
        | [] =>
          (ParsableCoeff.parseChars coeffPart).bind (fun c =>
            if hc : c = 0 then none else some ⟨⟨c, hc⟩, 1⟩)
        | '*' :: monicPart =>
          (ParsableCoeff.parseChars coeffPart).bind (fun c =>
            if hc : c = 0 then none
            else (MonicMonomial.parse (ord := ord) monicPart).map
              (fun m => ⟨⟨c, hc⟩, m⟩))
        | _ => none
    else
      -- Starts with non-minus syntax char (digit): span-based parsing
      let (coeffPart, rest') := cs.span (· != '*')
      match rest' with
      | [] =>
        (ParsableCoeff.parseChars coeffPart).bind (fun c =>
          if hc : c = 0 then none else some ⟨⟨c, hc⟩, 1⟩)
      | '*' :: monicPart =>
        (ParsableCoeff.parseChars coeffPart).bind (fun c =>
          if hc : c = 0 then none
          else (MonicMonomial.parse (ord := ord) monicPart).map
            (fun m => ⟨⟨c, hc⟩, m⟩))
      | _ => none

theorem toChars_ne_nil {R : Type _} [Semiring R] {σ : Type _} {n : ℕ} [LinearOrder σ]
    [pv : ParsableVar σ n] {ord : MonomialOrder}
    [DecidableEq R] [ParsableCoeff R]
    (m : Monomial σ R ord) : m.toChars ≠ [] := by
  unfold toChars
  split_ifs with h1 h2
  · exact ParsableCoeff.toChars_nonempty _
  · exact MonicMonomial.toChars_ne_nil m.monic h1
  · cases hn : ParsableCoeff.negOne (R := R) with
    | none => intro h; simp at h
    | some c => dsimp only [hn]; split_ifs <;> (intro h; simp at h)

theorem plus_notin_toChars {R : Type _} [Semiring R] {σ : Type _} {n : ℕ} [LinearOrder σ]
    [pv : ParsableVar σ n] {ord : MonomialOrder}
    [DecidableEq R] [ParsableCoeff R]
    (m : Monomial σ R ord) : '+' ∉ m.toChars := by
  unfold toChars
  split_ifs with h1 h2
  · intro h; exact ParsableCoeff.toChars_no_syntax _ _ h (Or.inl rfl)
  · exact MonicMonomial.plus_notin_toChars m.monic
  · cases hn : ParsableCoeff.negOne (R := R) with
    | none =>
      intro h; rw [List.mem_append, List.mem_append] at h
      rcases h with (h | h) | h
      · exact ParsableCoeff.toChars_no_syntax _ _ h (Or.inl rfl)
      · simp at h
      · exact MonicMonomial.plus_notin_toChars m.monic h
    | some c =>
      dsimp only [hn]
      split_ifs with hc
      · intro h; simp at h; exact MonicMonomial.plus_notin_toChars m.monic h
      · intro h; rw [List.mem_append, List.mem_append] at h
        rcases h with (h | h) | h
        · exact ParsableCoeff.toChars_no_syntax _ _ h (Or.inl rfl)
        · simp at h
        · exact MonicMonomial.plus_notin_toChars m.monic h

theorem minus_notin_tail_toChars {R : Type _} [Semiring R] {σ : Type _} {n : ℕ} [LinearOrder σ]
    [pv : ParsableVar σ n] {ord : MonomialOrder}
    [DecidableEq R] [ParsableCoeff R]
    (m : Monomial σ R ord) : '-' ∉ m.toChars.tail := by
  unfold toChars
  split_ifs with h1 h2
  · exact fun h => ParsableCoeff.toChars_no_minus_tail _ _ h rfl
  · exact fun h => MonicMonomial.minus_notin_toChars m.monic (List.mem_of_mem_tail h)
  · cases hn : ParsableCoeff.negOne (R := R) with
    | none =>
      have hne := ParsableCoeff.toChars_nonempty m.coeff.val
      rw [List.append_assoc, List.tail_append_of_ne_nil hne]
      intro h; rw [List.mem_append] at h
      rcases h with h | h
      · exact ParsableCoeff.toChars_no_minus_tail _ _ h rfl
      · simp only [List.singleton_append, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h (by decide)
        · exact MonicMonomial.minus_notin_toChars m.monic h
    | some c =>
      dsimp only [hn]
      split_ifs with hc
      · exact fun h => MonicMonomial.minus_notin_toChars m.monic h
      · have hne := ParsableCoeff.toChars_nonempty m.coeff.val
        rw [List.append_assoc, List.tail_append_of_ne_nil hne]
        intro h; rw [List.mem_append] at h
        rcases h with h | h
        · exact ParsableCoeff.toChars_no_minus_tail _ _ h rfl
        · simp only [List.singleton_append, List.mem_cons] at h
          rcases h with h | h
          · exact absurd h (by decide)
          · exact MonicMonomial.minus_notin_toChars m.monic h

lemma takeWhile_all (l : List Char) (h : ∀ x ∈ l, (x != '*') = true) :
    List.takeWhile (· != '*') l = l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [h a (List.mem_cons_self ..)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma dropWhile_all (l : List Char) (h : ∀ x ∈ l, (x != '*') = true) :
    List.dropWhile (· != '*') l = [] := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [h a (List.mem_cons_self ..)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma coeffChars_bne_star {R : Type _} [Semiring R] [ParsableCoeff R] (r : R) :
    ∀ x ∈ ParsableCoeff.toChars r, (x != '*') = true := by
  intro x hx; simp [bne_iff_ne]
  intro heq; exact ParsableCoeff.toChars_no_syntax _ _ (heq ▸ hx) (Or.inr (Or.inl rfl))

end Monomial

/-- Parse-toChars round-trip: `parse` correctly inverts `toChars`. -/
theorem Monomial.parse_toChars {R : Type _} [Semiring R] {σ : Type _} {n : ℕ} [LinearOrder σ]
    [pv : ParsableVar σ n] {ord : MonomialOrder}
    [DecidableEq R] [ParsableCoeff R]
    (m : Monomial σ R ord) :
    Monomial.parse m.toChars = some m := by
  unfold Monomial.toChars
  split_ifs with hmonic hcoeff
  · -- Case 1: monic = 1
    have hne := ParsableCoeff.toChars_nonempty m.coeff.val
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    rw [hct]; unfold Monomial.parse
    simp only [List.span_eq_takeWhile_dropWhile]
    have his_syntax : isPolySyntaxChar c := by
      obtain ⟨_, hs⟩ := ParsableCoeff.toChars_head_is_syntax m.coeff.val
      simp only [hct, List.head_cons] at hs; exact hs
    simp only [show ¬ (¬ isPolySyntaxChar c) from not_not.mpr his_syntax,
      decide_false, Bool.false_eq_true, ↓reduceIte]
    have hall : ∀ x ∈ (c :: t), (x != '*') = true :=
      fun x hx => Monomial.coeffChars_bne_star m.coeff.val x (by rw [hct]; exact hx)
    have hparse := ParsableCoeff.parse_toChars m.coeff.val
    rw [hct] at hparse
    by_cases hcm : c = '-'
    · subst hcm; cases t with
      | nil =>
        simp_all [dif_neg m.coeff.property, Option.bind_some]
        cases m with | mk => simp_all
      | cons c' t' =>
        have ⟨_, hsynt⟩ := ParsableCoeff.toChars_minus_next_syntax m.coeff.val hne (by simp [hct])
        have hcs : isPolySyntaxChar c' := by
          have h2 : (ParsableCoeff.toChars m.coeff.val).tail ≠ [] := by simp [hct]
          have := hsynt h2; simp [hct] at this; exact this
        have hall' : ∀ x ∈ c' :: t', (x != '*') = true :=
          fun x hx => hall x (List.mem_cons_of_mem _ hx)
        simp only [dite_true, show ¬ ¬ isPolySyntaxChar c' from not_not.mpr hcs,
          decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [Monomial.takeWhile_all ('-' :: c' :: t') hall, Monomial.dropWhile_all ('-' :: c' :: t') hall]
        simp_all [dif_neg m.coeff.property, Option.bind_some]
        cases m with | mk => simp_all
    · rw [Monomial.takeWhile_all (c :: t) hall, Monomial.dropWhile_all (c :: t) hall]
      simp only [hcm, dite_false]
      simp_all [dif_neg m.coeff.property, Option.bind_some]
      cases m with | mk => simp_all
  · -- Case 2: coeff = 1, monic ≠ 1
    have hne := MonicMonomial.toChars_ne_nil m.monic hmonic
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    rw [hct]; unfold Monomial.parse
    have hnot_syntax : ¬ isPolySyntaxChar c := by
      have h := MonicMonomial.toChars_head_not_syntax m.monic hmonic
      simp only [hct, List.head_cons] at h; exact h
    simp only [decide_eq_true hnot_syntax, ↓reduceIte]
    rw [← hct, MonicMonomial.parse_toChars]
    show Option.some { coeff := ⟨1, ParsableCoeff.one_ne_zero⟩, monic := m.monic } = some m
    congr 1; cases m; simp only [Monomial.mk.injEq]; exact ⟨Subtype.ext hcoeff.symm, trivial⟩
  · -- Case 3: coeff ≠ 1, monic ≠ 1
    suffices hCM : ∀ (hne : ParsableCoeff.toChars m.coeff.val ≠ []),
      Monomial.parse (ParsableCoeff.toChars m.coeff.val ++ ['*'] ++ m.monic.toChars) = some m by
      match hn : ParsableCoeff.negOne (R := R) with
      | some ⟨cneg, hne_neg, hne_one⟩ =>
        dsimp only; split_ifs with hcoeff_neg
        · have hne_monic := MonicMonomial.toChars_ne_nil m.monic hmonic
          obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne_monic
          rw [hct]; unfold Monomial.parse
          have hnot_syntax : ¬ isPolySyntaxChar c := by
            have h := MonicMonomial.toChars_head_not_syntax m.monic hmonic
            simp only [hct, List.head_cons] at h; exact h
          simp only [show isPolySyntaxChar '-' from (Or.inr (Or.inr (Or.inl rfl))),
            ↓reduceIte, decide_eq_true hnot_syntax]
          rw [hn]; simp only
          rw [← hct, MonicMonomial.parse_toChars, Option.map_some]
          simp only [dite_true]
          cases m
          simp_all [Monomial.mk.injEq]
          exact Subtype.ext hcoeff_neg.symm
        · exact hCM (ParsableCoeff.toChars_nonempty m.coeff.val)
      | none => exact hCM (ParsableCoeff.toChars_nonempty m.coeff.val)
    -- Prove the coeff*monic helper
    intro hne
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    have his_syntax : isPolySyntaxChar c := by
      obtain ⟨_, hs⟩ := ParsableCoeff.toChars_head_is_syntax m.coeff.val
      simp only [hct, List.head_cons] at hs; exact hs
    rw [hct]; unfold Monomial.parse
    simp only [List.span_eq_takeWhile_dropWhile]
    have hc_bne : (c != '*') = true :=
      Monomial.coeffChars_bne_star m.coeff.val c (by rw [hct]; exact List.mem_cons_self ..)
    have hall : ∀ x ∈ t, (x != '*') = true :=
      fun x hx => Monomial.coeffChars_bne_star m.coeff.val x
        (by rw [hct]; exact List.mem_cons_of_mem _ hx)
    have htw : List.takeWhile (· != '*') (c :: (t ++ ['*'] ++ m.monic.toChars)) = c :: t := by
      simp [hc_bne, List.takeWhile_append, Monomial.takeWhile_all t hall]
    have hdw : List.dropWhile (· != '*') (c :: (t ++ ['*'] ++ m.monic.toChars)) =
        '*' :: m.monic.toChars := by
      simp [hc_bne, List.dropWhile_append, Monomial.dropWhile_all t hall]
    simp only [show ¬ (¬ isPolySyntaxChar c) from not_not.mpr his_syntax,
      decide_false, Bool.false_eq_true, ↓reduceIte,
      List.cons_append, htw, hdw]
    have hparse := ParsableCoeff.parse_toChars m.coeff.val
    rw [hct] at hparse
    by_cases hcm : c = '-'
    · subst hcm; cases t with
      | nil =>
        simp only [dite_true, List.nil_append, List.singleton_append]
        simp only [show isPolySyntaxChar '*' from (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
        simp_all [dif_neg m.coeff.property, MonicMonomial.parse_toChars, Option.map_some,
          Option.bind_some]
      | cons c' t' =>
        have ⟨_, hsynt⟩ := ParsableCoeff.toChars_minus_next_syntax m.coeff.val hne (by simp [hct])
        have hcs : isPolySyntaxChar c' := by
          have h2 : (ParsableCoeff.toChars m.coeff.val).tail ≠ [] := by simp [hct]
          have := hsynt h2; simp [hct] at this; exact this
        simp only [dite_true]
        simp_all [dif_neg m.coeff.property, MonicMonomial.parse_toChars, Option.map_some,
          Option.bind_some]
    · simp only [hcm, dite_false]
      simp_all [dif_neg m.coeff.property, MonicMonomial.parse_toChars, Option.map_some,
        Option.bind_some]

/-! ### ParsableCoeff instances -/

section ParsableCoeffInstances

private lemma tail_mem_of_drop {c : α} {l : List α} (h : c ∈ l.tail) : c ∈ l.drop 1 := by
  cases l <;> simp_all

private lemma natToChars_no_coeff_syntax (n : ℕ) (c : Char) (hc : c ∈ natToChars n) :
    ¬ isCoeffSyntaxChar c := by
  intro h; rcases h with rfl | rfl | rfl
  · exact not_mem_natToChars_of_not_digit '+' (by decide) n hc
  · exact not_mem_natToChars_of_not_digit '*' (by decide) n hc
  · exact not_mem_natToChars_of_not_digit '^' (by decide) n hc

private lemma intToChars_no_coeff_syntax (z : ℤ) (c : Char) (hc : c ∈ intToChars z) :
    ¬ isCoeffSyntaxChar c := by
  rw [intToChars_natAbs] at hc
  split at hc
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · intro h
      rcases h with h | h | h <;> exact absurd h (by decide)
    · exact natToChars_no_coeff_syntax _ c hc
  · exact natToChars_no_coeff_syntax _ c hc

private lemma ratToChars_no_coeff_syntax (q : ℚ) (c : Char) (hc : c ∈ ratToChars q) :
    ¬ isCoeffSyntaxChar c := by
  simp only [ratToChars] at hc
  split at hc
  · exact intToChars_no_coeff_syntax _ c hc
  · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with (hc | rfl) | hc
    · exact intToChars_no_coeff_syntax _ c hc
    · intro h
      rcases h with h | h | h <;> exact absurd h (by decide)
    · exact natToChars_no_coeff_syntax _ c hc

private lemma natToChars_head_is_syntax (n : ℕ) :
    ∃ h : natToChars n ≠ [], isPolySyntaxChar ((natToChars n).head h) := by
  have hne := natToChars_ne_nil n
  refine ⟨hne, ?_⟩
  have ⟨hge, hle⟩ := mem_natToChars_only_digits n _ (List.head_mem hne)
  left; exact ⟨hge, hle⟩

private lemma intToChars_head_is_syntax (z : ℤ) :
    ∃ h : intToChars z ≠ [], isPolySyntaxChar ((intToChars z).head h) := by
  have hne := intToChars_ne_nil z
  obtain ⟨c, rest, hcr⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨hne, ?_⟩
  have hhead : (intToChars z).head hne = c := by simp [hcr]
  rw [hhead]
  have hc_mem : c ∈ intToChars z := by rw [hcr]; exact List.mem_cons_self ..
  rcases mem_intToChars_only_digits_or_dash z c hc_mem with hdash | hdig
  · rw [hdash]; exact Or.inr (Or.inr (Or.inl rfl))
  · left; exact hdig

private lemma ratToChars_head_is_syntax (q : ℚ) :
    ∃ h : ratToChars q ≠ [], isPolySyntaxChar ((ratToChars q).head h) := by
  have hne := ratToChars_ne_nil q
  obtain ⟨c, rest, hcr⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨hne, ?_⟩
  have hhead : (ratToChars q).head hne = c := by simp [hcr]
  rw [hhead]
  simp only [ratToChars] at hcr
  split at hcr
  · have hc_int : c ∈ intToChars q.num := by rw [hcr]; exact List.mem_cons_self ..
    rcases mem_intToChars_only_digits_or_dash q.num c hc_int with hdash | hdig
    · rw [hdash]; exact Or.inr (Or.inr (Or.inl rfl))
    · left; exact hdig
  · obtain ⟨hne_int, hsyn⟩ := intToChars_head_is_syntax q.num
    obtain ⟨c', rest', hcr'⟩ := List.exists_cons_of_ne_nil hne_int
    simp [hcr'] at hcr hsyn
    rw [← hcr.1]; exact hsyn

private lemma intToChars_minus_next_syntax (z : ℤ) :
    ∀ h : intToChars z ≠ [],
    (intToChars z).head h = '-' →
    (intToChars z).tail ≠ [] ∧ ∀ h2, isPolySyntaxChar ((intToChars z).tail.head h2) := by
  rw [intToChars_natAbs]; split_ifs with hz
  · intro _ _; simp only [List.tail_cons]
    exact ⟨natToChars_ne_nil _, fun h2 => by
      have ⟨hge, hle⟩ := mem_natToChars_only_digits z.natAbs _ (List.head_mem h2)
      exact Or.inl ⟨hge, hle⟩⟩
  · intro h hhead; exfalso
    have ⟨hge, _⟩ := mem_natToChars_only_digits z.natAbs _ (List.head_mem h)
    rw [hhead] at hge; exact absurd hge (by decide)

private lemma ratToChars_minus_next_syntax (q : ℚ) :
    ∀ h : ratToChars q ≠ [],
    (ratToChars q).head h = '-' →
    (ratToChars q).tail ≠ [] ∧ ∀ h2, isPolySyntaxChar ((ratToChars q).tail.head h2) := by
  unfold ratToChars; split_ifs with hden
  · simp only [intToChars_natAbs]; split_ifs with hlt
    · intro _ _; simp only [List.tail_cons]
      exact ⟨natToChars_ne_nil _, fun h2 => by
        have ⟨hge, hle⟩ := mem_natToChars_only_digits q.num.natAbs _ (List.head_mem h2)
        exact Or.inl ⟨hge, hle⟩⟩
    · intro h hhead; exfalso
      have ⟨hge, _⟩ := mem_natToChars_only_digits q.num.natAbs _ (List.head_mem h)
      rw [hhead] at hge; exact absurd hge (by decide)
  · intro h hhead
    obtain ⟨c, rest, hcr⟩ := List.exists_cons_of_ne_nil (intToChars_ne_nil q.num)
    simp only [hcr, List.cons_append, List.head_cons, List.tail_cons] at hhead ⊢
    subst hhead
    simp only [intToChars_natAbs] at hcr
    split_ifs at hcr with hlt
    · cases hcr
      exact ⟨List.append_ne_nil_of_left_ne_nil
        (List.append_ne_nil_of_left_ne_nil (natToChars_ne_nil _) _) _,
        fun h2 => by
          rw [List.head_append_of_ne_nil
            (List.append_ne_nil_of_left_ne_nil (natToChars_ne_nil _) _),
            List.head_append_of_ne_nil (natToChars_ne_nil _)]
          have ⟨hge, hle⟩ := mem_natToChars_only_digits q.num.natAbs _
            (List.head_mem (natToChars_ne_nil _))
          exact Or.inl ⟨hge, hle⟩⟩
    · exfalso
      have ⟨hge, _⟩ := mem_natToChars_only_digits q.num.natAbs '-'
        (by rw [hcr]; exact List.mem_cons_self ..)
      exact absurd hge (by decide)

instance : ParsableCoeff ℕ where
  one_ne_zero := by omega
  toChars := natToChars
  parseChars := parseNatChars
  parse_toChars := parseNatChars_natToChars
  toChars_nonempty := natToChars_ne_nil
  toChars_no_syntax := natToChars_no_coeff_syntax
  toChars_no_minus_tail := fun n _ hc heq =>
    not_mem_natToChars n (heq ▸ List.mem_of_mem_tail hc)
  toChars_head_is_syntax := natToChars_head_is_syntax
  toChars_minus_next_syntax := fun n h hhead => by
    exfalso
    have ⟨hge, _⟩ := mem_natToChars_only_digits n _ (List.head_mem h)
    simp [hhead] at hge

instance : ParsableCoeff ℤ where
  one_ne_zero := by omega
  toChars := intToChars
  parseChars := parseIntChars
  parse_toChars := parseIntChars_intToChars
  toChars_nonempty := intToChars_ne_nil
  toChars_no_syntax := intToChars_no_coeff_syntax
  toChars_no_minus_tail := fun z _ hc heq =>
    not_mem_tail_intToChars z (heq ▸ tail_mem_of_drop hc)
  toChars_head_is_syntax := intToChars_head_is_syntax
  negOne := some ⟨-1, by omega, by omega⟩
  toChars_minus_next_syntax := intToChars_minus_next_syntax

instance : ParsableCoeff ℚ where
  one_ne_zero := by exact one_ne_zero
  toChars := ratToChars
  parseChars := parseRatChars
  parse_toChars := parseRatChars_ratToChars
  toChars_nonempty := ratToChars_ne_nil
  toChars_no_syntax := ratToChars_no_coeff_syntax
  toChars_no_minus_tail := fun q _ hc heq =>
    not_mem_tail_ratToChars q (heq ▸ tail_mem_of_drop hc)
  toChars_head_is_syntax := ratToChars_head_is_syntax
  negOne := some ⟨-1, by decide, by decide⟩
  toChars_minus_next_syntax := ratToChars_minus_next_syntax

/-- Parse a character list as a `ZMod n` value: parse as ℕ, check `< n`, cast. -/
def parseZmodChars (m : ℕ) [NeZero m] (cs : List Char) : Option (ZMod m) :=
  (parseNatChars cs).bind (fun k => if k < m then some (k : ZMod m) else none)

private lemma parseZmodChars_zmodToChars {m : ℕ} [NeZero m] (c : ZMod m) :
    parseZmodChars m (zmodToChars c) = some c := by
  simp only [parseZmodChars, zmodToChars, parseNatChars_natToChars]
  simp only [Option.bind, if_pos (ZMod.val_lt c)]
  congr 1
  exact ZMod.natCast_zmod_val c

instance {m : ℕ} [NeZero m] [Fact (1 < m)] : ParsableCoeff (ZMod m) where
  one_ne_zero := by exact one_ne_zero
  toChars := zmodToChars
  parseChars := parseZmodChars m
  parse_toChars := parseZmodChars_zmodToChars
  toChars_nonempty := zmodToChars_ne_nil
  toChars_no_syntax := fun c _ch hch => natToChars_no_coeff_syntax c.val _ch hch
  toChars_no_minus_tail := fun c _ch hch heq =>
    not_mem_natToChars c.val (heq ▸ List.mem_of_mem_tail hch)
  toChars_head_is_syntax := fun c => natToChars_head_is_syntax c.val
  toChars_minus_next_syntax := fun c h hhead => by
    exfalso
    have := mem_natToChars_only_digits c.val _ (List.head_mem h)
    simp [hhead] at this

end ParsableCoeffInstances

section MonomialGuards

-- Use ℤ coefficients with AbcVar 3 variables: a, b, c
private def mkMon (c : ℤ) (hc : c ≠ 0) (v : Vector ℕ 3) : Monomial (AbcVar 3) ℤ :=
  ⟨⟨c, hc⟩, ⟨v⟩⟩

-- toChars: coefficient only (monic = 1)
#guard (mkMon 5 (by omega) (Vector.mk #[0, 0, 0] rfl)).toChars == "5".toList
#guard (mkMon (-3) (by omega) (Vector.mk #[0, 0, 0] rfl)).toChars == "-3".toList

-- toChars: monic only (coeff = 1)
#guard (mkMon 1 (by omega) (Vector.mk #[1, 0, 0] rfl)).toChars == "a".toList
#guard (mkMon 1 (by omega) (Vector.mk #[2, 1, 0] rfl)).toChars == "a^2*b".toList

-- toChars: coefficient * monic
#guard (mkMon 3 (by omega) (Vector.mk #[1, 0, 0] rfl)).toChars == "3*a".toList
#guard (mkMon (-2) (by omega) (Vector.mk #[1, 1, 0] rfl)).toChars == "-2*a*b".toList
#guard (mkMon 7 (by omega) (Vector.mk #[0, 0, 3] rfl)).toChars == "7*c^3".toList

-- parse round-trip: parse then toChars should give back the original string
#guard (Monomial.parse (σ := AbcVar 3) (R := ℤ) (ord := .Degrevlex) "5".toList ).map
  Monomial.toChars == some "5".toList
#guard (Monomial.parse (σ := AbcVar 3) (R := ℤ) (ord := .Degrevlex) "a".toList ).map
  Monomial.toChars == some "a".toList
#guard (Monomial.parse (σ := AbcVar 3) (R := ℤ) (ord := .Degrevlex) "3*a".toList ).map
  Monomial.toChars == some "3*a".toList
#guard (Monomial.parse (σ := AbcVar 3) (R := ℤ) (ord := .Degrevlex) "-2*a*b".toList ).map
  Monomial.toChars == some "-2*a*b".toList
#guard (Monomial.parse (σ := AbcVar 3) (R := ℤ) (ord := .Degrevlex) "a^2*b".toList ).map
  Monomial.toChars == some "a^2*b".toList

-- parse rejects invalid input
#guard (Monomial.parse (σ := AbcVar 3) (R := ℤ) (ord := .Degrevlex) "".toList ).map
  Monomial.toChars == (none : Option (List Char))
#guard (Monomial.parse (σ := AbcVar 3) (R := ℤ) (ord := .Degrevlex) "0".toList ).map
  Monomial.toChars == (none : Option (List Char))

end MonomialGuards

end Azurite

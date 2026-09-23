/-
  Monomials (coefficient × monic monomial) for `Monomial` — Fin-indexed.
-/
import Azurite.AzMvPolynomial.ParsableCoeff
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzMvPolynomial.ParsableCoeff.AzRat
import Azurite.AzMvPolynomial.MonicMonomial
import Azurite.AzMvPolynomial.MonicMonomialProofs

namespace Azurite
open AzPolynomial

/-- A monomial: a nonzero coefficient of type `R` paired with a
    Fin-indexed monic monomial.  The variable type is fixed to `Fin n`;
    naming is a display-layer concern. -/
structure Monomial (n : ℕ) (R : Type _) [Semiring R]
    (ord : MonomialOrder := .Degrevlex) where
  coeff : {c : R // c ≠ 0}
  monic : MonicMonomial n ord

instance {R : Type _} [Semiring R] [DecidableEq R] {n : ℕ} {ord : MonomialOrder} :
    DecidableEq (Monomial n R ord) :=
  fun a b => by
    cases a; cases b
    simp only [Monomial.mk.injEq]
    exact instDecidableAnd

namespace Monomial

variable {R : Type _} [Semiring R] {n : ℕ} {ord : MonomialOrder}

/-- The identity monomial with coefficient `1` and all exponents zero. -/
def one (h : (1 : R) ≠ 0) : Monomial n R ord :=
  ⟨⟨1, h⟩, MonicMonomial.one⟩

/-- Negate a monomial by negating its coefficient. -/
def neg [Neg R] (hne : ∀ c : R, c ≠ 0 → -c ≠ 0) (m : Monomial n R ord) :
    Monomial n R ord :=
  ⟨⟨-m.coeff.val, hne m.coeff.val m.coeff.property⟩, m.monic⟩

/-- `Neg` instance for `Monomial` when the coefficient type is a `Ring`. -/
instance {R : Type _} [Ring R] {n : ℕ} {ord : MonomialOrder} :
    Neg (Monomial n R ord) where
  neg m := ⟨⟨-m.coeff.val, neg_ne_zero.mpr m.coeff.property⟩, m.monic⟩

/-- Convert a monomial to use a different monomial ordering. -/
def withOrder (m : Monomial n R ord) (ord' : MonomialOrder) :
    Monomial n R ord' :=
  ⟨m.coeff, m.monic.withOrder ord'⟩

@[simp] theorem coeff_withOrder (m : Monomial n R ord) (ord' : MonomialOrder) :
    (m.withOrder ord').coeff = m.coeff := rfl

/-- The total degree of a monomial (sum of all exponents in the monic part). -/
def totalDegree (m : Monomial n R ord) : ℕ :=
  m.monic.totalDegree

set_option linter.overlappingInstances false in
/-- Evaluate a monomial at a point given by `f : Fin n → R`. -/
def eval [CommMonoidWithZero R] (m : Monomial n R ord) (f : Fin n → R) : R :=
  m.coeff.val * m.monic.eval f

/-- Rename variables via a map `f : Fin n → Fin n₂`. -/
def rename {n₂ : ℕ} (m : Monomial n R ord) (f : Fin n → Fin n₂)
    (ord₂ : MonomialOrder := ord) : Monomial n₂ R ord₂ :=
  ⟨m.coeff, m.monic.rename f ord₂⟩

set_option linter.overlappingInstances false in
/-- Evaluating a renamed monomial equals evaluating the original with a composed assignment. -/
theorem eval_rename {n₂ : ℕ} [CommMonoidWithZero R]
    (m : Monomial n R ord) (f : Fin n → Fin n₂) (g : Fin n₂ → R) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).eval g = m.eval (g ∘ f) := by
  simp only [eval, rename, MonicMonomial.eval_rename]

/-- Evaluating the negation of a monomial gives the negation of its evaluation. -/
theorem eval_neg {R : Type _} [CommRing R] {n : ℕ} {ord : MonomialOrder}
    (m : Monomial n R ord) (f : Fin n → R) :
    (-m).eval f = -(m.eval f) := by
  simp only [eval, Neg.neg, neg_mul]

/-- Multiply two monomials (multiply coefficients, multiply monic parts). -/
def mul [NoZeroDivisors R] (a b : Monomial n R ord) : Monomial n R ord :=
  ⟨⟨a.coeff.val * b.coeff.val, mul_ne_zero a.coeff.property b.coeff.property⟩,
   a.monic * b.monic⟩

instance [NoZeroDivisors R] : Mul (Monomial n R ord) := ⟨mul⟩

theorem eval_mul {R : Type _} [CommSemiring R] [NoZeroDivisors R]
    {n : ℕ} {ord : MonomialOrder}
    (a b : Monomial n R ord) (f : Fin n → R) :
    (a * b).eval f = a.eval f * b.eval f := by
  simp only [eval]
  simp only [show (a * b).coeff.val = a.coeff.val * b.coeff.val from rfl,
             show (a * b).monic = a.monic * b.monic from rfl]
  simp only [MonicMonomial.eval, MonicMonomial.mul_exponents,
             Fin.getElem_fin, Vector.getElem_ofFn, pow_add]
  rw [Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

instance [Nontrivial R] : One (Monomial n R ord) :=
  ⟨⟨⟨1, one_ne_zero⟩, MonicMonomial.one⟩⟩

@[ext] theorem ext' (a b : Monomial n R ord)
    (hc : a.coeff.val = b.coeff.val) (hm : a.monic = b.monic) : a = b := by
  rcases a with ⟨ac, am⟩; rcases b with ⟨bc, bm⟩
  simp only at hc hm
  subst hm; congr 1; exact Subtype.ext hc

section CommMonoidInstance

set_option linter.unusedSectionVars false in
@[simp] theorem mul_coeff_val [NoZeroDivisors R] (a b : Monomial n R ord) :
    (a * b).coeff.val = a.coeff.val * b.coeff.val := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem mul_monic [NoZeroDivisors R] (a b : Monomial n R ord) :
    (a * b).monic = a.monic * b.monic := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem one_coeff_val [Nontrivial R] : (1 : Monomial n R ord).coeff.val = 1 := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem one_monic [Nontrivial R] : (1 : Monomial n R ord).monic = 1 := rfl

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {n : ℕ} {ord : MonomialOrder}

omit [Nontrivial R] in
theorem mul_assoc (a b c : Monomial n R ord) : a * b * c = a * (b * c) := by
  apply ext' <;> simp [_root_.mul_assoc]

theorem one_mul (a : Monomial n R ord) : 1 * a = a := by
  apply ext' <;> simp

theorem mul_one (a : Monomial n R ord) : a * 1 = a := by
  apply ext' <;> simp

omit [Nontrivial R] in
theorem mul_comm (a b : Monomial n R ord) : a * b = b * a := by
  apply ext' <;> simp [_root_.mul_comm]

instance : CommMonoid (Monomial n R ord) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

end CommMonoidInstance

/-! ### Display layer — parameterized over a display type `F` -/

section Display
variable (F : Type _) [LinearOrder F] [pv : ParsableVar F n]
variable [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R]

/-- Convert a monomial to a list of characters using the `F`-naming scheme.  -/
def toCharsWith (m : Monomial n R ord) : List Char :=
  if m.monic = 1 then
    ParsableCoeff.toChars m.coeff.val
  else if m.coeff.val = 1 then
    m.monic.toCharsWith F
  else match ParsableCoeff.negOne (R := R) with
    | some ⟨c, _⟩ =>
      if m.coeff.val = c then '-' :: m.monic.toCharsWith F
      else ParsableCoeff.toChars m.coeff.val ++ ['*'] ++ m.monic.toCharsWith F
    | none => ParsableCoeff.toChars m.coeff.val ++ ['*'] ++ m.monic.toCharsWith F

/-- Parse a char list of the form `<coeff>` or `<coeff>*<monic>` into a
    `Monomial`. The coefficient is passed verbatim to `ParsableCoeff.parseChars`
    (so any leading `-` is delegated to the coefficient parser). -/
def parseCoeffAndOptionalMonic (cs : List Char) : Option (Monomial n R ord) :=
  let (coeffPart, rest') := cs.span (· != '*')
  match rest' with
  | [] =>
    (ParsableCoeff.parseChars coeffPart).bind (fun c =>
      if hc : c = 0 then none else some ⟨⟨c, hc⟩, 1⟩)
  | '*' :: monicPart =>
    (ParsableCoeff.parseChars coeffPart).bind (fun c =>
      if hc : c = 0 then none
      else (MonicMonomial.parseWith (ord := ord) F monicPart).map
        (fun m => ⟨⟨c, hc⟩, m⟩))
  | _ => none

/-- Parse a character list into a `Monomial` using the `F`-naming scheme. -/
def parseWith (cs : List Char) : Option (Monomial n R ord) :=
  match cs with
  | [] => none
  | c :: rest =>
    if decide (¬ isPolySyntaxChar c) then
      -- "x", "x*y" — implicit coefficient 1
      (MonicMonomial.parseWith (ord := ord) F cs).map
        (fun m => ⟨⟨1, one_ne_zero⟩, m⟩)
    else
      match rest with
      | c' :: _ =>
        if _ : c = '-' ∧ ¬ isPolySyntaxChar c' then
          -- "-x", "-x*y" — use `negOne` since there is no explicit coefficient
          match ParsableCoeff.negOne (R := R) with
          | some ⟨negOneVal, hne, _⟩ =>
            (MonicMonomial.parseWith (ord := ord) F rest).map
              (fun m => ⟨⟨negOneVal, hne⟩, m⟩)
          | none => none
        else
          -- "3", "3*x", "-3", "-3*x" — explicit (possibly signed) coefficient
          parseCoeffAndOptionalMonic F cs
      | [] =>
        parseCoeffAndOptionalMonic F cs

/-- Parsing a `*`-free char list that is a valid coefficient representation
    produces a monomial with monic part `1`. -/
lemma parseCoeffAndOptionalMonic_coeff_only (cs : List Char) (r : R) (hr : r ≠ 0)
    (hall : ∀ x ∈ cs, (x != '*') = true)
    (hparse : ParsableCoeff.parseChars cs = some r) :
    parseCoeffAndOptionalMonic F (ord := ord) cs = some ⟨⟨r, hr⟩, 1⟩ := by
  unfold parseCoeffAndOptionalMonic
  simp only [List.span_eq_takeWhile_dropWhile]
  rw [(List.takeWhile_eq_self_iff).mpr hall, (List.dropWhile_eq_nil_iff).mpr hall]
  rw [hparse]
  simp only [Option.bind_some, dite_eq_right hr]

/-- Parsing a char list of the form `coeffCs ++ '*' :: monicCs` where the
    coefficient part parses correctly and the monic part parses correctly. -/
lemma parseCoeffAndOptionalMonic_coeff_times
    (coeffCs : List Char) (monicCs : List Char)
    (r : R) (hr : r ≠ 0) (mm : MonicMonomial n ord)
    (hcoeff_nonempty : coeffCs ≠ [])
    (hall : ∀ x ∈ coeffCs, (x != '*') = true)
    (hparse_coeff : ParsableCoeff.parseChars coeffCs = some r)
    (hparse_monic : MonicMonomial.parseWith (ord := ord) F monicCs = some mm) :
    parseCoeffAndOptionalMonic F (ord := ord) (coeffCs ++ ['*'] ++ monicCs) =
      some ⟨⟨r, hr⟩, mm⟩ := by
  unfold parseCoeffAndOptionalMonic
  obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hcoeff_nonempty
  have hc : (c != '*') = true := hall c (hct ▸ List.mem_cons_self ..)
  have hall_t : ∀ x ∈ t, (x != '*') = true :=
    fun x hx => hall x (hct ▸ List.mem_cons_of_mem _ hx)
  rw [hct]
  simp only [List.span_eq_takeWhile_dropWhile, List.cons_append,
    List.append_assoc, List.nil_append]
  have htw : List.takeWhile (· != '*') (c :: (t ++ '*' :: monicCs)) = c :: t := by
    simp [hc, List.takeWhile_append, (List.takeWhile_eq_self_iff).mpr hall_t]
  have hdw : List.dropWhile (· != '*') (c :: (t ++ '*' :: monicCs)) = '*' :: monicCs := by
    simp [hc, List.dropWhile_append, (List.dropWhile_eq_nil_iff).mpr hall_t]
  rw [htw, hdw]
  rw [← hct, hparse_coeff]
  simp only [Option.bind_some, dite_eq_right hr, hparse_monic, Option.map_some]

theorem toCharsWith_ne_nil (m : Monomial n R ord) : m.toCharsWith F ≠ [] := by
  unfold toCharsWith
  split_ifs with h1 h2
  · exact ParsableCoeff.toChars_nonempty _
  · exact MonicMonomial.toCharsWith_ne_nil F m.monic h1
  · cases hn : ParsableCoeff.negOne (R := R) with
    | none => intro h; simp at h
    | some c => dsimp only [hn]; split_ifs <;> (intro h; simp at h)

theorem plus_notin_toCharsWith (m : Monomial n R ord) : '+' ∉ m.toCharsWith F := by
  unfold toCharsWith
  split_ifs with h1 h2
  · intro h; exact ParsableCoeff.toChars_no_syntax _ _ h (Or.inl rfl)
  · exact MonicMonomial.plus_notin_toCharsWith F m.monic
  · cases hn : ParsableCoeff.negOne (R := R) with
    | none =>
      intro h; rw [List.mem_append, List.mem_append] at h
      rcases h with (h | h) | h
      · exact ParsableCoeff.toChars_no_syntax _ _ h (Or.inl rfl)
      · simp at h
      · exact MonicMonomial.plus_notin_toCharsWith F m.monic h
    | some c =>
      dsimp only [hn]
      split_ifs with hc
      · intro h; simp at h; exact MonicMonomial.plus_notin_toCharsWith F m.monic h
      · intro h; rw [List.mem_append, List.mem_append] at h
        rcases h with (h | h) | h
        · exact ParsableCoeff.toChars_no_syntax _ _ h (Or.inl rfl)
        · simp at h
        · exact MonicMonomial.plus_notin_toCharsWith F m.monic h

/-- Generic exclusion: a character `c` that is excluded from coefficient
    representations, variable names, and is neither a digit nor `*`/`^`/`-`,
    does not occur in `m.toCharsWith F`. -/
theorem char_notin_toCharsWith (c : Char)
    (hcoeff : ∀ r : R, c ∉ ParsableCoeff.toChars r)
    (hvar : ∀ v : F, c ∉ pv.toChars v)
    (hdig : ∀ k : ℕ, c ∉ natToChars k)
    (hnot_star : c ≠ '*') (hnot_caret : c ≠ '^') (hnot_minus : c ≠ '-')
    (m : Monomial n R ord) : c ∉ m.toCharsWith F := by
  unfold toCharsWith
  split_ifs with h1 h2
  · exact hcoeff _
  · exact MonicMonomial.char_notin_toCharsWith F c hvar hdig hnot_star hnot_caret m.monic
  · cases hn : ParsableCoeff.negOne (R := R) with
    | none =>
      intro h; rw [List.mem_append, List.mem_append] at h
      rcases h with (h | h) | h
      · exact hcoeff _ h
      · simp at h; exact hnot_star h
      · exact MonicMonomial.char_notin_toCharsWith
          F c hvar hdig hnot_star hnot_caret m.monic h
    | some cNeg =>
      dsimp only [hn]
      split_ifs with _hc
      · intro h; simp at h; rcases h with h | h
        · exact hnot_minus h
        · exact MonicMonomial.char_notin_toCharsWith
            F c hvar hdig hnot_star hnot_caret m.monic h
      · intro h; rw [List.mem_append, List.mem_append] at h
        rcases h with (h | h) | h
        · exact hcoeff _ h
        · simp at h; exact hnot_star h
        · exact MonicMonomial.char_notin_toCharsWith
            F c hvar hdig hnot_star hnot_caret m.monic h

theorem minus_notin_tail_toCharsWith (m : Monomial n R ord) :
    '-' ∉ (m.toCharsWith F).tail := by
  unfold toCharsWith
  split_ifs with h1 h2
  · exact fun h => ParsableCoeff.toChars_no_minus_tail _ _ h rfl
  · exact fun h => MonicMonomial.minus_notin_toCharsWith F m.monic (List.mem_of_mem_tail h)
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
        · exact MonicMonomial.minus_notin_toCharsWith F m.monic h
    | some c =>
      dsimp only [hn]
      split_ifs with hc
      · exact fun h => MonicMonomial.minus_notin_toCharsWith F m.monic h
      · have hne := ParsableCoeff.toChars_nonempty m.coeff.val
        rw [List.append_assoc, List.tail_append_of_ne_nil hne]
        intro h; rw [List.mem_append] at h
        rcases h with h | h
        · exact ParsableCoeff.toChars_no_minus_tail _ _ h rfl
        · simp only [List.singleton_append, List.mem_cons] at h
          rcases h with h | h
          · exact absurd h (by decide)
          · exact MonicMonomial.minus_notin_toCharsWith F m.monic h

end Display

end Monomial

/-- Helper: `parseWith` on `c :: t` reduces to `parseCoeffAndOptionalMonic`
    when `c` is a polynomial syntax character and — in the special case `c = '-'`
    — the next character is also a polynomial syntax character.  This is the
    common shape that arises from `ParsableCoeff.toChars` output. -/
private lemma Monomial.parseWith_cons_eq_helper
    {R : Type _} [Semiring R] [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R]
    {n : ℕ} {ord : MonomialOrder} (F : Type _) [LinearOrder F] [pv : ParsableVar F n]
    {c : Char} {t : List Char} (his : isPolySyntaxChar c)
    (hmns : c = '-' → ∃ c' t', t = c' :: t' ∧ isPolySyntaxChar c') :
    Monomial.parseWith (n := n) (ord := ord) (R := R) F (c :: t)
      = Monomial.parseCoeffAndOptionalMonic F (c :: t) := by
  unfold Monomial.parseWith
  dsimp only
  have h1 : decide (¬ isPolySyntaxChar c) = false := by
    simp only [decide_eq_false_iff_not, not_not]; exact his
  rw [h1]; simp only [Bool.false_eq_true, ↓reduceIte]
  cases t with
  | nil => rfl
  | cons c' t' =>
    dsimp only
    rw [dite_eq_right]
    rintro ⟨rfl, hnot⟩
    obtain ⟨_, _, hcons, hsyn⟩ := hmns rfl
    simp only [List.cons.injEq] at hcons
    obtain ⟨rfl, _⟩ := hcons
    exact hnot hsyn

/-- Round-trip theorem: `parseWith F (m.toCharsWith F) = some m`. -/
theorem Monomial.parseWith_toCharsWith {R : Type _} [Semiring R]
    [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R] {n : ℕ} {ord : MonomialOrder}
    (F : Type _) [LinearOrder F] [pv : ParsableVar F n]
    (m : Monomial n R ord) :
    Monomial.parseWith (n := n) (ord := ord) (R := R) F (m.toCharsWith F) = some m := by
  unfold Monomial.toCharsWith
  have hall_coeff : ∀ x ∈ ParsableCoeff.toChars m.coeff.val, (x != '*') = true :=
    fun x hx => Monomial.coeffChars_bne_star m.coeff.val x hx
  have hparse_coeff : ParsableCoeff.parseChars (ParsableCoeff.toChars m.coeff.val)
      = some m.coeff.val := ParsableCoeff.parse_toChars m.coeff.val
  split_ifs with hmonic hcoeff
  · -- Case 1: monic = 1, output is just the coefficient chars
    have hne := ParsableCoeff.toChars_nonempty m.coeff.val
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    have his_syntax : isPolySyntaxChar c :=
      ParsableCoeff.toChars_head_is_syntax m.coeff.val c t hct
    have hmns : c = '-' → ∃ c' t', t = c' :: t' ∧ isPolySyntaxChar c' := fun hceq => by
      subst hceq
      exact ParsableCoeff.toChars_minus_next_syntax m.coeff.val t hct
    rw [hct, Monomial.parseWith_cons_eq_helper F his_syntax hmns]
    have hall : ∀ x ∈ (c :: t), (x != '*') = true := fun x hx => hall_coeff x (hct ▸ hx)
    have hparse' : ParsableCoeff.parseChars (c :: t) = some m.coeff.val := hct ▸ hparse_coeff
    rw [parseCoeffAndOptionalMonic_coeff_only (ord := ord) F (c :: t) m.coeff.val
        m.coeff.property hall hparse']
    cases m with
    | mk coeff monic => simp at hmonic; subst hmonic; rfl
  · -- Case 2: coeff = 1, monic ≠ 1 — output is just `m.monic.toCharsWith F`
    have hne := MonicMonomial.toCharsWith_ne_nil F m.monic hmonic
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    rw [hct]; unfold Monomial.parseWith
    have hnot_syntax : ¬ isPolySyntaxChar c := by
      have h := MonicMonomial.toCharsWith_head_not_syntax F m.monic hmonic
      simp only [hct, List.head_cons] at h; exact h
    simp only [decide_eq_true hnot_syntax, ↓reduceIte]
    rw [← hct, MonicMonomial.parseWith_toCharsWith]
    show Option.some { coeff := ⟨1, one_ne_zero⟩, monic := m.monic} = some m
    congr 1; cases m; simp only [Monomial.mk.injEq]
    exact ⟨Subtype.ext hcoeff.symm, trivial⟩
  · -- Case 3: coeff ≠ 1, monic ≠ 1.  Splits on `ParsableCoeff.negOne`.
    have hne_monic := MonicMonomial.toCharsWith_ne_nil F m.monic hmonic
    -- Helper used in both "coeff*monic" sub-cases: the `coeff ++ '*' :: monic`
    -- char list satisfies the conditions of `parseWith_cons_eq_helper`.
    have hcoeff_times_monic :
        Monomial.parseWith (n := n) (ord := ord) (R := R) F
          (ParsableCoeff.toChars m.coeff.val ++ ['*'] ++ m.monic.toCharsWith F) = some m := by
      have hne_coeff := ParsableCoeff.toChars_nonempty m.coeff.val
      obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne_coeff
      have his_syntax : isPolySyntaxChar c :=
        ParsableCoeff.toChars_head_is_syntax m.coeff.val c t hct
      have hmns : c = '-' →
          ∃ c' t', t ++ ['*'] ++ m.monic.toCharsWith F = c' :: t' ∧ isPolySyntaxChar c' := by
        intro hceq
        subst hceq
        obtain ⟨c0, t0, hcons, hsyn⟩ :=
          ParsableCoeff.toChars_minus_next_syntax m.coeff.val t hct
        refine ⟨c0, t0 ++ ['*'] ++ m.monic.toCharsWith F, ?_, hsyn⟩
        rw [hcons]; rfl
      rw [hct]
      rw [show c :: t ++ ['*'] ++ m.monic.toCharsWith F
            = c :: (t ++ ['*'] ++ m.monic.toCharsWith F) from rfl]
      rw [Monomial.parseWith_cons_eq_helper F his_syntax hmns]
      have hall : ∀ x ∈ (c :: t), (x != '*') = true := fun x hx => hall_coeff x (hct ▸ hx)
      have hparse' : ParsableCoeff.parseChars (c :: t) = some m.coeff.val := hct ▸ hparse_coeff
      have hparse_monic := MonicMonomial.parseWith_toCharsWith F m.monic
      rw [show c :: (t ++ ['*'] ++ m.monic.toCharsWith F)
            = (c :: t) ++ ['*'] ++ m.monic.toCharsWith F from rfl]
      rw [parseCoeffAndOptionalMonic_coeff_times (ord := ord) F (c :: t)
        (m.monic.toCharsWith F) m.coeff.val m.coeff.property m.monic
        (List.cons_ne_nil c t) hall hparse' hparse_monic]
    match hn : ParsableCoeff.negOne (R := R) with
    | some ⟨cneg, hne_neg, hne_one⟩ =>
      dsimp only
      split_ifs with hcoeff_neg
      · -- Sub-case 3a: `m.coeff.val = negOne`, output is `'-' :: monicChars`
        obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne_monic
        have hnot_syntax : ¬ isPolySyntaxChar c := by
          have h := MonicMonomial.toCharsWith_head_not_syntax F m.monic hmonic
          simp only [hct, List.head_cons] at h; exact h
        have his_syntax_minus : isPolySyntaxChar '-' := Or.inr (Or.inr (Or.inl rfl))
        rw [hct]
        show Monomial.parseWith (n := n) (ord := ord) (R := R) F ('-' :: c :: t) = some m
        unfold Monomial.parseWith
        dsimp only
        rw [show decide (¬ isPolySyntaxChar '-') = false by
              simp only [decide_eq_false_iff_not, not_not]; exact his_syntax_minus]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [dite_eq_left (show True ∧ ¬ isPolySyntaxChar c from ⟨trivial, hnot_syntax⟩)]
        simp only [hn]
        rw [← hct, MonicMonomial.parseWith_toCharsWith, Option.map_some]
        obtain ⟨mc, mm⟩ := m
        dsimp only at hcoeff_neg ⊢
        refine congrArg some ?_
        refine Monomial.ext' _ _ ?_ rfl
        exact hcoeff_neg.symm
      · -- Sub-case 3b: explicit "coeff*monic" representation
        exact hcoeff_times_monic
    | none =>
      dsimp only
      exact hcoeff_times_monic

namespace Monomial

/-! ### Default display (uses `IndexedVar n`) -/

variable {R : Type _} [Semiring R] [NeZero (1 : R)] {n : ℕ} {ord : MonomialOrder}

/-- Default `toChars`: `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def toChars [DecidableEq R] [ParsableCoeff R]
    (m : Monomial n R ord) : List Char :=
  m.toCharsWith (IndexedVar n)

/-- Default `parse`: accepts the `IndexedVar n` naming. -/
@[inline] def parse [DecidableEq R] [ParsableCoeff R]
    (cs : List Char) : Option (Monomial n R ord) :=
  parseWith (IndexedVar n) cs

theorem toChars_ne_nil [DecidableEq R] [ParsableCoeff R] (m : Monomial n R ord) :
    m.toChars ≠ [] :=
  toCharsWith_ne_nil (IndexedVar n) m

theorem plus_notin_toChars [DecidableEq R] [ParsableCoeff R] (m : Monomial n R ord) :
    '+' ∉ m.toChars :=
  plus_notin_toCharsWith (IndexedVar n) m

theorem minus_notin_tail_toChars [DecidableEq R] [ParsableCoeff R] (m : Monomial n R ord) :
    '-' ∉ m.toChars.tail :=
  minus_notin_tail_toCharsWith (IndexedVar n) m

theorem parse_toChars [DecidableEq R] [ParsableCoeff R] (m : Monomial n R ord) :
    parse (n := n) (ord := ord) (R := R) m.toChars = some m :=
  Monomial.parseWith_toCharsWith (IndexedVar n) m

end Monomial

section MonomialGuards

private def mkMonN (c : AzInt) (hc : c ≠ 0) (v : Vector ℕ 3) : Monomial 3 AzInt :=
  ⟨⟨c, hc⟩, ⟨v⟩⟩

-- default (`IndexedVar`) display
#guard (mkMonN 5 (AzInt.ofNat_ne_zero 5) (Vector.mk #[0, 0, 0] rfl)).toChars == "5".toList
#guard (mkMonN 1 (by decide) (Vector.mk #[1, 0, 0] rfl)).toChars == "x₀".toList
#guard (mkMonN 3 (AzInt.ofNat_ne_zero 3) (Vector.mk #[1, 0, 0] rfl)).toChars == "3*x₀".toList
#guard (mkMonN (-2) (AzInt.neg_ofNat_ne_zero 2) (Vector.mk #[1, 1, 0] rfl)).toChars == "-2*x₀*x₁".toList

-- `toCharsWith (AbcVar 3)` same monomial, different naming
#guard (mkMonN 1 (by decide) (Vector.mk #[1, 0, 0] rfl)).toCharsWith (AbcVar 3) == "a".toList
#guard (mkMonN 3 (AzInt.ofNat_ne_zero 3) (Vector.mk #[1, 0, 0] rfl)).toCharsWith (AbcVar 3) == "3*a".toList
#guard (mkMonN (-2) (AzInt.neg_ofNat_ne_zero 2) (Vector.mk #[1, 1, 0] rfl)).toCharsWith (AbcVar 3) == "-2*a*b".toList

-- parse round-trip via default display
#guard (Monomial.parse (n := 3) (R := AzInt) (ord := .Degrevlex) "5".toList).map
    Monomial.toChars == some "5".toList
#guard (Monomial.parse (n := 3) (R := AzInt) (ord := .Degrevlex) "x₀".toList).map
    Monomial.toChars == some "x₀".toList
#guard (Monomial.parse (n := 3) (R := AzInt) (ord := .Degrevlex) "3*x₀".toList).map
    Monomial.toChars == some "3*x₀".toList
#guard (Monomial.parse (n := 3) (R := AzInt) (ord := .Degrevlex) "-2*x₀*x₁".toList).map
    Monomial.toChars == some "-2*x₀*x₁".toList

-- parse round-trip via `AbcVar 3`
#guard (Monomial.parseWith (n := 3) (R := AzInt) (ord := .Degrevlex) (AbcVar 3) "3*a".toList).map
    (fun m => m.toCharsWith (AbcVar 3)) == some "3*a".toList

end MonomialGuards

end Azurite

/-
  Monomials (coefficient × monic monomial) for `Monomial` — Fin-indexed.
-/
import Azurite.AzMvPolynomial.ParsableCoeff
import Azurite.AzMvPolynomial.MonicMonomial
import Azurite.AzMvPolynomial.MonicMonomialProofs

namespace Azurite
open AzPolynomial

/-- A monomial: a nonzero coefficient of type `R` paired with a
    Fin-indexed monic monomial.  Unlike `Monomial σ R ord`, this version
    carries no `Var` typeclass — the variable type is fixed to `Fin n`. -/
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
def one [One R] (h : (1 : R) ≠ 0) : Monomial n R ord :=
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

/-- Evaluate a monomial at a point given by `f : Fin n → R`. -/
def eval [CommMonoidWithZero R] (m : Monomial n R ord) (f : Fin n → R) : R :=
  m.coeff.val * m.monic.eval f

/-- Rename variables via a map `f : Fin n → Fin n₂`. -/
def rename {n₂ : ℕ} (m : Monomial n R ord) (f : Fin n → Fin n₂)
    (ord₂ : MonomialOrder := ord) : Monomial n₂ R ord₂ :=
  ⟨m.coeff, m.monic.rename f ord₂⟩

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
variable [DecidableEq R] [ParsableCoeff R]

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

/-- Parse a character list into a `Monomial` using the `F`-naming scheme. -/
def parseWith (cs : List Char) : Option (Monomial n R ord) :=
  match cs with
  | [] => none
  | c :: rest =>
    if decide (¬ isPolySyntaxChar c) then
      (MonicMonomial.parseWith (ord := ord) F cs).map
        (fun m => ⟨⟨1, ParsableCoeff.one_ne_zero⟩, m⟩)
    else if _ : c = '-' then
      match rest with
      | c' :: _ =>
        if decide (¬ isPolySyntaxChar c') then
          match ParsableCoeff.negOne (R := R) with
          | some ⟨negOneVal, hne, _⟩ =>
            (MonicMonomial.parseWith (ord := ord) F rest).map
              (fun m => ⟨⟨negOneVal, hne⟩, m⟩)
          | none => none
        else
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
      | [] =>
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
    else
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

/-- Round-trip theorem: `parseWith F (m.toCharsWith F) = some m`. -/
theorem Monomial.parseWith_toCharsWith {R : Type _} [Semiring R]
    [DecidableEq R] [ParsableCoeff R] {n : ℕ} {ord : MonomialOrder}
    (F : Type _) [LinearOrder F] [pv : ParsableVar F n]
    (m : Monomial n R ord) :
    Monomial.parseWith (n := n) (ord := ord) (R := R) F (m.toCharsWith F) = some m := by
  unfold Monomial.toCharsWith
  split_ifs with hmonic hcoeff
  · -- Case 1: monic = 1, output is just the coefficient chars
    have hne := ParsableCoeff.toChars_nonempty m.coeff.val
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    rw [hct]; unfold Monomial.parseWith
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
        have ⟨_, hsynt⟩ :=
          ParsableCoeff.toChars_minus_next_syntax m.coeff.val hne (by simp [hct])
        have hcs : isPolySyntaxChar c' := by
          have h2 : (ParsableCoeff.toChars m.coeff.val).tail ≠ [] := by simp [hct]
          have := hsynt h2; simp [hct] at this; exact this
        have hall' : ∀ x ∈ c' :: t', (x != '*') = true :=
          fun x hx => hall x (List.mem_cons_of_mem _ hx)
        simp only [dite_true, show ¬ ¬ isPolySyntaxChar c' from not_not.mpr hcs,
          decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [Monomial.takeWhile_all ('-' :: c' :: t') hall,
            Monomial.dropWhile_all ('-' :: c' :: t') hall]
        simp_all [dif_neg m.coeff.property, Option.bind_some]
        cases m with | mk => simp_all
    · rw [Monomial.takeWhile_all (c :: t) hall, Monomial.dropWhile_all (c :: t) hall]
      simp only [hcm, dite_false]
      simp_all [dif_neg m.coeff.property, Option.bind_some]
      cases m with | mk => simp_all
  · -- Case 2: coeff = 1, monic ≠ 1
    have hne := MonicMonomial.toCharsWith_ne_nil F m.monic hmonic
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    rw [hct]; unfold Monomial.parseWith
    have hnot_syntax : ¬ isPolySyntaxChar c := by
      have h := MonicMonomial.toCharsWith_head_not_syntax F m.monic hmonic
      simp only [hct, List.head_cons] at h; exact h
    simp only [decide_eq_true hnot_syntax, ↓reduceIte]
    rw [← hct, MonicMonomial.parseWith_toCharsWith]
    show Option.some { coeff := ⟨1, ParsableCoeff.one_ne_zero⟩, monic := m.monic} = some m
    congr 1; cases m; simp only [Monomial.mk.injEq]
    exact ⟨Subtype.ext hcoeff.symm, trivial⟩
  · -- Case 3: coeff ≠ 1, monic ≠ 1
    suffices hCM : ∀ (hne : ParsableCoeff.toChars m.coeff.val ≠ []),
      Monomial.parseWith (n := n) (ord := ord) (R := R) F
        (ParsableCoeff.toChars m.coeff.val ++ ['*'] ++ m.monic.toCharsWith F) = some m by
      match hn : ParsableCoeff.negOne (R := R) with
      | some ⟨cneg, hne_neg, hne_one⟩ =>
        dsimp only; split_ifs with hcoeff_neg
        · have hne_monic := MonicMonomial.toCharsWith_ne_nil F m.monic hmonic
          obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne_monic
          rw [hct]; unfold Monomial.parseWith
          have hnot_syntax : ¬ isPolySyntaxChar c := by
            have h := MonicMonomial.toCharsWith_head_not_syntax F m.monic hmonic
            simp only [hct, List.head_cons] at h; exact h
          simp only [show isPolySyntaxChar '-' from (Or.inr (Or.inr (Or.inl rfl))),
            ↓reduceIte, decide_eq_true hnot_syntax]
          rw [hn]; simp only
          rw [← hct, MonicMonomial.parseWith_toCharsWith, Option.map_some]
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
    rw [hct]; unfold Monomial.parseWith
    simp only [List.span_eq_takeWhile_dropWhile]
    have hc_bne : (c != '*') = true :=
      Monomial.coeffChars_bne_star m.coeff.val c (by rw [hct]; exact List.mem_cons_self ..)
    have hall : ∀ x ∈ t, (x != '*') = true :=
      fun x hx => Monomial.coeffChars_bne_star m.coeff.val x
        (by rw [hct]; exact List.mem_cons_of_mem _ hx)
    have htw : List.takeWhile (· != '*') (c :: (t ++ ['*'] ++ m.monic.toCharsWith F)) = c :: t := by
      simp [hc_bne, List.takeWhile_append, Monomial.takeWhile_all t hall]
    have hdw : List.dropWhile (· != '*') (c :: (t ++ ['*'] ++ m.monic.toCharsWith F)) =
        '*' :: m.monic.toCharsWith F := by
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
        simp_all [dif_neg m.coeff.property, MonicMonomial.parseWith_toCharsWith,
          Option.map_some, Option.bind_some]
      | cons c' t' =>
        have ⟨_, hsynt⟩ :=
          ParsableCoeff.toChars_minus_next_syntax m.coeff.val hne (by simp [hct])
        have hcs : isPolySyntaxChar c' := by
          have h2 : (ParsableCoeff.toChars m.coeff.val).tail ≠ [] := by simp [hct]
          have := hsynt h2; simp [hct] at this; exact this
        simp only [dite_true]
        simp_all [dif_neg m.coeff.property, MonicMonomial.parseWith_toCharsWith,
          Option.map_some, Option.bind_some]
    · simp only [hcm, dite_false]
      simp_all [dif_neg m.coeff.property, MonicMonomial.parseWith_toCharsWith,
        Option.map_some, Option.bind_some]

namespace Monomial

/-! ### Default display (uses `IndexedVar n`) -/

variable {R : Type _} [Semiring R] {n : ℕ} {ord : MonomialOrder}

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

private def mkMonN (c : ℤ) (hc : c ≠ 0) (v : Vector ℕ 3) : Monomial 3 ℤ :=
  ⟨⟨c, hc⟩, ⟨v⟩⟩

-- default (`IndexedVar`) display
#guard (mkMonN 5 (by omega) (Vector.mk #[0, 0, 0] rfl)).toChars == "5".toList
#guard (mkMonN 1 (by omega) (Vector.mk #[1, 0, 0] rfl)).toChars == "x₀".toList
#guard (mkMonN 3 (by omega) (Vector.mk #[1, 0, 0] rfl)).toChars == "3*x₀".toList
#guard (mkMonN (-2) (by omega) (Vector.mk #[1, 1, 0] rfl)).toChars == "-2*x₀*x₁".toList

-- `toCharsWith (AbcVar 3)` same monomial, different naming
#guard (mkMonN 1 (by omega) (Vector.mk #[1, 0, 0] rfl)).toCharsWith (AbcVar 3) == "a".toList
#guard (mkMonN 3 (by omega) (Vector.mk #[1, 0, 0] rfl)).toCharsWith (AbcVar 3) == "3*a".toList
#guard (mkMonN (-2) (by omega) (Vector.mk #[1, 1, 0] rfl)).toCharsWith (AbcVar 3) == "-2*a*b".toList

-- parse round-trip via default display
#guard (Monomial.parse (n := 3) (R := ℤ) (ord := .Degrevlex) "5".toList).map
    Monomial.toChars == some "5".toList
#guard (Monomial.parse (n := 3) (R := ℤ) (ord := .Degrevlex) "x₀".toList).map
    Monomial.toChars == some "x₀".toList
#guard (Monomial.parse (n := 3) (R := ℤ) (ord := .Degrevlex) "3*x₀".toList).map
    Monomial.toChars == some "3*x₀".toList
#guard (Monomial.parse (n := 3) (R := ℤ) (ord := .Degrevlex) "-2*x₀*x₁".toList).map
    Monomial.toChars == some "-2*x₀*x₁".toList

-- parse round-trip via `AbcVar 3`
#guard (Monomial.parseWith (n := 3) (R := ℤ) (ord := .Degrevlex) (AbcVar 3) "3*a".toList).map
    (fun m => m.toCharsWith (AbcVar 3)) == some "3*a".toList

end MonomialGuards

end Azurite

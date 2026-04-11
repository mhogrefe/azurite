/-
  `ParsableCoeff` class + canonical instances (`ℕ`/`ℤ`/`ℚ`/`ZMod`) and
  generic `takeWhile`/`dropWhile`/coeffChars helper lemmas.

  Extracted from the legacy `Azurite.AzMvPolynomial.Monomial` so the New
  tree's display layer does not depend on the `[Var σ n]`-polymorphic
  `Monomial σ R` structure.
-/
import Azurite.AzMvPolynomial.New.Var
import Azurite.AzPolynomial.StringLemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.TakeDrop

namespace Azurite
open AzPolynomial

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

namespace Monomial

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

end Azurite

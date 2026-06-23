/-
  `ParsableElement` instance for `AzMvPolynomial n R ord`, using the default
  `IndexedVar n` display.  This allows `AzMvPolynomial` values to be used as
  entries inside `AzVector` / `AzMatrix` string representations.

  Establishes `,` and `;` do not occur in `toChars` at each layer
  (`MonicMonomial`, `Monomial`, `AzMvPolynomial`) and combines with the
  round-trip proof from `AzMvPolynomial.ParseToString`.
-/
import Azurite.AzMvPolynomial.ParseToString
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMatrix.Parse
import Azurite.AzMatrix.Mul
import Azurite.AzMatrix.Equiv.Algebra
import Azurite.AzVector.ParsableElement
import Azurite.AzInt.Instances
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt

namespace Azurite

open AzPolynomial Monomial MonicMonomial AzMvPolynomial

/-! ### Variable-layer lemmas for `IndexedVar n` -/

namespace IndexedVar

theorem toChars_no_comma {n : ℕ} (v : IndexedVar n) :
    ',' ∉ IndexedVar.toChars v := by
  intro hc
  simp only [toChars, List.cons_append, List.nil_append, List.mem_cons] at hc
  rcases hc with heq | hc
  · exact absurd heq (by decide)
  · have ⟨hge, _⟩ := mem_natToSubscriptChars_range v.val ',' hc
    exact absurd hge (by decide)

theorem toChars_no_semicolon {n : ℕ} (v : IndexedVar n) :
    ';' ∉ IndexedVar.toChars v := by
  intro hc
  simp only [toChars, List.cons_append, List.nil_append, List.mem_cons] at hc
  rcases hc with heq | hc
  · exact absurd heq (by decide)
  · have ⟨hge, _⟩ := mem_natToSubscriptChars_range v.val ';' hc
    exact absurd hge (by decide)

end IndexedVar

/-! ### AzMvPolynomial layer: `joinMonomialsAux` / `joinMonomials` exclusion -/

section MvPoly

variable {R : Type _} [DecidableEq R] [Semiring R] [NeZero (1 : R)] [ParsableCoeff R]
variable {n : ℕ} {ord : MonomialOrder}
variable (F : Type _) [LinearOrder F] [ParsableVar F n]

private theorem char_notin_joinMonomialsAux (c : Char) (hnot_plus : c ≠ '+')
    (ms : List (List Char)) (hms : ∀ m ∈ ms, c ∉ m) :
    c ∉ joinMonomialsAux ms := by
  induction ms with
  | nil => intro h; simp [joinMonomialsAux] at h
  | cons m rest ih =>
    have hmc : c ∉ m := hms m (List.mem_cons_self ..)
    have hrest : ∀ m' ∈ rest, c ∉ m' := fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')
    simp only [joinMonomialsAux]
    intro hmem
    split at hmem
    · rcases List.mem_append.mp hmem with h | h
      · exact hmc h
      · exact ih hrest h
    · rcases List.mem_append.mp hmem with h | h
      · rcases List.mem_append.mp h with h | h
        · simp at h; exact hnot_plus h
        · exact hmc h
      · exact ih hrest h

private theorem char_notin_joinMonomials (c : Char) (hnot_plus : c ≠ '+')
    (ms : List (List Char)) (hms : ∀ m ∈ ms, c ∉ m) :
    c ∉ joinMonomials ms := by
  match ms with
  | [] => intro h; simp [joinMonomials] at h
  | m :: rest =>
    have hmc : c ∉ m := hms m (List.mem_cons_self ..)
    have hrest : ∀ m' ∈ rest, c ∉ m' := fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')
    simp only [joinMonomials]
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hmc h
    · exact char_notin_joinMonomialsAux c hnot_plus rest hrest h

/-- Generic exclusion: a character `c` avoided by coefficient chars, variable
    names, digits, and various monomial-syntax characters does not appear in
    `p.toCharsWith F`. -/
theorem AzMvPolynomial.char_notin_toCharsWith (c : Char)
    (hcoeff : ∀ r : R, c ∉ ParsableCoeff.toChars r)
    (hvar : ∀ v : F, c ∉ ParsableVar.toChars v)
    (hdig : ∀ k : ℕ, c ∉ natToChars k)
    (hnot_plus : c ≠ '+') (hnot_star : c ≠ '*')
    (hnot_caret : c ≠ '^') (hnot_minus : c ≠ '-')
    (p : AzMvPolynomial n R ord) : c ∉ p.toCharsWith F := by
  unfold AzMvPolynomial.toCharsWith
  split_ifs with hemp
  · exact hcoeff 0
  · apply char_notin_joinMonomials c hnot_plus
    intro cs hcs
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hcs
    exact Monomial.char_notin_toCharsWith F c hcoeff hvar hdig
      hnot_star hnot_caret hnot_minus m

end MvPoly

/-! ### `ParsableElement (AzMvPolynomial n R ord)` instance -/

section Instance

variable {R : Type _} [DecidableEq R] [Semiring R] [NeZero (1 : R)] [ParsableCoeff R]
variable {n : ℕ} {ord : MonomialOrder}

instance instParsableElementAzMvPolynomial : ParsableElement (AzMvPolynomial n R ord) where
  toChars := AzMvPolynomial.toChars
  parseChars := AzMvPolynomial.parse
  parse_toChars := AzMvPolynomial.parse_toChars
  toChars_no_comma p :=
    AzMvPolynomial.char_notin_toCharsWith (IndexedVar n) ','
      ParsableCoeff.toChars_no_comma
      IndexedVar.toChars_no_comma
      (not_mem_natToChars_of_not_digit ',' (by decide))
      (by decide) (by decide) (by decide) (by decide) p
  toChars_no_semicolon p :=
    AzMvPolynomial.char_notin_toCharsWith (IndexedVar n) ';'
      ParsableCoeff.toChars_no_semicolon
      IndexedVar.toChars_no_semicolon
      (not_mem_natToChars_of_not_digit ';' (by decide))
      (by decide) (by decide) (by decide) (by decide) p

end Instance

/-! ### Demonstration: `AzMatrix` over `AzMvPolynomial`

    Two `2 × 2` matrices with `AzMvPolynomial 8 AzInt` entries are parsed from
    strings, multiplied, and the product is serialized back to a string.
    This exercises the full `ParsableElement` chain: both `parseStr` and
    `toString` on `AzMatrix` delegate to the `AzMvPolynomial` instance for
    individual entries. -/
section MatrixDemo

private abbrev MvInt8 := AzMvPolynomial 8 AzInt .Degrevlex

private def demoA : AzMatrix MvInt8 2 2 :=
  (AzMatrix.parseStr "[x₀, x₁; x₂, x₃]").getD (AzMatrix.ofFn (fun _ _ => 0))

private def demoB : AzMatrix MvInt8 2 2 :=
  (AzMatrix.parseStr "[x₄, x₅; x₆, x₇]").getD (AzMatrix.ofFn (fun _ _ => 0))

#guard toString (demoA * demoB) =
  "[x₀*x₄+x₁*x₆, x₀*x₅+x₁*x₇; x₂*x₄+x₃*x₆, x₂*x₅+x₃*x₇]"

end MatrixDemo

end Azurite

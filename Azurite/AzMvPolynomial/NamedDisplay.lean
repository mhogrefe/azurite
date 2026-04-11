/-
  Named display layer for `AzMvPolynomial (Fin n) R ord`.

  The core `AzMvPolynomial` machinery is (in the long run) indexed by `Fin n`,
  matching Mathlib. Human-readable `toString` / `parse` happen through a
  user-chosen display type `F` carrying a `[ParsableVar F n]` instance — i.e.
  a bijection `F ≃ Fin n` together with a character-level naming scheme.

  The default display type is `IndexedVar n`, which prints variables as
  `x₀, x₁, …`.  Users who want custom names (e.g. `a, b, c` or `X, Y, Z`)
  define their own `Var` / `ParsableVar` instance on a small wrapper and call
  `toStringWith` / `parseWith` explicitly.
-/
import Azurite.AzMvPolynomial.ToString
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.Rename

namespace Azurite

/-! ### Named display: toString -/

/-- Convert a `Fin n`-indexed polynomial to a char list using a named display
    type `F` (via its `[ParsableVar F n]` instance).

    Renames `Fin n → F` through `Var.embed` at `h = le_refl n` (which is
    `Var.ofFin ∘ Var.toFin`, trivially strictly monotone), then delegates to
    the existing `[Var]`-generic `toChars`. -/
def AzMvPolynomial.toCharsWith (F : Type _) {n : ℕ} [LinearOrder F] [ParsableVar F n]
    {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
    {ord : MonomialOrder}
    (p : AzMvPolynomial (Fin n) R ord) : List Char :=
  (p.renameMonotone (Var.embed (le_refl n) : Fin n → F)
    (Var.embed_fin_strictMono (le_refl n))).toChars

/-- Convert a `Fin n`-indexed polynomial to a string using `F`'s naming scheme. -/
def AzMvPolynomial.toStringWith (F : Type _) {n : ℕ} [LinearOrder F] [ParsableVar F n]
    {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
    {ord : MonomialOrder}
    (p : AzMvPolynomial (Fin n) R ord) : String :=
  String.ofList (p.toCharsWith F)

/-- Default display for `Fin n`-indexed polynomials: uses `IndexedVar n` to
    print variables as `x₀, x₁, …`. -/
def AzMvPolynomial.toCharsFin {n : ℕ}
    {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
    {ord : MonomialOrder}
    (p : AzMvPolynomial (Fin n) R ord) : List Char :=
  p.toCharsWith (IndexedVar n)

/-- Default display for `Fin n`-indexed polynomials. Uses `IndexedVar n` for
    the `x₀, x₁, …` naming scheme. -/
def AzMvPolynomial.toStringFin {n : ℕ}
    {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
    {ord : MonomialOrder}
    (p : AzMvPolynomial (Fin n) R ord) : String :=
  p.toStringWith (IndexedVar n)

/-! ### Named display: parse -/

/-- Parse a char list into a `Fin n`-indexed polynomial using a named display
    type `F` (via its `[ParsableVar F n]` instance).

    Delegates to the existing `[ParsableVar]`-generic `AzMvPolynomial.parse`
    at `σ := F`, then renames `F → Fin n` through `Var.embed`. -/
def AzMvPolynomial.parseWith (F : Type _) {n : ℕ} [LinearOrder F] [ParsableVar F n]
    {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
    {ord : MonomialOrder}
    (cs : List Char) : Option (AzMvPolynomial (Fin n) R ord) :=
  (AzMvPolynomial.parse (σ := F) cs).map fun p =>
    p.renameMonotone (Var.embed (le_refl n) : F → Fin n)
      (Var.embed_fin_strictMono (le_refl n))

/-- Default parse for `Fin n`-indexed polynomials: accepts the `x₀, x₁, …`
    naming scheme provided by `IndexedVar n`. -/
def AzMvPolynomial.parseFin {n : ℕ}
    {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
    {ord : MonomialOrder}
    (cs : List Char) : Option (AzMvPolynomial (Fin n) R ord) :=
  AzMvPolynomial.parseWith (IndexedVar n) cs

/-- Parse a string into a `Fin n`-indexed polynomial using `IndexedVar n`'s
    naming scheme (`x₀, x₁, …`). -/
def AzMvPolynomial.parseStrFin {n : ℕ}
    {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
    {ord : MonomialOrder}
    (s : String) : Option (AzMvPolynomial (Fin n) R ord) :=
  AzMvPolynomial.parseFin s.toList

end Azurite

/-! ### Round-trip examples -/

open Azurite

section NamedDisplayExamples

-- Parse `x₀+x₁` into a `Fin 2` polynomial, then pretty-print it back using
-- the default `IndexedVar`-based display.
#guard
  ((AzMvPolynomial.parseStrFin (R := ℤ) (ord := .Degrevlex) (n := 2) "x₀+x₁").map
      AzMvPolynomial.toStringFin) == some "x₀+x₁"

-- Parse a polynomial with a constant and a nonlinear term, round-trip.
#guard
  ((AzMvPolynomial.parseStrFin (R := ℤ) (ord := .Degrevlex) (n := 3)
      "3*x₀^2*x₁-2*x₀*x₂+5").map AzMvPolynomial.toStringFin)
    == some "3*x₀^2*x₁-2*x₀*x₂+5"

end NamedDisplayExamples

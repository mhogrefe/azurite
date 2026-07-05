import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse
import Azurite.AzInt.ParsableElement
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement
import Azurite.AzInt.Equiv.Compare

/-!
# A total order on `AzPolynomial` (ordered coefficients)

Polynomials are ordered **by degree first, then lexicographically with the
higher-degree coefficients most significant** — a canonical total order for
sorting lists of polynomials. Concretely, since the coefficient arrays are
normalized (no trailing zeros), this is: compare array sizes, then scan the
coefficients downward from the top.

The zero polynomial (empty array) is the least element; any polynomial of
lower degree precedes any of higher degree regardless of coefficient signs.

`LT`/`LE`/`Ord` instances (with decidability) live here; the `LinearOrder`
instance with its laws is in `Azurite.AzPolynomial.Equiv.Compare`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [LinearOrder R]

/-- Top-down lexicographic scan: compare coefficients at indices
`k-1, k-2, …, 0`, most significant first. -/
def compareTopDown (a b : Array R) : ℕ → Ordering
  | 0 => .eq
  | k + 1 =>
    match compare (a.getD k 0) (b.getD k 0) with
    | .eq => compareTopDown a b k
    | o => o

/-- **Degree-then-lexicographic comparison**: by size of the (normalized)
coefficient array, then top-down through the coefficients. -/
def compare (p q : AzPolynomial R) : Ordering :=
  if p.coeffs.size < q.coeffs.size then .lt
  else if q.coeffs.size < p.coeffs.size then .gt
  else compareTopDown p.coeffs q.coeffs p.coeffs.size

instance : Ord (AzPolynomial R) := ⟨compare⟩

instance : LT (AzPolynomial R) := ⟨fun p q => compare p q = .lt⟩

instance : LE (AzPolynomial R) := ⟨fun p q => compare p q ≠ .gt⟩

instance : DecidableLT (AzPolynomial R) := fun _ _ => inferInstanceAs (Decidable (_ = _))

instance : DecidableLE (AzPolynomial R) := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!
private def pq (s : String) : AzPolynomial AzRat := (parseAzPolynomial s).get!

-- degree dominates, regardless of signs
#guard pp "x" < pp "-5*x^2"
#guard pp "0" < pp "-3"
#guard pp "7" < pp "x"
-- equal degree: top coefficient first …
#guard pp "2*x^2+100*x" < pp "3*x^2-100*x"
-- … then the next coefficients down
#guard pp "x^2+x+5" < pp "x^2+2*x-100"
#guard pp "x^2+x+1" < pp "x^2+x+2"
#guard compare (pp "x^2+x+1") (pp "x^2+x+1") == .eq
#guard pp "x^3-1" > pp "x^2+50*x"
-- over `AzRat` too
#guard pq "1/2*x+1/3" < pq "2/3*x"
#guard pq "0" < pq "-1/2"
-- sorting a list gives the canonical order
#guard ([pp "x^2", pp "0", pp "-x^3", pp "x^2-1", pp "5"].mergeSort (· ≤ ·)).map toChars
    == ["0", "5", "x^2-1", "x^2", "-x^3"]

end Tests

end Azurite.AzPolynomial

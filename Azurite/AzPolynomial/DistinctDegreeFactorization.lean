/-
  Distinct-degree factorization (Gathen–Gerhard, "Modern Computer Algebra",
  Algorithm 14.3), computable.

  Given a squarefree monic `f ∈ F_q[x]`: starting from `h₀ = x` and
  `f₀ = f`, repeatedly compute `hᵢ = hᵢ₋₁^q rem fᵢ₋₁`,
  `gᵢ = gcd(hᵢ − x, fᵢ₋₁)`, and `fᵢ = fᵢ₋₁ / gᵢ`, until `fᵢ = 1`; return the
  distinct-degree decomposition `(g₁, …, g_s)` of `f` (`gᵢ` the product of
  the monic irreducible factors of `f` of degree `i`).

  Performance choices:

  * the `q`-th powers run in the quotient ring `AzPolyMod fᵢ`
    (`powModByMonic`): limb-level sliding-window exponentiation reducing
    at every multiplication — the exponent `q` (a prime power, in
    application huge) is read at the limb level, never through a unary `ℕ`;
  * **`hᵢ` is powered modulo `fᵢ₋₁`, not modulo `f`** (the book's remark
    after Theorem 14.4): `hᵢ` is only ever consumed by
    `gcd(hᵢ − x, fᵢ₋₁)`, so its class mod `fᵢ₋₁` is all that matters, and
    as factors are peeled off the modulus — hence the cost of every
    multiplication inside the powering — shrinks with `fᵢ`.  The carried
    `h` is congruent to `x^(qⁱ)` modulo the CURRENT `fᵢ` (not modulo `f`),
    which is exactly what the correctness invariant tracks;
  * the gcd is the signed-subresultant monic gcd `gcdMonic`, and the exact
    division `fᵢ₋₁ / gᵢ` is the field-free `divByMonic` (`gᵢ` is monic);
  * **early abort** (also the book's): as soon as `deg fᵢ < 2(i + 1)` the
    loop stops — all irreducible factors of `fᵢ` have degree at least
    `i + 1`, so `fᵢ` is itself irreducible, and the remaining output is
    `(1, …, 1, fᵢ)` with `fᵢ` in position `deg fᵢ`.  This caps the
    iteration count at `max(m₁/2, m₂) ≤ (deg f)/2`, where `m₁ ≥ m₂` are
    the two largest factor degrees — in particular the most expensive
    modular powers are skipped for the largest factor.

  The loop is fueled by `deg f` (factor degrees are at most `deg f`, so the
  fuel is never exhausted).  Correctness — the output represents
  `Azurite.GG.distinctDegreeDecomposition` of the represented polynomial —
  is `Azurite.GG.map_toPoly_distinctDegreeFactorization`, proved in
  `Azurite/GathenGerhard/Chapter14/Algorithm_14_3.lean` by transporting GG
  Theorem 14.4 along `toPoly`.
-/
import Azurite.AzPolyMod.Basic
import Azurite.AzPolynomial.Gcd
import Azurite.AzZMod.Field

namespace Azurite.AzPolynomial

/-- **Modular exponentiation of polynomials**: `(a rem f)^q rem f`,
computed in the quotient ring `AzPolyMod f` — limb-level sliding-window
exponentiation with reduction mod `f` at every multiplication (`ofPoly`
reduces the base on entry).  Meaningful for monic `f` (the reduction
primitive's contract). -/
def powModByMonic {R : Type _} [CommRing R] [DecidableEq R]
    (a : AzPolynomial R) (q : AzNat) (f : AzPolynomial R) : AzPolynomial R :=
  ((AzPolyMod.ofPoly (f := f) a) ^ q).val

variable {K : Type _} [Field K] [DecidableEq K]

/-- The loop of Algorithm 14.3: given `h = hᵢ` (congruent to `x^(qⁱ)` mod
`fᵢ`) and `fi = fᵢ`, run steps `i+1, i+2, …` until `fᵢ = 1` or the early
abort fires (or the fuel runs out), returning `(gᵢ₊₁, gᵢ₊₂, …)`.  The
`q`-th power runs mod the CURRENT `fᵢ`, which shrinks as factors are
removed. -/
def distinctDegreeFactorizationLoop (q : AzNat) :
    (fuel i : ℕ) → AzPolynomial K → AzPolynomial K → List (AzPolynomial K)
  | 0, _, _, _ => []
  | fuel + 1, i, h, fi =>
    if fi = 1 then []
    else if fi.natDegree < 2 * (i + 1) then
      List.replicate (fi.natDegree - i - 1) 1 ++ [fi]
    else
      let h' := powModByMonic h q fi
      let g := gcdMonic (h' - X) fi
      g :: distinctDegreeFactorizationLoop q fuel (i + 1) h' (divByMonic fi g)

/-- **Distinct-degree factorization** (GG Algorithm 14.3, with early
abort and per-iteration moduli).  For a squarefree monic `f` over a finite
field with `q` elements, returns the distinct-degree decomposition
`(g₁, …, g_s)` of `f`. -/
def distinctDegreeFactorization (q : AzNat) (f : AzPolynomial K) :
    List (AzPolynomial K) :=
  distinctDegreeFactorizationLoop q f.natDegree 0 X f

end Azurite.AzPolynomial

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! ### The book's `F_3` example, and the early-abort paths

`f = x(x+1)(x²+1)(x²+x+2) = (x²+x)·(x⁴+x³+x+2)` reproduces the book's
decomposition (no abort: the degree-4 tail at `i = 1` fails
`4 < 2·2`).  `f = x·(x³+2x+1)` (the cubic irreducible, no zeros in `F_3`)
aborts at `i = 1` (`3 < 4`), emitting the gap `g₂ = 1` and the cubic in
position 3.  An irreducible quadratic aborts at `i = 1` (`2 < 4`) with a
leading gap.  `f = 1` is the empty decomposition. -/

section Tests

open Azurite Azurite.AzPolynomial

private instance : Fact (Nat.Prime (AzNat.ofNat 3).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private def q3 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 3)) :=
  (parseAzPolynomial s).get!

-- the book's example: parts of degree 1 and 2
#guard ((distinctDegreeFactorization (AzNat.ofNat 3)
    (q3 "x^2+x" * q3 "x^4+x^3+x+2")).map toChars) == ["x^2+x", "x^4+x^3+x+2"]

-- a gap: f = x·(x³+2x+1), no quadratic part (early abort at i = 1)
#guard ((distinctDegreeFactorization (AzNat.ofNat 3)
    (q3 "x" * q3 "x^3+2*x+1")).map toChars) == ["x", "1", "x^3+2*x+1"]

-- an irreducible input is its own single (last) part (early abort at i = 1)
#guard ((distinctDegreeFactorization (AzNat.ofNat 3)
    (q3 "x^2+1")).map toChars) == ["1", "x^2+1"]

-- a large irreducible tail: f = x(x+1)(x⁴+x+2), with the quartic
-- irreducible (no roots, and not among the products of the three monic
-- irreducible quadratics over F_3): after the degree-2 round leaves the
-- quartic (4 < 2·2 fails at i = 1), the abort fires at i = 2 (4 < 2·3),
-- skipping the degree-3 and degree-4 rounds
#guard ((distinctDegreeFactorization (AzNat.ofNat 3)
    (q3 "x^2+x" * q3 "x^4+x+2")).map toChars) == ["x^2+x", "1", "1", "x^4+x+2"]

-- f = 1: the empty decomposition
#guard ((distinctDegreeFactorization (AzNat.ofNat 3) (q3 "1")).map toChars)
  == ([] : List String)

/-! #### GG Example 14.5

`f = x⁸+x⁷−x⁶+x⁵−x³−x²−x ∈ F_3[x]` (squarefree, `−1 ≡ 2`): the book's run
of Algorithm 14.3 gives `(g₁, g₂, g₃) = (x, x⁴+x³+x−1, x³−x+1)` — the
linear factor, the two irreducible quadratics, and an irreducible cubic.
The third round early-aborts at `i = 2` (`deg f₂ = 3 < 2·3`), with an empty
gap.  The parts multiply back to `f`. -/

private def f145 : AzPolynomial (AzZMod (AzNat.ofNat 3)) :=
  q3 "x^8+x^7+2*x^6+x^5+2*x^3+2*x^2+2*x"

#guard ((distinctDegreeFactorization (AzNat.ofNat 3) f145).map toChars)
  == ["x", "x^4+x^3+x+2", "x^3+2*x+1"]

#guard toChars ((distinctDegreeFactorization (AzNat.ofNat 3) f145).foldl (· * ·) 1)
  == toChars f145

end Tests

import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse
import Azurite.AzPolynomial.ToString
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R]

/-- **Newton sums of a monic polynomial (BPR Definition 4.7).**

    For a monic polynomial `P ∈ R[X]` of degree `p` with coefficients
    `P = X^p + a_{p-1} X^{p-1} + ⋯ + a_0`, the `i`-th Newton sum is

      `N_i(P) = ∑_{x ∈ roots(P)} x^i`,

    where roots are counted with multiplicity in an algebraic closure.

    The Newton recurrence (BPR Proposition 4.8) states

      `(p - i) · a_{p - i} = a_p · N_i + a_{p-1} · N_{i-1} + ⋯ + a_0 · N_{i-p}`

    (with `a_j = N_j = 0` for `j < 0`). For monic `P` (where `a_p = 1`),
    solving for `N_i` gives the recurrence used here:

      `N_0 = p`,
      `N_i = (p - i) · a_{p-i} - ∑_{k = 1}^{min(i, p)} a_{p-k} · N_{i-k}`,

    where the leading-term contribution `(p - i) · a_{p-i}` is taken to
    be `0` when `i > p`.

    The result matches the mathematical Newton sum exactly when `P` is
    monic; for non-monic `P` one would have to divide by the leading
    coefficient at each step (see `newtonSumMonic_toPoly` for the
    correctness statement, in `Equiv/NewtonSum`). -/
def newtonSumMonic (P : AzPolynomial R) : ℕ → R
  | 0 => (P.natDegree : R)
  | i + 1 =>
    let p := P.natDegree
    let leading : R :=
      if i + 1 ≤ p then ((p - (i + 1) : ℕ) : R) * P.coeff (p - (i + 1)) else 0
    leading - ∑ k ∈ Finset.range (min (i + 1) p),
      P.coeff (p - (k + 1)) * P.newtonSumMonic (i - k)

/-- The first `n` Newton sums `[N_0, N_1, …, N_{n-1}]` of a monic
    polynomial `P`. -/
def newtonSumsMonic (P : AzPolynomial R) (n : ℕ) : Array R :=
  (Array.range n).map P.newtonSumMonic

-- Sanity checks.
-- P = X - 5, roots = {5}, N_i = 5^i.
#guard (parseAzPolynomial (R := ℤ) "x-5").get!.newtonSumsMonic 4 == #[1, 5, 25, 125]

-- P = X^2 - 3X + 2 = (X-1)(X-2), roots = {1, 2}, N_i = 1 + 2^i.
#guard (parseAzPolynomial (R := ℤ) "x^2-3*x+2").get!.newtonSumsMonic 5 ==
       #[2, 3, 5, 9, 17]

-- P = X^2 + b·X + c (general monic quadratic) with b = -3, c = 2:
--   N_0 = 2, N_1 = -b = 3, N_2 = b² - 2c = 5.
#guard (parseAzPolynomial (R := ℤ) "x^2-3*x+2").get!.newtonSumMonic 2 == 5

-- P = X^3, roots = {0, 0, 0}, N_i = 0 for i ≥ 1 and N_0 = 3.
#guard (parseAzPolynomial (R := ℤ) "x^3").get!.newtonSumsMonic 4 == #[3, 0, 0, 0]

-- P = X^3 - 6X^2 + 11X - 6 = (X-1)(X-2)(X-3), roots = {1, 2, 3}.
-- N_0 = 3, N_1 = 6, N_2 = 1 + 4 + 9 = 14, N_3 = 1 + 8 + 27 = 36.
#guard (parseAzPolynomial (R := ℤ) "x^3-6*x^2+11*x-6").get!.newtonSumsMonic 4 ==
       #[3, 6, 14, 36]

section PolyFromNewtonSums

variable {D : Type _} [Field D]

/-- Recursive specification of the coefficient at index `k` of the
    monic polynomial returned by BPR Algorithm 8.11, given Newton
    sums `N` and intended degree `p`:

      `coeffFromNewtonSums N p p = 1`,
      `coeffFromNewtonSums N p k = -(1 / (p - k)) ·
          ∑_{j = 1}^{p - k} coeffFromNewtonSums N p (k + j) · N_j`
        for `k < p`,
      `coeffFromNewtonSums N p k = 0` for `k > p`.

    The recursion is on `p - k` (which decreases at each recursive
    call since `k + j > k`). The leading coefficient at `k = p`
    serves as the base case. -/
def coeffFromNewtonSums (N : Array D) (p : ℕ) (k : ℕ) : D :=
  if k < p then
    -(((p - k : ℕ) : D))⁻¹ * ∑ j ∈ Finset.range (p - k),
      coeffFromNewtonSums N p (k + (j + 1)) * (N.getD (j + 1) 0)
  else if k = p then 1
  else 0
termination_by p - k
decreasing_by omega

/-- **BPR Algorithm 8.11: Newton sums → monic polynomial.**

    Given the Newton sums `N = [N_0, N_1, …, N_p]` of a monic
    polynomial `P = X^p + a_{p-1} X^{p-1} + ⋯ + a_0 ∈ D[X]`, returns
    the polynomial `P : AzPolynomial D` whose coefficients are
    determined by the Newton recurrence (BPR Proposition 4.8):

      `a_p = 1`,
      `a_{p-i} = (-1/i) · ∑_{j=1}^{i} a_{p-i+j} · N_j`  for `i = 1, …, p`.

    Each iteration `i` uses the entries `a_{p-i+1}, …, a_p` of the
    coefficient array (the higher-degree coefficients already
    determined in previous iterations) together with the input Newton
    sums `N_1, …, N_i`. Internally this is the recursive
    `coeffFromNewtonSums`, indexed downward from the leading
    coefficient.

    Although BPR phrases the output as "the list of coefficients",
    here we return an actual `AzPolynomial D`: the underlying
    coefficient array has the leading `1` at the high end and lower
    coefficients below, automatically satisfying the
    `last_ne_zero` invariant since `(1 : D) ≠ (0 : D)` in a field.

    \-\- BPR's "Structure: a ring D with division in Z" (the D₁
    structure) is a strictly more general home; we use `[Field D]`
    since divisions by `(i : D)` for `i ∈ {1, …, p}` are required and
    `Field` is the standard Mathlib type-class with that operation.
    When `N` is empty, the result is the zero polynomial; otherwise
    the result has `natDegree = N.size - 1`. -/
def polyFromNewtonSumsMonic (N : Array D) : AzPolynomial D :=
  if N.isEmpty then 0
  else
    let p := N.size - 1
    let coeffs := (Array.range p).map (coeffFromNewtonSums N p)
    ⟨coeffs.push 1, by
      rw [Array.back?_push]
      intro h
      exact one_ne_zero (Option.some_inj.mp h)⟩

-- Sanity checks.
-- P = X - 5, Newton sums [1, 5].
#guard toString (polyFromNewtonSumsMonic (D := ℚ) #[1, 5]) == "x-5"

-- P = X^2 - 3X + 2, Newton sums [2, 3, 5].
#guard toString (polyFromNewtonSumsMonic (D := ℚ) #[2, 3, 5]) == "x^2-3*x+2"

-- P = X^3, Newton sums [3, 0, 0, 0].
#guard toString (polyFromNewtonSumsMonic (D := ℚ) #[3, 0, 0, 0]) == "x^3"

-- P = X^3 - 6X^2 + 11X - 6, Newton sums [3, 6, 14, 36].
#guard toString (polyFromNewtonSumsMonic (D := ℚ) #[3, 6, 14, 36]) ==
       "x^3-6*x^2+11*x-6"

-- N = [0] (just N_0 = 0 = degree, monic of degree 0 → constant 1).
#guard toString (polyFromNewtonSumsMonic (D := ℚ) #[0]) == "1"

-- Empty input → zero polynomial.
#guard toString (polyFromNewtonSumsMonic (D := ℚ) #[]) == "0"

end PolyFromNewtonSums

end Azurite.AzPolynomial

/-
  Equal-degree splitting (Gathen–Gerhard, "Modern Computer Algebra",
  Algorithm 14.8), computable — for an ODD prime power `q`.

  Input: a squarefree monic `f ∈ F_q[x]` of degree `n > 0` all of whose
  irreducible factors have degree `d < n`.  One attempt: pick a random
  `a ∈ F_q[x]` with `deg a < n`; fail if `a` is constant; return
  `gcd(a, f)` if it is nontrivial; otherwise compute
  `b = a^((q^d−1)/2) rem f` and return `gcd(b − 1, f)` if it is a proper
  factor, else fail.  By GG Lemma 14.7, `a`'s image in each of the `q^d`-
  element residue fields `F_q[x]/(fᵢ)` lands on `±1` under the
  `(q^d−1)/2`-th power with an even split, so `b − 1` vanishes mod some
  factors and not others with probability ≈ 1/2 (Theorem 14.9).

  THE CANDIDATE STREAM (`hybridPolyCandidate`) is a hybrid, per the design
  note: indices below `2^64` draw a pseudorandom polynomial of degree
  `< n` (a per-index-seeded `SplitMix64`, one 64-bit word per coefficient,
  mapped into `K` through its exhaustive enumeration mod `card K` — the
  word-level reduction is slightly biased and reaches only `2^64`
  coefficient values, which is irrelevant in practice and harmless in
  principle); indices from `2^64` on replay the EXHAUSTIVE bounded-degree
  enumeration `azPolynomialDegreeLtGen`.  In practice only the PRNG
  prefix is ever consumed, but the practically-unreachable exhaustive
  tail makes the stream provably surjective onto the degree-`< n`
  polynomials (`hybridPolyCandidate_hits`) — the hook for turning the
  expected-2-attempts loop into termination by theorem.

  The output contract — any `some g` is a proper monic factor of `f` —
  is `Azurite.GG.equalDegreeSplitting_correct`, proved in
  `Azurite/GathenGerhard/Chapter14/Algorithm_14_8.lean`.
-/
import Azurite.AzPolynomial.DistinctDegreeFactorization
import Azurite.ExhaustiveGenerator.Polynomials
import Azurite.Random.Gen
import Azurite.AzNat.Pow
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.ShiftRight

namespace Azurite.AzPolynomial

open Azurite.ExhaustiveGenerator

/-! ### The hybrid candidate stream -/

/-- One coefficient from a 64-bit PRNG word: an index into the exhaustive
enumeration of the (finite) coefficient ring, reduced mod its cardinality.
(For `card K > 2^64` only the first `2^64` elements are reachable, and the
reduction is slightly biased — acceptable for the pseudorandom prefix; the
exhaustiveness guarantees come from the tail, not from here.) -/
def coeffOfWord (K : Type _) [Zero K] [ExhaustiveGenerator K]
    [FiniteGenerator K] (u : UInt64) : K :=
  (ExhaustiveGenerator.gen (u.toNat % FiniteGenerator.card K)).getD 0

/-- `n` PRNG coefficients from a `SplitMix64` state. -/
def randomCoeffs (K : Type _) [Zero K] [ExhaustiveGenerator K]
    [FiniteGenerator K] : ℕ → Random.SplitMix64 → List K
  | 0, _ => []
  | m + 1, g =>
    let (u, g') := (Random.RandomGen.next g : UInt64 × Random.SplitMix64)
    coeffOfWord K u :: randomCoeffs K m g'

/-- The pseudorandom polynomial of degree `< n` at stream index `i`:
a per-index-seeded `SplitMix64` supplies `n` coefficients (trailing zeros
trimmed by `normalize`). -/
def randomPolyDegreeLt (K : Type _) [Semiring K] [DecidableEq K]
    [ExhaustiveGenerator K] [FiniteGenerator K] (seed : UInt64) (n i : ℕ) :
    AzPolynomial K :=
  normalize
    (randomCoeffs K n (Random.mkSplitMix64 (seed + UInt64.ofNat i))).toArray

/-- `normalize` only trims, so the size never grows. -/
theorem size_normalize_le {R : Type _} [Semiring R] [DecidableEq R]
    (a : Array R) : (normalize a).coeffs.size ≤ a.size := by
  change (a.popWhile (· = 0)).size ≤ a.size
  rw [← Array.length_toList, ← Array.length_toList,
    toList_popWhile_eq_dropTrailingZeros]
  exact (dropTrailingZeros_prefix _).length_le

theorem randomCoeffs_length (K : Type _) [Zero K] [ExhaustiveGenerator K]
    [FiniteGenerator K] :
    ∀ (n : ℕ) (g : Random.SplitMix64), (randomCoeffs K n g).length = n
  | 0, _ => rfl
  | n + 1, g => by
    rw [randomCoeffs]
    simpa using randomCoeffs_length K n _

theorem natDegree_randomPolyDegreeLt_lt (K : Type _) [Semiring K]
    [DecidableEq K] [ExhaustiveGenerator K] [FiniteGenerator K]
    (seed : UInt64) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    (randomPolyDegreeLt K seed n i).natDegree < n := by
  have hsz : (randomPolyDegreeLt K seed n i).coeffs.size ≤ n := by
    have h1 := size_normalize_le
      (randomCoeffs K n (Random.mkSplitMix64 (seed + UInt64.ofNat i))).toArray
    have h2 : (randomCoeffs K n
        (Random.mkSplitMix64 (seed + UInt64.ofNat i))).toArray.size = n := by
      rw [List.size_toArray, randomCoeffs_length]
    rw [h2] at h1
    exact h1
  show (randomPolyDegreeLt K seed n i).coeffs.size - 1 < n
  omega

/-- **The hybrid candidate stream**: pseudorandom polynomials of degree
`< n` for the first `2^64` indices, then the exhaustive bounded-degree
enumeration.  Practically random, provably exhaustive
(`hybridPolyCandidate_hits`). -/
def hybridPolyCandidate (K : Type _) [Semiring K] [DecidableEq K]
    [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})]
    (seed : UInt64) (n : ℕ) (i : ℕ) : AzPolynomial K :=
  if i < 2 ^ 64 then randomPolyDegreeLt K seed n i
  else (((azPolynomialDegreeLtGen (R := K) n).gen (i - 2 ^ 64)).map
    Subtype.val).getD 0

/-- **The stream is surjective** onto the polynomials of degree `< n`:
every one appears at some index (in the exhaustive tail, if nowhere
earlier).  This is what upgrades "retry with fresh randomness" into a
provably terminating search. -/
theorem hybridPolyCandidate_hits (K : Type _) [Semiring K] [DecidableEq K]
    [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})]
    (seed : UInt64) {n : ℕ} {p : AzPolynomial K}
    (hp : p.degree < (n : WithBot ℕ)) :
    ∃ i, hybridPolyCandidate K seed n i = p := by
  obtain ⟨j, hj, -⟩ :=
    (azPolynomialDegreeLtGen (R := K) n).occurs_exactly_once ⟨p, hp⟩
  refine ⟨2 ^ 64 + j, ?_⟩
  rw [hybridPolyCandidate, if_neg (by omega), Nat.add_sub_cancel_left, hj]
  rfl

/-- Every stream element has degree `< n` (for `n > 0`). -/
theorem natDegree_hybridPolyCandidate_lt (K : Type _) [Semiring K]
    [DecidableEq K] [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})]
    (seed : UInt64) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    (hybridPolyCandidate K seed n i).natDegree < n := by
  rw [hybridPolyCandidate]
  by_cases hi : i < 2 ^ 64
  · rw [if_pos hi]
    exact natDegree_randomPolyDegreeLt_lt K seed hn i
  · rw [if_neg hi]
    cases hgen : (azPolynomialDegreeLtGen (R := K) n).gen (i - 2 ^ 64) with
    | none =>
      show (0 : AzPolynomial K).natDegree < n
      have h0 : (0 : AzPolynomial K).natDegree = 0 := rfl
      omega
    | some pq =>
      show pq.val.natDegree < n
      have hdeg := pq.property
      rw [degree_lt_iff_size_le] at hdeg
      show pq.val.coeffs.size - 1 < n
      omega

/-! ### Algorithm 14.8 -/

/-- The Cantor–Zassenhaus exponent `(q^d − 1)/2`, limb-level. -/
def czExponent (q : AzNat) (d : ℕ) : AzNat :=
  (q.pow d - AzNat.ofNat 1).shiftRight 1

@[simp] theorem toNat_czExponent (q : AzNat) (d : ℕ) :
    (czExponent q d).toNat = (q.toNat ^ d - 1) / 2 := by
  rw [czExponent, AzNat.toNat_shiftRight, AzNat.toNat_sub, AzNat.toNat_pow,
    AzNat.toNat_ofNat, pow_one]

variable {K : Type _} [Field K] [DecidableEq K]

/-- **One attempt of Algorithm 14.8 (equal-degree splitting)**, on a given
candidate `a`: fail if `a` is constant; return `gcd(a, f)` if nontrivial;
else return `gcd(a^((q^d−1)/2) rem f − 1, f)` if it is a proper factor.
`none` is the algorithm's "failure". -/
def equalDegreeSplittingStep (q : AzNat) (d : ℕ) (f a : AzPolynomial K) :
    Option (AzPolynomial K) :=
  if a.natDegree = 0 then none
  else
    let g₁ := gcdMonic a f
    if g₁ ≠ 1 then some g₁
    else
      let g₂ := gcdMonic (powModByMonic a (czExponent q d) f - 1) f
      if g₂ ≠ 1 ∧ g₂ ≠ f then some g₂ else none

/-- **Algorithm 14.8 (equal-degree splitting)** at stream index `i`: one
attempt on the `i`-th hybrid candidate.  Callers retry with `i + 1` on
`none` (expected ≈ 2 attempts; the exhaustive tail makes the retry loop
provably terminating). -/
def equalDegreeSplitting (q : AzNat) (d : ℕ) (f : AzPolynomial K)
    [ExhaustiveGenerator K] [FiniteGenerator K]
    [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})]
    (seed : UInt64) (i : ℕ) : Option (AzPolynomial K) :=
  equalDegreeSplittingStep q d f (hybridPolyCandidate K seed f.natDegree i)

end Azurite.AzPolynomial

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! ### Equal-degree splitting over `F_3`

`f = (x²+1)(x²+x+2) = x⁴+x³+x+2` (the two irreducible quadratics, `d = 2`,
exponent `(3²−1)/2 = 4`): candidate `a = x` extracts `x²+1` through the
power path (`x⁴ ≡ 2x³+2x+1 mod f`, `gcd(2x³+2x, f) = x²+1`); `a = x+2`
extracts the OTHER factor; `a = x+1` fails (its power lands on the same
sign in both residue fields); `a = x³+x = x(x²+1)` short-circuits through
`g₁ = gcd(a, f)`; constants fail by rule.  A `d = 1` run splits
`f = x(x+1)`.  The driver `equalDegreeSplitting` (seed 0) succeeds on its
first candidate — expected ≈ 2 attempts. -/

section Tests

open Azurite Azurite.AzPolynomial

private instance : Fact (Nat.Prime (AzNat.ofNat 3).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; decide⟩

private def p3 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 3)) :=
  (parseAzPolynomial s).get!

private def fEDS : AzPolynomial (AzZMod (AzNat.ofNat 3)) := p3 "x^4+x^3+x+2"

-- the exponent: (3² − 1)/2 = 4
#guard (czExponent (AzNat.ofNat 3) 2).toNat == 4

-- the power path, extracting each factor
#guard ((equalDegreeSplittingStep (AzNat.ofNat 3) 2 fEDS (p3 "x")).map toChars)
  == some "x^2+1"
#guard ((equalDegreeSplittingStep (AzNat.ofNat 3) 2 fEDS (p3 "x+2")).map toChars)
  == some "x^2+x+2"

-- an unlucky candidate: same sign in both residue fields
#guard (equalDegreeSplittingStep (AzNat.ofNat 3) 2 fEDS (p3 "x+1")) == none

-- the `g₁` short-circuit: `a` shares the factor `x²+1` with `f`
#guard ((equalDegreeSplittingStep (AzNat.ofNat 3) 2 fEDS (p3 "x^3+x")).map toChars)
  == some "x^2+1"

-- constants fail by rule (including 0)
#guard (equalDegreeSplittingStep (AzNat.ofNat 3) 2 fEDS (p3 "2")) == none
#guard (equalDegreeSplittingStep (AzNat.ofNat 3) 2 fEDS (p3 "0")) == none

-- d = 1: splitting x(x+1) (exponent (3−1)/2 = 1)
#guard ((equalDegreeSplittingStep (AzNat.ofNat 3) 1 (p3 "x^2+x")
    (p3 "x+2")).map toChars) == some "x+1"

-- the driver on the hybrid stream (seed 0): first candidate already splits,
-- the second fails, the third finds the other factor
#guard ((equalDegreeSplitting (AzNat.ofNat 3) 2 fEDS (0 : UInt64) 0).map toChars)
  == some "x^2+1"
#guard (equalDegreeSplitting (AzNat.ofNat 3) 2 fEDS (0 : UInt64) 1) == none
#guard ((equalDegreeSplitting (AzNat.ofNat 3) 2 fEDS (0 : UInt64) 2).map toChars)
  == some "x^2+x+2"

end Tests

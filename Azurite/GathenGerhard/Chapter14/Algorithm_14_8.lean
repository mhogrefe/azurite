/-
  Gathen–Gerhard, Algorithm 14.8 (equal-degree splitting): the OUTPUT
  CONTRACT — whatever the algorithm returns is a proper monic factor.

  The computable algorithm lives in
  `Azurite/AzPolynomial/EqualDegreeSplitting.lean` (one attempt
  `equalDegreeSplittingStep` on a given candidate `a`, and the driver
  `equalDegreeSplitting` on the hybrid pseudorandom-then-exhaustive
  candidate stream).  Here we prove the algorithm's specification "Output:
  a proper monic factor `g ∈ F_q[x]` of `f`, or failure": whenever a
  `some g` is returned, the represented `g` is monic, divides `f`, and is
  neither `1` nor `f`.

  Notably the contract needs only `f` monic and `deg a < deg f` — no
  squarefreeness, no equal-degree hypothesis, and nothing about `q` or
  `d`.  The `g₁` branch is proper because `gcd(a, f)` divides the
  nonconstant `a` of degree `< deg f`; the `g₂` branch checks properness
  explicitly.  (The equal-degree hypotheses govern the success
  PROBABILITY — GG Theorem 14.9 — not the validity of a success.)

  The end-to-end `equalDegreeSplitting_correct` instantiates the contract
  at the hybrid stream, whose elements all have degree `< deg f` by
  `natDegree_hybridPolyCandidate_lt`.
-/
import Azurite.GathenGerhard.Chapter14.Lemma_14_7
import Azurite.AzPolynomial.EqualDegreeSplitting
import Azurite.AzPolynomial.Equiv.Gcd

namespace Azurite

namespace GG

open Polynomial

/- Prefer Mathlib's `NormalizedGCDMonoid` gcd over the Chapter-1
`EuclideanDomain`-derived instance imported through the subresultant
theory (same as in `Algorithm_14_3.lean`). -/
attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- Nonconstant `AzPolynomial`s are nonzero. -/
private theorem ne_zero_of_natDegree_ne_zero {a : AzPolynomial K}
    (h : a.natDegree ≠ 0) : AzPolynomial.toPoly a ≠ 0 := by
  intro h0
  apply h
  have : a = 0 := by rwa [← toPoly_inj, toPoly_zero]
  rw [this]
  rfl

/-- A monic-normalized gcd with a nonzero argument is a monic divisor. -/
private theorem gcdMonic_monic_right {a f : AzPolynomial K}
    (hf0 : AzPolynomial.toPoly f ≠ 0) :
    (AzPolynomial.toPoly (AzPolynomial.gcdMonic a f)).Monic := by
  rw [AzPolynomial.toPoly_gcdMonic]
  have h0 : gcd (AzPolynomial.toPoly a) (AzPolynomial.toPoly f) ≠ 0 := by
    rw [Ne, gcd_eq_zero_iff]
    rintro ⟨-, h⟩
    exact hf0 h
  exact (Polynomial.normalize_eq_self_iff_monic h0).mp (normalize_gcd _ _)

/-- **The output contract of one attempt of Algorithm 14.8**: for monic
`f` and a candidate of degree `< deg f`, any returned `g` is a proper
monic factor — monic, dividing `f`, and neither `1` nor `f`.  No
squarefree or equal-degree hypotheses are needed (those govern the
success probability, not the validity of a success). -/
theorem equalDegreeSplittingStep_correct {q : AzNat} {d : ℕ}
    {f a g : AzPolynomial K} (hm : (AzPolynomial.toPoly f).Monic)
    (hdeg : a.natDegree < f.natDegree)
    (h : AzPolynomial.equalDegreeSplittingStep q d f a = some g) :
    (AzPolynomial.toPoly g).Monic ∧
    AzPolynomial.toPoly g ∣ AzPolynomial.toPoly f ∧
    AzPolynomial.toPoly g ≠ 1 ∧
    AzPolynomial.toPoly g ≠ AzPolynomial.toPoly f := by
  rw [AzPolynomial.equalDegreeSplittingStep] at h
  by_cases ha : a.natDegree = 0
  · rw [if_pos ha] at h
    exact absurd h (by simp)
  rw [if_neg ha] at h
  simp only [] at h
  by_cases hg1 : AzPolynomial.gcdMonic a f ≠ 1
  · rw [if_pos hg1] at h
    obtain rfl : AzPolynomial.gcdMonic a f = g := Option.some.inj h
    have ha0 : AzPolynomial.toPoly a ≠ 0 := ne_zero_of_natDegree_ne_zero ha
    have hgmonic : (AzPolynomial.toPoly (AzPolynomial.gcdMonic a f)).Monic := by
      rw [AzPolynomial.toPoly_gcdMonic]
      have h0 : gcd (AzPolynomial.toPoly a) (AzPolynomial.toPoly f) ≠ 0 := by
        rw [Ne, gcd_eq_zero_iff]
        rintro ⟨h', -⟩
        exact ha0 h'
      exact (Polynomial.normalize_eq_self_iff_monic h0).mp (normalize_gcd _ _)
    refine ⟨hgmonic, ?_, ?_, ?_⟩
    · rw [AzPolynomial.toPoly_gcdMonic]
      exact gcd_dvd_right _ _
    · rw [Ne, ← toPoly_one (R := K), toPoly_inj]
      exact hg1
    · -- the gcd divides the nonconstant `a` of degree `< deg f`
      intro heq
      have hdvd : AzPolynomial.toPoly (AzPolynomial.gcdMonic a f)
          ∣ AzPolynomial.toPoly a := by
        rw [AzPolynomial.toPoly_gcdMonic]
        exact gcd_dvd_left _ _
      have hle := Polynomial.natDegree_le_of_dvd hdvd ha0
      rw [heq, AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly]
        at hle
      omega
  · rw [if_neg hg1] at h
    by_cases hg2 : AzPolynomial.gcdMonic
        (AzPolynomial.powModByMonic a (AzPolynomial.czExponent q d) f - 1) f ≠ 1
        ∧ AzPolynomial.gcdMonic
        (AzPolynomial.powModByMonic a (AzPolynomial.czExponent q d) f - 1) f ≠ f
    · rw [if_pos hg2] at h
      obtain rfl : AzPolynomial.gcdMonic
          (AzPolynomial.powModByMonic a (AzPolynomial.czExponent q d) f - 1) f
          = g := Option.some.inj h
      refine ⟨gcdMonic_monic_right hm.ne_zero, ?_, ?_, ?_⟩
      · rw [AzPolynomial.toPoly_gcdMonic]
        exact gcd_dvd_right _ _
      · rw [Ne, ← toPoly_one (R := K), toPoly_inj]
        exact hg2.1
      · rw [Ne, toPoly_inj]
        exact hg2.2
    · rw [if_neg hg2] at h
      exact absurd h (by simp)

/-- **The output contract of the driver**: any success on the hybrid
candidate stream is a proper monic factor of `f`.  (Success at SOME index
is what the equal-degree hypotheses buy — the stream is surjective onto
the degree-`< n` candidates by `hybridPolyCandidate_hits`, and once `f`
has at least two equal-degree factors, splitting candidates exist.) -/
theorem equalDegreeSplitting_correct [ExhaustiveGenerator K]
    [FiniteGenerator K] [ExhaustiveGenerator {t : K // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector K (m + 1) × {t : K // t ≠ 0})]
    {q : AzNat} {d : ℕ} {f g : AzPolynomial K} {seed : UInt64} {i : ℕ}
    (hm : (AzPolynomial.toPoly f).Monic) (hn : 0 < f.natDegree)
    (h : AzPolynomial.equalDegreeSplitting q d f seed i = some g) :
    (AzPolynomial.toPoly g).Monic ∧
    AzPolynomial.toPoly g ∣ AzPolynomial.toPoly f ∧
    AzPolynomial.toPoly g ≠ 1 ∧
    AzPolynomial.toPoly g ≠ AzPolynomial.toPoly f :=
  equalDegreeSplittingStep_correct hm
    (AzPolynomial.natDegree_hybridPolyCandidate_lt K seed hn i) h

end GG

end Azurite

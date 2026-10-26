# DLMF formalization ledger

A walk through the NIST Digital Library of Mathematical Functions (<https://dlmf.nist.gov>),
one Lean theorem per equation, in `Azurite/DLMF/ChapterC/SectionS.lean` with the theorem
`dlmf_C_S_N` for equation C.S.N (suffixes for the several equalities of one equation).  Each
theorem is either a thin restatement of a Mathlib lemma, named in its docstring and here, or a
proof of its own.  Statements follow the DLMF text (variables, hypotheses, ranges); where the
DLMF leaves a type implicit (for example the ring of the binomial theorem) the theorem is stated
at the natural generality.

## Chapter 1: Algebraic and Analytic Methods

### §1.2 Elementary Algebra (`Azurite/DLMF/Chapter1/Section2.lean`)

| Equation | Theorem | Mathlib |
|---|---|---|
| 1.2.1 | `dlmf_1_2_1` (in `ℕ`, exact division), `dlmf_1_2_1_cast` (in `ℂ`), `dlmf_1_2_1_symm` | `Nat.choose_eq_factorial_div_factorial`, `Nat.cast_choose`, `Nat.choose_symm` |
| 1.2.2 | `dlmf_1_2_2` (any commutative semiring) | `add_pow` |
| 1.2.3 | `dlmf_1_2_3` | `Nat.sum_range_choose` |
| 1.2.4 | `dlmf_1_2_4` (`n ≥ 1`) | `Int.alternating_sum_range_choose_of_ne` |
| 1.2.5 | `dlmf_1_2_5` (`n ≥ 1`; the sum over even `k ≤ n`) | proven from 1.2.3 and 1.2.4 |
| 1.2.6 | `dlmf_1_2_6` (falling product), `dlmf_1_2_6_asc` (`(−1)^k (−z)_k / k!`), `dlmf_1_2_6_neg` (`(−1)^k C(k − z − 1, k)`), for `z : ℂ` with `Ring.choose` | `Ring.descPochhammer_eq_factorial_smul_choose`, `descPochhammer_eval_eq_prod_range`, `ascPochhammer_eval_neg_eq_descPochhammer`; helper `descPochhammer_smeval_eq_prod` |
| 1.2.7 | `dlmf_1_2_7` (with `k + 1`) | `Ring.choose_succ_succ` |
| 1.2.8 | `dlmf_1_2_8` | proven (induction with 1.2.7) |
| 1.2.9 | `dlmf_1_2_9` | proven (induction with 1.2.7) |
| 1.2.10–1.2.62 | — | not yet |

Conventions: the generalized binomial coefficient `C(z, k)` of the DLMF is Mathlib's
`Ring.choose z k` (`BinomialRing`), which agrees with `Nat.choose` on the natural numbers
(`Ring.choose_natCast`); the rising factorial `(z)_k` is `(ascPochhammer ℂ k).eval z`.

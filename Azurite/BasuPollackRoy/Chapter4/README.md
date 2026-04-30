# BPR Chapter 4: Algebra

Formalization of Basu, Pollack, Roy's *Algorithms in Real Algebraic Geometry*,
Chapter 4.

## File organization

- One BPR-numbered statement (definition, lemma, proposition, theorem,
  corollary) per file, named `Definition_4_NN.lean`, `Theorem_4_NN.lean`, etc.
- Section/subsection placeholder files (e.g. `Section4_1.lean`,
  `Section4_2/Subsection4_2_1.lean`) host each section's docstring and may
  later evolve into barrel files re-exporting the statement files.
- Helper lemmas that aren't BPR-numbered live in the same file as the
  BPR statement they support, in a `section Helpers` or `private` block.

## Sections

| § | Title | Path | Status |
|---|---|---|---|
| 4.1 | Discriminant and Subdiscriminant | `Section4_1.lean` | not started |
| 4.2.1 | Resultant | `Section4_2/Subsection4_2_1.lean` | not started |
| 4.2.2 | Subresultant Coefficients | `Section4_2/Subsection4_2_2.lean` | not started |
| 4.2.3 | Subresultant Coefficients and Cauchy Index | `Section4_2/Subsection4_2_3.lean` | not started |
| 4.3.1 | Quadratic Forms | `Section4_3/Subsection4_3_1.lean` | not started |
| 4.3.2 | Hermite's Quadratic Form | `Section4_3/Subsection4_3_2.lean` | not started |
| 4.4.1 | Hilbert's Basis Theorem | `Section4_4/Subsection4_4_1.lean` | not started |
| 4.4.2 | Hilbert's Nullstellensatz | `Section4_4/Subsection4_4_2.lean` | not started |
| 4.5 | Zero-Dimensional Systems | `Section4_5.lean` | not started |
| 4.6 | Multivariate Hermite's Quadratic Form | `Section4_6.lean` | not started |
| 4.7 | Projective Space and a Weak Bézout's Theorem | `Section4_7.lean` | not started |

## Statements

| BPR ref | Statement | File | Status |
|---|---|---|---|

(Empty — populated as Chapter 4 is formalized. Each row links the BPR-numbered
statement to the Lean file proving it.)

## Blueprint

The corresponding LaTeX blueprint lives at
`blueprint/src/chapter4/` and mirrors this directory's structure.

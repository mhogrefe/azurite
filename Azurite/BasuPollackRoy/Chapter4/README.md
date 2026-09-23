# BPR Chapter 4: Algebra

Formalization of Basu, Pollack, Roy's *Algorithms in Real Algebraic Geometry*,
Chapter 4 (namespace `Azurite.BPR.Chapter4`). All sections (4.1 through 4.7,
including the weak Bézout theorem) are formalized; the statement-level catalog
with Lean names is in [`docs/module_map.md`](../../../docs/module_map.md).

## File organization

- One BPR-numbered statement (definition, lemma, proposition, theorem,
  corollary, notation, remark) per file, named `Definition_4_NN.lean`,
  `Theorem_4_NN.lean`, etc., placed in the directory of its section or
  subsection (`Section4_1/`, `Section4_2/Subsection4_2_1/`, ...).
- Helper lemmas that are not BPR-numbered live in the same file as the
  BPR statement they support, in a `section Helpers` or `private` block.
- Files without a BPR number (for example `Section4_3/QuadraticForm.lean` or
  `Section4_4/FiniteMapping.lean`) hold definitions and infrastructure shared by
  several statements of their section.

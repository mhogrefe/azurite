# Guidelines for AI Agents Working on Azurite

Welcome! When working on the Azurite project, please adhere to the following guidelines to ensure high-performance compilation and idiomatic Lean 4 code.

## Mathlib Usage

You are encouraged to make free and extensive use of Mathlib lemmas, definitions, and theorems to prove properties about `Azurite`.

When implementing new functions, keep provability in mind. For example, avoid legacy for loops, since there aren't many available theorems about them.

### Finding Mathlib Relevant Code
You can search the Mathlib source code locally in the project workspace at:
`.lake/packages/mathlib`

or (preferred) by using the lean-lsp MCP server. If the MCP server is not available, ask the user to restart it.

### ⚠️ IMPORTANT: Avoid Blanket Imports
**NEVER** do a blanket `import Mathlib` at the top of a file. 
Importing all of Mathlib adds immense overhead to compile times and significantly slows down the build process.

Instead:
1. Find the specific file in Mathlib that contains the theorem or definition you need.
2. Import only that specific module (e.g., `import Mathlib.Algebra.Polynomial.Basic` or `import Mathlib.Data.List.Basic`).
3. If a theorem is available natively in Lean 4 Core (e.g., in `Init.Data`), you do not need to import anything from Mathlib or Batteries at all! Always check if Core has what you need first.

# Crash guidance

If the user just messages "c", that means "You crashed, probably because you tried to write too much. Try writing to a temp file and using sed to insert the content into its final location."

# Guidelines for AI Agents Working on Azurite

Welcome! When working on the Azurite project, please adhere to the following guidelines to ensure high-performance compilation and idiomatic Lean 4 code.

## Mathlib Usage

You are encouraged to make free and extensive use of Mathlib lemmas, definitions, and theorems to prove properties about `Azurite`.

When implementing new functions, keep provability in mind. For example, avoid legacy for loops, since there aren't many available theorems about them.

### Finding Mathlib Relevant Code
You can search the Mathlib source code locally in the project workspace at:
`.lake/packages/mathlib`

or (preferred) by using the lean-lsp MCP server.

### ⚠️ If the LSP / MCP Server Is Down
If the lean-lsp MCP server returns connection errors or is unavailable, **stop and ask the user to restart it**. It only takes a few seconds to restart, and working without LSP feedback is much slower due to stale diagnostics and inability to check proof states. Do not try to power through without it.

### ⚠️ IMPORTANT: Avoid Blanket Imports
**NEVER** do a blanket `import Mathlib` at the top of a file. 
Importing all of Mathlib adds immense overhead to compile times and significantly slows down the build process.

Instead:
1. Find the specific file in Mathlib that contains the theorem or definition you need.
2. Import only that specific module (e.g., `import Mathlib.Algebra.Polynomial.Basic` or `import Mathlib.Data.List.Basic`).
3. If a theorem is available natively in Lean 4 Core (e.g., in `Init.Data`), you do not need to import anything from Mathlib or Batteries at all! Always check if Core has what you need first.

# Crash guidance

If the user just messages "c", that means "You crashed. Continue where you left off, but work differently to avoid crashing again." This typically happens after a context truncation or interruption.

To reduce the risk of crashes and improve reliability:
1. **Work incrementally.** Test proof snippets via `lean_run_code` before assembling a full file. Most proof attempts fail on the first try; iterating in small steps avoids wasting large writes.
2. **Don't promise to "write everything at once."** Long conversations accumulate context, and a large generation near the end is more likely to hit limits. Break work into pieces.
3. **When resuming after "c"**, re-read the relevant files to regain context before continuing.

# Lean 4 Tips

## Visibility: Avoid `private` for Provable Functions
When implementing pipeline internals (e.g., `collapseAux`, `collapseMonics`) that will need equivalence proofs later, do **not** mark them `private`. Private declarations are invisible outside their file, which forces you to put all related proofs in the same file. Instead, leave them as plain namespace-scoped definitions.

## `omit` Placement
`omit [Instance] in` must come **before** any doc comment, not between the doc comment and the declaration:
```lean
-- ✅ Correct
omit [DecidableEq R] in
/-- My theorem. -/
theorem foo ...

-- ❌ Wrong (causes "unexpected token 'omit'; expected 'lemma'")
/-- My theorem. -/
omit [DecidableEq R] in
theorem foo ...
```

## `Function.comp_def` for Beta-Reducing Compositions
When `rfl` fails on goals like `(f ∘ g) x = f (g x)`, or `map (f ∘ g) l = map (fun x => f (g x)) l`, use:
```lean
simp only [Function.comp_def]
```
This beta-reduces `(f ∘ g)` to `fun x => f (g x)`.

# Guidelines for AI Agents Working on Azurite

Welcome! When working on the Azurite project, please adhere to the following guidelines to ensure high-performance compilation and idiomatic Lean 4 code.

## README and Project Orientation

**Always consult `README.md` first** when orienting yourself in the project. It contains:
- A module map describing every directory and its purpose
- A table of all equivalence proofs (the `Equiv/` subdirectories)
- A catalog of implemented algorithms with BPR cross-references
- The project structure overview

**Keep the README updated.** When you add a new module, algorithm, equivalence proof, or BPR formalization, update the relevant section of `README.md` so that future agents and contributors can discover it.

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

If the user just messages "c", that means "You crashed. Try to not write so much text all at once." This typically happens after a context truncation or interruption.

To reduce the risk of crashes and improve reliability:
1. **Don't promise to "write everything at once."** Long conversations accumulate context, and a large generation near the end is more likely to hit limits. Break work into pieces.
2. **When resuming after "c"**, re-read the relevant files to regain context before continuing.

## Proof Development Workflow

**Work directly in the target file**, not in `lean_run_code` scratch snippets. The scratch approach causes two problems:
- **Environment mismatch:** `open` declarations, namespaces, and `variable` blocks change name resolution. Proofs that compile in a scratch snippet often fail when copied to the real file (e.g., `C_mul_X_eq_X_mul` resolving differently under `open Polynomial`).
- **Copy-paste crashes:** Writing or overwriting large file sections in one shot is the #1 crash trigger.

Instead, follow this workflow:
1. **Add the theorem statement + `sorry`** directly in the target file.
2. **Use `lean_goal`** at the `sorry` to see the exact proof state in the real environment.
3. **Use `lean_multi_attempt`** to try multiple tactics without modifying the file.
4. **Replace the `sorry`** with the working proof via a small edit.

This keeps edits small, uses the real environment, and avoids copy-paste. Don't worry about dirtying the file with `sorry`s — the user commits often and can easily revert.

# Lean 4 Tips

## Avoid Panicking (`!`) Functions
Never use panicking operations like `a[i]!`, `a.get!`, `a.head!`, `a.back!`, etc. in Azurite code. The `!` suffix in Lean 4 denotes functions that call `panic!` when a precondition fails at runtime.

Instead, use proof-bounded variants (e.g., `a[i]` with a proof `h : i < a.size`). Lean's compiler erases `Prop` proofs at runtime, so there is zero performance cost — but the result is a function that is *structurally* panic-free: no `panic!` call site exists in the compiled code. Thread bound proofs through function parameters where needed (see `compareLoop` for an example).

## Visibility: Always Allowed to Make `private` Public
If you encounter a `private` definition, theorem, or lemma that you need to reference from another file, you are **always allowed** to remove the `private` modifier. Do not ask for permission — just do it.

## Infrastructural Improvements
When working on a proof or feature, if you identify an opportunity to build reusable infrastructure that would benefit the project long-term (e.g., a bridge between Azurite's data types and Mathlib's abstractions, or shared lemma libraries), **take the time to do it**. Well-designed infrastructure pays for itself many times over. Prefer investing in solid foundations over ad-hoc workarounds.

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

## Avoid `#check` and `#eval` in Committed Code
`#check` and `#eval` produce info-level output that pollutes the build log. **Do not leave them in committed files.**

- **For tests/assertions:** Use `#guard` (for decidable equalities) or `example` (for proofs).
  ```lean
  -- ✅ Silent
  #guard rootBound p == 5
  #guard toString poly == "x^2+1"
  example : 0 ≤ |a| := abs_nonneg a

  -- ❌ Noisy
  #eval rootBound p          -- prints to build log
  #check @abs_nonneg         -- prints type to build log
  ```
- **For documenting Mathlib API references:** Put the reference in a `/-! ... -/` doc block instead of a `#check`. The doc block is silent and more readable.
- **During development:** `#check` and `#eval` are fine in scratch work and `lean_run_code` snippets. Just remove them before finalizing.

---
description: How to update Lean and Mathlib for the Azurite project
---

# Updating Lean & Mathlib

## Key Constraint

Azurite's Lean version must match what **Mathlib requires**. You cannot upgrade Lean independently.

## Quick Update (same Lean version, newer Mathlib)

// turbo-all

1. Run `lake update` to fetch the latest Mathlib and all transitive dependencies
2. Run `lake build` to rebuild (expect 30+ min for full Mathlib rebuild)
3. Fix any breaking changes in Azurite code

## Full Lean Version Upgrade

1. Check the latest Lean version Mathlib uses:
   ```
   curl -s https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain
   ```
2. Update `lean-toolchain` in the project root to match
3. Run `lake update` to fetch matching dependency versions
4. Run `lake clean` to remove stale `.olean` files from the old version
5. Run `lake build` to rebuild everything
6. Fix any API breakages (renamed lemmas, changed signatures, etc.)

## Checking Current Versions

| What                | Command |
|---------------------|---------|
| Project Lean version | `cat lean-toolchain` |
| Installed toolchains | `elan show` |
| Current Mathlib commit | `git -C .lake/packages/mathlib log -1 --oneline` |
| Mathlib commit date | `git -C .lake/packages/mathlib log -1 --format="%ci"` |
| Latest Mathlib Lean  | `curl -s https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain` |

## Common API Breakages After Updates

- Renamed lemmas (e.g. `Array.ext_getElem` → `Array.ext`)
- Changed function signatures (new implicit args, different typeclass assumptions)
- Removed `private` → accessible; or vice versa
- `simp` lemma set changes (proofs using `simp` may need adjustments)

## Rollback

If the update breaks things and you need to revert:
```bash
git checkout lean-toolchain lake-manifest.json
lake update
lake build
```

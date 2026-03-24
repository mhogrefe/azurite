---
description: Refresh stale .olean files after changing declaration visibility or signatures
---

# Refresh Stale Oleans

Use this when the LSP reports stale errors (e.g., `Unknown constant` after making a `private` declaration public).

## Steps

1. Delete the stale `.olean` and `.c` files for the affected modules:

```bash
# Example: refresh Equiv/Basic and Rename
for mod in Azurite/AzMvPolynomial/Equiv/Basic Azurite/AzMvPolynomial/Rename; do
  rm -f .lake/build/lib/${mod}.olean .lake/build/ir/${mod}.c
done
```

Adjust the module paths to match what you changed.

// turbo
2. Rebuild:

```bash
lake build
```

3. If the LSP MCP server still shows stale diagnostics after the rebuild, ask the user to restart the MCP server (takes a few seconds).

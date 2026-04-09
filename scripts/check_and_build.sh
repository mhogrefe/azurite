#!/usr/bin/env bash
# check_and_build.sh
#
# Validates that every .lean file under Azurite/ is imported in Azurite.lean,
# that the imports are alphabetically sorted, and then runs lake build.
#
# Usage: ./scripts/check_and_build.sh [--axioms]
#   --axioms  After building, print all axioms used by Azurite declarations (slow)

set -euo pipefail

CHECK_AXIOMS=false
for arg in "$@"; do
  case "$arg" in
    --axioms) CHECK_AXIOMS=true ;;
    *) echo "Unknown option: $arg"; exit 1 ;;
  esac
done

cd "$(dirname "$0")/.."

ROOT_FILE="Azurite.lean"
SRC_DIR="Azurite"

errors=0

# ── 1. Collect expected module names from .lean files ──

expected=$(find "$SRC_DIR" -name '*.lean' -type f \
  | sed "s|^$SRC_DIR/||; s|\.lean$||; s|/|.|g" \
  | sed 's/^/Azurite./' \
  | sort)

# ── 2. Collect actual imports from Azurite.lean ──

actual=$(grep '^import ' "$ROOT_FILE" | sed 's/^import //')

# ── 3. Check for missing imports and stale imports ─���

missing=$(comm -23 <(echo "$expected") <(echo "$actual" | sort))
extra=$(comm -13 <(echo "$expected") <(echo "$actual" | sort))

# ─��� 4. Check for duplicates ──

dupes=$(echo "$actual" | sort | uniq -d)

# ── 5. Auto-fix: add missing, remove stale/dupes, and sort ──

needs_fix=false

if [[ -n "$missing" ]]; then
  echo "Adding missing imports:"
  while IFS= read -r m; do
    echo "  import $m"
  done <<< "$missing"
  needs_fix=true
fi

if [[ -n "$extra" ]]; then
  echo "Removing stale imports (no corresponding file):"
  while IFS= read -r m; do
    echo "  import $m"
  done <<< "$extra"
  needs_fix=true
fi

if [[ -n "$dupes" ]]; then
  echo "Removing duplicate imports:"
  while IFS= read -r m; do
    echo "  import $m"
  done <<< "$dupes"
  needs_fix=true
fi

sorted=$(echo "$actual" | sort)
if [[ "$actual" != "$sorted" ]]; then
  echo "Reordering imports alphabetically."
  needs_fix=true
fi

if [[ "$needs_fix" == true ]]; then
  # Preserve the header comment (lines before the first import)
  header=$(sed '/^import /,$d' "$ROOT_FILE")
  # Generate the correct sorted import list from the filesystem
  imports=$(echo "$expected" | sed 's/^/import /')
  {
    echo "$header"
    echo "$imports"
  } > "$ROOT_FILE"
  echo "Fixed $ROOT_FILE."
else
  echo "All imports valid and sorted."
fi

echo "Running lake build..."
echo ""

# ── 8. Build ──

lake build
build_status=$?

if [[ $build_status -ne 0 ]]; then
  echo ""
  echo "Build failed."
  exit $build_status
fi

# ── 9. Print axioms (opt-in) ──

if [[ "$CHECK_AXIOMS" == true ]]; then
  echo ""
  echo "Checking axioms..."
  echo ""
  lake env lean scripts/print_axioms.lean
else
  echo ""
  echo "Build succeeded. (Run with --axioms to check axioms)"
fi

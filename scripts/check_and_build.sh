#!/usr/bin/env bash
# check_and_build.sh
#
# Validates that every .lean file under Azurite/ is imported in Azurite.lean,
# that the imports are alphabetically sorted, and then runs lake build.
#
# Usage: ./scripts/check_and_build.sh

set -euo pipefail

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

# ── 3. Check that every file is imported ──

missing=$(comm -23 <(echo "$expected") <(echo "$actual" | sort))
if [[ -n "$missing" ]]; then
  echo "ERROR: The following modules are missing from $ROOT_FILE:"
  while IFS= read -r m; do
    echo "  import $m"
  done <<< "$missing"
  errors=1
fi

# ── 4. Check for imports that don't correspond to any file ──

extra=$(comm -13 <(echo "$expected") <(echo "$actual" | sort))
if [[ -n "$extra" ]]; then
  echo "ERROR: The following imports in $ROOT_FILE have no corresponding file:"
  while IFS= read -r m; do
    echo "  import $m"
  done <<< "$extra"
  errors=1
fi

# ── 5. Check alphabetical ordering ──

sorted=$(echo "$actual" | sort)
if [[ "$actual" != "$sorted" ]]; then
  echo "ERROR: Imports in $ROOT_FILE are not sorted alphabetically."
  echo ""
  echo "First out-of-order import:"
  diff <(echo "$actual") <(echo "$sorted") | head -5
  errors=1
fi

# ── 6. Check for duplicates ──

dupes=$(echo "$actual" | sort | uniq -d)
if [[ -n "$dupes" ]]; then
  echo "ERROR: Duplicate imports in $ROOT_FILE:"
  while IFS= read -r m; do
    echo "  import $m"
  done <<< "$dupes"
  errors=1
fi

# ── 7. Bail if there were errors ──

if [[ $errors -ne 0 ]]; then
  echo ""
  echo "Fix the errors above before building."
  exit 1
fi

echo "All imports valid and sorted. Running lake build..."
echo ""

# ── 8. Build ──

exec lake build

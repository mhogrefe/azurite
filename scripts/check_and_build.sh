#!/usr/bin/env bash
# check_and_build.sh
#
# Validates that every .lean file under Azurite/ is imported by the root
# module of the lake target that owns it, then runs lake build.
#
#   * Library files                  -> Azurite.lean        (auto-fixed)
#   * Test files (*/Tests/*)         -> AzuriteTests.lean   (auto-fixed)
#   * Benchmark/ and */Tune.lean     -> Azurite/Benchmark/Main.lean
#                                       (checked only; Main.lean is the
#                                       curated root of the benchmark exe)
#
# Root-file imports are also checked to be alphabetically sorted and
# duplicate-free.
#
# Usage: ./scripts/check_and_build.sh [--axioms]
#   --axioms  After building, verify all Azurite declarations use only
#             allowed axioms (fails on sorryAx or unexpected axioms)

set -euo pipefail

# Pin collation so `sort` produces identical orderings on every machine
# (macOS and Linux locales disagree about case, e.g. `Pow` vs `PRem`).
export LC_ALL=C

CHECK_AXIOMS=false
for arg in "$@"; do
  case "$arg" in
    --axioms) CHECK_AXIOMS=true ;;
    *) echo "Unknown option: $arg"; exit 1 ;;
  esac
done

cd "$(dirname "$0")/.."

SRC_DIR="Azurite"

# ── 1. Partition .lean files by owning target ──

all_modules=$(find "$SRC_DIR" -name '*.lean' -type f \
  | sed "s|^$SRC_DIR/||; s|\.lean$||; s|/|.|g" \
  | sed 's/^/Azurite./' \
  | sort)

lib_expected=$(echo "$all_modules" \
  | grep -v '^Azurite\.Benchmark\.' \
  | grep -v '\.Tests\.' \
  | grep -v '\.Tune$')

tests_expected=$(echo "$all_modules" | grep '\.Tests\.' || true)

bench_expected=$(echo "$all_modules" \
  | grep -e '^Azurite\.Benchmark\.' -e '\.Tune$' \
  | grep -v '^Azurite\.Benchmark\.Main$' || true)

# ── 2. Check (and auto-fix) a root file against an expected module list ──

check_root_file() {
  local root_file="$1" expected="$2"

  local actual missing extra dupes sorted needs_fix
  actual=$(grep '^import ' "$root_file" | sed 's/^import //')
  missing=$(comm -23 <(echo "$expected") <(echo "$actual" | sort))
  extra=$(comm -13 <(echo "$expected") <(echo "$actual" | sort))
  dupes=$(echo "$actual" | sort | uniq -d)
  needs_fix=false

  if [[ -n "$missing" ]]; then
    echo "$root_file: adding missing imports:"
    while IFS= read -r m; do
      echo "  import $m"
    done <<< "$missing"
    needs_fix=true
  fi

  if [[ -n "$extra" ]]; then
    echo "$root_file: removing stale imports (no corresponding file, or file owned by another target):"
    while IFS= read -r m; do
      echo "  import $m"
    done <<< "$extra"
    needs_fix=true
  fi

  if [[ -n "$dupes" ]]; then
    echo "$root_file: removing duplicate imports:"
    while IFS= read -r m; do
      echo "  import $m"
    done <<< "$dupes"
    needs_fix=true
  fi

  sorted=$(echo "$actual" | sort)
  if [[ "$actual" != "$sorted" ]]; then
    echo "$root_file: reordering imports alphabetically."
    needs_fix=true
  fi

  if [[ "$needs_fix" == true ]]; then
    # Preserve the header comment (lines before the first import)
    local header imports
    header=$(sed '/^import /,$d' "$root_file")
    # Generate the correct sorted import list from the filesystem
    imports=$(echo "$expected" | sed 's/^/import /')
    {
      echo "$header"
      echo "$imports"
    } > "$root_file"
    echo "Fixed $root_file."
  else
    echo "$root_file: all imports valid and sorted."
  fi
}

check_root_file "Azurite.lean" "$lib_expected"
check_root_file "AzuriteTests.lean" "$tests_expected"

# ── 3. Check benchmark/tune coverage (no auto-fix: Main.lean is curated) ──

BENCH_MAIN="$SRC_DIR/Benchmark/Main.lean"
# A module is covered if it is imported by Main.lean or by any other
# benchmark/tune file (Main imports those directly, so one level of
# indirection suffices for the transitive closure).
bench_actual=$(cat "$BENCH_MAIN" \
    $(find "$SRC_DIR/Benchmark" -name '*.lean' -type f) \
    $(find "$SRC_DIR" -name 'Tune.lean' -type f) \
  | grep '^import ' | sed 's/^import //' | sort -u)
bench_missing=$(comm -23 <(echo "$bench_expected") <(echo "$bench_actual"))
if [[ -n "$bench_missing" ]]; then
  echo "ERROR: $BENCH_MAIN does not (transitively) import:"
  while IFS= read -r m; do
    echo "  import $m"
  done <<< "$bench_missing"
  echo "Add the missing imports to $BENCH_MAIN by hand (its order is curated)."
  exit 1
fi
echo "$BENCH_MAIN: covers all Benchmark and Tune modules."

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

# ── 9. Compile Asymptote diagrams ──

ASY_DIR="blueprint/src/asymptote"
if [[ -d "$ASY_DIR" ]] && compgen -G "$ASY_DIR/*.asy" >/dev/null; then
  echo ""
  echo "Compiling Asymptote diagrams (in parallel)..."
  # dvisvgm (used by `asy -f svg`) needs libgs to convert LaTeX-typeset
  # axis labels embedded as PostScript specials. Point LIBGS at the
  # Homebrew install if present; otherwise rely on system search.
  if [[ -z "${LIBGS:-}" ]]; then
    for candidate in \
        /opt/homebrew/lib/libgs.dylib \
        /usr/local/lib/libgs.dylib \
        /usr/lib/x86_64-linux-gnu/libgs.so; do
      if [[ -e "$candidate" ]]; then
        export LIBGS="$candidate"
        break
      fi
    done
  fi
  # Determine which .asy files need rebuilding. A diagram is rebuilt
  # if any of:
  #   * either of its outputs (.pdf, .svg) is missing,
  #   * `git status` reports its .asy file as modified or untracked, or
  #   * any shared library file under lib/ is modified or untracked
  #     (every diagram imports from lib/, so all need rebuilding).
  # The bash glob `*.asy` matches only top-level files, so library
  # files in lib/*.asy are never compiled standalone.
  #
  # Launch one background job per .asy (pdf+svg sequentially within
  # each), then wait on all and propagate the worst exit status. PDF
  # for the print build, SVG for the web build — plastex picks SVG
  # when both are present.
  (cd "$ASY_DIR" || exit
   lib_changed=false
   if [[ -d lib ]] && compgen -G "lib/*.asy" >/dev/null; then
     for libfile in lib/*.asy; do
       if [[ -n "$(git status --porcelain -- "$libfile" 2>/dev/null)" ]]; then
         lib_changed=true
         break
       fi
     done
   fi
   to_build=()
   for f in *.asy; do
     [[ -f "$f" ]] || continue
     base="${f%.asy}"
     if [[ ! -f "$base.pdf" ]] || [[ ! -f "$base.svg" ]]; then
       to_build+=("$f")
     elif [[ "$lib_changed" == true ]]; then
       to_build+=("$f")
     elif [[ -n "$(git status --porcelain -- "$f" 2>/dev/null)" ]]; then
       to_build+=("$f")
     fi
   done

   if [[ ${#to_build[@]} -eq 0 ]]; then
     echo "  All diagrams up to date."
     exit 0
   fi

   echo "  Rebuilding ${#to_build[@]} diagram(s):"
   pids=()
   for f in "${to_build[@]}"; do
     echo "  $f -> ${f%.asy}.{pdf,svg}"
     (asy -f pdf "$f" && asy -f svg "$f") &
     pids+=($!)
   done
   status=0
   for pid in "${pids[@]}"; do
     wait "$pid" || status=1
   done
   exit "$status")
fi

# ── 10. Build the blueprint (PDF and web) ──

echo ""
echo "Running leanblueprint pdf..."
leanblueprint pdf

echo ""
echo "Running leanblueprint web..."
leanblueprint web

# ── 11. Check axioms (opt-in) ──

if [[ "$CHECK_AXIOMS" == true ]]; then
  echo ""
  echo "Checking axioms..."
  echo ""
  lake env lean scripts/check_axioms.lean
else
  echo ""
  echo "Build succeeded. (Run with --axioms to check axioms)"
fi

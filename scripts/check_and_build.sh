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
# The Lean build and the blueprint pipeline (Asymptote diagrams, then the
# PDF and web blueprints in parallel) are independent, so they run
# concurrently: blueprint logs are captured to a temp dir and summarized at
# the end, while `lake build` streams live. Lean parallelism is capped at
# `-j 4` (full parallelism can exhaust memory on typical machines).
#
# Usage: ./scripts/check_and_build.sh [--axioms] [--serial]
#   --axioms  After building, verify all Azurite declarations use only
#             allowed axioms (fails on sorryAx or unexpected axioms)
#   --serial  Run the build steps sequentially (pre-parallel behavior),
#             e.g. when debugging blueprint/diagram failures interactively

set -euo pipefail

# Pin collation so `sort` produces identical orderings on every machine
# (macOS and Linux locales disagree about case, e.g. `Pow` vs `PRem`).
export LC_ALL=C

CHECK_AXIOMS=false
SERIAL=false
for arg in "$@"; do
  case "$arg" in
    --axioms) CHECK_AXIOMS=true ;;
    --serial) SERIAL=true ;;
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

# ── 3b. Trailing whitespace (auto-fixed) ──

# Strip trailing whitespace from every tracked text file. CI rejects it
# (`.github/workflows/lean.yml`), so fix it here before it gets committed.
ws_files=$(git grep -lE '[[:space:]]+$' -- \
  '*.lean' '*.md' '*.tex' '*.yml' '*.yaml' '*.sh' '*.toml' '*.rs' '*.html' '*.scss' \
  2>/dev/null || true)
if [[ -n "$ws_files" ]]; then
  echo "Stripping trailing whitespace from:"
  while IFS= read -r f; do
    echo "  $f"
    # BSD and GNU sed differ on `-i`; a temp file works for both.
    sed -E 's/[[:space:]]+$//' "$f" > "$f.ws.tmp" && mv "$f.ws.tmp" "$f"
  done <<< "$ws_files"
else
  echo "No trailing whitespace in tracked text files."
fi

# Cap Lean parallelism unless the caller overrides: full parallelism can
# exhaust memory on typical machines.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

# ── 4. Blueprint pipeline (diagrams, then PDF ∥ web) ──

# ── 4a. Compile Asymptote diagrams ──

build_diagrams() {
  local ASY_DIR="blueprint/src/asymptote"
  [[ -d "$ASY_DIR" ]] && compgen -G "$ASY_DIR/*.asy" >/dev/null || return 0
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
}

# ── 4b. Diagrams, then `leanblueprint pdf` and `leanblueprint web` in
#        parallel (both only read blueprint/src; pdf writes to print/, web
#        to web/, so they do not collide) ──

BP_LOG_DIR=$(mktemp -d /tmp/azurite-blueprint-logs.XXXXXX)

build_blueprint() {
  if ! build_diagrams > "$BP_LOG_DIR/diagrams.log" 2>&1; then
    echo "diagrams" >> "$BP_LOG_DIR/failed"
    return 1
  fi
  leanblueprint pdf > "$BP_LOG_DIR/pdf.log" 2>&1 &
  local pdf_pid=$!
  leanblueprint web > "$BP_LOG_DIR/web.log" 2>&1 &
  local web_pid=$!
  local st=0
  wait "$pdf_pid" || { echo "pdf" >> "$BP_LOG_DIR/failed"; st=1; }
  wait "$web_pid" || { echo "web" >> "$BP_LOG_DIR/failed"; st=1; }
  return "$st"
}

report_blueprint() {
  # $1 = blueprint status
  if [[ "$1" -eq 0 ]]; then
    echo "Blueprint: diagrams ✓  pdf ✓  web ✓  (logs in $BP_LOG_DIR)"
  else
    echo "Blueprint FAILED in: $(tr '\n' ' ' < "$BP_LOG_DIR/failed")"
    for what in $(cat "$BP_LOG_DIR/failed"); do
      echo ""
      echo "── tail of $BP_LOG_DIR/$what.log ──"
      tail -n 40 "$BP_LOG_DIR/$what.log"
    done
  fi
}

# ── 5. Build (Lean live in the foreground; blueprint in the background) ──

overall_status=0

if [[ "$SERIAL" == true ]]; then
  echo "Running lake build..."
  echo ""
  lake build

  echo ""
  build_diagrams

  echo ""
  echo "Running leanblueprint pdf..."
  leanblueprint pdf

  echo ""
  echo "Running leanblueprint web..."
  leanblueprint web

  echo ""
  echo "Checking blueprint \\lean declarations (checkdecls)..."
  lake exe checkdecls blueprint/lean_decls || overall_status=1
else
  build_blueprint &
  bp_pid=$!

  echo "Running lake build (blueprint building in parallel; logs in $BP_LOG_DIR)..."
  echo ""
  lake_status=0
  lake build || lake_status=$?

  if [[ "$lake_status" -ne 0 ]]; then
    echo ""
    echo "Lean build failed; waiting for the blueprint pipeline to finish..."
    overall_status=$lake_status
  fi

  # ── 6. Check axioms (opt-in; needs the Lean build, overlaps the blueprint) ──

  if [[ "$CHECK_AXIOMS" == true && "$lake_status" -eq 0 ]]; then
    echo ""
    echo "Checking axioms (blueprint still building in parallel)..."
    echo ""
    lake env lean scripts/check_axioms.lean || overall_status=1
  fi

  bp_status=0
  wait "$bp_pid" || bp_status=1
  echo ""
  report_blueprint "$bp_status"
  [[ "$bp_status" -ne 0 ]] && overall_status=1

  # ── 6b. Verify every blueprint \lean{} reference resolves (needs both
  #        the fresh lean_decls from the web build and the built oleans) ──
  if [[ "$lake_status" -eq 0 && "$bp_status" -eq 0 ]]; then
    echo ""
    echo "Checking blueprint \\lean declarations (checkdecls)..."
    lake exe checkdecls blueprint/lean_decls || {
      echo "Blueprint references stale declarations (see above)."
      overall_status=1
    }
  fi
fi

# ── 7. Axiom check for --serial mode, and final summary ──

if [[ "$SERIAL" == true && "$CHECK_AXIOMS" == true ]]; then
  echo ""
  echo "Checking axioms..."
  echo ""
  lake env lean scripts/check_axioms.lean || overall_status=1
fi

echo ""
if [[ "$overall_status" -eq 0 ]]; then
  if [[ "$CHECK_AXIOMS" == true ]]; then
    echo "Build succeeded (axioms checked)."
  else
    echo "Build succeeded. (Run with --axioms to check axioms)"
  fi
else
  echo "BUILD FAILED."
fi
exit "$overall_status"

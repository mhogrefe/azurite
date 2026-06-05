import Lake
open Lake DSL

package «azurite» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «Azurite» where
  -- add any library configuration options here

@[default_target]
lean_lib «Examples» where
  -- add any library configuration options here

-- Build the nanosecond timer C shim as a static library.
extern_lib timerLib pkg := do
  let leanInclude := (← getLeanIncludeDir).toString
  let cFile  := pkg.dir / "Azurite" / "Benchmark" / "timer.c"
  let oFile  := pkg.buildDir / "timer.o"
  let aFile  := pkg.buildDir / "lib" / "libtimer.a"
  let srcJob ← inputBinFile cFile
  let oJob   ← buildO oFile srcJob #[s!"-I{leanInclude}"] #["-O2"] "cc"
  buildStaticLib aFile #[oJob]

@[default_target]
lean_exe «benchmark» where
  root := `Azurite.Benchmark.Main

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

-- Mathlib goes last so its transitive dependency pins (e.g. plausible)
-- take precedence over doc-gen4's, keeping `lake exe cache get` valid.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master-2026-06-04"
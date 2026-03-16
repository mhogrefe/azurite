import Lake
open Lake DSL

package «azurite» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

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

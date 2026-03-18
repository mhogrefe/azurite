import Azurite.Benchmark.RatCmp

-- ── Config parsing ──────────────────────────────────────────────────────────

def parseConfig (s : String) : Std.HashMap String String :=
  s.splitOn "," |>.foldl (init := {}) fun m entry =>
    match entry.splitOn ":" with
    | [k, v] => m.insert k.trimAscii.toString v.trimAscii.toString
    | _      => m

-- ── Main ────────────────────────────────────────────────────────────────────

def validBenchmarks : List String := ["rat_cmp"]

def main (args : List String) : IO Unit := do
  -- Usage: benchmark <name> <limit> [config]
  -- config example: "meanBitLength:64"
  match args with
  | name :: limitStr :: rest =>
    let seed : UInt64 := 1337
    let cfg  := parseConfig (rest.headD "")
    match limitStr.toNat? with
    | none =>
      IO.eprintln s!"Error: limit must be a natural number, got '{limitStr}'"
    | some limit =>
      match name with
      | "rat_cmp" => runRatCmp limit cfg seed
      | _ =>
        IO.eprintln s!"Unknown benchmark: '{name}'"
        IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
  | _ =>
    IO.eprintln "Usage: benchmark <name> <limit> [config]"
    IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
    IO.eprintln "Config example:   meanBitLength:64"

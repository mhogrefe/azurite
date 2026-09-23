import Azurite.APRCL.Select
import Azurite.CohenLenstra.Impl_7
import Azurite.Benchmark.Common

open Azurite Azurite.APRCL Azurite.Benchmark

/-!
# APR-CL timing

`benchmark aprcl <limit> "digits:D"` finds the first `limit` primes above `10^D`
(composites are rejected almost instantly by the Lucas–Lehmer stage) and, for each,
times the generator (`generateSel`), the checker (`aprclCheck`), and the checker's
stages separately: the Lucas–Lehmer stage, the per-`q` Jacobi checks (with the
number of `(p, q)` tests), the odd-prime checks and the final trial division.
`"paper:180"` / `"paper:247"` run the 1987 paper's Table-4 examples instead.
Times in milliseconds.
-/

namespace Azurite.Benchmark.Aprcl

def ms (ns : UInt64) : String :=
  let m := ns / 1000000
  let f := (ns / 10000) % 100
  s!"{m}.{if f < 10 then "0" else ""}{f}"

def timeOnce {α : Type} (f : Unit → α) : IO (α × UInt64) := timeNsIter 1 f

/-- Profile one number: generator, checker, and the stages. -/
def profile (n : AzNat) (detail : Bool := false) : IO Unit := do
  if h : 1 < n.toNat then
    haveI : Fact (1 < n.toNat) := ⟨h⟩
    profileAux n detail
  else IO.println "n ≤ 1"
where
 profileAux (n : AzNat) (detail : Bool) [Fact (1 < n.toNat)] : IO Unit := do
  let digits := (toString n.toNat).length
  let (cert, tGen) ← timeOnce fun _ => generateSel n
  let (res, tCheck) ← timeOnce fun _ => aprclCheck n cert
  -- stages
  let (llRes, tLL) ← timeOnce fun _ => llStage n cert.ll
  let F := llF cert.ll
  let (qRes, tQ) ← timeOnce fun _ => qStage n F cert.t' cert.qs
  let nTests := (cert.qs.map fun d => (d.q - 1).primeFactorsList.length).sum
  let llPrimes := cert.ll.minus.map (·.1) ++ cert.ll.plus.map (·.1)
  let hs := match qRes with | .pass hs => hs | _ => []
  let (_, tP) ← timeOnce fun _ =>
    Outcome.all (cert.t'.primeFactorsList.map (pCheck n llPrimes hs cert.aux))
  let s := F * AzNat.ofNat (s2Of cert.qs)
  let (_, tFD) ← timeOnce fun _ => finalDiv n s cert.t' 1
  let llOk := match llRes with | .pass _ => "pass" | .fail => "fail" | .composite => "composite"
  IO.println s!"n≈10^{digits - 1} ({digits} digits): result={repr res}  gen={ms tGen}ms  check={ms tCheck}ms"
  IO.println s!"   LL stage={ms tLL}ms ({llOk}, F has {F.toNat.log2 + 1} bits)  t'={cert.t'}  qs={cert.qs.map (·.q)}  (p,q)-tests={nTests}  jacobi={ms tQ}ms  pChecks={ms tP}ms  finalDiv={ms tFD}ms"
  if detail then
    for d in cert.qs do
      let f := CL.indexTableOf (CL.indexTableArr d.q d.g)
      let (_, tIdx) ← timeOnce fun _ => CL.checkIndexTable d.q d.g f
      for p in (d.q - 1).primeFactorsList do
        let k := padicValNat p (d.q - 1)
        let (_, tTab) ← timeOnce fun _ => AzPolyMod.coeffT (CL.jacobiSumT n p k d.q f 1 1) 0
        let J := CL.jacobiSumT n p k d.q f 1 1
        let (_, tPow) ← timeOnce fun _ => AzPolyMod.coeffT (AzPolyMod.cycPow n p k J (uQuot n (p ^ k))) 0
        let (r, tJ) ← timeOnce fun _ => jTest n p k d.q f
        IO.println s!"      q={d.q} p={p} k={k}: indexTable check={ms tIdx}ms  one table={ms tTab}ms  one u-power={ms tPow}ms  jTest={ms tJ}ms  h={repr r}"

/-- The first `k` primes above `m` (odd candidates, certified by `aprclTestSel`). -/
partial def nextPrimes (m : AzNat) (k : ℕ) (acc : List AzNat := []) : List AzNat :=
  if k = 0 then acc.reverse
  else
    let c := if m.isOdd then m else m + 1
    if aprclTestSel c = some true then nextPrimes (c + AzNat.ofNat 2) (k - 1) (c :: acc)
    else nextPrimes (c + AzNat.ofNat 2) k acc

/-- Primitive costs at the size of `n`: `AzNat` mul, mod, `AzZMod` mul, and the `CycT`
multiplication/squaring at `p^k`. -/
def prims (n : AzNat) (p k : ℕ) : IO Unit := do
  if h : 1 < n.toNat then
    haveI : Fact (1 < n.toNat) := ⟨h⟩
    primsAux n p k
  else pure ()
where
 primsAux (n : AzNat) (p k : ℕ) [Fact (1 < n.toNat)] : IO Unit := do
    let iters := 2000
    let b : AzZMod n := AzZMod.ofAzNat n (n / AzNat.ofNat 7)
    -- distinct operands per iteration, so nothing is shared across the loop
    let as : List (AzZMod n) := (List.range iters).map fun i => AzZMod.ofAzNat n (n / AzNat.ofNat 3 + AzNat.ofNat i)
    let asN : List AzNat := as.map (·.val)
    let prods : List AzNat := asN.map fun x => x * b.val
    let (rMul, tMul) ← timeOnce fun _ => (asN.foldl (fun acc x => acc + x * b.val) 0).size
    let (rMod, tMod) ← timeOnce fun _ => (prods.foldl (fun acc x => acc + x % n) 0).size
    let (rZ, tZ) ← timeOnce fun _ => (as.foldl (fun acc x => acc + x * b) 0).val.size
    let (rS, tS) ← timeOnce fun _ => (as.foldl (fun acc x => acc + x * x) 0).val.size
    let (rA, tA) ← timeOnce fun _ => (as.foldl (fun acc x => acc + (x + b)) 0).val.size
    let per (t : UInt64) := t / iters.toUInt64
    IO.println s!"{n.toNat.log2 + 1}-bit n ({rMul + rMod + rZ + rS + rA - rMul - rMod - rZ - rS - rA}): AzNat mul={per tMul}ns  mod={per tMod}ns  AzZMod mul={per tZ}ns  AzZMod x*x={per tS}ns  add={per tA}ns"
    let f := CL.indexTableOf (CL.indexTableArr 53 2)
    let J : AzPolyMod.CycT n p k := CL.jacobiSumT n p k 53 f 1 1
    let J2 := J * J
    let xs : List (AzPolyMod.CycT n p k) := (List.range 100).map fun i => J2 + (i : AzPolyMod.CycT n p k)
    let (rR, tRaw) ← timeOnce fun _ => (xs.foldl (fun acc x => acc + (x.val * J.val).coeffs.size) 0)
    IO.println s!"   raw AzPolynomial product (no Φ-reduction) ={tRaw / 100 / 1000}µs ({rR - rR})"
    let (rC, tC) ← timeOnce fun _ => (xs.foldl (fun acc x => acc + AzPolyMod.cycMul n p k x J) 0).val.coeffs.size
    IO.println s!"   cycMul (additive Φ-reduction) ={tC / 100 / 1000}µs ({rC - rC})"
    let (rP, tPM) ← timeOnce fun _ => (xs.foldl (fun acc x => acc + x * J) 0).val.coeffs.size
    let (rQ, tPS) ← timeOnce fun _ => (xs.foldl (fun acc x => acc + x * x) 0).val.coeffs.size
    IO.println s!"CycT p^k={p}^{k} (degree {(p - 1) * p ^ (k - 1)}, {rP + rQ - rP - rQ}): mul={tPM / 100 / 1000}µs  x*x={tPS / 100 / 1000}µs"

def run (limit : Nat) (cfg : Std.HashMap String String) : IO Unit := do
  if cfg.contains "prims" then
    prims (AzNat.ofNat CL.prime247_2_892) 13 1
    prims (AzNat.ofNat CL.prime247_2_892) 2 4
    prims (AzNat.ofNat CL.prime180_table2) 13 1
    prims (AzNat.ofNat (10 ^ 100 + 267)) 7 1
    return
  match cfg.get? "paper" with
  | some "180" => profile (AzNat.ofNat CL.prime180_table2) (cfg.contains "detail")
  | some "247" => profile (AzNat.ofNat CL.prime247_2_892) (cfg.contains "detail")
  | _ =>
    let d := configGetNat cfg "digits" 30
    let detail := cfg.contains "detail"
    let start := AzNat.ofNat (10 ^ d) + 1
    let (ps, tSearch) ← timeOnce fun _ => nextPrimes start limit
    IO.println s!"-- {limit} prime(s) above 10^{d} found in {ms tSearch}ms (search includes rejected composites)"
    for p in ps do
      profile p detail

end Azurite.Benchmark.Aprcl

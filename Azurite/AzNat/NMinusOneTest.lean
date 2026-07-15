/-
  **Algorithm 4.1.7 (the `n − 1` test)**, Crandall–Pomerance: given
  `n ≥ 214` and the complete prime factorization of a divisor `F` of
  `n − 1` with `F ≥ n^(3/10)`, decide primality.

  Stage 1 (Pocklington test) tries witnesses `a ∈ [2, n − 2]`: reject
  (composite) if `a^(n−1) ≢ 1 (mod n)`; for each prime `q ∣ F` compute
  `g = gcd(a^((n−1)/q) − 1, n)` — a `g` strictly between `1` and `n` is
  a nontrivial factor (composite), `g = n` retries with a fresh witness,
  and surviving every `q` establishes the Pocklington conditions (4.3).
  Witnesses come from the same PRACTICALLY-RANDOM, PROVABLY-EXHAUSTIVE
  hybrid stream design as equal-degree splitting: SplitMix64-seeded
  values for the first `2^64` indices, then a deterministic sweep.

  Stages 2–4 dispatch on the magnitude of `F`:
  * `F² ≥ n` — prime outright (Pocklington's corollary 4.1.4);
  * `n^(1/3) ≤ F < n^(1/2)` — prime iff the base-`F` discriminant
    `c₁² − 4c₂` is not a square (Brillhart–Lehmer–Selfridge 4.1.5);
  * `n^(3/10) ≤ F < n^(1/3)` — prime iff the six shifted discriminants
    are non-squares and no factor `xF + 1` exists with `3xF³ < n`
    (Konyagin–Pomerance, in the divisor-bound form `theorem_4_1_6'`;
    the scan range has size about `n^(1/10)`.  The book's condition (2)
    — integer roots of a cubic built from a continued-fraction
    convergent — is the sub-linear refinement of this scan, a future
    optimization).

  The output is `Option Bool`: `some true` = proven prime, `some false`
  = proven composite (`nMinusOneTest_eq_some_true/false` in
  `Azurite/AzNat/Equiv/NMinusOneTest.lean`), `none` = invalid input
  (factorization doesn't check out, or `F < n^(3/10)`) or witness
  attempts exhausted.  All arithmetic is limb-level: `AzZMod.powAzNat`
  powering, binary `gcd`, `sqrtRem`-backed `isSquare`.
-/
import Azurite.AzNat.Pratt
import Azurite.AzNat.IsSquare
import Azurite.AzNat.Gcd

namespace Azurite

namespace AzNat

/-- Verdict of one Pocklington witness attempt. -/
inductive Nm1Step where
  /-- A compositeness certificate was found. -/
  | comp
  /-- Some `gcd` came out `n`: retry with a fresh witness. -/
  | retry
  /-- The Pocklington conditions (4.3) hold for this witness. -/
  | pass
  deriving DecidableEq

/-- Classify `g = gcd(x − 1, n)` for one power residue `x`: `g = 1`
passes (for `x = 0` the difference is `−1`, coprime to `n`), `g = n`
forces a retry, and anything else is a nontrivial factor of `n`. -/
def gcdVerdict (n x : AzNat) : Nm1Step :=
  if x == 0 then .pass
  else
    let g := gcd (x - 1) n
    if g == n then .retry
    else if g == 1 then .pass
    else .comp

/-- The gcd conditions of (4.3), one prime factor of `F` at a time. -/
def pocklingtonGcds (n M : AzNat) [NeZero n.toNat] (a : AzZMod n) :
    List AzNat → Nm1Step
  | [] => .pass
  | q :: rest =>
    match gcdVerdict n (a.powAzNat (M / q)).val with
    | .pass => pocklingtonGcds n M a rest
    | .retry => .retry
    | .comp => .comp

/-- One witness attempt of stage 1: the Fermat condition at `n − 1`,
then the gcd conditions. -/
def pocklingtonStep (n M : AzNat) [NeZero n.toNat] (factors : List AzNat)
    (a : AzNat) : Nm1Step :=
  let a' := AzZMod.ofAzNat n a
  if a'.powAzNat M == 1 then pocklingtonGcds n M a' factors
  else .comp

/-- `k` pseudorandom limbs from a SplitMix64 stream. -/
def randomLimbs : ℕ → Random.SplitMix64 → Array UInt64 → Array UInt64
  | 0, _, acc => acc
  | k + 1, g, acc =>
    let (u, g') := (Random.RandomGen.next g : UInt64 × Random.SplitMix64)
    randomLimbs k g' (acc.push u)

/-- **The hybrid witness stream** on `[2, n − 2]` (for `n ≥ 5`):
pseudorandom values for the first `2^64` indices, then a deterministic
sweep — practically random, exhaustive in the tail. -/
def hybridWitness (n : AzNat) (seed : UInt64) (i : ℕ) : AzNat :=
  let m := n - ofNat 3
  let z : AzNat :=
    if i < 2 ^ 64 then
      ofLimbs (randomLimbs n.limbs.size
        (Random.mkSplitMix64 (seed + UInt64.ofNat i)) #[])
    else ofNat (i - 2 ^ 64)
  z % m + ofNat 2

/-- The bounded divisor scan of the Konyagin–Pomerance branch: try
`x, x + 1, …` while `3xF³ < n`, looking for a factor `xF + 1` of `n`.
`F3` is `F³`, precomputed. -/
def kpDivisorScan (n F F3 : AzNat) : AzNat → ℕ → Bool
  | _, 0 => false
  | x, fuel + 1 =>
    if compare (ofNat 3 * (x * F3)) n = .lt then
      if n % (x * F + 1) == 0 then true
      else kpDivisorScan n F F3 (x + 1) fuel
    else false

/-- Stages 2–4 of the `n − 1` test: magnitude dispatch on `F`, assuming
the Pocklington conditions have been established and `n³ ≤ F¹⁰`. -/
def nm1Magnitude (n F : AzNat) : Bool :=
  let F2 := square F
  if compare n F2 ≠ .gt then true            -- `n ≤ F²`: Corollary 4.1.4
  else
    let F3 := F2 * F
    let m := (n - 1) / F
    let c₁ := m % F
    let chi := m / F                          -- `c₂` (stage 3) / `c₄` (stage 4)
    let four_chi := ofNat 4 * chi
    if compare n F3 ≠ .gt then                -- `F² < n ≤ F³`: BLS 4.1.5
      let c1sq := square c₁
      if compare c1sq four_chi = .gt then !isSquare (c1sq - four_chi)
      else !(c1sq == four_chi)                -- zero is a square; negative isn't
    else                                      -- `F³ < n`: KP 4.1.6
      let bad1 := (List.range 6).any (fun t =>
        let s := square (c₁ + ofNat t * F) + ofNat (4 * t)
        if compare s four_chi = .gt then isSquare (s - four_chi)
        else s == four_chi)
      if bad1 then false
      else
        let threeF3 := ofNat 3 * F3
        !(kpDivisorScan n F F3 1 ((n / threeF3).toNat + 1))

/-- The witness loop of stage 1, dispatching to the magnitude stages on
a pass. -/
def nm1Loop (n M F : AzNat) [NeZero n.toNat] (factors : List AzNat)
    (seed : UInt64) : ℕ → ℕ → Option Bool
  | _, 0 => none
  | i, fuel + 1 =>
    match pocklingtonStep n M factors (hybridWitness n seed i) with
    | .comp => some false
    | .pass => some (nm1Magnitude n F)
    | .retry => nm1Loop n M F factors seed (i + 1) fuel

/-- **The `n − 1` test** (Crandall–Pomerance Algorithm 4.1.7): given the
prime factorization `factors` of a divisor `F = ∏ qᵢ^eᵢ` of `n − 1`
with `F ≥ n^(3/10)` and `n ≥ 214`, decide primality of `n`.
`some true` is a primality proof and `some false` a compositeness proof
(`Azurite/AzNat/Equiv/NMinusOneTest.lean`); `none` means invalid input
or witness attempts exhausted. -/
def nMinusOneTest (n : AzNat) (factors : List (AzNat × ℕ))
    (attempts : ℕ) (seed : UInt64) : Option Bool :=
  if h : 214 ≤ n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    if factors.all (fun qe => isPrime qe.1)
        && (n - 1) % certProduct factors == 0
        && compare (pow n 3) (pow (certProduct factors) 10) ≠ .gt then
      nm1Loop n (n - 1) (certProduct factors) (factors.map (·.1)) seed 0
        attempts
    else none
  else none

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

private def nm1 (n : ℕ) (factors : List (ℕ × ℕ)) : Option Bool :=
  nMinusOneTest (ofNat n) (factors.map (fun qe => (ofNat qe.1, qe.2))) 64 0

-- stage 2 (`F ≥ √n`): 10⁹ + 7 with `F = 500000003` (10⁹ + 6 = 2·500000003)
#guard nm1 1000000007 [(500000003, 1)] == some true

-- stage 3 (BLS band): 271 with `F = 10` (270 = 2·3³·5; disc 7² − 4·2 = 41)
#guard nm1 271 [(2, 1), (5, 1)] == some true

-- stage 4 (KP band): 223 with `F = 6` (222 = 2·3·37)
#guard nm1 223 [(2, 1), (3, 1)] == some true

-- composites are rejected (Fermat, for a generic witness)
#guard nm1 341 [(2, 2), (5, 1)] == some false      -- 341 = 11·31, F = 20

-- invalid input: `F` does not divide `n − 1`
#guard nm1 271 [(7, 1)] == none

-- invalid input: `F` below `n^(3/10)`
#guard nm1 1000000007 [(2, 1)] == none

-- invalid input: `n < 214`
#guard nm1 191 [(2, 1), (5, 1)] == none

end Tests

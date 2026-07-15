/-
  Lucas–Pratt primality certificates: the checker and the proven-prime
  generator (raw layer).

  A CERTIFICATE for `p` is a witness `a` and the factorization
  `p − 1 = ∏ qᵢ^eᵢ`; it CHECKS if each `qᵢ` is (recursively or directly)
  certified prime, `a^(p−1) ≡ 1 (mod p)`, and `a^((p−1)/qᵢ) ≢ 1` for each
  `qᵢ` — i.e. `a` has full order `p − 1`, which forces `|F_p^×| = p − 1`,
  i.e. `p` prime (Lucas; Mathlib's `lucas_primality`).  Soundness is
  `checkPrattChain_sound` in `Azurite/AzNat/Equiv/Pratt.lean`: a passing
  check PROVES `Nat.Prime`.

  Certificates form a CHAIN (a topologically sorted list): each link may
  cite earlier links' primes as factors, and small factors can instead be
  verified directly by the trial-division `isPrime`.  This flat encoding
  keeps both the checker's recursion and the soundness induction plain
  list folds.

  THE GENERATOR (`findPrattPrime`) searches Proth-shaped candidates
  `n = k·2^m + 1` with `k` an odd prime — chosen precisely so that
  `n − 1 = 2^m·k` factors BY CONSTRUCTION, sidestepping integer
  factorization entirely — filters with Miller–Rabin, and then searches a
  small witness pool for a full-order `a` (a primitive root; for a genuine
  prime a small one usually exists, and failures just advance `k`).  The
  proof-carrying wrapper `findProvenPrime` (in the `Equiv` file) re-checks
  the returned certificate with a dependent `if` and packages the result
  as `{n : AzNat // Nat.Prime n.toNat}` — a proven prime, generated at
  runtime.

  All arithmetic is limb-level (`AzZMod.powAzNat`, `AzNat` mul/div/pow).
-/
import Azurite.AzNat.MillerRabin
import Azurite.AzNat.IsPrime
import Azurite.AzNat.Pow
import Azurite.AzNat.Pow2

namespace Azurite

namespace AzNat

/-- One certificate link: the prime `p`, the witness `a`, and the
factorization `p − 1 = ∏ qᵢ^eᵢ` as `(qᵢ, eᵢ)` pairs. -/
abbrev PrattLink := AzNat × AzNat × List (AzNat × ℕ)

/-- `∏ qᵢ^eᵢ`. -/
def certProduct : List (AzNat × ℕ) → AzNat
  | [] => 1
  | (q, e) :: rest => q.pow e * certProduct rest

/-- Check one link against a pool of already-certified primes: the factor
list must multiply to `p − 1` with every base either previously certified
or small enough for trial division; the witness must have full order
(Fermat at `p − 1`, and not a root of unity at any `(p − 1)/qᵢ`). -/
def checkPrattLink (certified : List AzNat) (p a : AzNat)
    (factors : List (AzNat × ℕ)) : Bool :=
  if h : 1 < p.toNat then
    haveI : NeZero p.toNat := ⟨by omega⟩
    certProduct factors = p - 1
      && factors.all (fun qe => qe.1 ∈ certified || isPrime qe.1)
      && (let a' := AzZMod.ofAzNat p a
          a'.powAzNat (p - 1) = 1
            && factors.all (fun qe => ¬(a'.powAzNat ((p - 1) / qe.1) = 1)))
  else false

/-- Check a certificate chain: each link may cite the primes of earlier
links. -/
def checkPrattChain (certified : List AzNat) : List PrattLink → Bool
  | [] => true
  | (p, a, factors) :: rest =>
    checkPrattLink certified p a factors
      && checkPrattChain (p :: certified) rest

/-- The witness pool for the generator. -/
def prattWitnesses : List AzNat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23].map ofNat

/-- Try to certify `n = k·2^m + 1` (`k` an odd prime, so
`n − 1 = 2^m · k` by construction): filter with Miller–Rabin, then search
the witness pool.  Returns the passing link. -/
def prattCertify (m : ℕ) (k : ℕ) (seed : UInt64) : Option PrattLink :=
  if !(isPrime (ofNat k)) then none
  else
    let n := ofNat k * pow2 m + 1
    if !(millerRabin n 4 seed) then none
    else
      let factors : List (AzNat × ℕ) := [(ofNat 2, m), (ofNat k, 1)]
      (prattWitnesses.find? (fun a => checkPrattLink [] n a factors)).map
        (fun a => (n, a, factors))

/-- **Search for a certified Proth-shaped prime** `k·2^m + 1`, trying odd
`k = k₀, k₀ + 2, …` for at most `attempts` steps.  Returns the full
single-link certificate; the proof-carrying wrapper is
`findProvenPrime` in `Azurite/AzNat/Equiv/Pratt.lean`. -/
def findPrattPrime (m : ℕ) (seed : UInt64) :
    (attempts k₀ : ℕ) → Option PrattLink
  | 0, _ => none
  | attempts + 1, k =>
    match prattCertify m k seed with
    | some link => some link
    | none => findPrattPrime m seed attempts (k + 2)

end AzNat

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! ### Hand-built certificates, and generated proven primes

`1009 − 1 = 2^4·3^2·7` with primitive root `11`; a chain certifying
`2027` via `1013` (`2026 = 2·1013`, `1012 = 2^2·11·23`); and the
generator at several sizes (the returned `k` and witness are pinned —
deterministic given the seed). -/

section Tests

open Azurite Azurite.AzNat

-- 1009: single link, all factors by trial division
#guard checkPrattChain []
  [(ofNat 1009, ofNat 11, [(ofNat 2, 4), (ofNat 3, 2), (ofNat 7, 1)])]

-- a genuine chain: 1013 first (1012 = 2^2·11·23), then 2027 citing it
#guard checkPrattChain []
  [(ofNat 1013, ofNat 3, [(ofNat 2, 2), (ofNat 11, 1), (ofNat 23, 1)]),
   (ofNat 2027, ofNat 2, [(ofNat 2, 1), (ofNat 1013, 1)])]

-- wrong witness order: 3 has order dividing 1008/… — rejected
#guard !(checkPrattChain []
  [(ofNat 1009, ofNat 3, [(ofNat 2, 4), (ofNat 3, 2), (ofNat 7, 1)])])

-- incomplete factorization of p − 1: rejected
#guard !(checkPrattChain []
  [(ofNat 1009, ofNat 11, [(ofNat 2, 4), (ofNat 3, 2)])])

-- generated Proth-shaped proven primes (deterministic for a fixed seed)
#guard (findPrattPrime 16 0 64 3).isSome
#guard (findPrattPrime 61 0 64 3).isSome

end Tests

/-
  **The (5.5) selection of `t'` and `s₂`, on the generator side** — the `AzNat`
  port of the ℕ-level specification `CL.selection_5_5` (`CohenLenstra/Impl_5_2.lean`).

  Only the guard `s₁·s₂ > √n` (`bigEnoughAz`: `n < (F·s₂)²`) touches the large
  number `n`; everything else is small-number arithmetic on `t'`, the
  `q`-primes and the cost model.  With the (5.2) `s₁ = liftedS1 ll t'` (the Lucas–Lehmer
  part lifted by `t'`), for each even divisor `t'` of `t` Procedure (5.2)
  starts from the `q`-primes of `t'` not dividing `n·F`, checks the guard,
  greedily removes the `q` with the largest `w(q)/log(q^{e_q})` while the
  guard survives, and the `t'` of least cost `t'·c_ftd + Σ w(q)` is kept.
  The exponent `e_q` is the largest `e` with `n^{t'} ≡ 1 (mod q^e)` (the
  paper's `v_q(n^{q−1} − 1) + v_q(t')` when `q ∣ t'`, else `1`), which is what
  the checker verifies.  Nothing here is proven: the certificate produced is
  checked by `aprclCheck`.
-/
import Azurite.APRCL.Test
import Azurite.CohenLenstra.Impl_5_2

namespace Azurite

namespace APRCL

open CL

/-- The exponent `e_q`: the largest `e ≤ 64` with `n^{t'} ≡ 1 (mod q^e)`. -/
def qExp (n : AzNat) (t' q : ℕ) : ℕ :=
  if q ∣ t' then go 1 63 else 1
where
  go (e : ℕ) : ℕ → ℕ
    | 0 => e
    | fuel + 1 => if powModEqOne n t' (q ^ (e + 1)) then go (e + 1) fuel else e

/-- `s₂` from the list `s̄₂` of `q`-primes. -/
def s2OfListAz (n : AzNat) (t' : ℕ) (qs : List ℕ) : ℕ := (qs.map fun q => q ^ qExp n t' q).prod

/-- The guard `F·s₂ > √n`. -/
def bigEnoughAz (n s₁ : AzNat) (s₂ : ℕ) : Bool := decide (n < (s₁ * AzNat.ofNat s₂).square)

/-- The initial `s̄₂`: the `q`-primes of `t'` dividing neither `n` nor `F`. -/
def s2barInitAz (n s₁ : AzNat) (t' : ℕ) : List ℕ :=
  (qPrimesFast t').filter fun q => !(n % AzNat.ofNat q = 0) && !(s₁ % AzNat.ofNat q = 0)

/-- One greedy step of (5.2). -/
def pruneStepAz (c : ℕ → ℕ → ℕ) (n F : AzNat) (t' : ℕ) (qs : List ℕ) : Option ℕ :=
  let s₂ := s2OfListAz n t' qs
  let cands := qs.filter fun q => bigEnoughAz n F (s₂ / q ^ qExp n t' q)
  cands.foldl (fun best q =>
    match best with
    | none => some q
    | some q' =>
      if qCost c q * Nat.log 2 (q' ^ qExp n t' q') > qCost c q' * Nat.log 2 (q ^ qExp n t' q)
      then some q else some q') none

/-- The greedy pruning loop of (5.2). -/
def pruneAz (c : ℕ → ℕ → ℕ) (n F : AzNat) (t' : ℕ) : List ℕ → ℕ → List ℕ
  | qs, 0 => qs
  | qs, fuel + 1 =>
    match pruneStepAz c n F t' qs with
    | none => qs
    | some q => pruneAz c n F t' (qs.erase q) fuel

/-- **Procedure (5.2)** for one even `t'`: the pruned `s̄₂` (empty if `F` alone suffices),
or `none` if `t'` is too small. -/
def procedureAz (c : ℕ → ℕ → ℕ) (n : AzNat) (ll : LLCert) (t' : ℕ) : Option (List ℕ) :=
  let s₁ := liftedS1 ll t'
  if n < s₁.square then some []
  else
    let qs := s2barInitAz n s₁ t'
    if bigEnoughAz n s₁ (s2OfListAz n t' qs) then some (pruneAz c n s₁ t' qs qs.length) else none

/-- **(5.5)**: over the even divisors `t'` of `t`, the `t'` of least total cost. -/
def selectionAz (c : ℕ → ℕ → ℕ) (cftd : ℕ) (n : AzNat) (ll : LLCert) (t : ℕ) : Option (ℕ × List ℕ) :=
  let divs := ((divisorsFast t).filter fun d => 2 ∣ d).mergeSort
  divs.foldl (fun best t' =>
    match procedureAz c n ll t' with
    | none => best
    | some qs =>
      match best with
      | none => some (t', qs)
      | some (t₀, qs₀) =>
        if totalCost c cftd t' qs < totalCost c cftd t₀ qs₀ then some (t', qs) else some (t₀, qs₀))
    none

/-- The certificate for a selected `(t', s̄₂)`. -/
def certOfSelection (n : AzNat) (ll : LLCert) (t' : ℕ) (qs : List ℕ) : Cert :=
  ⟨ll, t', qs.map fun q => ⟨q, qExp n t' q, (findGenerator q).getD 0⟩, generateAux n t'⟩

/-- **The cost model** `c_{p^k}`: a `(p, q)` test is a `u`-th power in a ring of degree
`m = (p−1)p^(k−1)` whose multiplication costs about `m²` coefficient products (the tables
are negligible after `expCounts`), so `c_{p^k} = m²`. -/
def testCost (p k : ℕ) : ℕ := ((p - 1) * p ^ (k - 1)) ^ 2

/-- **The generator with the (5.5) selection**: the Lucas–Lehmer data, then the first `t`
from a list of highly composite candidates (`2, 12, 60, …, 720720 = 2⁴·3²·5·7·11·13,
4324320 = 2⁵·3³·5·7·11·13, 36756720 = ·17, 367567200 = 2⁵·3³·5²·7·11·13·17,
6983776800 = ·19`) for which the selection succeeds, with the cost model `testCost`,
`c_ftd = 1`. -/
def generateSel (n : AzNat) (B : ℕ := 0) : Cert :=
  -- default trial-division bound by size: `10^4` below 256 bits, `10^5` below 512, else `10^6`
  let B := if B ≠ 0 then B else if n.size ≤ 256 then 10000 else if n.size ≤ 512 then 100000
    else 1000000
  let ll := llGenerate n B
  let ts : List ℕ := [2, 12, 60, 120, 720, 5040, 55440, 720720, 4324320, 36756720, 367567200,
    6983776800]
  match ts.findSome? fun t => (selectionAz testCost 1 n ll t).map fun s => (t, s) with
  | some (_, t', qs) => certOfSelection n ll t' qs
  | none => ⟨ll, 2, [], []⟩

/-- **The APR-CL test with the (5.5)-selected certificate.** -/
def aprclTestSel (n : AzNat) (B : ℕ := 0) : Option Bool := aprclCheck n (generateSel n B)

/-! ### Guards -/

#guard (selectionAz (fun p k => p ^ k) 1 (AzNat.ofNat 1000003) (llGenerate (AzNat.ofNat 1000003)) 60).isSome
#guard divisorsFast 12 = [1, 3, 2, 6, 4, 12] ∨ (divisorsFast 12).mergeSort = [1, 2, 3, 4, 6, 12]
#guard qPrimesFast 60 = CL.qPrimes 60
#guard aprclTestSel (AzNat.ofNat 1000003) = some true
#guard aprclTestSel (AzNat.ofNat 1000001) = some false
#guard aprclTestSel (AzNat.parse "1000000000000000003").get! = some true
#guard aprclTestSel (AzNat.parse "1000000000000000009").get! = some true
#guard aprclTestSel (AzNat.parse "170141183460469231731687303715884105727").get! = some true  -- 2^127 − 1

end APRCL

end Azurite

/-
  **The APR-CL primality test** `aprclCheck : AzNat → Cert → Option Bool` —
  Phase C3 of `docs/aprcl_implementation_plan.md`, computable side.

  A certificate is the Lucas–Lehmer certificate (`LLCert`) together with the
  (5.5) selection: the even exponent `t'` and the list of `q`-primes of `s₂`
  with their exponents and primitive roots (`QCert`).  The checker:

  * runs the Lucas–Lehmer stage (`llStage`, giving `F` and the ring parameters);
  * for each `q`: `q` prime, `q − 1 ∣ t'`, `1 ≤ e`, `2 ≤ e → q ∣ t'`, `q ∤ n`
    (else composite), `q ∤ s₁`, `n^t' ≡ 1 (mod q^e)` (computed in `ZMod (q^e)`),
    a certified generator and index table, and the Jacobi test `jTest` for
    every prime `p ∣ q − 1` (the exponents `h` are recorded) — (1.3)(i);
  * for each odd `p ∣ t'`: `p ∤ n` (else composite), `p` non-Wieferich
    (`2^p ≢ 2 (mod p²)`, the (8.6)-condition for `a = b = 1`), and a (6.4) source
    (`sixFourOK`): `p ∣ F` (Lucas–Lehmer side), or `n^(p−1) ≢ 1 (mod p²)`
    (Proposition (7.18)), or some `q` with `p ∣ q − 1` whose exponent `h` has
    `p ∤ h` ((1.3)(i3), Theorem (7.19)), or the additional test (1.3)(k) at an
    auxiliary prime `q'` from the certificate (`auxOK`); with no source, `n` a
    `p`-th power is composite ((1.3)(j));
  * `s = s₁·s₂ > √n` with the (5.2) lift `s₁ = 2^(e₂+v₂(t')−1)·∏ p^(e+v_p(t'))`
    (`liftedS1`), and the final trial division (1.3)(l) over `i ≤ t'`.

  Soundness of both verdicts is `aprclCheck_true`/`aprclCheck_false` in
  `Azurite/APRCL/Equiv/Test.lean`.  The Jacobi tests are complete
  (`Azurite/APRCL/Equiv/Complete.lean`: for prime `n` an `h` always exists), so a
  test finding no `h` reports `composite`.  The flag/`λ`-route (i2a) is not
  implemented, and the auxiliary-prime route (k) reports `none` when its `h` is
  divisible by `p`.
-/
import Azurite.APRCL.LucasLehmer
import Azurite.APRCL.JacobiStage
import Azurite.AzNat.RootInt

namespace Azurite

namespace APRCL

open AzZMod

/-- **A `q`-prime of `s₂`**: `q^e ∥ s₂`, with a primitive root `g` mod `q`. -/
structure QCert where
  q : ℕ
  e : ℕ
  g : ℕ
  deriving Repr

/-- **The APR-CL certificate.**  `aux` holds the auxiliary primes of the additional tests
(1.3)(j)/(k): `(p, q', g')` with `q' ≡ 1 (mod 2p)`, `g'` a primitive root mod `q'`. -/
structure Cert where
  ll : LLCert
  t' : ℕ
  qs : List QCert
  aux : List (ℕ × ℕ × ℕ)
  deriving Repr

/-- **The (5.2) `s₁`**: the Lucas–Lehmer part `F` lifted by `t'`,
`s₁ = 2^(e₂ + v₂(t') − 1) · ∏ p^(e + v_p(t'))` (the paper's `½ ∏_{p ∣ F} p^(v_p(t') + v_p(F))`). -/
def liftedS1 (cert : LLCert) (t' : ℕ) : AzNat :=
  AzNat.ofNat (2 ^ (cert.e2 + padicValNat 2 t' - 1))
    * (cert.minus.map fun pe => AzNat.ofNat (pe.1 ^ (pe.2.1 + padicValNat pe.1 t'))).prod
    * (cert.plus.map fun pe => AzNat.ofNat (pe.1 ^ (pe.2.1 + padicValNat pe.1 t'))).prod

/-- `s₂ = ∏ q^e`. -/
def s2Of (qs : List QCert) : ℕ := (qs.map fun d => d.q ^ d.e).prod

/-- `n^t' ≡ 1 (mod m)`, computed in `ZMod m` from the small residue `n mod m`. -/
def powModEqOne (n : AzNat) (t' m : ℕ) : Bool :=
  decide ((((n % AzNat.ofNat m).toNat : ℕ) : ZMod m) ^ t' = 1)

/-- `n^(p−1) ≢ 1 (mod p²)` — the Proposition (7.18) route to (6.4). -/
def notOneModSq (n : AzNat) (p : ℕ) : Bool :=
  decide ((((n % AzNat.ofNat (p ^ 2)).toNat : ℕ) : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)

/-- `2^p ≢ 2 (mod p²)`: `p` is not a Wieferich prime. -/
def wieferichFree (p : ℕ) : Bool := decide ((2 : ZMod (p ^ 2)) ^ p ≠ 2)

section Checks

variable (n : AzNat) [Fact (1 < n.toNat)]

/-- **The per-`q` check** of (1.3)(i): returns the exponents `(p, h)` for the primes
`p ∣ q − 1`.  A prime `p ∣ q − 1` dividing `n` is a factor (composite unless `n = p`), and a
Jacobi test finding no `h` is composite (`jTest_isSome_of_checks`: for prime `n` an `h` always
exists). -/
def qCheck (F : AzNat) (t' : ℕ) (d : QCert) : Outcome (List (ℕ × ℕ)) :=
  if !(isPrimeNat d.q && decide ((d.q - 1) ∣ t') && decide (1 ≤ d.e)
      && decide (2 ≤ d.e → d.q ∣ t') && powModEqOne n t' (d.q ^ d.e)) then .fail
  else if n % AzNat.ofNat d.q = 0 then (if AzNat.ofNat d.q < n then .composite else .fail)
  else if F % AzNat.ofNat d.q = 0 then .fail
  else if !(CL.checkGenerator d.q d.g) then .fail
  else
    let tbl := CL.indexTableArr d.q d.g
    let f := CL.indexTableOf tbl
    if !(CL.checkIndexTable d.q d.g f) then .fail
    else
      let ps := (d.q - 1).primeFactorsList
      if ps.any (fun p => decide (n % AzNat.ofNat p = 0)) then
        (if ps.any (fun p => decide (n % AzNat.ofNat p = 0) && decide (AzNat.ofNat p < n))
          then .composite else .fail)
      else
        let res := ps.map fun p => (p, jTest n p (padicValNat p (d.q - 1)) d.q f)
        if res.all (fun ph => ph.2.isSome) then .pass (res.map fun ph => (ph.1, ph.2.getD 0))
        else .composite

/-- **The additional test (1.3)(k)** for an odd `p` with the auxiliary prime `q'`: `q'` prime,
`p ∣ q' − 1`, `q' ∤ n`, certified generator and index table, and the `k = 1` odd-`p` test at
`q'` with `p ∤ h`. -/
def auxOK (p q' g' : ℕ) : Bool :=
  isPrimeNat q' && decide (p ∣ q' - 1) && !(n % AzNat.ofNat q' = 0) && CL.checkGenerator q' g'
    && (let tbl := CL.indexTableArr q' g'
        let f := CL.indexTableOf tbl
        CL.checkIndexTable q' g' f
          && match jOdd n p 1 q' f with
            | some h => decide (¬ p ∣ h)
            | none => false)

/-- **The (6.4) source for an odd prime `p ∣ t'`**: Lucas–Lehmer side, Proposition (7.18),
a `q` with `p ∣ q − 1` and `p ∤ h` (Theorem (7.19)), or the additional test (k). -/
def sixFourOK (llPrimes : List ℕ) (hs : List (ℕ × List (ℕ × ℕ))) (aux : List (ℕ × ℕ × ℕ))
    (p : ℕ) : Bool :=
  llPrimes.contains p || notOneModSq n p
    || hs.any (fun qh => decide (p ∣ qh.1 - 1) && qh.2.any fun ph => ph.1 = p && decide (¬ p ∣ ph.2))
    || aux.any fun a => a.1 = p && auxOK n p a.2.1 a.2.2

/-- **The odd-prime checks** for `p ∣ t'`: `p ∤ n` (else composite), non-Wieferich, a
(6.4) source; failing that, `n` a `p`-th power is composite ((1.3)(j)). -/
def pCheck (llPrimes : List ℕ) (hs : List (ℕ × List (ℕ × ℕ))) (aux : List (ℕ × ℕ × ℕ))
    (p : ℕ) : Outcome Unit :=
  if p = 2 then .pass ()
  else if n % AzNat.ofNat p = 0 then (if AzNat.ofNat p < n then .composite else .fail)
  else if wieferichFree p && sixFourOK n llPrimes hs aux p then .pass ()
  else if n.isPow p then .composite else .fail

/-- Collect the per-`q` outcomes. -/
def qStage (F : AzNat) (t' : ℕ) : List QCert → Outcome (List (ℕ × List (ℕ × ℕ)))
  | [] => .pass []
  | d :: ds =>
    match qCheck n F t' d with
    | .fail => .fail
    | .composite => .composite
    | .pass hs =>
      match qStage F t' ds with
      | .fail => .fail
      | .composite => .composite
      | .pass rest => .pass ((d.q, hs) :: rest)

end Checks

/-- **The final trial division (1.3)(l)**: `r ← r·ñ mod s`, at most `fuel` times. -/
def finalDiv (n s : AzNat) : ℕ → AzNat → Option Bool
  | 0, _ => none
  | fuel + 1, r =>
    let r' := (r * (n % s)) % s
    if r' = 1 then some true
    else if r' ≠ 0 ∧ n % r' = 0 ∧ r' < n then some false
    else finalDiv n s fuel r'

/-- **The APR-CL test.** -/
def aprclCheck (n : AzNat) (cert : Cert) : Option Bool :=
  if h : 2 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    haveI : Fact (1 < n.toNat) := ⟨by omega⟩
    if !n.isOdd then some false
    else if !structOK n cert.ll then none
    else
      match llStage n cert.ll with
      | .fail => none
      | .composite => some false
      | .pass _ =>
        let F := liftedS1 cert.ll cert.t'
        if !(decide (2 ∣ cert.t') && decide (0 < cert.t')
            && decide ((cert.qs.map (·.q)).Nodup)) then none
        else
          match qStage n F cert.t' cert.qs with
          | .fail => none
          | .composite => some false
          | .pass hs =>
            let llPrimes := cert.ll.minus.map (·.1) ++ cert.ll.plus.map (·.1)
            match Outcome.all (cert.t'.primeFactorsList.map (pCheck n llPrimes hs cert.aux)) with
            | .fail => none
            | .composite => some false
            | .pass () =>
              let s := F * AzNat.ofNat (s2Of cert.qs)
              if !(n < s.square) then none
              else finalDiv n s cert.t' 1
  else if n.toNat = 2 then some true else some false

/-! ### The generator (search side, unproven) -/

/-- All divisors of `t` from its prime factorization (`Nat.divisors` scans `[1, t]`). -/
def divisorsFast (t : ℕ) : List ℕ :=
  (t.primeFactorsList.dedup.map fun p => (p, padicValNat p t)).foldl
    (fun acc pe => (List.range (pe.2 + 1)).flatMap fun i => acc.map (· * pe.1 ^ i)) [1]

/-- The `q`-primes of `t` (primes `q` with `q − 1 ∣ t`), via `divisorsFast`. -/
def qPrimesFast (t : ℕ) : List ℕ :=
  ((divisorsFast t).filter fun d => isPrimeNat (d + 1)).map (· + 1) |>.mergeSort

/-- The `q`-primes for `t'` not dividing `n·F`, with `e = v_q(t') + 1` and the least
primitive root. -/
def generateQs (n F : AzNat) (t' : ℕ) : List QCert :=
  (qPrimesFast t').filterMap fun q =>
    if n % AzNat.ofNat q = 0 ∨ F % AzNat.ofNat q = 0 then none
    else some ⟨q, padicValNat q t' + 1, (CL.findGenerator q).getD 0⟩

/-- **(1.3)(j)**: an auxiliary prime `q' = 2pm + 1 ≤ 2p·50 + 1` with `q' ∤ n` and
`n^((q'−1)/p) ≢ 1 (mod q')`, with its least primitive root. -/
def findAux (n : AzNat) (p : ℕ) : Option (ℕ × ℕ) :=
  ((List.range 50).map fun m => 2 * p * (m + 1) + 1).findSome? fun q' =>
    if isPrimeNat q' && !(n % AzNat.ofNat q' = 0)
        && decide ((((n % AzNat.ofNat q').toNat : ℕ) : ZMod q') ^ ((q' - 1) / p) ≠ 1)
    then some (q', (CL.findGenerator q').getD 0) else none

/-- The auxiliary primes for the odd primes of `t'`. -/
def generateAux (n : AzNat) (t' : ℕ) : List (ℕ × ℕ × ℕ) :=
  (t'.primeFactorsList.filter (· ≠ 2)).filterMap fun p => (findAux n p).map fun qg => (p, qg)

/-- Search a certificate: the Lucas–Lehmer data, then the first `t'` from a fixed list
of smooth even exponents whose `s = F·s₂` exceeds `√n`. -/
def generate (n : AzNat) (B : ℕ := 10000) : Cert :=
  let ll := llGenerate n B
  let F := llF ll
  let ts : List ℕ := [2, 4, 12, 24, 60, 120, 360, 720, 2520, 5040, 55440, 720720, 4324320,
    24504480, 73513440, 367567200]
  let pick := ts.find? fun t' =>
    let qs := generateQs n F t'
    n < (F * AzNat.ofNat (s2Of qs)).square
  match pick with
  | some t' => ⟨ll, t', generateQs n F t', generateAux n t'⟩
  | none => ⟨ll, 2, [], []⟩

/-- **The APR-CL test with generated certificate.** -/
def aprclTest (n : AzNat) (B : ℕ := 10000) : Option Bool := aprclCheck n (generate n B)

/-! ### Guards -/

#guard aprclTest (AzNat.ofNat 1000003) = some true
#guard aprclTest (AzNat.ofNat 1000033) = some true
#guard aprclTest (AzNat.ofNat 999983) = some true
#guard aprclTest (AzNat.ofNat 1000001) = some false        -- 101 · 9901
#guard aprclTest (AzNat.ofNat 8191) = some true
#guard aprclTest (AzNat.ofNat 561) = some false
#guard aprclTest (AzNat.parse "1000000000000000003").get! = some true  -- 10^18 + 3, prime
#guard aprclTest (AzNat.parse "1000000000000000009").get! = some true  -- 10^18 + 9, prime

end APRCL

end Azurite

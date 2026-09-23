/-
  **The APR-CL primality test** `aprclCheck : AzNat → Cert → Option Bool` —
  Phase C3 of `docs/aprcl_implementation_plan.md`, computable side.

  A certificate is the Lucas–Lehmer certificate (`LLCert`) together with the
  (5.5) selection: the even exponent `t'` and the list of `q`-primes of `s₂`
  with their exponents and primitive roots (`QCert`).  The checker:

  * runs the Lucas–Lehmer stage (`llStage`, giving `F` and the ring parameters);
  * for each `q`: `q` prime, `q − 1 ∣ t'`, `1 ≤ e`, `2 ≤ e → q ∣ t'`, `q ∤ n`
    (else composite), `q ∤ F`, `n^t' ≡ 1 (mod q^e)` (computed in `ZMod (q^e)`),
    a certified generator and index table, and the Jacobi test `jTest` for
    every prime `p ∣ q − 1` (the exponents `h` are recorded) — (1.3)(i);
  * for each odd `p ∣ t'`: `p ∤ n` (else composite), `p` non-Wieferich
    (`2^p ≢ 2 (mod p²)`, the (8.6)-condition for `a = b = 1`), and a (6.4) source
    (`sixFourOK`): `p ∣ F` (Lucas–Lehmer side), or `n^(p−1) ≢ 1 (mod p²)`
    (Proposition (7.18)), or some `q` with `p ∣ q − 1` whose exponent `h` has
    `p ∤ h` ((1.3)(i3), Theorem (7.19));
  * `s = F·s₂ > √n` and the final trial division (1.3)(l) over `i ≤ t'`.

  Soundness of both verdicts is `aprclCheck_true`/`aprclCheck_false` in
  `Azurite/APRCL/Equiv/Test.lean`.  The additional tests (1.3)(j)/(k) with an
  auxiliary `q` and the flag/`λ`-route (i2a) are not implemented (the checker
  reports `none` where they would be needed).
-/
import Azurite.APRCL.LucasLehmer
import Azurite.APRCL.JacobiStage

namespace Azurite

namespace APRCL

open AzZMod

/-- **A `q`-prime of `s₂`**: `q^e ∥ s₂`, with a primitive root `g` mod `q`. -/
structure QCert where
  q : ℕ
  e : ℕ
  g : ℕ
  deriving Repr

/-- **The APR-CL certificate.** -/
structure Cert where
  ll : LLCert
  t' : ℕ
  qs : List QCert
  deriving Repr

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
`p ∣ q − 1`. -/
def qCheck (F : AzNat) (t' : ℕ) (d : QCert) : Outcome (List (ℕ × ℕ)) :=
  if !(isPrimeNat d.q && decide ((d.q - 1) ∣ t') && decide (1 ≤ d.e)
      && decide (2 ≤ d.e → d.q ∣ t') && powModEqOne n t' (d.q ^ d.e)) then .fail
  else if n % AzNat.ofNat d.q = 0 then (if AzNat.ofNat d.q < n then .composite else .fail)
  else if F % AzNat.ofNat d.q = 0 then .fail
  else if !(CL.checkGenerator d.q d.g) then .fail
  else
    let f := CL.indexTable d.q d.g
    if !(CL.checkIndexTable d.q d.g f) then .fail
    else
      let res := (d.q - 1).primeFactorsList.map fun p =>
        (p, jTest n p (padicValNat p (d.q - 1)) d.q f)
      if res.all (fun ph => ph.2.isSome) then .pass (res.map fun ph => (ph.1, ph.2.getD 0))
      else .fail

/-- **The (6.4) source for an odd prime `p ∣ t'`**: Lucas–Lehmer side, Proposition (7.18),
or a `q` with `p ∣ q − 1` and `p ∤ h` (Theorem (7.19)). -/
def sixFourOK (llPrimes : List ℕ) (hs : List (ℕ × List (ℕ × ℕ))) (p : ℕ) : Bool :=
  llPrimes.contains p || notOneModSq n p
    || hs.any fun qh => decide (p ∣ qh.1 - 1) && qh.2.any fun ph => ph.1 = p && decide (¬ p ∣ ph.2)

/-- **The odd-prime checks** for `p ∣ t'`: `p ∤ n` (else composite), non-Wieferich, a
(6.4) source. -/
def pCheck (llPrimes : List ℕ) (hs : List (ℕ × List (ℕ × ℕ))) (p : ℕ) : Outcome Unit :=
  if p = 2 then .pass ()
  else if n % AzNat.ofNat p = 0 then (if AzNat.ofNat p < n then .composite else .fail)
  else if wieferichFree p && sixFourOK n llPrimes hs p then .pass () else .fail

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
        let F := llF cert.ll
        if !(decide (2 ∣ cert.t') && decide (0 < cert.t')
            && decide ((cert.qs.map (·.q)).Nodup)) then none
        else
          match qStage n F cert.t' cert.qs with
          | .fail => none
          | .composite => some false
          | .pass hs =>
            let llPrimes := cert.ll.minus.map (·.1) ++ cert.ll.plus.map (·.1)
            match Outcome.all (cert.t'.primeFactorsList.map (pCheck n llPrimes hs)) with
            | .fail => none
            | .composite => some false
            | .pass () =>
              let s := F * AzNat.ofNat (s2Of cert.qs)
              if !(n < s.square) then none
              else finalDiv n s cert.t' 1
  else if n.toNat = 2 then some true else some false

/-! ### The generator (search side, unproven) -/

/-- The `q`-primes for `t'` not dividing `n·F`, with `e = v_q(t') + 1` and the least
primitive root. -/
def generateQs (n F : AzNat) (t' : ℕ) : List QCert :=
  (CL.qPrimes t').filterMap fun q =>
    if n % AzNat.ofNat q = 0 ∨ F % AzNat.ofNat q = 0 then none
    else some ⟨q, padicValNat q t' + 1, (CL.findGenerator q).getD 0⟩

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
  | some t' => ⟨ll, t', generateQs n F t'⟩
  | none => ⟨ll, 2, []⟩

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

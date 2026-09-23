/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **The Lucas–Lehmer stage of APR-CL as a certified test** — Phase C1/C2 of
  `docs/aprcl_implementation_plan.md`.

  A stage returns an `Outcome`: `fail` (give up — the `none` of the final
  `Option Bool`), `composite` (a proven compositeness verdict), or `pass`
  with data.  The Lucas–Lehmer certificate `LLCert` records the searches of
  (4.4): the (c1) prime `a`/(c2) integer `u`, the exponent `e₂` with
  `2^e₂ ∣ n² − 1`, and for the odd primes `p` of `n ∓ 1` the exponents
  `e` (`p^e ∣ n ∓ 1`) and the Test (4.2) witnesses `x`, resp.\ the (4.10)
  parameters `c` of the norm-one elements of Test (4.3).  The checker
  `llCheck` recomputes everything deterministically:

  * structural checks (odd `n > 2`, distinct listed primes, `p^e ∣ n ∓ 1`,
    `2^e₂ ∣ n² − 1`);
  * the ring parameters (`ringParams`): (c1) `a^((n−1)/2) = −1`, or (c2)
    `((u² + 4)/n) = −1` and `α^(n+1) = −1`;
  * Test (4.2) per `(p, x)` (`test42`) and Test (4.3) per `(p, c)`
    (`test43`), each with the gcd checks of (4.4)(f) done per witness;
  * the milestone bound `n < F²` for `F = 2^e₂ ∏ p^e` (the `s₁` of (5.2) at
    `t' = 2`), and the final trial division (1.3)(l) with `t' = 2`:
    `r = n mod F` — `r = 1` or `r ∤ n` proves primality, `r ∣ n`, `r < n`
    proves compositeness.

  Soundness of both verdicts is `llCheck_true`/`llCheck_false` in
  `Azurite/APRCL/Equiv/LucasLehmer.lean`, via the generalized Theorem (6.3)
  with `s₁ = F`, `s₂ = 1`.  `llGenerate` searches the witnesses (unproven,
  generator side); `llTest n := llCheck n (llGenerate n)`.
-/
import Azurite.AzZMod.Quad
import Azurite.AzNat.JacobiSym
import Azurite.AzNat.Gcd
import Azurite.AzNat.Parity
import Azurite.AzNat.Square
import Azurite.AzNat.ModPow2
import Azurite.AzNat.TrailingZeros
import Azurite.AzZMod.Pow

namespace Azurite

namespace APRCL

open AzZMod

/-- **Stage outcome**: give up, proven composite, or pass with data. -/
inductive Outcome (α : Type) where
  | fail
  | composite
  | pass (a : α)
  deriving DecidableEq

/-- Combine a list of unit outcomes: any `composite` wins, then any `fail`. -/
def Outcome.all (l : List (Outcome Unit)) : Outcome Unit :=
  if l.any (· = .composite) then .composite
  else if l.any (· = .fail) then .fail
  else .pass ()

/-- Computable primality of a small natural number: `minFac p = p`. -/
def isPrimeNat (p : ℕ) : Bool := decide (2 ≤ p) && decide (Nat.minFac p = p)

/-- **The Lucas–Lehmer certificate.** -/
structure LLCert where
  /-- (c1): the prime `a` with `a^((n−1)/2) ≡ −1`; (c2): the `u` with `((u²+4)/n) = −1`. -/
  w : ℕ
  /-- `2^e₂ ∣ n² − 1`. -/
  e2 : ℕ
  /-- Odd primes `p ∣ n − 1`: `(p, e, x)` with `p^e ∣ n − 1` and Test (4.2) witness `x`. -/
  minus : List (ℕ × ℕ × ℕ)
  /-- Odd primes `p ∣ n + 1`: `(p, e, c)` with `p^e ∣ n + 1` and (4.10) parameter `c`. -/
  plus : List (ℕ × ℕ × ℕ)
  deriving Repr

section Checks

variable (n : AzNat) [NeZero n.toNat]

/-- **Test (4.2)** for an odd prime `p ∣ n − 1` with witness `x`. -/
def test42 (p x : ℕ) : Outcome Unit :=
  let X : AzZMod n := AzZMod.ofNat n x
  if X = 0 then .fail
  else if X.powAzNat (n - 1) ≠ 1 then .composite
  else
    let Y := X.powAzNat ((n - 1) / AzNat.ofNat p)
    let g := AzNat.gcd (Y - 1).val n
    if g = 1 then .pass () else if g = n then .fail else .composite

/-- **Test (4.3)** for an odd prime `p ∣ n + 1`, in `A = (ℤ/nℤ)[T]/(T² − uT − a)`,
with the norm-one element `(α + c)/(ᾱ + c)` of Remark (4.10). -/
def test43 (u a : AzZMod n) (p c : ℕ) : Outcome Unit :=
  match (QuadT.normOneCandidate (AzZMod.ofNat n c) : Option (NormOne n u a)) with
  | none => .composite
  | some x =>
    if (NormOne.powAzNat x (n + 1)).1 ≠ 1 then .composite
    else
      let d := (NormOne.powAzNat x ((n + 1) / AzNat.ofNat p)).1 - 1
      if d.x₀ = 0 ∧ d.x₁ = 0 then .fail
      else
        let cc := if d.x₀ ≠ 0 then d.x₀ else d.x₁
        if AzNat.gcd cc.val n = 1 then .pass () else .composite

/-- **(4.4)(c)**: the parameters `(u, a)` of the ring `A`.  (c1) for
`n ≡ 1 (mod 4)`: `u = 0`, `a = w` with `a^((n−1)/2) = −1`; (c2) for
`n ≡ 3 (mod 4)`: `u = w` with `((u² + 4)/n) = −1` and `α^(n+1) = −1`, `a = 1`. -/
def ringParams (w : ℕ) : Outcome (AzZMod n × AzZMod n) :=
  if n.modPow2 2 = AzNat.ofNat 1 then
    let A : AzZMod n := AzZMod.ofNat n w
    if A = 0 then .fail
    else
      let e := A.powAzNat ((n - 1) / AzNat.ofNat 2)
      if e = -1 then .pass (0, A) else if e = 1 then .fail else .composite
  else
    if AzNat.jacobi (AzNat.ofNat (w * w + 4)) n ≠ -1 then .fail
    else
      let U : AzZMod n := AzZMod.ofNat n w
      if (QuadT.alpha : QuadT n U 1).powAzNat (n + 1) ≠ QuadT.const (-1) then .composite
      else .pass (U, 1)

/-- The factored part `F = 2^e₂ · ∏ p^e` (the `s₁` of (5.2) at `t' = 2`). -/
def llF (cert : LLCert) : AzNat :=
  AzNat.ofNat (2 ^ cert.e2)
    * (cert.minus.map fun pe => AzNat.ofNat (pe.1 ^ pe.2.1)).prod
    * (cert.plus.map fun pe => AzNat.ofNat (pe.1 ^ pe.2.1)).prod

/-- The structural checks on a certificate. -/
def structOK (cert : LLCert) : Bool :=
  decide ((cert.minus.map (·.1) ++ cert.plus.map (·.1)).Nodup)
    && cert.minus.all (fun pe => isPrimeNat pe.1 && decide (pe.1 ≠ 2) && decide (1 ≤ pe.2.1)
        && decide ((n - 1) % AzNat.ofNat (pe.1 ^ pe.2.1) = 0))
    && cert.plus.all (fun pe => isPrimeNat pe.1 && decide (pe.1 ≠ 2) && decide (1 ≤ pe.2.1)
        && decide ((n + 1) % AzNat.ofNat (pe.1 ^ pe.2.1) = 0))
    && decide (1 ≤ cert.e2) && decide ((n.square - 1).modPow2 cert.e2 = 0)

/-- **The Lucas–Lehmer stage checks** (everything but the size bound): the
ring parameters and all Tests (4.2)/(4.3). -/
def llStage (cert : LLCert) : Outcome (AzZMod n × AzZMod n) :=
  match ringParams n cert.w with
  | .fail => .fail
  | .composite => .composite
  | .pass ua =>
    match Outcome.all ((cert.minus.map fun pe => test42 n pe.1 pe.2.2)
        ++ (cert.plus.map fun pe => test43 n ua.1 ua.2 pe.1 pe.2.2)) with
    | .fail => .fail
    | .composite => .composite
    | .pass () => .pass ua

end Checks

/-- **The Lucas–Lehmer primality test** for odd `n > 2` (the C2 milestone):
`some true` = proven prime, `some false` = proven composite, `none` = gave up. -/
def llCheck (n : AzNat) (cert : LLCert) : Option Bool :=
  if h : 2 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    if !n.isOdd then some false
    else if !structOK n cert then none
    else
      match llStage n cert with
      | .fail => none
      | .composite => some false
      | .pass _ =>
        let F := llF cert
        if !(n < F.square) then none
        else
          let r := n % F
          if r = 1 then some true
          else if r = 0 then none
          else if n % r = 0 ∧ r < n then some false
          else some true
  else if n.toNat = 2 then some true else some false

/-! ### The generator (search side, unproven) -/

/-- The odd primes `≤ B` dividing `m`, with exponents. -/
def factorOddSmall (m : AzNat) (B : ℕ) : List (ℕ × ℕ) := Id.run do
  let mut cur := m
  let mut out : List (ℕ × ℕ) := []
  for d in [3:B+1:2] do
    if isPrimeNat d then
      let dz := AzNat.ofNat d
      if cur % dz = 0 then
        let mut e := 0
        while cur % dz = 0 do
          cur := cur / dz
          e := e + 1
        out := out ++ [(d, e)]
  return out

/-- Search the certificate data: trial division to `B`, witnesses among the
first primes / small `c` (the first non-`fail` outcome is kept, so a
compositeness verdict found on the way is passed on to the checker). -/
def llGenerate (n : AzNat) (B : ℕ := 10000) : LLCert :=
  if h : 2 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    let small : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    let w : ℕ :=
      if n.modPow2 2 = AzNat.ofNat 1 then
        (small.find? fun a => ringParams n a ≠ .fail).getD 0
      else
        ((List.range 50).map (· + 1) |>.find? fun u => ringParams n u ≠ .fail).getD 0
    let e2 : ℕ := ((n.square - 1).trailingZeros).getD 1
    let minusF := factorOddSmall (n - 1) B
    let plusF := factorOddSmall (n + 1) B
    let minus := minusF.map fun pe =>
      (pe.1, pe.2, (small.find? fun x => test42 n pe.1 x ≠ .fail).getD 2)
    match ringParams n w with
    | .pass ua =>
      let plus := plusF.map fun pe =>
        (pe.1, pe.2, ((List.range 50).map (· + 1) |>.find? fun c =>
          test43 n ua.1 ua.2 pe.1 c ≠ .fail).getD 1)
      ⟨w, e2, minus, plus⟩
    | _ => ⟨w, e2, minus, plusF.map fun pe => (pe.1, pe.2, 1)⟩
  else ⟨0, 1, [], []⟩

/-- **The Lucas–Lehmer test with generated certificate.** -/
def llTest (n : AzNat) (B : ℕ := 10000) : Option Bool := llCheck n (llGenerate n B)

/-! ### Guards -/

-- Fermat primes (`n ≡ 1 (mod 4)`, the (c1) route; `n − 1` a power of two)
#guard llTest (AzNat.ofNat 257) = some true
#guard llTest (AzNat.ofNat 65537) = some true
-- Mersenne primes (`n ≡ 3 (mod 4)`, the (c2) route; `n + 1` a power of two)
#guard llTest (AzNat.ofNat 8191) = some true
#guard llTest (AzNat.ofNat 131071) = some true
#guard llTest (AzNat.parse "2305843009213693951").get! = some true          -- 2^61 − 1
#guard llTest (AzNat.parse "170141183460469231731687303715884105727").get! = some true  -- 2^127 − 1
-- primes needing both sides
#guard llTest (AzNat.ofNat 1000003) = some true
-- composites: Mersenne composite `2^11 − 1 = 23·89`, `341 = 11·31`, `561`, an even number
#guard llTest (AzNat.ofNat 2047) = some false
#guard llTest (AzNat.ofNat 341) = some false
#guard llTest (AzNat.ofNat 561) = some false
#guard llTest (AzNat.ofNat 1000) = some false
-- small cases
#guard llTest (AzNat.ofNat 2) = some true
#guard llTest (AzNat.ofNat 1) = some false
#guard llTest (AzNat.ofNat 3) = some true
#guard llTest (AzNat.ofNat 7) = some true
#guard llTest (AzNat.ofNat 9) = some false

end APRCL

end Azurite

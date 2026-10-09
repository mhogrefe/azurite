/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Instances
import Azurite.AzZMod.Pow
import Azurite.AzNat.JacobiSym
import Azurite.AzNat.ModPow2
import Azurite.AzNat.ParseBase
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare

/-!
## Square roots modulo a prime

`sqrt? a` returns a square root of `a` in `ℤ / p` for prime `p`, or `none` when `a` is a
non-residue.  Three cases, chosen by the residue of `p` modulo 8 (read off the low bits of `p`):

* `p ≡ 3 (mod 4)`: `a^((p+1)/4)` — one exponentiation.
* `p ≡ 5 (mod 8)` (Atkin's method): with `v = (2a)^((p−5)/8)` and `i = 2 a v²` (so `i² = −1`),
  the root is `a v (i − 1)` — one exponentiation and four multiplications.
* `p ≡ 1 (mod 8)`: the Tonelli–Shanks algorithm.  Write `p − 1 = 2^s q` with `q` odd and take a
  quadratic non-residue `z`, found by trying `2, 3, …` with the Jacobi symbol (`AzNat.jacobi`).
  Start from `c = z^q`, `t = a^q`, `R = a^((q+1)/2)`, `M = s`; the invariants are `R² = a t`,
  `t^(2^(M−1)) = 1` and `c^(2^(M−1)) = −1`.  While `t ≠ 1`, let `i` be the least exponent with
  `t^(2^i) = 1` (found by repeated squaring, `0 < i < M`) and `b = c^(2^(M−i−1))`; replace
  `(M, c, t, R)` by `(i, b², t b², R b)`.  When `t = 1`, `R` is the root.  Each round lowers `M`,
  so `s` rounds suffice.

Among the two roots the one with the smaller residue is returned.  The candidate is always
verified by one squaring, so `sqrt?_some` (`sqrt? a = some r → r * r = a`) holds for every
modulus; completeness (`sqrt?_isSome_iff`: a root is found exactly when `a` is a square) holds
for prime moduli.  The algorithms are the textbook ones (Tonelli 1891, Shanks 1972, Atkin 1992);
no library code was consulted.  Cipolla's algorithm is asymptotically better when the 2-adic
valuation `s` of `p − 1` is large (the crossover is about `s (s − 1) > 8 log₂ p + 20`), and the
quadratic ring `AzZMod.QuadT` would support it; it is not implemented.

For a composite modulus a square root requires the factorization of the modulus (roots modulo
each prime power, lifted and combined by the Chinese remainder theorem); that is out of scope
here, and `sqrt?` may then return `none` for a square.

### References

The algorithms were implemented from the following descriptions (no library source code was
consulted):

* A. Tonelli, *Bemerkung über die Auflösung quadratischer Congruenzen*, Nachrichten von der
  Königl. Gesellschaft der Wissenschaften zu Göttingen (1891), 344–346.
* D. Shanks, *Five number-theoretic algorithms*, Proceedings of the Second Manitoba Conference
  on Numerical Mathematics (1972), 51–70 (the RESSOL algorithm).
* A. O. L. Atkin, *Probabilistic primality testing*, summary by F. Morain in P. Flajolet and
  P. Zimmermann (eds.), *Algorithms Seminar 1991–1992*, INRIA Research Report 1779 (1992),
  159–163 — the `p ≡ 5 (mod 8)` method, as cited and generalized in A. S. Rotaru and S. Iftene,
  *A complete generalization of Atkin's square root algorithm*, Fundamenta Informaticae 125
  (2013), 71–94, <https://journals.sagepub.com/doi/10.3233/FI-2013-853>.
* *Tonelli–Shanks algorithm*, Wikipedia,
  <https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm> — the loop in the form used
  here, its invariants, and the multiplication count
  `2m + 2k + S(S−1)/4 + 1/2^(S−1) − 9` (`m` bits, `k` one bits of `p`).
* *Cipolla's algorithm*, Wikipedia, <https://en.wikipedia.org/wiki/Cipolla%27s_algorithm> — the
  cost `4m + 2k − 4` multiplications in `F_{p²}` and the crossover `S(S−1) > 8m + 20`.
* D. J. Bernstein, *Faster square roots in annoying finite fields* (2001),
  <https://cr.yp.to/papers/sqroot-20011123-retypeset20220327.pdf> — the table-driven variant
  for large `S`, not implemented.
* P. Sarkar, *Computing square roots faster than the Tonelli–Shanks/Bernstein algorithm*,
  Advances in Mathematics of Communications (2024), IACR ePrint 2020/1407,
  <https://eprint.iacr.org/2020/1407.pdf>; N. Koo, G. H. Cho and S. Kwon, *Square root algorithm
  in F_q for q ≡ 2^s + 1 (mod 2^(s+1))*, IACR ePrint 2013/087,
  <https://eprint.iacr.org/2013/087.pdf>; J. Doliskani and É. Schost, *Taking roots over high
  extensions of finite fields*, Mathematics of Computation 83 (2014),
  <https://arxiv.org/abs/1110.4350> — the complexity comparison
  `O(S · log³ q)` (Tonelli–Shanks) against `O(log³ q)` (Cipolla–Lehmer) that informed the
  choice to keep Tonelli–Shanks with the two special cases.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- `c^(2^k)` by `k` squarings. -/
def squarePow2 [NeZero m.toNat] (c : AzZMod m) : Nat → AzZMod m
  | 0 => c
  | k + 1 => squarePow2 (Azurite.Square.square c) k

/-- The least `i` with `1 ≤ i ≤ fuel` and `t^(2^i) = 1`, by repeated squaring; `none` if there
is none. -/
def squareUntilOne [NeZero m.toNat] : Nat → AzZMod m → Option Nat
  | 0, _ => none
  | fuel + 1, t =>
    let t' := Azurite.Square.square t
    if t' = 1 then some 1 else (squareUntilOne fuel t').map (· + 1)

/-- The Tonelli–Shanks loop on the state `(M, c, t, R)`; see the module docstring. -/
def tonelliShanksLoop [NeZero m.toNat] :
    Nat → Nat → AzZMod m → AzZMod m → AzZMod m → Option (AzZMod m)
  | 0, _, _, _, _ => none
  | fuel + 1, M, c, t, R =>
    if t = 1 then some R
    else
      match squareUntilOne (M - 1) t with
      | none => none
      | some i =>
        let b := squarePow2 c (M - i - 1)
        let b2 := Azurite.Square.square b
        tonelliShanksLoop fuel i b2 (t * b2) (R * b)

/-- The least quadratic non-residue `z ≥ z₀` modulo `p`, by the Jacobi symbol; `none` when the
candidates reach `p`.  For an odd prime `p` the search from `2` always succeeds. -/
def findNonResidue (p z : AzNat) : Option AzNat :=
  if h : z < p then
    if AzNat.jacobi z p = -1 then some z else findNonResidue p (z + 1)
  else none
termination_by p.toNat - z.toNat
decreasing_by
  rw [AzNat.lt_iff_toNat_lt] at h
  rw [AzNat.toNat_add, show (1 : AzNat).toNat = 1 from rfl]
  omega

/-- **Tonelli–Shanks**: a square root of `a` modulo the prime `m`, unverified. -/
def tonelliShanks [NeZero m.toNat] (a : AzZMod m) : Option (AzZMod m) :=
  let pm1 := m - 1
  match pm1.trailingZeros with
  | none => none
  | some s =>
    let q := pm1 >>> s
    match findNonResidue m (AzNat.ofNat 2) with
    | none => none
    | some z =>
      let c := (ofAzNat m z).powAzNat q
      let t := a.powAzNat q
      let R := a.powAzNat ((q + 1) >>> 1)
      tonelliShanksLoop (s + 1) s c t R

/-- **Atkin's method** for `m ≡ 5 (mod 8)`: `v = (2a)^((m−5)/8)`, `i = 2 a v²`, root
`a v (i − 1)`; unverified. -/
def atkin [NeZero m.toNat] (a : AzZMod m) : AzZMod m :=
  let a2 := a + a
  let v := a2.powAzNat ((m - AzNat.ofNat 5) >>> 3)
  let i := a2 * Azurite.Square.square v
  a * v * (i - 1)

/-- The unverified candidate root, by the residue of `m` modulo `8`.  An even modulus is treated
as `2`, where every residue is its own root. -/
def sqrtCandidate [NeZero m.toNat] (a : AzZMod m) : Option (AzZMod m) :=
  if m.isEven then some a
  else if m.modPow2 2 = AzNat.ofNat 3 then some (a.powAzNat ((m + 1) >>> 2))
  else if m.modPow2 3 = AzNat.ofNat 5 then some (atkin a)
  else tonelliShanks a

/-- The root with the smaller residue among `r` and `−r`. -/
def canonicalRoot [NeZero m.toNat] (r : AzZMod m) : AzZMod m :=
  if r.val ≤ (-r).val then r else -r

/-- **Square root modulo a prime.**  `some r` with `r * r = a` and `r ≤ −r` (as residues), or
`none`.  Verified by one squaring, so the `some` case is correct for every modulus; for a prime
modulus a root is found whenever one exists. -/
def sqrt? [NeZero m.toNat] (a : AzZMod m) : Option (AzZMod m) :=
  if a = 0 then some 0
  else
    (sqrtCandidate a).bind fun r =>
      if Azurite.Square.square r = a then some (canonicalRoot r) else none

end Azurite.AzZMod

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZMod

private def N (s : String) : AzNat := (AzNat.parse s).get!

/-- `sqrt?` of `a` modulo `p`, as a decimal string (`"none"` for a non-residue). -/
private def S (p a : String) : String :=
  let m := N p
  if h : m.limbs.size = 0 then "zero modulus" else
    haveI : NeZero m.toNat := ⟨fun h0 => h ((AzNat.toNat_eq_zero_iff m).mp h0)⟩
    match sqrt? (ofAzNat m (N a)) with
    | none => "none"
    | some r => toString r.val

/-- A found root squares back to the input. -/
private def squaresBack (p a : String) : Bool :=
  let m := N p
  if h : m.limbs.size = 0 then false else
    haveI : NeZero m.toNat := ⟨fun h0 => h ((AzNat.toNat_eq_zero_iff m).mp h0)⟩
    match sqrt? (ofAzNat m (N a)) with
    | none => true
    | some r => Square.square r = ofAzNat m (N a)

-- `p = 2`
#guard S "2" "0" == "0"
#guard S "2" "1" == "1"
-- `p ≡ 3 (mod 4)`: `7`, `11`, `19`
#guard S "7" "2" == "3"              -- 3² = 9 ≡ 2; roots 3, 4
#guard S "7" "3" == "none"
#guard S "7" "0" == "0"
#guard S "11" "5" == "4"             -- 4² = 16 ≡ 5; roots 4, 7
#guard S "19" "11" == "7"            -- 7² = 49 ≡ 11; roots 7, 12
-- `p ≡ 5 (mod 8)`: `5`, `13`, `29`
#guard S "5" "4" == "2"
#guard S "5" "2" == "none"
#guard S "13" "10" == "6"            -- 6² = 36 ≡ 10; roots 6, 7
#guard S "13" "12" == "5"            -- 5² = 25 ≡ 12; roots 5, 8
#guard S "29" "5" == "11"            -- 11² = 121 ≡ 5; roots 11, 18
#guard S "29" "2" == "none"
-- `p ≡ 1 (mod 8)` (Tonelli–Shanks): `17`, `41`, `97`, `257`
#guard S "17" "2" == "6"             -- 6² = 36 ≡ 2; roots 6, 11
#guard S "17" "3" == "none"
#guard S "41" "5" == "13"            -- 13² = 169 ≡ 5; roots 13, 28
#guard S "97" "2" == "14"            -- 14² = 196 ≡ 2; roots 14, 83
#guard S "97" "5" == "none"
#guard S "257" "2" == "60"           -- 60² = 3600 ≡ 2; roots 60, 197
#guard S "257" "3" == "none"
-- `p = 2^255 − 19 ≡ 5 (mod 8)`: `sqrt(−1) = 2^((p−1)/4)`
#guard S "57896044618658097711785492504343953926634992332820282019728792003956564819949"
  "57896044618658097711785492504343953926634992332820282019728792003956564819948" ==
  "19681161376707505956807079304988542015446066515923890162744021073123829784752"
-- `p = 2^127 − 1 ≡ 3 (mod 4)`
#guard S "170141183460469231731687303715884105727" "4" == "2"
#guard S "170141183460469231731687303715884105727" "2" == "18446744073709551616"  -- 2^64
-- `p = 2^64 − 2^32 + 1 ≡ 1 (mod 8)` with `2^32 ∣ p − 1` (deep Tonelli–Shanks loop)
#guard S "18446744069414584321" "4" == "2"
#guard S "18446744069414584321" "9" == "3"
#guard S "18446744069414584321" "7" == "none"
-- the result squares back to the input, on a batch
#guard [("18446744069414584321", "1234567890123"), ("18446744069414584321", "3"),
    ("170141183460469231731687303715884105727", "123456789"),
    ("57896044618658097711785492504343953926634992332820282019728792003956564819949", "17"),
    ("97", "33"), ("41", "40"), ("13", "4")].all fun (p, a) => squaresBack p a

end Tests

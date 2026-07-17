/-
  **Optimistic irreducibility test over `Z_m[x]`** — step 1 of the
  finite field primality test (C&P Algorithm 4.3.4, using the
  distinct-degree / Ben-Or criterion of C&P Algorithm 2.2.9).

  Given monic `f` over `AzZMod m` for `m` of UNKNOWN primality, run
  the sweep `gcd(x^(m^i) − x, f) = 1` for `i = 1, …, ⌊deg f / 2⌋`.
  All ring arithmetic is inversion-free: the modular powers
  `x^(m^i) mod f` are `powModByMonic` (sliding-window powering in
  `AzPolyMod f`, limb-level exponent, monic reduction), and every gcd
  runs through `gcdOrFactor` (Algorithm 4.3.2), whose only possible
  failure — a non-invertible leading coefficient — EXHIBITS a
  nontrivial factor of `m`.

  Verdicts (`irreducibleOrFactor m f : AzNat ⊕ Bool`):
  * `.inl d`   — `d` is a nontrivial factor of `m` (unconditionally
                 sound: `irreducibleOrFactor_factor`);
  * `.inr true`  — `f` is irreducible IF `m` is prime
                 (`irreducibleOrFactor_eq_inr_true_iff`, an iff);
  * `.inr false` — `f` is reducible if `m` is prime.
  For prime `m` the `.inl` verdict never fires
  (`irreducibleOrFactor_ne_inl_of_prime`).  All correctness proofs
  live in `Azurite/AzPolynomial/Equiv/IrreducibleOrFactor.lean`.
-/
import Azurite.AzPolynomial.DistinctDegreeFactorization
import Azurite.AzPolynomial.GcdOrFactor

namespace Azurite.AzPolynomial

/-- The sweep: on entry `h` represents `x^(m^i) mod f` for the current
index `i`; check `gcd(h − x, f)` and advance `h` by an `m`-th modular
power.  `steps` counts the remaining indices. -/
def benOrLoop (m : AzNat) [NeZero m.toNat] (f : AzPolynomial (AzZMod m)) :
    ℕ → AzPolynomial (AzZMod m) → AzNat ⊕ Bool
  | 0, _ => .inr true
  | steps + 1, h =>
    match gcdOrFactor m (h - X) f with
    | .inl d => .inl d
    | .inr w =>
      if w = 1 then benOrLoop m f steps (powModByMonic h m f)
      else .inr false

/-- **The optimistic irreducibility test** (Ben-Or sweep over `Z_m[x]`
with `gcdOrFactor` gcds): for monic `f`, either a nontrivial factor of
`m`, or an irreducibility verdict that is correct when `m` is
prime. -/
def irreducibleOrFactor (m : AzNat) [NeZero m.toNat]
    (f : AzPolynomial (AzZMod m)) : AzNat ⊕ Bool :=
  if f.natDegree = 0 then .inr false
  else benOrLoop m f (f.natDegree / 2) (powModByMonic X m f)

end Azurite.AzPolynomial

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolynomial

private instance : Fact (1 < (AzNat.ofNat 5).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩

private instance : Fact (1 < (AzNat.ofNat 7).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩

private def s5 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 5)) :=
  (parseAzPolynomial s).get!

private def s7 (s : String) : AzPolynomial (AzZMod (AzNat.ofNat 7)) :=
  (parseAzPolynomial s).get!

-- `x² + 1` is irreducible mod 7 (−1 is not a square) …
#guard irreducibleOrFactor (AzNat.ofNat 7) (s7 "x^2+1") == .inr true
-- … but splits mod 5: `x² + 1 = (x + 2)(x + 3)`
#guard irreducibleOrFactor (AzNat.ofNat 5) (s5 "x^2+1") == .inr false
-- `x² + x + 1`: the discriminant `−3 ≡ 2` is not a square mod 5
#guard irreducibleOrFactor (AzNat.ofNat 5) (s5 "x^2+x+1") == .inr true
-- a cubic with no roots mod 5 — one sweep index (`⌊3/2⌋ = 1`) suffices
#guard irreducibleOrFactor (AzNat.ofNat 5) (s5 "x^3+x+1") == .inr true
-- a quartic with only quadratic factors: caught at `i = 2`, not `i = 1`
--   `(x² + 1)(x² + x + 2)` has no roots mod 7
#guard irreducibleOrFactor (AzNat.ofNat 7)
  (s7 "x^2+1" * s7 "x^2+x+2") == .inr false
-- linear polynomials are irreducible (empty sweep)
#guard irreducibleOrFactor (AzNat.ofNat 7) (s7 "x+3") == .inr true
-- monic constants are units, not irreducible
#guard irreducibleOrFactor (AzNat.ofNat 7) (s7 "1") == .inr false

end Tests

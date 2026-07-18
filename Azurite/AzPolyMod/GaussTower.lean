/-
  **The computable Gauss-sum tower** — the limb-level rail of
  Algorithm 4.4.5's symbolic arithmetic: the ring
  `(ℤ/n)[x]/(Φ_p)[y]/(Φ_q)` as an `AzPolyMod` tower over `AzZMod n`,
  in which the algorithm's step-3/4/5 checks are computed.

  For primes `p`, `Φ_p = 1 + x + ⋯ + x^(p−1)` is the all-ones
  polynomial (`cyclotomicPrime`), monic for any nonzero length, so
  the proven `AzPolyMod` machinery applies at both levels.  The
  Gauss sum `G(p,q) = Σ_k χ(g^k) ψ(g^k) = Σ_k ζ_p^k ζ_q^(g^k)`
  is accumulated by walking the powers of the primitive root `g`
  (`gaussSumT`); the step-3/4 probable-prime check is the search
  for `l` with `G^(p^w u) = ζ_p^l` in the tower
  (`findZetaExponent`, exponents at the `AzNat` limb level via
  `powAzNat`); and the step-5 check is the content gcd
  `gcd(n, c(H − ζ_p^j))` read off the flattened coefficient grid
  (`towerContentGcd`) — the choice of coefficient lifts is
  irrelevant under `gcd(n, ·)`.

  This is **Phase 1** (data + `#guard`s): the checks compute; their
  bridges to the `CycPQ` tower semantics (via
  `AzPolyMod.ringEquivAdjoinRoot` at both levels and the
  quotient-commutation `CycPQ/(n) ≅` this tower) are the next
  phase, wiring into `theorem_4_4_6_composite_tower` through the
  `Algorithm_4_4_5` bridge lemmas.

  Kernel-checked here: the classical quadratic Gauss sum —
  `G(2,3) = ζ_3 − ζ_3²` and `G(2,3)² = −3` — computed in the tower
  mod `7`, and the step-3-style exponent search finding
  `G^((7^1−1)/2·…)`-shaped powers as `ζ_p`-powers.
-/
import Azurite.AzPolyMod.Equiv.AdjoinRoot
import Azurite.AzZMod.Equiv.RingEquiv
import Azurite.AzNat.Gcd

namespace Azurite

/-- `Fact (1 < k)` supplies `NeZero k`. -/
instance neZero_of_fact_one_lt {k : ℕ} [hk : Fact (1 < k)] : NeZero k :=
  ⟨by have := hk.out; omega⟩

/-- `AzZMod m` is nontrivial for `m > 1`. -/
instance azZMod_nontrivial {m : AzNat} [hm : Fact (1 < m.toNat)] :
    Nontrivial (AzZMod m) := by
  haveI : NeZero m.toNat := ⟨by have := hm.out; omega⟩
  haveI : Fact (1 < m.toNat) := hm
  refine ⟨0, 1, fun h => ?_⟩
  have h2 := congrArg (AzZMod.ringEquivZMod (m := m)) h
  rw [map_zero, map_one] at h2
  exact zero_ne_one h2

namespace AzPolynomial

variable (R : Type _) [Semiring R] [DecidableEq R] [Nontrivial R]

/-- The `p`-th cyclotomic polynomial for PRIME `p`:
`Φ_p = 1 + x + ⋯ + x^(p−1)`, the all-ones polynomial of length
`p` (the empty — zero — polynomial for `p = 0`). -/
def cyclotomicPrime (p : ℕ) : AzPolynomial R :=
  ⟨Array.replicate p (1 : R), by
    cases p with
    | zero => simp
    | succ k =>
      intro h
      rw [Array.back?_replicate] at h
      exact one_ne_zero (α := R) (Option.some.inj h)⟩

omit [DecidableEq R] in
@[simp] theorem cyclotomicPrime_coeffs_size (p : ℕ) :
    (cyclotomicPrime R p).coeffs.size = p := by
  simp [cyclotomicPrime]

theorem leadingCoeff_cyclotomicPrime {p : ℕ} (hp : p ≠ 0) :
    (cyclotomicPrime R p).leadingCoeff = 1 := by
  cases p with
  | zero => omega
  | succ k =>
    rw [AzPolynomial.leadingCoeff, AzPolynomial.coeff,
      AzPolynomial.natDegree]
    simp [cyclotomicPrime]

/-- `Φ_p` is monic (as a Mathlib polynomial) for `p ≠ 0` — the
gate of the proven `AzPolyMod` machinery. -/
theorem monic_toPoly_cyclotomicPrime {p : ℕ} (hp : p ≠ 0) :
    (AzPolynomial.toPoly (cyclotomicPrime R p)).Monic := by
  have h := leadingCoeff_toPoly (cyclotomicPrime R p)
  rw [Polynomial.Monic, h]
  exact leadingCoeff_cyclotomicPrime R hp

instance factMonicCyclotomicPrime {p : ℕ} [NeZero p] :
    Fact (AzPolynomial.toPoly (cyclotomicPrime R p)).Monic :=
  ⟨monic_toPoly_cyclotomicPrime R (NeZero.ne p)⟩

end AzPolynomial

namespace AzPolyMod

open _root_.Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Nontrivial R]

/-- `R[x]/(Φ_p)` is nontrivial for `p > 1`: the classes of `0` and
`1` have distinct reduced representatives. -/
instance instNontrivialCyclotomicPrime {p : ℕ} [hp : Fact (1 < p)] :
    Nontrivial (AzPolyMod (cyclotomicPrime R p)) := by
  refine ⟨⟨⟨#[(1 : R)], by simp⟩, Or.inl ?_⟩, 0, fun h => ?_⟩
  · rw [cyclotomicPrime_coeffs_size]
    simpa using hp.out
  · have hval := congrArg (fun a : AzPolyMod (cyclotomicPrime R p) =>
      a.val.coeffs.size) h
    have h0 : (0 : AzPolyMod (cyclotomicPrime R p)).val = 0 := rfl
    rw [h0] at hval
    simp at hval

/-! ### The tower -/

/-- Level 1 of the tower: `(ℤ/n)[x]/(Φ_p)` — the ring of `ζ_p` mod
`n`. -/
abbrev GaussTowerP (n : AzNat) (p : ℕ) [Fact (1 < n.toNat)] :=
  AzPolyMod (cyclotomicPrime (AzZMod n) p)

/-- Level 2 of the tower: `(ℤ/n)[x]/(Φ_p)[y]/(Φ_q)` — the model of
`ℤ[ζ_p, ζ_q]` mod `n`, where Algorithm 4.4.5 computes. -/
abbrev GaussTowerPQ (n : AzNat) (p q : ℕ) [Fact (1 < n.toNat)]
    [NeZero p] [Fact (1 < p)] :=
  AzPolyMod (cyclotomicPrime (GaussTowerP n p) q)

section Tower

variable (n : AzNat) (p q : ℕ) [Fact (1 < n.toNat)] [NeZero p]
  [Fact (1 < p)]

/-- `ζ_p` at level 1: the class of `x`. -/
def zetaPT : GaussTowerP n p := ofPoly AzPolynomial.X

/-- `ζ_q` at level 2: the class of `y`. -/
def zetaQT : GaussTowerPQ n p q := ofPoly AzPolynomial.X

/-- A level-1 element as a level-2 constant. -/
def constT (c : GaussTowerP n p) : GaussTowerPQ n p q := ofCoeff c

/-- `ζ_p^j` as a level-2 element — the candidate values of the
character `χ_(p,q)`. -/
def zetaPPowT (j : ℕ) : GaussTowerPQ n p q :=
  constT n p q ((zetaPT n p) ^ j)

/-- The accumulation loop of the Gauss sum: `steps` terms remaining,
`gk = g^k mod q` and `zk = ζ_p^k` maintained incrementally. -/
def gaussSumTAux (g : ℕ) : ℕ → ℕ → GaussTowerP n p →
    GaussTowerPQ n p q → GaussTowerPQ n p q
  | 0, _, _, acc => acc
  | steps + 1, gk, zk, acc =>
    gaussSumTAux g steps (gk * g % q) (zk * zetaPT n p)
      (acc + ofPoly (AzPolynomial.monomial gk zk))

/-- **The Gauss sum in the tower**:
`G(p,q) = Σ_(k=0)^(q−2) ζ_p^k ζ_q^(g^k mod q)` for the primitive
root `g` mod `q`. -/
def gaussSumT (g : ℕ) : GaussTowerPQ n p q :=
  gaussSumTAux n p q g (q - 1) (1 % q) 1 0

/-- **The step-3/4 exponent search**: the least `l < p` with
`A = ζ_p^l`, if any — applied to `A = G^(p^w u)` this reads off
`l(p,q)` (`none` on a composite-revealing failure). -/
def findZetaExponent (A : GaussTowerPQ n p q) : Option ℕ :=
  (List.range p).find? fun j => A = zetaPPowT n p q j

/-- **The step-5 content gcd**: `gcd(n, c(x))` for a tower element
`x`, read off the flattened coefficient grid — the choice of
coefficient lifts is irrelevant under `gcd(n, ·)`. -/
def towerContentGcd (x : GaussTowerPQ n p q) : AzNat :=
  x.val.coeffs.foldl (fun acc c2 =>
    c2.val.coeffs.foldl (fun acc' c1 => AzNat.gcd acc' c1.val) acc) n

/-- **The step-5 check** at a pair `(p, q₀(p))`: every
`gcd(n, c(H − ζ_p^j))`, `0 ≤ j < p`, equals `1`. -/
def step5Check (H : GaussTowerPQ n p q) : Bool :=
  (List.range p).all fun j =>
    towerContentGcd n p q (H - zetaPPowT n p q j) = AzNat.ofNat 1

end Tower

end AzPolyMod

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolyMod

private instance : Fact (1 < (AzNat.ofNat 7).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; omega⟩
private instance : Fact (1 < 2) := ⟨by omega⟩

/-! The classical quadratic Gauss sum in the tower mod `7`:
`G(2,3) = ζ_3 − ζ_3²` (primitive root `g = 2` mod `3`), so
`G(2,3)² = −3` — the `(−1|3)·3` of quadratic reciprocity. -/

private def G23 : GaussTowerPQ (AzNat.ofNat 7) 2 3 :=
  gaussSumT (AzNat.ofNat 7) 2 3 2

-- `G = ζ_q − ζ_q²` (the `ζ_p = ζ_2 = −1` coefficient shows as `-1`)
#guard G23 = zetaQT (AzNat.ofNat 7) 2 3
  - ofPoly (AzPolynomial.monomial 2 1)
-- `G² = −3`
#guard G23 ^ 2
  = constT (AzNat.ofNat 7) 2 3 (ofCoeff (-3 : AzZMod (AzNat.ofNat 7)))
-- the exponent search: `G²` is NOT a `ζ_2`-power mod 7 (it is `−3 ≡ 4`),
-- while `G⁶ = (−3)³ = −27 ≡ 1 = ζ_2⁰` is found at `l = 0`
#guard findZetaExponent (AzNat.ofNat 7) 2 3 (G23 ^ 2) = none
#guard findZetaExponent (AzNat.ofNat 7) 2 3 (G23 ^ 6) = some 0
-- `G⁴ = 9 ≡ 2` is not a `ζ_2`-power; `G³ = −3G` is not constant
#guard findZetaExponent (AzNat.ofNat 7) 2 3 (G23 ^ 4) = none
-- the step-5-style content gcd: `c(G) = 1` (coefficients `±1`), and
-- `gcd(7, c(G − G)) = gcd(7, 0) = 7`
#guard towerContentGcd (AzNat.ofNat 7) 2 3 G23 = AzNat.ofNat 1
#guard towerContentGcd (AzNat.ofNat 7) 2 3 (G23 - G23) = AzNat.ofNat 7
-- step 5 passes for `H = G` (no `ζ_2`-power is congruent to `G` mod 7)
#guard step5Check (AzNat.ofNat 7) 2 3 G23 = true

end Tests

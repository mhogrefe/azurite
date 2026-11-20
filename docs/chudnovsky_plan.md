# Chudnovsky's theorem: `π` and `Γ(1/4)`, `π` and `Γ(1/3)` — ledger

Goal: the irrationality (in fact transcendence) of `Γ(1/4)` and `Γ(1/3)`, to make
`gammaOneQuarterPrecRound` and `gammaOneThirdPrecRound` (`AzFloat/GammaConstants.lean`)
fuel-free.  Started 2026-11-18.

Source: M. Waldschmidt, *Les travaux de G. V. Čudnovskiĭ sur les nombres transcendants*,
Sém. Bourbaki 1975/76, exp. 488, pp. 274–292 (`~/azurite-sources/chudnovsky-gamma-constants.pdf`).
Only §1 (pp. 274–278) concerns the Gamma constants; §§2–5 are about `α^β` (Gel'fond's method
and its extensions) and are not needed.

## Statements of §1

* **Théorème 1.1.**  For a Weierstrass `℘` with invariants `g₂`, `g₃`, fundamental periods
  `ω₁`, `ω₂` and quasi-periods `ηᵢ = 2ζ(ωᵢ/2)`: two of `g₂, g₃, ω₁, ω₂, η₁, η₂` are
  algebraically independent over `ℚ`.
* **Corollaire 1.2.**  `g₂`, `g₃` algebraic and complex multiplication ⟹ `ω₁` and `π`
  algebraically independent.  (From 1.1 with the Legendre relation `ω₂η₁ − ω₁η₂ = 2πi` and
  the fact that under CM the `ℚ̄`-span of `1, ω₁, ω₂, η₁, η₂, 2πi` has dimension 4 — cited
  from Masser, LNM 437, ch. III.)
* **Application.**  `y² = 4x³ − 4x` (CM by `i`): `ω₁ = 2∫₁^∞ dt/√(4t³ − 4t) = ½ B(1/4, 1/2)
  = Γ(1/4)²/√(8π)`, so `Γ(1/4)` and `π` are algebraically independent; `y² = 4x³ − 4` gives
  `Γ(1/3)`.
* **Définitions.**  Size `t(P) = max(log H(P), deg P)` of `P ∈ ℤ[z₁..z_q]`; size of an element
  of `ℤ[θ₁..θ_k]` and of a number algebraic over `ℚ(θ₁..θ_k)`.  Transcendence type `≤ τ` of a
  field: `log |P(x₁..x_q)| ≥ −C t(P)^τ` on a transcendence basis.
* **Lemme 1.3 (Fel'dman 1951, th. 4).**  `ℚ(π)` has transcendence type `≤ 2 + ε` for every
  `ε > 0`.  **Cited, not proven in the exposé.**  The proof of 1.1 needs any type `< 3`.

## Proof of 1.1 (pp. 276–278), by contradiction

Suppose false; then (Legendre) `π ∈ K = ℚ(i, g₂, g₃, ω₁, ω₂, η₁, η₂)`, and `K = ℚ(π, θ)` with
`θ` integral over `ℤ[π]`.  `z, ℘(z), ζ(z)` and all their derivatives take values in `K` at
the points `ω₁/2 + h₁ω₁ + h₂ω₂`.  Fix `0 < ν < 1`, `N` large, `L = [N^(1−ν/4)]`,
`H = [N^(1−ν/2)]`.

1. **Auxiliary function** `Φ(z) = ∑_{λ₀,λ₁,λ₂ ≤ L} φ(λ) z^λ₀ ℘(z)^λ₁ ζ(z)^λ₂`, `φ(λ) ∈ ℤ[π]`
   not all zero, with `Φ⁽ⁿ⁾(ω₁/2 + h₁ω₁ + h₂ω₂) = 0` for `n < N`, `1 ≤ hᵢ ≤ H`: `H²N`
   equations, `(L + 1)³` unknowns, Siegel's lemma; `dⁿ/dzⁿ (z^λ₀ ℘^λ₁ ζ^λ₂)` is a polynomial
   in `z, ℘, ζ, ℘′` of degree `≤ c₁N` with coefficients of size `≤ c₂ N log N`; so `φ(λ)` of
   degree `≤ N` in `π` and size `≤ c₃N`.
2. **Choice of `ξ`.**  `N₁` maximal with the vanishing for `m < N₁`, `kᵢ ≤ N₁^(1−ν/2)`; a
   first nonzero derivative `ξ = Φ⁽ᵐ′⁾(w)` at the next level.
3. **Upper bound.**  `ψ = σ^(3L) Φ` is entire, `ψ⁽ᵐ′⁾(w) = σ(w)^(3L) ξ`; maximum principle on
   `|z| ≤ N₁^(1−7ν/16)` after dividing by the `N₁H₁²` zeros in `|z| ≤ c₄H₁`:
   `log |ξ| ≤ −c₅ N₁ H₁² log N₁`.
4. **Size, back to `ℤ[π]`.**  `t(ξ) ≤ c₆ N₁ log N₁`; denominator and norm over `ℚ(π)` give
   `P ∈ ℤ[z]`, `P ≠ 0`, `t(P) ≤ c₇ N₁ log N₁`, `log |P(π)| ≤ −c₈ N₁^(3−ν) log N₁`.
5. **Contradiction** with Lemme 1.3.

## What the exposé leaves out (to be supplied)

* Lemme 1.3 itself (Fel'dman's transcendence measure of `π`): a separate theorem with its
  own auxiliary-function proof.  Needs a source.
* Siegel's lemma over a finite extension of `ℚ(π)` with sizes (Lang; Waldschmidt LNM 402,
  lemme 4.3.1).  Mathlib has the integer Siegel lemma (`NumberTheory/SiegelsLemma.lean`).
* `Φ ≢ 0`, i.e. the algebraic independence of the functions `z, ℘(z), ζ(z)` over `ℂ`, and the
  finiteness of `N₁`.
* The theory of `ζ` and `σ`: `ζ′ = −℘`, `σ′/σ = ζ`, `σ` entire with simple zeros on the
  lattice, quasi-periodicity, `|σ(z)| ≤ exp(c|z|²)`, the Legendre relation.  Mathlib has `℘`,
  `℘′`, periodicity, the Laurent expansion and `℘′² = 4℘³ − g₂℘ − g₃`
  (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`), not `ζ` or `σ`.
* The CM relations.  For our two curves they are elementary and need no general theory:
  the lattice is `ω₁ℤ[i]` or `ω₁ℤ[ρ]`, and homogeneity (`ζ(iz) = −iζ(z)`, `ζ(ρz) = ρ⁻¹ζ(z)`)
  gives `η₂` from `η₁`; Legendre then gives `η₁ = π/ω₁` up to an algebraic factor.
* The period integrals `ω₁ = Γ(1/4)²/√(8π)` and its analogue for `Γ(1/3)`: that the lattice
  with these periods has `g₂ = 4, g₃ = 0` (resp. `g₂ = 0, g₃ = 4`).  The Beta integrals are
  in `Transcendental/GammaAGM.lean`.

## Specialization

Only the two CM curves are needed, and only the conclusion "`Γ(1/4)` (resp. `Γ(1/3)`) is not
algebraic".  Assuming it algebraic makes `K` explicit (`ω₁² π` algebraic, `ω₂ = iω₁`,
`η₁ = cπ/ω₁`, `η₂ = −iη₁`), which removes the primitive-element step and Masser's dimension
count; the analytic core (steps 1–4) and Lemme 1.3 are unchanged.

## Milestones

| | piece | status |
|---|---|---|
| M1 | sizes of polynomials, Siegel's lemma over `ℤ[π]`-modules | open |
| M2 | `ζ`, `σ` for a `PeriodPair`: derivatives, quasi-periods, Legendre, growth of `σ` | open |
| M3 | the two CM lattices: `g₂`, `g₃`, quasi-periods, `ω₁` as a Gamma value | open |
| M4 | derivatives of `z^a ℘^b ζ^c` as polynomials with size bounds | open |
| M5 | `z, ℘, ζ` algebraically independent; zero count and Schwarz lemma | open |
| M6 | Lemme 1.3: transcendence type of `ℚ(π)` below 3 (Fel'dman, th. 4) | **DONE 2026-11-19** (`pi_measure`) |
| M7 | assembly: `Γ(1/4)`, `Γ(1/3)` transcendental; fuel-free constants | open |

## Fel'dman's measure for `π` (M6)

Source: N. I. Fel'dman, *Approximation of certain transcendental numbers. I. Approximation of
logarithms of algebraic numbers*, Izv. Akad. Nauk SSSR Ser. Mat. 15 (1951), 53–74, Russian
original (`~/azurite-sources/feldman-the-approximation-of-certain-transcendental-numbers.pdf`).
Self-contained; complete proofs with explicit constants.

* **Теорема 4** (p. 72) — the Lemme 1.3 of the exposé:
  `|P(π)| > exp(−γ₄ n (n ln n + 1 + ln H) ln(n ln n + 2 + ln H))` for `P ∈ ℤ[z]`, `P ≠ 0`, of
  degree `n` and height `H`.  With `t = max(n, ln H)` the exponent is `O(t² ln² t)`: type
  `≤ 2 + ε`.
* **Теорема 3** (pp. 68–72): `|ξ − π| > exp(−γ₃ n (1 + n ln n + ln H) ln(2 + n ln n + ln H))`
  for algebraic `ξ` of degree `n`, height `H`.  Theorem 4 follows from it as Theorem 2 from
  Theorem 1 (p. 68): pass to an irreducible factor (height `≤ H·6ⁿ` by Lemma 2) and to its
  root nearest `π` (Lemma 5).
* **Lemmas needed** (§1, pp. 54–61):
  1. Dirichlet's box principle for real linear forms with small values.
  2. `|ξ_{ν₁} ⋯ ξ_{ν_s}| ≤ (n + 1) 2ⁿ H` for distinct roots of a monic polynomial; 3. the
     corollary `∏ (1 + |ξ_ν|) ≤ (n + 1) 4ⁿ |a₀|⁻¹ H`.
  4. Liouville's inequality for `β = ∑ a_{k,l} α₁^k ξ₁^l ≠ 0` (used with `α₁ = i`).
  5. `|P(ζ)| ≥ a₀ δ₀ e^{−(2n + ln H)…}`-type bound from the distance `δ₀` to the nearest root
     (no multiple roots; via the discriminant).
  6. The coefficients `C_{k,l}` of `f(z) = ∑ C_{k,l} z^k e^{lz}` from the values
     `f⁽ˢ⁾(2πix)` (explicit inverse with Vandermonde cofactors), with the cofactor bounds
     (26′)–(28).
  7. Hermite interpolation: derivatives of `φ` on a larger disc from its derivatives at the
     points `ζx`, `|x| ≤ y₀`, and its maximum on a still larger one.
* **Proof of Theorem 3**: `f(z) = ∑_{k<q₀, l<q} C_{k,l} z^k e^{lz}`, `C_{k,l} = ∑_τ C⁽τ⁾ ξ^τ`
  with small integers `C⁽τ⁾` (Lemma 1) making `f⁽ˢ⁾(πix)` small; replace `π` by `ξ`, Liouville
  (Lemma 4) forces the algebraic values to vanish; Lemma B extrapolates to more points
  (Lemma 7) repeatedly; then Lemma 6 makes every `C_{k,l}` tiny, hence zero by Lemma 4 —
  contradiction.  Theorems 1 and 2 (for `ln α`) are not needed.

### Progress on M6

**Lemmas 1–5 DONE (2026-11-18)**, `Azurite/Feldman/Dirichlet.lean`, `Azurite/Feldman/Liouville.lean`.
Differences from the paper, all recorded in the module docstrings:

* Lemma 1: `dirichlet_box` takes the number `N` of subdivisions as a parameter
  (`N^m < (z + 1)^r` ⟹ `|L_i(x)| ≤ 2A/N`); `dirichlet_box_rpow` is Fel'dman's form with `≤`
  instead of `<` (strictness fails for `A = 0`).
* Lemmas 2, 3: from Mathlib's Mahler measure (`|a₀| ∏ max(1, |ξ|) ≤ (n + 1) H`), with better
  constants: `(n + 1) H` and `2ⁿ (n + 1) H` instead of `(n + 1) 2ⁿ H` and `(n + 1) 4ⁿ H`.
* Lemma 4: only `α₁ = i` (all that `π` needs).  `liouville_int`:
  `1 ≤ |R(ξ)| ((M + 1) A)^(n−1) ((n + 1) H)^M` by Mathlib's resultant
  (`resultant_eq_prod_eval`); `liouville_gaussian` for `Q₁(ξ) + i Q₂(ξ)`:
  `1 ≤ |β| · 2(M + 1)A · (2(2M + 1)(M + 1)A²)^(n−1) · ((n + 1)H)^(3M)`.  Same shape as
  Fel'dman's `exp(−γ{M(n₀ + ln H₀) + n₀(N₀ + ln A)})`.
* Lemma 5: for an irreducible `p` (the only case used), from `|p(ζ)| ≥ |ζ − ξ| 2^(1−n) |p′(ξ)|`
  and Liouville for `p′(ξ)` — no discriminant:
  `|ζ − ξ| ≤ |p(ζ)| · 2^(n−1) (n²H)^(n−1) ((n + 1)H)^(n−1)`, which is `e^{O(n ln n + n ln H)}`
  against Fel'dman's `e^{2n² + n ln H}`.

Next: Lemma 6 (inverse of the interpolation at `2πix`), Lemma 7 (Hermite interpolation),
then Theorem 3.

### Plan for Lemmas 6 and 7 (2026-11-18)

**Lemma 6** (`Azurite/Feldman/Interpolation.lean`), by norms instead of the explicit cofactor
formula (2).  `f(z) = ∑_{l<q} P_l(z) e^{lz}`, `deg P_l < q₀`, `D = d/dz`, `‖·‖₁` the sum of the
absolute values of the coefficients.
1. `f⁽ˢ⁾(z) = ∑_l e^{lz} ((D + l)^s P_l)(z)`; at `z = 2πix` the exponentials are `1`, so
   `f⁽ˢ⁾(2πix) = A_s(2πix)` with the polynomial `A_s = ∑_l (D + l)^s P_l`, `deg A_s < q₀`.
2. Lagrange at the nodes `0, …, m − 1`: `‖ℓ_x‖₁ ≤ ∏_{j≠x} (1 + j)/|x − j| = C(m, x + 1) ≤ 2^m`;
   so `|A_s(2πix)| ≤ ε` for `x < q₀` gives `‖A_s‖₁ ≤ q₀ 2^{q₀} ε` (`|2πi| ≥ 1`).
3. Moments `M_s = ∑_l l^s P_l = ∑_t C(s,t) (−D)^t A_{s−t}` (binomial theorem for the commuting
   operators `D + l` and `−D`), so `‖M_s‖₁ ≤ (1 + q₀)^s max ‖A‖₁`.
4. `P_l = ∑_s (coeff of λ^s in ℓ_l) M_s`, so `‖P_l‖₁ ≤ 2^q (1 + q₀)^q q₀ 2^{q₀} ε`.
(Fel'dman: `q q₀ 2^{q₀−1} (q − 1)! 4^{q−1} 4^{q₀−1} ε`; same order `e^{O(q ln q)}`.)

**Lemma 7** (Hermite interpolation; needed for `π` only with `k = 6, k₁ = 2, k₂ = 3`, nodes
`a_x = πix`, `|x| ≤ y₀`, multiplicity `t₀`, `R = πy₀`).  Avoid the contour formula (5) on a
domain with holes:
* `P = ∏_x (z − a_x)^{t₀}`, `Q_x = P/(z − a_x)^{t₀}`, `T_x` the Taylor polynomial of `φ` at `a_x`
  of degree `< t₀` (coefficients `≤ δ/s!`).  Hermite interpolant `H = ∑_x Q_x U_x`, `U_x` the
  Taylor polynomial of degree `< t₀` at `a_x` of `T_x/Q_x`; its coefficients by Cauchy's
  estimates on `|ξ − a_x| = |ζ|/2`, where `|Q_x(ξ)| ≥ ((|ζ|/2)^{2y₀} (y₀!)²)^{t₀}`.
* `φ − H` vanishes to order `t₀` at every node, so `(φ − H)/P` is analytic (iterate `dslope`,
  orders by `analyticOrderAt`), and the maximum principle on `|w| = kR` gives
  `|φ(z)| ≤ |H(z)| + |P(z)| max_{|w|=kR} |φ − H| / min_{|w|=kR} |P|`,
  the factor `((k₁ + 1)/(k − 1))^{(2y₀+1)t₀}` replacing Fel'dman's `((k₂² + 1)/(k² − 1))^{y₀t₀}`.
* Derivatives `φ^{(σ)}` on `|z| ≤ k₁R` by Cauchy's estimate from `|z| ≤ k₂R`.

### What the theorem buys for `Γ` (user question, 2026-11-18)

With `π` and `Γ(1/4)` (resp. `Γ(1/3)`) algebraically independent — the full Corollaire 1.2,
not only "`Γ(1/4)` is not algebraic", so **do not specialize M7 to the weaker statement** —
reflection, duplication and the recurrence give the irrationality of `Γ(q)` for every
non-integer rational `q` with denominator `2, 3, 4` or `6`: `Γ(3/4) = √2 π/Γ(1/4)`,
`Γ(2/3) = 2π/(√3 Γ(1/3))`, `Γ(1/6) = 2^(−1/3) √(3/π) Γ(1/3)²`, `Γ(5/6) = 2π/Γ(1/6)`,
`Γ(1/2) = √π` (the transcendence of `π` is a corollary of Fel'dman's Theorem 4), and
`Γ(q + n)` is a rational multiple of `Γ(q)`.  So `gammaRatPrecRound` can be fuel-free on
those `q`, and `gammaPrecRound` on the floats that are quarter- or half-integers.  Nothing
is known for other denominators (the transcendence of `Γ(1/5)` is open), so the general loop
keeps its fuel.

**Lemma 6 DONE (2026-11-19)**, `Azurite/Feldman/Interpolation.lean`, as planned above:
`l1_le_of_iteratedDeriv_le`.  Next: Lemma 7, then Theorem 3.

### Deliverable after M7 (user request, 2026-11-19)

Once the theorem is proven: in `AzFloat/Equiv/Gamma.lean` (and `Equiv/GammaRat.lean`), prove
that for the special fractions — non-integer rationals with denominator `2, 3, 4, 6` — the
gamma function returns the correctly rounded value **unconditionally** (no "or `NaN`").  This
needs the implementation to take a fuel-free path on those arguments: `zivLoopCertified` with
the irrationality proof as its termination argument (the swap recipe of the
pending-irrationality notes), for the constants `Γ(1/4)`, `Γ(1/3)` and for the values derived
from them and from `√π` by reflection, duplication and the recurrence.

**Lemma 7 DONE (2026-11-19)**, `Azurite/Feldman/Hermite.lean`, as planned: `norm_le_of_small_jets`
with abstract nodes.  All of Fel'dman's §1 is now formal.  Next: **Theorem 3** (pp. 68–72):
the auxiliary function by `dirichlet_box`, the zero step by `liouville_gaussian`, Lemma B by
`norm_le_of_small_jets` (nodes `πix`, `ρ = π/2`; needs `D ≥ ((π/2)^{2y₀}(y₀!)²)^T` and Cauchy's
estimate for the derivatives), the end by `l1_le_of_iteratedDeriv_le` and `liouville_int`; then
Theorem 4 by `norm_aeval_ge_dist_root` and a bound for the height of an irreducible factor
(Mathlib: `norm_coeff_le_choose_mul_mahlerMeasure`).  The parameter bookkeeping
(`λ`, `q₀`, `q`, `C`, `x₀`, `s₀`, `N`) is the bulk of the remaining work on M6.

### Plan for Theorem 3 (2026-11-19) — simplified constants, same structure

Only a transcendence type `< 3` is needed, so the bookkeeping is done in powers of two with
one "log" parameter `b` and crude bounds; the result is `|π − ξ| ≥ 2^(−Φ)`, `Φ = O(n N b³)`
(`n = deg ξ ≤ N`, `(n + 1) H ≤ 2^(N b)`, `b ≈ log N`), against Fel'dman's `n N ln² N`.

**Objects.**  `ξ` a root of an irreducible `p ∈ ℤ[X]`, `deg p = n`, height `≤ H`, `|π − ξ| ≤ 1`
(so `|ξ| ≤ 5`).  Integers `y(k, l, τ)`, `k < q₀`, `l < q`, `τ < n`, `|y| ≤ C = 2^c`.
`P_l = ∑_k (∑_τ y(k,l,τ) ξ^τ) X^k`, `f(z) = ∑_l e^{lz} P_l(z)`, `B_{s,l} = (D + l)^s P_l`,

  `V(s, x, w) = ∑_l (−1)^{lx} B_{s,l}(i x w)`,   `V(s, x, π) = f⁽ˢ⁾(πix)`,

and `V(s, x, ξ) = Q₁(ξ) + i Q₂(ξ)` with `Q₁, Q₂ ∈ ℤ[X]` of degree `≤ q₀ + n − 2` (integrality:
`(D + l)^s X^k` has integer coefficients — `shiftDZ`; `i^j = reI j + i·imI j`).

**Bounds** (`‖·‖₁` machinery; `W = 3n + 3b + b s₀ + b q₀`, all sizes `≤ 2^b`):
`‖P_l‖₁ ≤ q₀ n C 5^(n−1)`, `‖B_{s,l}‖₁ ≤ (q₀ + q)^s ‖P_l‖₁`, so for `|x| ≤ 4q₀`, `s < s₀`:
`|V(s,x,w)| ≤ 2^(c+W)` (`|w| ≤ 5`), `|V(s,x,π) − V(s,x,ξ)| ≤ |π − ξ| 2^(c+W+2b)`, heights of
`Q₁, Q₂` `≤ 2^(c+W)`, and Liouville (`liouville_gaussian`): `V(s,x,ξ) ≠ 0 ⟹ |V(s,x,ξ)| ≥ 2^(−Y)`,
`Y = 2n(c + W) + 3bn + 3(q₀ + n) N b`.  On `|w| = 9πX`: `|f(w)| ≤ 2^(41qX + c + W)`.

**Steps.**  Invariant `Z(X)`: `V(s, x, ξ) = 0` for `s < s₀`, `|x| ≤ X`.
1. `Z(x₀)`: `dirichlet_box` (finset-indexed wrapper) on the `2 s₀ (2x₀ + 1)` real forms
   `Re, Im V(s, x, π)` in the `n q q₀` unknowns, `N_D = 2^g`; then Liouville.  Needs
   `g · 2s₀(2x₀+1) ≤ c n q q₀` and `g ≥ c + W + Y + 4`, `Φ ≥ c + W + 2b + Y + 2`.
2. `Z(X) ⟹ Z(2X)` for `x₀ ≤ X ≤ 2q₀`: `norm_le_of_small_jets` with nodes `πix`, `|x| ≤ X`,
   `T = s₀`, `ρ = π/2`, **`D = 1`** (each factor `≥ π/2 > 1`; this costs one factor `b` in
   `Φ`), `r = 9πX`, `L = 10πX`, `d = 8πX`, `L_z ≤ 3πX + 1` (ratio `≤ 1/2`), then Cauchy's
   estimate with radius `1` for the derivatives, then Liouville.  Needs `41 q ≤ s₀`-type
   `(2s₀ − 41q) x₀ ≥ b s₀ + c + W + Y + 2` and `Φ ≥ 4 b s₀ q₀ + 2 b s₀ + c + W + Y + 4b + 6`.
3. `Z(2q₀)` ⟹ `|f⁽ˢ⁾(2πix')| ≤ |π − ξ| 2^(c+W+2b)` for `s < q ≤ s₀`, `x' < q₀`;
   `l1_le_of_iteratedDeriv_le`; `liouville_int` on `∑_τ y(k,l,τ) ξ^τ` ⟹ all are `0` ⟹ `y = 0`
   (degree `< n`), contradicting Dirichlet.  Needs
   `Φ ≥ q + b q + q₀ + c + W + 3b + n (b + c + N b) + 1`.

**Parameters** (one consistent choice): `q = a_q N b`, `s₀ = a_s N b`, `x₀ = a_x n b`,
`q₀ = a₀ n b`, `c = a_c N b²`, `g = 4 n c`, with `a_q = 1200`, `a_s = 41 a_q`, `a_x = 27`,
`a₀ = 24 a_s a_x / a_q = 26568`, `a_c = 3a_s + 6a₀ + 30`, `Φ = 5 b s₀ q₀`.

**Files**: `Feldman/Dirichlet` (finset wrapper), `Feldman/ExpPoly` (more `l1`, `shiftDZ`,
`reI`/`imI`), `Feldman/Auxiliary` (`V`, bounds, `Q₁`, `Q₂`), `Feldman/Extrapolation` (Hermite at
`πix`), `Feldman/Theorem3` (core with exponent hypotheses, then the parameter choice).

**Theorem 3 progress (2026-11-19).**  Done and compiling: `Feldman/Dirichlet` (`dirichlet_box`
for Fintype indices, `dirichlet_box_finset`), `Feldman/ExpPoly`, `Feldman/Auxiliary` (all of
`auxV`, bounds, `auxV_eq_sum`, `auxV_eq_aeval`, `auxQ` degree and heights), `Feldman/Extrapolation`
(`extrapolate`, `extrapolate_deriv`, nodes `πix` for **`0 ≤ x ≤ X` only** — one-sided, so the
exponent hypotheses read `42 q ≤ s₀`, `(s₀ − 42q) x₀ ≥ b s₀ + c + W + Y + 2`,
`Φ ≥ 2 b s₀ q₀ + 2 b s₀ + c + W + Y + 4b + 6`, Dirichlet with `2 s₀ (x₀ + 1)` forms), and in
`Feldman/Theorem3`: the structure `Thm3Data` (fields `h2`–`h6`, `Y = 2n(c+W) + 2bn + 3(q₀+n)Nb`),
`norm_auxV_le_two_pow`, `norm_auxV_pi_sub_le`, `auxV_ξ_eq_zero` (Liouville).  Remaining in
`Theorem3`: the step `Z(X) ⟹ Z(2X)`, the start by Dirichlet, the end by Lemma 6, the
parameter choice; then Theorem 4.

**THEOREM 3 DONE (2026-11-19)**: `feldman_theorem3` in `Azurite/Feldman/Theorem3.lean`, via
`Thm3Data.false`.  Final parameters: `q = 1000 N b`, `s₀ = 84000 N b`, `x₀ = 43 n b`,
`q₀ = 29568 n b`, `c = 429435 N b²`, `g = 4 n c`, `Φ = 4 b s₀ q₀`; hypotheses `n ≤ N`, `b ≥ 1`,
`(n + 1) H ≤ 2^(N b)`, `2^23 N b ≤ 2^b`.  Statement: `1 ≤ ‖ξ − π‖ · 2^Φ`.

Next: **Theorem 4** (`|P(π)|` from below for any nonzero `P ∈ ℤ[X]`): an irreducible factor
`p` of `P` with small `|p(π)|` (height of a factor by `norm_coeff_le_choose_mul_mahlerMeasure`),
its root nearest `π` (`norm_aeval_ge_dist_root`), Theorem 3; then the transcendence type
`≤ τ < 3` of `ℚ(π)` in the form the Chudnovsky argument uses (M6 complete), and as a corollary
the transcendence of `π`.

**THEOREM 4 DONE, M6 COMPLETE (2026-11-19)**: `Azurite/Feldman/Theorem4.lean`.
`pi_measure`: for `P ∈ ℤ[X]`, `P ≠ 0`, `deg P ≤ t`, height `≤ 2^t`, `t ≥ 1`, `b = 2 size t + 30`:
`1 ≤ ‖P(π)‖ · 2^(kappa t b · t)`, `kappa N b = 1 + b + 2Nb + 9934848000 N b³`.  So
`log₂ |P(π)| ≥ −O(t² log³ t)`: type `≤ 2 + ε`, which is what step 5 of the proof of
Théorème 1.1 needs (there `t(P) ≤ c₇ N₁ log N₁` against `−c₈ N₁^(3−ν) log N₁`).
Corollary: `transcendental_pi : Transcendental ℤ (π : ℂ)` and `transcendental_pi_real`.

Remaining milestones: M1 (sizes/Siegel over `ℤ[π]`), M2 (`ζ`, `σ`, Legendre), M3 (the two CM
lattices and their periods), M4 (derivatives of `z^a ℘^b ζ^c`), M5 (independence of
`z, ℘, ζ`, zero count), M7 (assembly, fuel-free Gamma constants, unconditional theorems in
`Equiv/Gamma.lean`).

## The elliptic side: plan (2026-11-19)

Lattices `Λ_τ = ℤ + ℤτ`, `τ = i` and `τ = e^{iπ/3}`, on Mathlib's `PeriodPair` (`℘`, `℘′`,
periodicity, Laurent expansion, `℘′² = 4℘³ − g₂℘ − g₃`), then rescaled by `ω`.

* **F1. `ζ`.**  `ζ(z) = 1/z + ∑′ [1/(z − l) + 1/l + z/l²]` (terms `O(|l|⁻³)`), differentiable off
  the lattice, `ζ′ = −℘` (termwise, as Mathlib does for `℘ → ℘′`), odd, quasi-periodic
  `ζ(z + l) = ζ(z) + η(l)` with `η` additive; `ζ(ω/2) = η(ω)/2`.
* **F2. Legendre relation** `η₁ ω₂ − η₂ ω₁ = 2πi`, for lattices with a rectangular sublattice:
  `∮ ζ` over a rectangle (Mathlib has Cauchy on rectangles; `∮ dz/z` over a rectangle by
  explicit integration).  With CM, homogeneity `ζ(τz) = τ⁻¹ ζ(z)` gives `η₂` from `η₁`, so
  `η₁ = π` for `ℤ[i]` and the analogue for `ℤ[e^{iπ/3}]`.
* **F3.** `℘″ = 6℘² − g₂/2`; derivatives of `z^a ℘^b ζ^c` as polynomials in `z, ℘, ℘′, ζ` with
  size bounds (M4).
* **F4. Values** at `w = ω₁/2 + h₁ω₁ + h₂ω₂`: `℘ = e₁`, `℘′ = 0`, `ζ = η₁/2 + h₁η₁ + h₂η₂`;
  `4e₁³ − g₂e₁ − g₃ = 0`.
* **F5. No `σ`.**  The pole-cancelling entire function `σ^{3L}` can be replaced by the
  polynomial `D(z) = ∏_{|l| ≤ R′} (z − l)^{3L}`: `DΦ` is analytic on the disc, which is all that
  `norm_le_of_zeros` (Schwarz with zeros) needs after restricting.  Needs: a radius `r` whose
  circle stays `≥ c/R` away from the lattice (pigeonhole), the bounds `|℘(z)| ≤ C/dist(z, Λ)²`,
  `|ζ(z)| ≤ C(1 + |z|)/dist(z, Λ)` (periodicity and compactness; local structure from
  `weierstrassPExcept`), `#{l : |l| ≤ R} ≤ C R²`, and `|w − l| ≥ dist(ω₁/2, Λ)`.
  (`norm_le_of_zeros` is stated for entire functions; restate for functions analytic on a
  neighbourhood of the closed disc, or multiply out to an entire function.)
* **F6. `z, ℘, ζ` algebraically independent** over `ℂ` as functions (so the auxiliary function is
  not `≡ 0`).
* **F7. Periods and Gamma values.**  `e₁ ≠ e₂` by Liouville: `(℘(z) − e₁)(℘(z − ω₁/2) − e₁)` is
  elliptic without poles, hence the constant `(e₁ − e₂)(e₁ − e₃)`.  For `ℤ[i]`: `e₂ = −e₁`,
  `g₃ = 0`, `g₂ = 4e₁²`, `℘` real and `≥ e₁ > 0` on `(0, 1)`, strictly decreasing on `(0, 1/2]`
  (`℘″ = 4e₁² > 0` where `℘ = e₁`), so `1/2 = ∫_{e₁}^∞ dt/(2√(t(t² − e₁²)))` and
  `√e₁ = ∫₁^∞ ds/√(s³ − s) = ½B(1/4, 1/2) = ϖ`: `g₂(ℤ[i]) = 4ϖ⁴`, and `ϖℤ[i]` has `g₂ = 4`,
  `g₃ = 0`, `ω₁ = ϖ = Γ(1/4)²/(2√(2π))`.  Similarly `ℤ[e^{iπ/3}]`: `g₂ = 0`, `g₃` from `e₁`,
  and `∫₁^∞ dt/√(t³ − 1) = ⅓B(1/6, 1/2)`.
* **F8. Arithmetic** (M1): sizes in `ℤ[π]`, Siegel's lemma over a finite extension, norms.
* **F9. Assembly** (M7) for the two lattices, with the full Corollaire 1.2 (`ω₁` and `π`
  algebraically independent), then the Gamma consequences.

Order of work: F1, F3, F4 (pure series/ODE), F2, F7, F5, F6, F8, F9.

**F1, F3 (`℘″`), F4 DONE (2026-11-19)**: `Azurite/Chudnovsky/Zeta.lean` (`weierstrassZeta`,
`deriv_weierstrassZeta`, `weierstrassZeta_neg`), `QuasiPeriod.lean` (`quasiPeriod`,
`weierstrassZeta_add_coe`, `quasiPeriod_int_combo`, `weierstrassZeta_half_add`), `Values.lean`
(`halfValue`, `four_mul_halfValue_cube`, `derivWeierstrassP_half_add`,
`deriv_derivWeierstrassP`).  Next: F2 (Legendre relation by a rectangle integral).

**F2 DONE (2026-11-19), by a different route**: no rectangle integral.  `EtaG2.lean`:
`η(1) = G₂(τ)` for the lattice `ℤ + ℤτ` (`quasiPeriod_one_eq_G2`), with Mathlib's `G2`;
`CM.lean`: homogeneity (`weierstrassZeta_mul`, `weierstrassP_mul`, `quasiPeriod_mul`, `G_mul`),
`G2_I = π`, `G2_rho = 2π/√3` from Mathlib's `G2_S_transform`/`G2_T_transform` (note: Mathlib's
`ρ` is `e^{2πi/3}`, so the hexagonal lattice is `latRho = pairOf ρ`, `ρ² + ρ + 1 = 0`), and
for `latI = pairOf I`: `η₁ = π`, `η₂ = −iπ`, `g₃ = 0`; for `latRho`: `η₁ = 2π/√3`,
`η₂ = ρ⁻¹ η₁`, `g₂ = 0`.  (Mathlib's `G2Term`, `aux_identity`, `G2_eq_tsum_G2Term` are not
exported from their module; only the lemmas after `public section` are usable.)
Next: F7 (periods as Gamma values), starting with `e₁ ≠ e₂`.

## The core of Chudnovsky's theorem: plan B (2026-11-19) — Dirichlet + Liouville, no Siegel

Work directly with `Λ = ℤ + ℤτ` (`τ = i` or `ρ`), **no rescaling**: the statement to prove is
"`ϖ` and `e₁ = ℘(1/2)` are algebraically independent", `ϖ = η₁` (`π` or `2π/√3`); the Gamma
values come afterwards from F7 (`e₁` as a Gamma value).  Everything at the points
`w_h = 1/2 + h₁ + h₂τ` lies in `𝒪_F[1/2][ϖ, e₁]`, `𝒪_F = ℤ[τ]`: `z = w_h`, `℘ = e₁`, `℘′ = 0`,
`ζ = ϖ (1/2 + h₁ + h₂ α)` (`α = −i`, resp. `ρ⁻¹ = −ρ − 1`), and `℘″ = 6℘² − g₂/2` with
`g₂/2 = 2e₁²` (resp. `0`), so the derivation `D`: `Z ↦ 1`, `P ↦ P′`, `P′ ↦ 6P² − 2Y²` (resp.
`6P²`), `T ↦ −P` has integer coefficients.

Instead of Siegel's lemma over a finite extension of `ℚ(π)` (Waldschmidt's first step), follow
the structure of Fel'dman's Theorem 3, for which all tools exist:

* **P1. Liouville in `K = ℚ(ϖ, e₁)`** (transfer of the measure).  Assume `R ∈ ℤ[X][Y]`,
  `R(ϖ, e₁) = 0`, of minimal `Y`-degree `d ≥ 1` among nonzero relations, `δ = r_d(ϖ) ≠ 0`.  With
  the matrix `Cδ` over `ℤ[X]` (rows: `(i, i+1) ↦ r_d` for `i < d − 1`, last row `j ↦ −r_j`), the
  vector `b = (1, e₁, …, e₁^{d−1})` satisfies `Cδ(ϖ) b = δ e₁ b`; for `M = ∑ m_k Y^k` of degree
  `D`, `𝑀 = ∑ m_k r_d^{D−k} Cδ^k` has `𝑀(ϖ) b = δ^D M(ϖ, e₁) b`.  `𝒟 = det 𝑀 ∈ ℤ[X]` is nonzero
  when `M(ϖ, e₁) ≠ 0` (a left kernel vector over `ℤ[X]` would be a relation of degree `< d`:
  `Matrix.exists_vecMul_eq_zero_iff`), `𝒟(ϖ) = δ^D M(ϖ, e₁) (adj(𝑀(ϖ)) b)₀`, and the size of `𝒟`
  is linear in that of `M` (`l1` is sub-multiplicative; `Matrix.det_apply`).  So the measure of
  `ϖ` gives `|M(ϖ, e₁)| ≥ exp(−C t² log³ t)`.  Coefficients in `𝒪_F`: write `Q = A + τB` and use
  the norm `A² + tr·AB + nm·B²` (as in `liouville_gaussian`).  Measure of `2π/√3` from that of
  `π` by `S(cX) S(−cX)`, `c² = 4/3`.
* **P2/P3. Derivatives.**  `MvPolynomial` in `Z, P, P′, T, Y` with the derivation `D`;
  `iteratedDeriv n (z ↦ Q(z, ℘, ℘′, ζ, e₁)) = (Dⁿ Q)(…)` off the lattice; degree `≤ deg Q + n`,
  `ℓ¹`-norm `≤ (8(deg Q + n))ⁿ ‖Q‖₁`.
* **P4. Start.**  Unknown integers `a(λ, j)`, `λ ∈ [0, L]³`, `j ≤ J`,
  `Φ = ∑ (∑_j a(λ,j) ϖ^j) z^λ₀ ℘^λ₁ ζ^λ₂`; `dirichlet_box_finset` on `Re, Im Φ⁽ⁿ⁾(w_h)`,
  `n < N`, `h ∈ [1, H]²`; then P1 makes them vanish.  Needs `L³ J ≳ N log⁴N · N H²`,
  `log C ≈ N log N`.
* **P5. Analysis without `σ`.**  `D_r(z) = ∏_{|l| ≤ r+1} (z − l)^{3L}`; `ψ = D_r Φ` is analytic
  near `|z| ≤ r`; Schwarz with zeros on a disc (generalize `exists_eq_prod_mul`,
  `norm_le_of_zeros` from entire functions to functions differentiable on an open set); a
  radius `r ∈ [R, 2R]` with `dist(|z| = r, Λ) ≥ c/R`; `|℘| ≤ C/dist²`, `|ζ| ≤ C(1+|z|)/dist`;
  `#{|l| ≤ r} ≤ C r²`; `|w_h − l| ≥ 1/2`; `iteratedDeriv n ((z−w)ⁿ g) w = n! g(w)`.
* **P6. Induction on the stage `k`** (all powers integral): `N(k) = k¹⁶`, `H(k) = k¹⁰`,
  `R(k) ≈ k¹¹`, `L ≈ c k₀¹² ℓ₀²`, `J = k₀¹⁶`.  `Z(k)`: `Φ⁽ⁿ⁾(w_h) = 0` for `n < k¹⁶`,
  `h ∈ [1, k¹⁰]²`.  Step `k → k + 1`: for each `h` in the larger box, inner induction on
  `n < (k+1)¹⁶`: Schwarz with the `k¹⁶ · k²⁰` zeros (gain `≈ k³⁶ log k`), Cauchy on a circle of
  radius `1` round `w_h`, `ψ⁽ⁿ⁾(w) = D_r(w) Φ⁽ⁿ⁾(w)`, then P1 (cost `≈ k³² log⁵ k`) — margins
  `k²` (growth `L R² ≈ k³⁴`) and `k⁴`.  Hence `Φ` vanishes to infinite order at `w`, so `Φ ≡ 0`.
* **F6. `z, ℘, ζ` independent**: for fixed `z₀`, `(u, v) ↦ P(z₀ + u, ℘(z₀), ζ(z₀) + v)` vanishes
  on the lattice `ℤ(1, η₁) + ℤ(τ, η₂)`, which spans `ℂ²` (`η₂ − τη₁ = −2πi ≠ 0`), hence
  identically; then `℘` takes infinitely many values.
* Constants depend on `R`; "for large `k₀`" by lemmas of the form `∃ K, ∀ k ≥ K, …`
  (`(size k)^c ≤ k` eventually).

**F7 (after the core), revised.**  Sign of `e₁`: for `ℤ[i]`, from the mean value
`∫₀¹ ℘(1/2 + it) dt = π > 0` on the pole-free line `Re z = 1/2` (`RealStructure.lean`) and the
real ODE; for `ℤ[ρ]` every mirror line passes through lattice points, so treat both signs:
real axis if `e₁ > 0` (`√e₁ = I₊`), imaginary axis if `e₁ < 0` (`√|e₁| = I₊/√3`),
`I₊ = ∫₁^∞ ds/√(s³ − 1) = ⅓B(1/6, 1/2)`; `e₁ = 0` is excluded by non-integrability.  One generic
"half-period integral" lemma (monotone substitution `t = p(x)`).

**P1 (algebraic part) DONE (2026-11-19)**: `Chudnovsky/Transfer.lean`, theorem `transfer`:
`∃ 𝒟 ≠ 0`, `deg 𝒟 ≤ d(gM + Dρ)`, `‖𝒟‖₁ ≤ d!((D+1) LM (d·lam)^D)^d`,
`|𝒟(ϖ)| ≤ |δ|^D |M(ϖ,e)| · d · d! B₁^d max(1,|e|)^d`.  Still to do for P1: combine with the
measure (`pi_measure`, and its analogue for `2π/√3`), and the `𝒪_F`-coefficient version
(`Q = A + τB`, norm trick).  `Chudnovsky/RealStructure.lean` (conjugation, mean values) is also
done and registered.

**P1 complete, P2/P3 complete (2026-11-19).**  `Chudnovsky/PairMeasure.lean`
(`exists_pairMeasure`: `HasMeasure ϖ c₀` and a relation `R(ϖ, e) = 0`, `R ≠ 0`, give
`PairMeasure ϖ e τ c`) and `Chudnovsky/Derivation.lean` (`iteratedDeriv_aeval`, sizes).  The
variables are `Z = 2z`, `T = 2ζ` (so that the values at `w_h = 1/2 + m + nτ` are integral:
`Z ↦ 1 + 2m + 2nτ`, `P, Y ↦ e`, `P′ ↦ 0`, `T ↦ ϖ(1 + 2m + 2nα)`, `W ↦ ϖ`).

**The analytic part: plan B′** (what remains is "`PairMeasure` ⟹ `False`"):

* Domain: not discs but the parallelograms `U_K = {a + bτ : |a|, |b| < K + 1/2}`; their
  boundary is at distance `≥ 1/4` from the lattice, so no "good radius" is needed, and `℘`,
  `ζ` are bounded there by periodicity and compactness: `|℘| ≤ C₁`, `|ζ| ≤ C₂(1 + |z|)` on
  `{dist(z, Λ) ≥ 1/4}`.
* Pole cancelling: `E_S(z) = ∏_{l ∈ S}(z − l)`; analytic extensions `p̃`, `q̃` of `E²℘`, `Eζ`
  to `(Λ ∖ S)ᶜ` by a removable-singularity lemma with explicit local representatives
  (`℘ = ℘Except_s + 1/(z−s)² − 1/s²`); `ψ̃ = ∑ c_λ (2z)^λ₀ p̃^λ₁ (2q̃)^λ₂ E^(3L − 2λ₁ − λ₂)`.
* Schwarz lemma on a bounded open set (generalize `Feldman/Hermite.lean`); zeros of order `N`
  from `iteratedDeriv` (`natCast_le_analyticOrderAt…`).
* No inner induction on the order: Cauchy's estimate for `Φ` itself on `|z − w| = 1/4`, with
  `|E(z)| ≥ 4^(−|S|)` there.  Result:
  `|Φ⁽ⁿ⁾(w)| ≤ n! 4ⁿ (16K+8)^(3L(2K+1)²) L³ A₀ (C₃(K+1)²)^L (24H′/K)^(N H²)`, `K = 24H′k`.
* Arithmetic: `Rep` predicate (value `= A(ϖ,e) + τB(ϖ,e)` with sizes), closed under `+`, `×`;
  values `Φ⁽ⁿ⁾(w_h) = aeval (pt w_h) ((dD c)ⁿ Q)`; Dirichlet start (`dirichlet_box_finset`)
  with `U = L³J ≥ c·F·T₀(size T₀)³`, `F = 2N₀H₀²`; stages `N = k¹⁶`, `H = k¹⁰`.
* F6 at the end: `Φ ≡ 0` near `1/2` ⟹ all `c_λ = 0` ⟹ all `a(λ, j) = 0` (`ϖ` transcendental).
* Abstract setting `CMData`: `τ` with `|τ| = 1`, `|Re τ| ≤ 1/2`, `τ² = pτ − q`,
  `η(τ) = (u + vτ)η(1)`, `g₂ = 2ce²`.

## STATUS 2026-11-19 (night): the core is PROVEN

`Chudnovsky/Theorem.lean`: **`CMData.ev2_ne_zero`** (for a CM lattice as in `CMData`, a
Fel'dman-type measure for `ϖ = η(1)` implies that `ϖ` and `e = ℘(1/2)` are algebraically
independent) and **`chudnovsky_rho`** (the instance `ℤ[ρ]`: `2π/√3` and `℘(1/2)`), by plan B′:
`Schwarz`, `Bounds`, `AuxFunction` (analysis), `Rep`, `Start`, `Independence` (arithmetic,
Dirichlet start, independence of `z, ℘, ζ`), `Core` (stages `N = 2^(16s)`, `H = 2^(10s)`,
`K = 2^(11s+14)`; structure `Params`), `Parameters` (`exists_params`).

Remaining (F7 and consequences):

1. `ℤ[i]`: the instance needs `g₂ = 4e₁²`, i.e. `e₁ ≠ 0`.  Plan: mean value of `℘` on
   `Re z = 1/2` is `π > 0` and `℘′² ≤ 0` there, so `g₂ ≥ 4π² > 0`; on the real axis
   `℘(4℘² − g₂) = ℘′² ≥ 0`, `℘ → +∞` at `0`, so `℘ ≥ √g₂/2` on `(0, 1)` by connectedness.
2. Periods as Gamma values: `1/2 = ∫_{e₁}^∞ dt/√(4t³ − g₂t − g₃)` (monotone substitution on
   `(0, 1/2]`), evaluated with `Transcendental/GammaAGM.lean`:
   `e₁(ℤ[i]) = Γ(1/4)⁴/(8π)`, `e₁(ℤ[ρ]) = Γ(1/3)⁶/(2^(8/3)π²)` (sign of `e₁(ℤ[ρ])` first).
3. Corollaries: `π, Γ(1/4)` and `π, Γ(1/3)` algebraically independent; irrationality of the
   `Γ` values at rationals with denominators 2, 3, 4, 6; then fuel-free `zivLoopCertified`
   paths in `AzFloat/Gamma*.lean` and the unconditional theorems in `Equiv/Gamma.lean`.

## F7: detailed plan (2026-11-19)

**Algebraic layer** (`AlgOver ϖ x`: `x` is a root of a nonzero polynomial over `ℤ[X]` acting on
`ℂ` through `X ↦ ϖ`, i.e. `IsAlgebraic ℤ[X] x` for the algebra structure `(evX ϖ).toAlgebra`;
Mathlib's `IsAlgebraic.mul/.pow/.of_mul/.of_pow` hold over a domain).  `CMData.ev2_ne_zero` says
`¬AlgOver ϖ e`.  For the Gamma values only explicit polynomials are then needed
(e.g. `Γ(3/4) = r` gives `r²G² = 2π²`).

**Real analysis** (one generic lemma, used three times).  Let `f` on `(0, ℓ]` be real with
`f′ = q`, `q² = 4f³ − a f − b`, `f → +∞` at `0⁺`, `f(ℓ) = e`, `4t³ − at − b > 0` for `t > e`,
`f ≥ e`, and `f` not constant on any interval.  Then `f > e` on `(0, ℓ)` (an interior maximum
would be a zero of the cubic), `q < 0` there, `f` is strictly decreasing with image `(e, ∞)`,
and by `integral_image_eq_integral_abs_deriv_smul`:
`∫_{t > e} dt/√(4t³ − at − b) = ℓ`.

* `ℤ[i]` (`g₃ = 0`): on `Re z = 1/2` the function `g(y) = ℘(1/2 + iy)` is real with mean `π`
  (`integral_weierstrassP_segment`, `η(i) = −iπ`) and `℘′² ≤ 0` there (`℘′` is purely
  imaginary: `conj ℘′(z) = ℘′(1 − z) = −℘′(z)`), so `g₂` is real and `≥ 4π²`.  On the real
  axis `p(4p² − g₂) = ℘′² ≥ 0` and `p → +∞` at `0`, so `p ≥ √g₂/2` on `(0, 1)` by
  connectedness; `e₁ ∈ {0, ±√g₂/2}` gives `e₁ = √g₂/2 > 0`, **`g₂ = 4e₁²`** (the missing field
  of the `ℤ[i]` instance).  Generic lemma with `ℓ = 1/2`: `∫_{t > e₁} dt/√(4t³ − 4e₁²t) = 1/2`;
  `t = e₁(1 + s²)` gives `e₁^(−1/2) ∫₀^∞ agmKernel 1 √2 = 1/2`, so
  `√e₁ = π/AGM(1, √2)` and **`e₁ = Γ(1/4)⁴/(8π)`** (`gamma_one_quarter_sq`).
* `ℤ[ρ]` (`g₂ = 0`, `g₃ = 4e₁³`, `e₁ ≠ 0` by `chudnovsky_rho`): `I₊ = ∫₁^∞ du/√(u³ − 1)
  = 2∫₀^∞ quarticKernel (3/2) √3 = π/AGM(…) = Γ(1/3)³/(2·2^(1/3)·π)` (`gamma_one_third_cube`).
  If `e₁ > 0`: real axis, `ℓ = 1/2`, `e₁ = I₊²`.  If `e₁ < 0`: the segment from `1/2` to the
  pole `1 + ρ = 1/2 + i√3/2`, with `f(x) = −℘(1/2 + i(√3/2 − x))`, `ℓ = √3/2`, `e = −e₁`:
  `−e₁ = I₊²/3`.  In both cases **`e₁³ = c Γ(1/3)¹⁸/(2⁸π⁶)`, `c ∈ {1, −1/27}`** — enough for
  the algebraic independence of `π` and `Γ(1/3)`; the sign of `e₁` is not needed.

**Consequences**: `π, Γ(1/4)` and `π, Γ(1/3)` algebraically independent (`¬AlgOver`);
irrationality of `Γ(q)`, `q ∉ ℤ` with denominator 2, 3, 4, 6 (reflection and duplication
formulas, recurrence); fuel-free `Γ` in AzFloat for those arguments.

**2026-11-19 (late): `Γ(1/3)` DONE.**  `Chudnovsky/{AlgOver,HalfPeriod,AxisODE,PeriodRho,
GammaThird}.lean`: `not_algOver_gamma_one_third`, `irrational_gamma_one_third`.  Next: the
other values of the `ℤ[ρ]` family (`Γ(2/3)`, `Γ(1/6)`, `Γ(5/6)`: reflection and duplication,
with the `AlgOver` calculus), then `ℤ[i]` (the field `hg` of its `CMData` instance and
`e₁ = Γ(1/4)⁴/(8π)`), then the AzFloat side.

**2026-11-19 (final math): ALL GAMMA COROLLARIES DONE.**  `Chudnovsky/PeriodI.lean`
(`g₂_latI`, `iE_eq`) and `Chudnovsky/GammaValues.lean`: `cmI`, `not_algOver_gamma_one_quarter`,
`not_algOver_gamma_three_quarters`, `not_algOver_gamma_two_thirds`,
`not_algOver_gamma_one_sixth`, `not_algOver_gamma_five_sixths`, `irrational_gamma_one_half`,
**`irrational_gamma_of_den`** (`Γ(q)` irrational for every rational `q` with denominator
2, 3, 4, 6).  Remaining: the AzFloat side (fuel-free `Γ` at these arguments and the
unconditional correctness theorems).

**AzFloat side: DONE 2026-11-19.**  The widths of the Stirling bracket of `ln Γ` and of the
pieces of `Γ` are proven (`AzFloat/Equiv/EnclWidth.lean`, `Equiv/LnGammaWidth.lean`,
`Equiv/LnGammaEventually.lean`, `Equiv/GammaWidth.lean`, `Equiv/GammaRatBracket.lean`,
`Transcendental/StirlingTermBound.lean`); with `irrational_gamma_of_den` they give the Ziv
certificates `gammaApprox_cert` and `gammaRatApprox_cert` (`Equiv/GammaCertificate.lean`).
`gammaPrecRound` / `reciprocalGammaPrecRound` at the floats `n/4` that are not integers and
`gammaRatPrecRound` / `reciprocalGammaRatPrecRound` at the denominators `2, 3, 4, 6` run
without fuel, and are correctly rounded unconditionally: `gammaPrecRound_eq_of_special`,
`reciprocalGammaPrecRound_eq_of_special` (`Equiv/Gamma.lean`),
`gammaRatPrecRound_eq_of_special`, `reciprocalGammaRatPrecRound_eq_of_special`
(`Equiv/GammaRat.lean`).  See `docs/azfloat_plan.md`, "No fuel at the denominators".

**The constants themselves (2026-11-19).**  The enclosures of `Γ(1/4)` and `Γ(1/3)` converge
(`gammaOneQuarterEncl_conv`, `gammaOneThirdEncl_conv`, `AzFloat/Equiv/AgmConstants.lean`, by
the width of the interval AGM, `Equiv/AgmWidth.lean`, and the calculus of convergent
enclosures, `Equiv/EnclConv.lean`), so `gammaOneQuarterPrecRound` and `gammaOneThirdPrecRound`
have Ziv certificates and unconditional specifications (`gammaOneQuarterPrecRound_eq`,
`gammaOneThirdPrecRound_eq`).  Two more consequences of `not_algOver_gamma_one_quarter`:
Gauss's constant `1/AGM(1, √2) = Γ(1/4)²/(2π √(2π))` and the lemniscate constant are
irrational (`irrational_gauss`, `irrational_lemniscate`), and their rounded functions are free
of fuel too.  M7 is complete.

**Beta values (2026-11-19).**  `Azurite/Chudnovsky/BetaValues.lean`: for rational `a`, `b`
that are not integers, `B(a, b)` is irrational when `a + b` is a positive integer (`π` over
an algebraic sine) and when `a + b` is not an integer and the denominators both divide `4` or
both divide `6` (`irrational_beta_of_den`).  Each `Γ(N/4)` is `Γ(1/4)^d` and each `Γ(N/6)` is
`Γ(1/3)^d` up to a nonzero number algebraic over `ℤ[π]` (`GDeg`, `gdeg_gamma_div_four`,
`gdeg_gamma_div_six`), and the degree of the Beta value is `±2`, resp. `±3`.  `betaPrecRound`
and `betaRatPrecRound` run certified loops there.  See `docs/azfloat_plan.md`, item 10 of the
second round.

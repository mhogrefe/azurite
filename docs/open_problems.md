# Open problems whose resolution would benefit Azurite

Started 2026-11-23.  A correctly rounded function needs no fuel when its value is known **not to
be a dyadic rational** (a rounding boundary at precision `p` is one).  Irrationality is the usual
way to know that, but it is more than is needed: for every item below the weaker statement
"the value is not in `ℤ[1/2]`" would already remove the fuel.  Each entry names the functions
that are still on fuel (their `ZivSpec` has the argument outside its `N` set) and what a proof
would have to deliver.  Statuses are to the best of my knowledge and should be checked against
the literature before work starts.

## 1. Irrationality: genuinely open

| # | Statement (enough: "not dyadic") | Removes the fuel in | Notes |
|---|---|---|---|
| 1.1 | `γ` (Euler's constant) is irrational | `eulerGamma`; then, with 2.2, `ψ` at every rational | The classic.  Known: a rational `γ` has an astronomically large denominator (continued fraction), nothing more. |
| 1.2 | `ln A` / `A` (Glaisher–Kinkelin) is irrational; equivalently `ζ′(−1)`, or `ζ′(2)/π²` given 1.1 and 1.3 | `glaisherKinkelin` | `ln A = 1/12 − ζ′(−1)`. |
| 1.3 | `ln π` is irrational | `lnGamma` at half-integers (`ln Γ(1/2) = ½ ln π`), `lnAbsGamma`, `lnBeta` at such arguments | Open although `π` is transcendental; follows from Schanuel. |
| 1.4 | `Γ(a/q)` is irrational for a denominator `q ∉ {1, 2, 3, 4, 6}` | `gamma`, `reciprocalGamma`, `gammaRat` there; for floats this is every argument `k/8`, `k/16`, … | First cases `Γ(1/5)`, `Γ(1/8)`.  Known for `q = 5`: two of `π, Γ(1/5), Γ(2/5)` are algebraically independent, which does not settle `Γ(1/5)` alone.  The general statement is part of the Rohrlich–Lang conjecture. |
| 1.5 | `B(a, b)` is irrational off the cases of `betaRatSpecial` | `beta`, `betaRat`, `betaFloatRat` | Known transcendental when `a`, `b`, `a + b` are rational non-integers (Schneider, see 2.3) — so only the cases with `a + b ∈ ℤ` excluded there and the integer-sum degenerations are truly open; most of this row is in fact §2. |
| 1.6 | `Γ(x + y)/Γ(x)` and the Pochhammer family at non-integer `y` | `genPochhammer`, `genPochhammerRat`, falling factorials | Reduces to 1.4/1.5 in the rational case. |
| 1.7 | `ψ(a/q)` is irrational | `digamma`, `digammaRat` | By Gauss's formula `ψ(a/q) = −γ − (elementary terms)`; needs 1.1 and 2.2.  Known: `ψ(a/q) + γ` is transcendental (2.2). |
| 1.8 | `ψ⁽ⁿ⁾(a/q)` for even `n ≥ 2`, and for odd `n` off the certified cases | `polygamma`, `polygammaRat` | Even `n` at `q ≤ 2`: `ζ(n + 1)` — `ζ(3)` is known (Apéry), `ζ(5)` is open.  Odd `n` at `q = 4`: e.g. `ψ′(1/4) = π² + 8G` needs the linear independence of `1, π², G`, more than the irrationality of Catalan's `G`. |
| 1.9 | The zeros `xₙ` of `ψ` are irrational; `Γ(xₙ)` is irrational | `psiZero`, `gammaExtremum` | Nothing known, to my knowledge. |
| 1.10 | `G(a/q)` (Barnes) is irrational at a non-integer | `barnesG`, `barnesGRat` | `G(1/2) = 2^(1/24) e^(1/8) π^(−1/4) A^(−3/2)`: needs 1.2 and more.  `G(1/4)` also involves Catalan's constant and `Γ(1/4)`. |
| 1.11 | `ln Γ(a/q)` is irrational | `lnGamma`, `lnGammaRat` | Follows from the transcendence of `Γ(a/q)` only via a statement of Schanuel type. |
| 1.12 | `Γ_q(x)` is not dyadic for a rational (or dyadic) base `q ≠ 1` and a rational non-integer `x` | `qGamma`, `qGammaRat`, `qGammaFloatRat`, `qGammaRatFloat` | `Γ_q(x) = (1 − q)^(1−x) (q; q)_∞/(q^x; q)_∞`.  For a rational `q = 1/b` the values `(q; q)_∞` are of the kind covered by Nesterenko's theorem on modular functions (`η` at algebraic nome is transcendental), but the quotient with `(q^x; q)_∞` and the algebraic factor is not; irrationality results for `q`-series (Borwein, Bézivin, Bundschuh–Väänänen) treat `q`-logarithms and `q`-exponentials at `q = 1/b`, not this quotient, to my knowledge.  At a positive integer `x` the value is a known rational (exact above a size bound it goes through the loop: there one would want "the `q`-factorial is no `p + 1`-bit number", an elementary statement about its odd part). |
| 1.13 | `ln \|Γ_q(x)\|` is not dyadic for a rational (or dyadic) base `q ≠ 1` and a rational `x` that is no integer, and at the integers `n ≥ 3` beyond the size bound of the exact `q`-factorials | `lnAbsQGamma`, `lnQGamma` and their `Rat`, `FloatRat`, `RatFloat` variants | At an integer `n ≥ 3` the value is `ln` of a rational above `1`, irrational by Lindemann (formalized: `irrational_log_rat`), and the functions are fuel-free there as long as the `q`-factorial is formed; lifting the size bound only needs the bracket to certify "the value is not `0`", an engineering matter, not an open problem.  At a non-integer `x` the statement is of Schanuel type on top of 1.12, as 1.11 is on top of 1.4.  The one exceptional kind of point: a non-integer `x < 0` with `\|Γ_q(x)\| = 1` (they exist between the poles) has the dyadic value `0`; such `x` are presumably never rational, a statement of the kind of 1.9. |
| 1.14 | `B_q(a, b)` is not dyadic for a rational (or dyadic) base `q ≠ 1` and rational `a`, `b` off the integers and off the zeros and poles | `qBeta` and its five variants (`qBetaRat`, `qBetaFloatFloatRat`, …) | `B_q(a, b) = (1 − q) (q; q)_∞ (q^(a+b); q)_∞ / ((q^a; q)_∞ (q^b; q)_∞)`.  **Not true without exceptions**: for a positive integer `a = n` the value is `Γ_q(n) (1 − q)^n / ∏_{k<n} (1 − q^(b+k))`, algebraic in `q^b`, and it is rational where `q^b` is (`B_{1/4}(1, 1/2) = 3/2`).  So the statement to prove has two parts: (i) an elementary one — for an integer argument, decide when that algebraic number is dyadic (this would let the function answer without fuel there: a closed-form path, not written); (ii) off the integers, a statement about quotients of `q`-Pochhammer values of the kind of 1.12, open to my knowledge.  As for `B` (1.5), a classical transcendence theorem may cover part of (ii): `q`-analogues of Schneider's theorem on `B(a, b)` are not known to me. |
| 1.15 | `ln \|B_q(a, b)\|` is not dyadic for a rational (or dyadic) base `q ≠ 1` and rational `a`, `b` off the integers, the zeros and the poles | `lnAbsQBeta`, `lnQBeta` and their five variants each | At positive integers the value is `ln` of a positive rational, irrational unless that rational is `1` (formalized; the functions are fuel-free there while the rational is formed).  For an integer argument `n` and a rational `b` the value is `ln` of an algebraic number (see 1.14): irrational by Lindemann–Weierstrass unless that number is `1` — a known theorem in its general form (`ln` of an algebraic number `≠ 0, 1` is transcendental), **not formalized here beyond rationals**; it belongs in §2.  Off the integers: a statement of Schanuel type on top of 1.14.  Exceptional points with `\|B_q(a, b)\| = 1` (value `0`) exist on curves in the `(a, b)` plane; whether rational points lie on them is of the kind of 1.9. |

## 2. Known theorems that are not formalized

These are not open, but each is the missing step for some fuel, and a formalization is the same
kind of work as a new proof.

| # | Theorem | Removes the fuel in | Notes |
|---|---|---|---|
| 2.1 | Schneider (1937): a nonzero period `ω` of an elliptic curve with algebraic invariants is transcendental, and so is `ω/π` | the general `agm`, `agmRat`, `agmFloatRat` (`AGM(1, b) = π / (2 K(k′))`) | Only the lemniscatic case is in (through Chudnovsky).  See the memory note on AGM transcendence. |
| 2.2 | Baker's theorem on linear forms in logarithms | `ψ(a/q) + γ` transcendental (Murty–Saradha); with 1.1 this is 1.7 | The quadratic Gelfond–Schneider case is formalized; Baker is the general tool. |
| 2.3 | Schneider (1941): `B(a, b)` is transcendental for rational `a`, `b`, `a + b` not integers | `beta`, `betaRat` at all such arguments | Would replace the Chudnovsky-only list of `betaRatSpecial`. |
| 2.4 | Gelfond–Schneider in general (beyond the quadratic case) | nothing on fuel at present | For completeness; needed if `pow` ever takes algebraic irrational arguments. |
| 2.5 | Nesterenko (1996): `π`, `e^π`, `Γ(1/4)` are algebraically independent | nothing on fuel at present | Would give mixed values such as `Γ(1/4) e^π`. |
| 2.6 | Lindemann–Weierstrass (or just Lindemann's theorem for algebraic arguments): `ln α` is transcendental for an algebraic `α ≠ 0, 1` | `lnAbsQBeta`/`lnQBeta` at an integer argument (1.15), once a closed-form path for an integer argument exists; `lnAbsQGamma` nowhere new | Only the rational case (`irrational_log_rat`) is formalized. |

## 3. Not irrationality, to be extended

* **Worst-case precision** (the table maker's dilemma): an effective bound on how close a value
  can be to a `p`-bit rounding boundary would replace the Ziv loop by one evaluation at a known
  precision, for every function at once.  The known effective measures (Baker type) are far too
  weak to be useful; a bound of `p + O(log p)` extra bits is conjectured on probabilistic
  grounds.
* Constants and functions not yet in Azurite whose arithmetic nature is open (`ζ(5)`, `ζ(3)`
  beyond irrationality, Khinchin's constant, …) belong here when they are implemented.

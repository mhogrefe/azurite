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

## 3. Not irrationality, to be extended

* **Worst-case precision** (the table maker's dilemma): an effective bound on how close a value
  can be to a `p`-bit rounding boundary would replace the Ziv loop by one evaluation at a known
  precision, for every function at once.  The known effective measures (Baker type) are far too
  weak to be useful; a bound of `p + O(log p)` extra bits is conjectured on probabilistic
  grounds.
* Constants and functions not yet in Azurite whose arithmetic nature is open (`ζ(5)`, `ζ(3)`
  beyond irrationality, Khinchin's constant, …) belong here when they are implemented.

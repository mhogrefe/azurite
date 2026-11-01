# DLMF errata found during formalization

Discrepancies between the NIST Digital Library of Mathematical Functions and what is provable,
found while formalizing DLMF in `Azurite/DLMF/`. Every entry is backed by a Lean theorem; the
theorem names are given, and each proof uses only the axioms `propext`, `Classical.choice`,
`Quot.sound`.

There are two kinds of entry:

* **Errors**: the statement as printed is false, and a Lean counterexample (or a corrected
  statement together with a proof that the printed one fails) exists.
* **Imprecisions**: the statement is right in substance but omits a hypothesis, a degenerate
  case, or a convention needed to make it literally true.

The per-equation ledger is `docs/dlmf_plan.md`.

## Chapter 1

### Errors

| DLMF | DLMF states | What is true | Lean |
| --- | --- | --- | --- |
| Table 1.14.2, row 4 | `𝓕_c[4a³/(4a⁴ + t⁴)](x) = √π e^{−ax} sin(ax + π/4)` for `ℜa > 0` | Needs `\|ph a\| < π/4` (equivalently `\|ℑa\| < ℜa`). For `a = e^{iπ/4}` the denominator vanishes at `t = √2` and the integral diverges | `dlmf_table_1_14_2_r4` (`Section14TableCos.lean`) |
| Table 1.14.2, row 10 | the logarithmic row with `ln` of a quotient, for `ℜa, ℜb > 0` | The literal `ln(quotient)` form needs `\|ph a\|, \|ph b\| < π/4`; for `ℜa, ℜb > 0` the right form is `ln(a² + t²) − ln(b² + t²)` | `dlmf_table_1_14_2_r10`, `dlmf_table_1_14_2_r10_sub` (`Section14TableCosLog.lean`) |
| Table 1.14.3, row 12 | sine transform of `arctan(t/a)` | The integral diverges, even as an improper integral `lim_{R→∞} ∫_0^R`; DLMF's value is the Abel limit `ε → 0+` of `∫ e^{−εt} …` | `dlmf_table_1_14_3_r12_not_tendsto` (divergence), `dlmf_table_1_14_3_r12` (Abel form) (`Section14TableSinArctan.lean`) |
| Table 1.14.4, row 14 | Laplace transform of `2(1 − cosh(at))/t` for `ℜ(s + a) > 0` | The condition is insufficient: for `a = 1`, `s = 1/2` the integrand is not integrable. Holds for `ℜs > \|ℜa\|` | `dlmf_table_1_14_4_r14_condition` (counterexample), `dlmf_table_1_14_4_r14` (`Section14TableLaplaceLog.lean`) |
| 1.14.45 | `∫ \|ℋf\|^p ≤ A_p ∫ \|f\|^p` | The constant is `A_p^p` (Pichorides' `A_p = tan(π/2p)` for `1 < p ≤ 2`, `cot(π/2p)` for `p ≥ 2` is the operator norm); proved for all `p > 1` with the sharp constant | `dlmf_1_14_45` (`Section14HilbertLp.lean`; arc ledger `docs/hilbert_lp_plan.md`) |
| §1.15(ii) | all summability methods of §1.15(i), including `(C,α)` for every `α > −1`, are regular | `(C,α)` is not regular for `−1 < α < 0`: a sparse positive convergent series has unbounded `(C,α)` means | `dlmf_1_15_ii_cesaroGen_not_regular` (`Section15.lean`) |
| 1.15.40 | `ℑΦ(x + iy) → ℋf(x)` as `y → 0+` | The limit is `−ℋf(x)` under DLMF's own definition 1.14.41–1.14.42 (1.15.40's kernel is `(x − t)/…`, 1.14.41's is `(t − x)/…`) | `dlmf_1_15_40_hilbert` (`Section15FourierIntegrals.lean`) |
| 1.15.53 | `D^α D^β f = D^{α+β} f` under the stated proviso | False without further hypotheses on `f`: `α = 1/3`, `β = 3/2`, `f(t) = t^{1/2}` gives `D^β f = 0` but `D^{α+β} f ≠ 0` | `dlmf_1_15_53_counterexample`; corrected `dlmf_1_15_53` (`f = I^γ g`, `ℜγ > ℜ(α + β)`) (`Section15FractionalDeriv.lean`) |
| §1.16(i), 1.16.1–1.16.2 | convergence `φₙ → φ` in `𝒟(I)` as uniform convergence of all derivatives | With no condition `supp φₙ ⊆ K` (a fixed compact), `0 → φ` for every `φ`, so the only "distribution" is `0`. The standard definition adds the support condition | `testConvergesDLMF_zero`, `dlmf_1_16_2_literal`; corrected `TestConverges` (`Section16.lean`) |
| §1.16(vi) | the same definition on `ℝⁿ` | Same defect for `n ≥ 1` | `testConvergesNDLMF_zero`, `dlmf_1_16_vi_literal` (`Section16Several.lean`) |
| 1.17.19–1.17.20 | `∫_{−π}^{π} δₙ(x − a) φ(x) dx → φ(a)` for continuous `2π`-periodic `φ` | False: these are Fourier partial sums, and Banach–Steinhaus (Lebesgue constants `Lₙ ∼ (4/π²) ln n`) gives a continuous periodic `φ` where they diverge at `a = 0`. True under the 1.8.11 conditions or differentiability at `a` | `dlmf_1_17_19_counterexample`; `dlmf_1_17_19`, `dlmf_1_17_19_dirichlet` (`Section17Series.lean`) |
| §1.18(iii) | `T = d²/dx²` on Dirichlet `C²` functions of `[a, b]` has `𝒟(T*) = 𝒟(T)`, "thus `T` is indeed self adjoint" | `T` is symmetric but not self-adjoint: a `C¹` function with a jump in its second derivative lies in `𝒟(T*)` but not `𝒟(T)`. The self-adjoint operator is the closure (domain `H² ∩ H¹₀`) | `dlmf_1_18_iii_not_selfAdjoint` (`Section18DiffOp.lean`) |
| 1.18.54 | the Sokhotski–Plemelj formula for `f ∈ C(X)` | Continuity is not enough for the integrals to exist (`f = 1` on `[0, ∞)`). Needs integrability of `f` and existence of the principal value at `x` | `dlmf_1_18_54_counterexample`; `dlmf_1_18_54` (`Section18Plemelj.lean`) |
| §1.18(ix), boundary conditions | any self-adjoint extension of `ℒ` is obtained by restricting `ℒ*` to `B₁(f) = 0` (if `n₁ = 2`), `B₂(f) = 0` (if `n₂ = 2`), with `B₁` a boundary value at `a` and `B₂` one at `b` | False when both ends are limit circle. Dunford–Schwartz Cor. XIII.2.31 has the qualifier "if the boundary conditions are separated". Counterexample: `q = 0` on `(0, 1)` has a self-adjoint extension containing `e^{2πix}` but not its cut-off near `0`, which separated conditions would force. True when at most one end is limit circle | `dlmf_1_18_ix_ext_LC_LC_counterexample` (`Section18WeylCounter.lean`); `dlmf_1_18_ix_ext_LP_LP`, `dlmf_1_18_ix_ext_LC_LP`, `dlmf_1_18_ix_ext_LP_LC` (`Section18WeylExt.lean`) |

### Imprecisions

| DLMF | Issue | Lean |
| --- | --- | --- |
| §1.7(i), Cauchy–Schwarz, Hölder, Minkowski equality cases | The equality conditions ("iff `aⱼ = c bⱼ`") miss the degenerate case `b = 0` | `dlmf_1_7_1_eq_iff`, `dlmf_1_7_2_eq_iff`, `dlmf_1_7_3_eq_iff` (with `b = 0`); `_eq_iff_of_ne` versions keep DLMF's wording under `b ≠ 0` (`Section7.lean`) |
| 1.17.9 | The inner integral `∫ e^{i(x−a)t} dt` does not converge; the formula is only formal | `dlmf_1_17_9_not_integrable`; `dlmf_1_17_9` (generalized integral under the 1.17.6 hypotheses) (`Section17Integral.lean`) |
| §1.18(viii), Simon's bound-state theorem | DLMF omits Simon's decay hypothesis on the potential; the formalization assumes compact support | `dlmf_1_18_viii_simon` (`Section18Simon.lean`) |
| 1.18.67 | The measure `r² dr` belongs to `R = u/r`, not to the `u` of 1.18.67 (whose measure is `dr`) | `dlmf_1_18_67` (`Section18Radial3D.lean`) |
| §1.18(ix), von Neumann extensions | The isometry `U : N_i → N_{−i}` must be onto for `A_U` to be self-adjoint, and `n₊ = n₋` must mean equal Hilbert dimension | `vonNeumannExt_isSelfAdjoint_iff`, `exists_selfAdjoint_ext_iff` (`Section18VonNeumann.lean`) |

## Chapter 2

### Imprecisions

| DLMF | Issue | Lean |
| --- | --- | --- |
| 2.1.10 | DLMF says both relations `o(φ) = O(φ)` and `o(φ) + o(φ) = o(φ)` "are not reversible" (`=` meaning `⊆`). The first is not (`O(φ) ⊄ o(φ)`), but the second is: `o(φ) ⊆ o(φ) + o(φ)` (`f = f + 0`), so it holds as an equality of classes | `dlmf_2_1_10_1_not_reversible`, `dlmf_2_1_10_2_reverse`, `dlmf_2_1_10_2_eq` (`Chapter2/Section1.lean`) |
| §2.2, 2.2.1–2.2.2 | `f` is assumed continuous only for `a < x < ∞`, but the conclusion is stated for `y > f(a)`. Continuity at `a` (from the right) is needed: `f = x` on `(0, ∞)` with `f(0) = −1` has no root for `y = −½` | `dlmf_2_2_1_counterexample`; `rootDLMF_spec` (with continuity on `[a, ∞)`) (`Chapter2/Section2.lean`) |

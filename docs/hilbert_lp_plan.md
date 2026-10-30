# DLMF 1.14.45: the Hilbert transform on `L^p` (Riesz–Pichorides)

Goal (DLMF 1.14.45, corrected constant): for `1 < p < ∞` and real `f` with `|f|^p` integrable,
`ℋf(x)` exists for almost every `x`, `|ℋf|^p` is integrable, and
`∫ |ℋf|^p ≤ A_p^p ∫ |f|^p`, with `A_p = tan(π/2p)` for `1 < p ≤ 2` and `cot(π/2p)` for `p ≥ 2`.
DLMF prints `A_p` where `A_p^p` is meant (Pichorides' `A_p` is the operator norm, and it is sharp).

The route avoids maximal functions: the sharp bound is proved on a dense class through a smooth
subharmonic function and Green's identity, extended by density, and the principal value is shown
to exist almost everywhere using Lebesgue points only.

| # | Milestone | File | Status |
|---|---|---|---|
| M1 | Pichorides' inequality `|b|^p ≤ A_p^p |a|^p − B_p Re((|a| + ib)^p)` for `1 < p ≤ 2` | `Section14HilbertPichorides.lean` | DONE (`pichorides_trig`, `pichorides_ineq`) |
| M2 | Smooth subharmonic `Ψ_δ(w) = Re((√(a² + δ²) + ib)^p) − δ^p`, `O(|w|²)` at `0`, `|Ψ_δ| ≤ C|w|^p` | `Section14HilbertSubharmonic.lean` | DONE (`psiD_subharmonic`, `exists_psiD_bound`, `tendsto_psiD`) |
| M3 | Green with weight `y` on rectangles: `∫_ℝ Ψ(F(x)) dx ≥ 0` for holomorphic `F = O(1/z)` | `Section14HilbertGreen.lean` | DONE (`integral_comp_nonneg`) |
| M4 | Core bound `∫ |Im F|^p ≤ A_p^p ∫ |Re F|^p` on `ℝ`, `1 < p ≤ 2` | `Section14HilbertCore.lean` | DONE (`integral_im_rpow_le`) |
| M5 | Dense class `P_b ∗ g` (`g` integrable, bounded support): `F` = Cauchy integral, `ℋf = Q_b ∗ g = −Im F` | `Section14HilbertDense.lean` | DONE (`hasHilbert_poissonInt`, `integral_conjPoissonInt_rpow_le`) |
| M6 | Density in `L^p`: `P_b ∗ g → g` | `Section14HilbertDensity.lean` | DONE (`exists_poissonInt_approx`) |
| M7 | `p ≥ 2` by duality (`∫ ℋf · g = −∫ f · ℋg`) | `Section14HilbertLp.lean` | DONE (`denseBound_dual`) |
| M8a | Poisson kernel at Lebesgue points: `∫ ε/(ε² + s²) |f(x+s) − f(x)| ds → 0` a.e. (layer cake, no maximal function) | `Section14HilbertLebesgue.lean` | DONE (`ae_tendsto_poissonKernel`) |
| M8b | Semigroup `P_ε(Q_b g) = Q_{ε+b} g = Q_ε(P_b g)`, antisymmetry `∫ (Q_b g)(P_c g′) = −∫ (P_b g)(Q_c g′)` (Fourier transform of `p_b`) | `Section14HilbertSemigroup.lean` | DONE |
| M8c | Two-term dense bound (differences), Cauchy sequence in `L^p`, `Q_ε f = P_ε ∗ h`, a.e. existence, 1.14.45 | `Section14HilbertExtension.lean`, `Section14HilbertLp.lean` | DONE (`hilbert_Lp_of_denseBound`, `dlmf_1_14_45`) |

**Status (2026-10-30): COMPLETE.** `dlmf_1_14_45` proves DLMF 1.14.45 for all `p > 1` with the sharp constant.

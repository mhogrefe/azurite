# DLMF Table 1.14.1 (Fourier transforms) — ledger

Transform: `dlmfFourier f x = (2π)^{−1/2} ∫ f(t) e^{ixt} dt` (`Section14.lean`).  Rows 9–10 are not
Lebesgue integrable: there the transform is the limit of `∫_{−R}^{R}`.

| Row | f(t) | F(x) | Route | File | Status |
| --- | --- | --- | --- | --- | --- |
| r1 | `1` on `|t| < a` | `√(2/π) sin(ax)/x` | `integral_exp_mul_complex` | `Section14TableFourier.lean` | DONE |
| r2 | `e^{−a|t|}` | `√(2/π) a/(a²+x²)` | `integral_exp_mul_complex_Ioi`, even split | same | DONE |
| r3 | `t e^{−a|t|}` | `√(2/π) 2iax/(a²+x²)²` | `∫₀^∞ t e^{−ct} = 1/c²` (FTC) | same | DONE |
| r4 | `|t| e^{−a|t|}` | `√(2/π)(a²−x²)/(a²+x²)²` | same | same | DONE |
| r5 | `e^{−a|t|}/|t|^{1/2}` | `(a+(a²+x²)^{1/2})^{1/2}/(a²+x²)^{1/2}` | `t = u²` + complex Gaussian; `Re √` | same | DONE |
| r6 | `sinh(at)/sinh(πt)` | `(2π)^{−1/2} sin a/(cosh x + cos a)` | geometric series + tan partial fractions (from `cot_series_rep`) | `Section14TableHyperbolic.lean` | DONE |
| r7 | `cosh(at)/cosh(πt)` | `√(2/π) cos(a/2) cosh(x/2)/(cosh x + cos a)` | from r6: `cosh(at)/cosh(πt) = (sinh((a+π)t) − sinh((a−π)t))/sinh(2πt)` | same | DONE |
| r8 | `e^{−at²}` | `(2a)^{−1/2} e^{−x²/(4a)}` | `fourierIntegral_gaussian` | `Section14TableFourier.lean` | DONE |
| r9 | `sin(at²)` | `−(2a)^{−1/2} sin(x²/(4a) − π/4)` | improper; Abel convergence + Abelian theorem with `e^{−εt²}` and the complex Gaussian | `Section14TableFresnel.lean` | DONE |
| r10 | `cos(at²)` | `(2a)^{−1/2} cos(x²/(4a) − π/4)` | same | same | DONE |

Status: COMPLETE (2026-10-30).  Row 1 at `x = 0` is `dlmf_table_1_14_1_r1_zero` (DLMF's `sin(ax)/x` read as its limit).

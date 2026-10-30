# DLMF §1.14(vi) Stieltjes transform (ledger)

DLMF assumes only that `∫₀^∞ f(t)/(s+t) dt` converges (improper, possibly conditionally), with `f`
absolutely integrable on every `[0, R]`.  Everything rests on integration by parts against the
primitive of a merely integrable function (Abel/Dirichlet).

| Step | Content | File | Status |
| --- | --- | --- | --- |
| S0 | IBP with primitive (Fubini), Abel bound, Cauchy criteria for improper integrals | `Section14StieltjesAbel.lean` | DONE |
| S1 | 1.14.47 `stieltjes`; sufficient condition (`s > 0`, `f = O(t^{-δ})`) | `Section14Stieltjes.lean` | DONE |
| S2 | convergence at one `s₀ ∈ ℂ \ (−∞,0]` ⇒ uniform on compacts of the cut plane | `Section14Stieltjes.lean` | DONE |
| S3 | analyticity; 1.14.48 derivatives | `Section14Stieltjes.lean` | DONE |
| S4 | 1.14.49 inversion (Poisson kernel at a jump, Abel tail) | `Section14StieltjesInversion.lean` | DONE |
| S5 | 1.14.50 `𝒮 = ℒℒ` (improper Laplace transforms; Abelian theorem) | `Section14StieltjesLaplace.lean` | DONE |

Status: COMPLETE (2026-10-30).  1.14.50 is stated with both Laplace integrals improper (the faithful
reading under DLMF's hypotheses); no Lebesgue-integral corollary was added.

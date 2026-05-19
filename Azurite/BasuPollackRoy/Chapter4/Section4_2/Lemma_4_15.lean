import Azurite.BasuPollackRoy.Chapter4.Section4_2.Remark_4_14
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# BPR Lemma 4.15: vanishing resultant criterion

For non-zero polynomials `P, Q : D[X]` over a domain `D` of degrees
`p, q`, the resultant `Res(P, Q)` vanishes iff there exist non-zero
polynomials `U, V : D[X]` with `natDegree U < q`, `natDegree V < p`,
and `U · P + V · Q = 0`.

BPR phrases this over the fraction field `K = Frac(D)`, but the
`D[X]`-form proved here is equivalent: clearing denominators bridges
the two (and the embedding `D ↪ K` lifts the reverse direction).

Proof strategy. Combine the matrix kernel characterization
`Matrix.exists_mulVec_eq_zero_iff` (over the domain `D`) for
`(Syl P p Q q)ᵀ` with Remark 4.14
(`Syl.transpose_mulVec_apply`): vanishing `Sylᵀ`-mulVec on `uv` is
equivalent to all coefficients of `Syl.mulMap P p Q q uv` vanishing on
`[0, p + q)`, which combined with the degree bound becomes
`Syl.mulMap = 0`. The single-sum `mulMap` factors as `U · P + V · Q`
where `U, V` are decoded from `uv` via `Syl.encodeU` / `Syl.encodeV`.
The strong `U ≠ 0 ∧ V ≠ 0` follows from domain cancellation: `V = 0`
forces `U · P = 0`, hence `U = 0` since `P ≠ 0`, contradicting
`uv ≠ 0`. The full proof is deferred.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-! ### Decoding a coordinate vector into a polynomial pair -/

/-- The polynomial `U = u_{q-1} X^{q-1} + ⋯ + u_0` decoded from the first
    `q` coordinates of `uv`, where the coordinate at position
    `k ∈ [0, q)` plays the role of `u_{q - 1 - k}`. -/
noncomputable def Syl.encodeU (p q : ℕ) (uv : Fin (p + q) → D) : D[X] :=
  ∑ k : Fin q, C (uv ⟨k.val, by have := k.isLt; omega⟩) * X ^ (q - 1 - k.val)

/-- The polynomial `V = v_{p-1} X^{p-1} + ⋯ + v_0` decoded from the last
    `p` coordinates of `uv`. -/
noncomputable def Syl.encodeV (p q : ℕ) (uv : Fin (p + q) → D) : D[X] :=
  ∑ ℓ : Fin p, C (uv ⟨q + ℓ.val, by have := ℓ.isLt; omega⟩) *
    X ^ (p - 1 - ℓ.val)

/-! ### Lemma 4.15 -/

variable [IsDomain D] [DecidableEq D]

/-- **BPR Lemma 4.15.** Over a domain `D`, the resultant `Res(P, Q)` of
    non-zero `P, Q : D[X]` (with their actual degrees) vanishes if and
    only if there exist non-zero polynomials `U, V : D[X]` with
    `U.natDegree < Q.natDegree`, `V.natDegree < P.natDegree`, and
    `U · P + V · Q = 0`.

    Forward direction (`Res = 0 ⇒ ∃`): apply
    `Matrix.exists_mulVec_eq_zero_iff` to `(Syl P p Q q)ᵀ` to obtain a
    non-trivial null vector `uv`; decode via `Syl.encodeU`,
    `Syl.encodeV` to get `(U, V)`; Remark 4.14 turns the null condition
    into `U · P + V · Q = 0`; domain cancellation upgrades
    `(U, V) ≠ (0, 0)` to `U ≠ 0 ∧ V ≠ 0` using `P, Q ≠ 0`.

    Reverse direction (`∃ ⇒ Res = 0`): encode `(U, V)` as a coordinate
    vector `uv` and run the chain in the opposite order. -/
theorem Res_eq_zero_iff (P Q : D[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    Res P P.natDegree Q Q.natDegree = 0 ↔
      ∃ U V : D[X], U ≠ 0 ∧ V ≠ 0 ∧
        U.natDegree < Q.natDegree ∧ V.natDegree < P.natDegree ∧
        U * P + V * Q = 0 := by
  sorry

end Azurite.BPR.Chapter4

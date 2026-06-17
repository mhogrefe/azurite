import Azurite.BasuPollackRoy.Chapter4.Section4_3.Theorem_4_59
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Theorem_4_34

/-!
# BPR Remark 4.60: the real-root count from subdiscriminant signs

Combining Theorem 4.59 (the signature of `Her(P, 1)` is the number of distinct real roots of
`P`) with Theorem 4.34 (`PmV` of the subdiscriminant sequence is that same count), the
signature of `Her(P, 1)` equals `PmV(sDisc(P))`. So the number of real roots of `P` — the
signature of `Her(P, 1)` — is computed from the signs of the principal minors
`sDisc_{p-k}(P)` (`k = 1, …, p`) of the symmetric matrix `Newt₀(P) = HerMatrix P 1` defining
`Her(P, 1)` (`HerMatrix_one_eq_newtMat`).
-/

namespace Azurite.BPR.Chapter4

open _root_.Polynomial
open scoped Matrix
open Azurite.BPR Azurite.BPR.Theorem2_11

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Remark 4.60.** The signature of `Her(P, 1)` — the number of distinct real roots of
`P` (Theorem 4.59) — equals `PmV(sDisc(P))`, the permanences-minus-variations of the
subdiscriminant sequence (Theorem 4.34). Hence it is read off from the signs of the
principal minors `sDisc_{p-k}(P)` of the Newton matrix `Newt₀(P)` defining `Her(P, 1)`. -/
theorem remark_4_60 (P : R[X]) (hP : P.Monic) (hp : 0 < P.natDegree) :
    Sign (quadraticForm (HerMatR P 1)) = PmV (sDiscSeq P) := by
  rw [theorem_4_59_sign P hP, ← theorem_4_34 P hp]

end Azurite.BPR.Chapter4

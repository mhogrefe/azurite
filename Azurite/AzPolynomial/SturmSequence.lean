import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Neg
import Azurite.AzPolynomial.QuoRem
import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.Parse
import Azurite.AzPolynomial.ToString

/-!
# Sturm sequence on `AzPolynomial`

A computable Sturm sequence over a computable field. Mirrors
`Azurite.BPR.sturmSequence` (BPR Chapter 2.2) and
`Azurite.BPR.SRemS` (Definition 1.7) on `Polynomial K`.

For `P : AzPolynomial K`,
`sturmSequence P n` is the `n`-th element of the signed remainder sequence
of `P` and its derivative `P'`:

- `sturmSequence P 0 = P`
- `sturmSequence P 1 = derivative P`
- `sturmSequence P (n+2) = -((sturmSequence P n).rem (sturmSequence P (n+1)))`
  whenever `sturmSequence P (n+1) ≠ 0`, otherwise `0`.

Equivalence with the noncomputable `Polynomial`-side construction is
established in `Azurite.AzPolynomial.Equiv.SturmSequence`.
-/

namespace Azurite.AzPolynomial

variable {K : Type _} [Field K] [DecidableEq K] [PolynomialDerivative K]

/-- The Sturm sequence of `P : AzPolynomial K`: the signed remainder
    sequence of `P` and its formal derivative. -/
def sturmSequence (P : AzPolynomial K) : ℕ → AzPolynomial K
  | 0 => P
  | 1 => derivative P
  | n + 2 =>
      let prev := sturmSequence P (n + 1)
      if prev = 0 then 0
      else -((sturmSequence P n).rem prev)

@[simp] theorem sturmSequence_zero (P : AzPolynomial K) :
    sturmSequence P 0 = P := rfl

@[simp] theorem sturmSequence_one (P : AzPolynomial K) :
    sturmSequence P 1 = derivative P := rfl

theorem sturmSequence_succ_succ (P : AzPolynomial K) (n : ℕ) :
    sturmSequence P (n + 2) =
      (if sturmSequence P (n + 1) = 0 then 0
       else -((sturmSequence P n).rem (sturmSequence P (n + 1)))) := rfl

end Azurite.AzPolynomial

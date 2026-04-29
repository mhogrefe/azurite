import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Neg
import Azurite.AzPolynomial.QuoRem

/-!
# Two-argument signed remainder sequence on `AzPolynomial`

The two-argument signed remainder sequence `sRemS P Q` mirrors
`Azurite.BPR.SRemS` (BPR Definition 1.7) on `Polynomial K`:

* `sRemS P Q 0 = P`
* `sRemS P Q 1 = Q`
* `sRemS P Q (n+2) = -((sRemS P Q n).rem (sRemS P Q (n+1)))` when the
  `(n+1)`-th term is nonzero, otherwise `0`.

`sturmSequence P n = sRemS P (derivative P) n` for the Sturm sequence
specialisation.
-/

namespace Azurite.AzPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- Two-argument signed remainder sequence: matches the recursion of
    `Azurite.BPR.SRemS` after `toPoly`. -/
def sRemS (P Q : AzPolynomial K) : ℕ → AzPolynomial K
  | 0 => P
  | 1 => Q
  | n + 2 =>
      let prev := sRemS P Q (n + 1)
      if prev = 0 then 0
      else -((sRemS P Q n).rem prev)

@[simp] theorem sRemS_zero (P Q : AzPolynomial K) : sRemS P Q 0 = P := rfl

@[simp] theorem sRemS_one (P Q : AzPolynomial K) : sRemS P Q 1 = Q := rfl

theorem sRemS_succ_succ (P Q : AzPolynomial K) (n : ℕ) :
    sRemS P Q (n + 2) =
      (if sRemS P Q (n + 1) = 0 then 0
       else -((sRemS P Q n).rem (sRemS P Q (n + 1)))) := rfl

/-- The first `n` terms of `sRemS P Q` packaged as a list. Mirrors
    `Azurite.BPR.SRemSList`. -/
def sRemSList (P Q : AzPolynomial K) (n : ℕ) : List (AzPolynomial K) :=
  (List.range n).map (sRemS P Q)

end Azurite.AzPolynomial

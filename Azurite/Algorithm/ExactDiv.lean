/-
  Typeclass `ExactDiv D` for types with computable exact division.

  Semantics: when `b ∣ a` (`b` divides `a`) and `b ≠ 0`, `ExactDiv.exactDiv
  a b` is the unique `c : D` such that `b * c = a`. The lawfulness field
  `exactDiv_mul_self` bundles the operation and its specification in one
  typeclass, so that any consumer (e.g., the `bareissDet` correctness
  proof) gets both at once. The behavior on non-divisible inputs is
  unspecified — implementations typically return zero or garbage.

  Designed for fraction-free algorithms (BPR Algorithm 8.16 and friends),
  where exactness of each division is guaranteed by an external invariant
  (a determinant identity, in BPR's case).

  Instances:
  * `Field K` — uses field division `a / b`.
  * `AzInt` (in `Azurite.AzInt.ExactDiv`) — uses `AzInt.div`.
  * `AzPolynomial R` over a domain with `ExactDiv R`
    (in `Azurite.AzPolynomial.Equiv.ExactDiv`).
  * `AzMvPolynomial n R ord` over a domain with `ExactDiv R`
    (in `Azurite.AzMvPolynomial.Equiv.ExactDivCR`).
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Divisibility.Basic

namespace Azurite

/-- `ExactDiv D` bundles a computable exact-division operation with the
    specification that, when `b ∣ a` and `b ≠ 0`, it recovers the unique
    quotient `c` with `c * b = a`. -/
class ExactDiv (D : Type _) [CommRing D] where
  /-- Exact division: returns `c` with `c * b = a` when `b ∣ a` and `b ≠ 0`. -/
  exactDiv : D → D → D
  /-- When `b ∣ a` and `b ≠ 0`, `exactDiv` recovers the true quotient. -/
  exactDiv_mul_self : ∀ a b : D, b ∣ a → b ≠ 0 → exactDiv a b * b = a

namespace ExactDiv
scoped infixl:70 " /ₑ " => Azurite.ExactDiv.exactDiv
end ExactDiv

/-- Default instance for any `Field`: exact division is field division. -/
instance (priority := 100) instExactDivField {K : Type _} [Field K] :
    Azurite.ExactDiv K where
  exactDiv a b := a / b
  exactDiv_mul_self _ _ _ hb := div_mul_cancel₀ _ hb

end Azurite

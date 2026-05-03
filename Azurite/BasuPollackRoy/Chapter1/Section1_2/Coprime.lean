import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd

/-!
# Section 1.2: Coprime polynomials

$P$ and $Q$ in $K[X]$ are *coprime* if every greatest common divisor
of $P$ and $Q$ is a unit, i.e. a nonzero element of $K$.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- BPR Definition: P and Q are coprime if their GCD is a nonzero element of K
    (equivalently, a unit in K[X]). -/
def AreCoprime (P Q : K[X]) : Prop :=
  ∀ G : K[X], IsGCD G P Q → IsUnit G

/-- `AreCoprime` is equivalent to Mathlib's `IsCoprime`. -/
theorem areCoprime_iff_isCoprime (P Q : K[X]) :
    AreCoprime P Q ↔ IsCoprime P Q := by
  constructor
  · intro h
    exact (gcd_isUnit_iff P Q).mp
      (h (gcd P Q) ⟨gcd_dvd_left P Q, gcd_dvd_right P Q,
        fun _ h1 h2 => dvd_gcd h1 h2⟩)
  · intro ⟨u, v, h⟩ G ⟨hGP, hGQ, _⟩
    rw [isUnit_iff_dvd_one]
    exact h ▸ dvd_add (dvd_mul_of_dvd_right hGP u) (dvd_mul_of_dvd_right hGQ v)

end Azurite.BPR

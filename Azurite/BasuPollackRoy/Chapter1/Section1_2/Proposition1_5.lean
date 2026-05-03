import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lcm

/-!
# Proposition 1.5

If $G$ is a (nonzero) greatest common divisor of $P$ and $Q$ in $K[X]$,
then $P Q / G$ is a least common multiple of $P$ and $Q$.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- `IsLCM` is preserved under `Associated`. -/
private theorem isLCM_of_associated {L L' P Q : K[X]}
    (hL : IsLCM L P Q) (h : Associated L L') : IsLCM L' P Q :=
  ⟨dvd_trans hL.1 h.dvd, dvd_trans hL.2.1 h.dvd,
   fun M hP hQ => dvd_trans h.symm.dvd (hL.2.2 M hP hQ)⟩

/-- Dividing by associated nonzero divisors gives associated quotients. -/
private theorem div_associated {a G₁ G₂ : K[X]}
    (hG₁ : G₁ ≠ 0) (hG₁_dvd : G₁ ∣ a) (hG₂_dvd : G₂ ∣ a)
    (hAssoc : Associated G₁ G₂) : Associated (a / G₁) (a / G₂) := by
  obtain ⟨u, hu⟩ := hAssoc
  have hG₂0 : G₂ ≠ 0 := fun h =>
    hG₁ ((mul_eq_zero.mp (hu ▸ h : G₁ * ↑u = 0)).resolve_right (Units.ne_zero u))
  have h1 := EuclideanDomain.mul_div_cancel' hG₁ hG₁_dvd
  have h2 := EuclideanDomain.mul_div_cancel' hG₂0 hG₂_dvd
  have h3 : a / G₁ = ↑u * (a / G₂) :=
    mul_left_cancel₀ hG₁ (calc G₁ * (a / G₁) = a := h1
      _ = G₂ * (a / G₂) := h2.symm
      _ = (G₁ * ↑u) * (a / G₂) := by rw [hu]
      _ = G₁ * (↑u * (a / G₂)) := mul_assoc _ _ _)
  exact ⟨u⁻¹, by rw [h3]; calc ↑u * (a / G₂) * ↑u⁻¹
    = a / G₂ * (↑u * ↑u⁻¹) := by ring
    _ = a / G₂ := by simp⟩

/-- BPR Proposition 1.5 for Mathlib's canonical gcd: P * Q / gcd(P, Q) = lcm(P, Q)
    definitionally, so this is immediate. -/
theorem prop_1_5_gcd (P Q : K[X]) : IsLCM (P * Q / gcd P Q) P Q :=
  ⟨dvd_lcm_left P Q, dvd_lcm_right P Q, fun _ hP hQ => lcm_dvd hP hQ⟩

/-- BPR Proposition 1.5: If G is a GCD of P and Q (with G ≠ 0),
    then P * Q / G is a least common multiple of P and Q. -/
theorem prop_1_5 {P Q G : K[X]} (hG : IsGCD G P Q) (hG0 : G ≠ 0) :
    IsLCM (P * Q / G) P Q :=
  isLCM_of_associated (prop_1_5_gcd P Q)
    (div_associated hG0 (dvd_mul_of_dvd_left hG.1 Q)
      (dvd_mul_of_dvd_left (gcd_dvd_left P Q) Q)
      (associated_of_dvd_dvd
        ((gcd_isGCD P Q).2.2 G hG.1 hG.2.1)
        (hG.2.2 (gcd P Q) (gcd_dvd_left P Q) (gcd_dvd_right P Q)))).symm

end Azurite.BPR

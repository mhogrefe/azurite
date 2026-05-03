import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd

/-!
# Section 1.2: Least Common Multiple

$G \in K[X]$ is a *least common multiple* of $P$ and $Q$ if $P$ and $Q$
both divide $G$, and any common multiple of $P$ and $Q$ is a multiple of
$G$. Like the GCD, the LCM is unique only up to units.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- BPR: G is a least common multiple of P and Q if
    G is a multiple of both P and Q, and any common multiple of P and Q
    is a multiple of G. -/
def IsLCM (G P Q : K[X]) : Prop :=
  P ∣ G ∧ Q ∣ G ∧ ∀ M : K[X], P ∣ M → Q ∣ M → G ∣ M

/-- Mathlib's `lcm P Q` satisfies the BPR IsLCM relation. -/
theorem lcm_isLCM (P Q : K[X]) : IsLCM (lcm P Q) P Q :=
  ⟨dvd_lcm_left P Q, dvd_lcm_right P Q, fun _ hP hQ => lcm_dvd hP hQ⟩

/-- Any two LCMs of P and Q are associates (differ by a unit). -/
theorem isLCM_associated {G₁ G₂ P Q : K[X]}
    (h₁ : IsLCM G₁ P Q) (h₂ : IsLCM G₂ P Q) :
    Associated G₁ G₂ :=
  associated_of_dvd_dvd (h₁.2.2 G₂ h₂.1 h₂.2.1) (h₂.2.2 G₁ h₁.1 h₁.2.1)

/-- The degree of the LCM of P and Q. Well-defined since any two LCMs
    have the same degree (by `isLCM_associated`). -/
noncomputable def degLcm (P Q : K[X]) : WithBot ℕ := (lcm P Q).degree

/-- Any IsLCM witness has the same degree as `degLcm P Q`. -/
theorem isLCM_degree_eq_degLcm {G P Q : K[X]} (h : IsLCM G P Q) :
    G.degree = degLcm P Q :=
  degree_eq_degree_of_associated
    (associated_of_dvd_dvd
      (h.2.2 _ (dvd_lcm_left P Q) (dvd_lcm_right P Q))
      ((lcm_isLCM P Q).2.2 _ h.1 h.2.1))

end Azurite.BPR

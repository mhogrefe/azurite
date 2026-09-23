import Azurite.BasuPollackRoy.Chapter4.Section4_4.Definition_4_67
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Lemma_4_62
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Minimal

/-!
# BPR Proposition 4.70: Hilbert Basis Theorem (existence of Gröbner bases)

Every ideal `I ⊆ K[X₁, …, X_k]` has a Gröbner basis for any monomial ordering `m`.

The leading monomials of nonzero elements of `I` form an upward-closed subset `S` of `ℕ^k`
(if `X^a = lmon(P)` and `a ≤ b`, then `X^b = lmon(X^{b-a}·P)`). By Dickson's lemma
(`lemma_4_62`) `S` has finitely many minimal elements; by well-foundedness of `ℕ^k` every
element of `S` lies above a minimal one. Choosing one polynomial realizing each minimal
leading monomial gives a Gröbner basis.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- **BPR Proposition 4.70 (Hilbert Basis Theorem).** Every ideal of `K[X₁, …, X_k]` has a
Gröbner basis for the monomial ordering `m`. -/
theorem proposition_4_70 (m : MonomialOrder (Fin k)) (I : Ideal (MvPolynomial (Fin k) K)) :
    ∃ 𝒢 : Finset (MvPolynomial (Fin k) K), IsGrobnerBasisOf m I 𝒢 := by
  classical
  -- The set of leading monomials of nonzero elements of `I`.
  set S : Set (Fin k →₀ ℕ) := {d | ∃ P ∈ I, P ≠ 0 ∧ m.degree P = d} with hS
  -- Step 1: `S` is upward closed.
  have hup : ∀ a ∈ S, ∀ b, a ≤ b → b ∈ S := by
    rintro a ⟨P, hPI, hP0, rfl⟩ b hab
    have hmne : (monomial (b - m.degree P) 1 : MvPolynomial (Fin k) K) ≠ 0 := by
      rw [Ne, MvPolynomial.monomial_eq_zero]; exact one_ne_zero
    exact ⟨monomial (b - m.degree P) 1 * P, Ideal.mul_mem_left I _ hPI, mul_ne_zero hmne hP0, by
      rw [MonomialOrder.degree_mul hmne hP0, MonomialOrder.degree_monomial, ite_eq_right one_ne_zero,
        tsub_add_cancel_of_le hab]⟩
  -- Step 2: finitely many minimal leading monomials.
  have hfin : {a | Minimal (· ∈ S) a}.Finite := lemma_4_62 S hup
  -- Step 3: every leading monomial lies above a minimal one.
  have hbelow : ∀ a ∈ S, ∃ b, Minimal (· ∈ S) b ∧ b ≤ a := by
    intro a ha
    obtain ⟨b, hbmem, hbmin⟩ := (wellFounded_lt).has_min {x | x ∈ S ∧ x ≤ a} ⟨a, ha, le_refl a⟩
    refine ⟨b, ⟨hbmem.1, fun c hcS hcb => ?_⟩, hbmem.2⟩
    by_contra hbc
    exact hbmin c ⟨hcS, le_trans hcb hbmem.2⟩ (lt_of_le_of_ne hcb (fun h => hbc (h ▸ le_rfl)))
  -- Step 4: choose a polynomial realizing each minimal leading monomial.
  let g : (Fin k →₀ ℕ) → MvPolynomial (Fin k) K :=
    fun a => if h : Minimal (· ∈ S) a then h.1.choose else 0
  have hg : ∀ a, Minimal (· ∈ S) a → g a ∈ I ∧ g a ≠ 0 ∧ m.degree (g a) = a := by
    intro a h
    have hspec := h.1.choose_spec
    simp only [g, dite_eq_left h]
    exact hspec
  refine ⟨hfin.toFinset.image g, ?_, ?_, ?_⟩
  · -- (1) `𝒢 ⊆ I`
    intro G hG
    obtain ⟨a, haf, rfl⟩ := Finset.mem_image.mp hG
    exact (hg a (hfin.mem_toFinset.mp haf)).1
  · -- (2) every nonzero `P ∈ I` has its leading monomial divisible by some `G`.
    intro P hPI hP0
    have hmemS : m.degree P ∈ S := ⟨P, hPI, hP0, rfl⟩
    obtain ⟨b, hbmin, hble⟩ := hbelow (m.degree P) hmemS
    refine ⟨g b, Finset.mem_image_of_mem g (hfin.mem_toFinset.mpr hbmin),
      (hg b hbmin).2.1, ?_⟩
    rw [(hg b hbmin).2.2]
    exact hble
  · -- (3) no leading monomial of `𝒢` divides another's.
    intro G hG G' hG' hne hle
    obtain ⟨a, haf, rfl⟩ := Finset.mem_image.mp hG
    obtain ⟨a', haf', rfl⟩ := Finset.mem_image.mp hG'
    have ha := hfin.mem_toFinset.mp haf
    have ha' := hfin.mem_toFinset.mp haf'
    rw [(hg a ha).2.2] at hle
    rw [(hg a' ha').2.2] at hle
    -- `hle : a' ≤ a`. `a` minimal, `a' ∈ S` gives `a ≤ a'`, hence `a = a'`, so `g a = g a'`.
    have heq : a = a' := le_antisymm (ha.2 ha'.1 hle) hle
    exact hne (by rw [heq])

end Azurite.BPR.Chapter4

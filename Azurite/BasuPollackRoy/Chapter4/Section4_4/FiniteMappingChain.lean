import Azurite.BasuPollackRoy.Chapter4.Section4_4.FiniteMapping

/-!
# BPR §4.4.2: composite finite mappings

Let `𝒫 ⊆ K[X₁, …, X_k]` and `𝒯 ⊆ K[X₁, …, X_{k'}]` be finite sets of polynomials with `k > k'`.
The projection `Π : C^k → C^{k'}` forgetting the last `k - k'` coordinates is a *finite mapping*
from `Zer(𝒫, C^k)` to `Zer(𝒯, C^{k'})` if there is a chain of finite sets `𝒬_{k-i} ⊆
K[X₁, …, X_{k-i}]` (`0 ≤ i ≤ k - k'`) with `𝒬_k = 𝒫`, `𝒬_{k'} = 𝒯`, such that each one-coordinate
projection `C^{k-i} → C^{k-i-1}` is a (single-step) finite mapping from `Zer(𝒬_{k-i})` to
`Zer(𝒬_{k-i-1})` (Definition above, `IsFiniteMapping`).

As elsewhere in §4.4 we single out `X₀`, so each step forgets the first coordinate
(`Fin.tail`). Indexing by the number `d = k - k'` of forgotten coordinates (`k = k' + d`), the
chain condition becomes a recursion on `d`: `Π` is a composite finite mapping iff `𝒫` is linked
to `𝒯` by `d` consecutive single-step finite mappings.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {K : Type*} [Field K]

/-- **BPR Definition (composite finite mapping).** `IsFiniteMappingChain C k' d 𝒫 𝒯` holds when
`𝒫 ⊆ K[X₁, …, X_{k'+d}]` is linked to `𝒯 ⊆ K[X₁, …, X_{k'}]` by `d` consecutive single-coordinate
finite mappings; equivalently, the composite projection `C^{k'+d} → C^{k'}` (forgetting the first
`d` coordinates) is a finite mapping from `Zer(𝒫)` to `Zer(𝒯)`. -/
def IsFiniteMappingChain (C : Type*) [Field C] [Algebra K C] (k' : ℕ) :
    (d : ℕ) → Finset (MvPolynomial (Fin (k' + d)) K) →
      Finset (MvPolynomial (Fin k') K) → Prop
  | 0, P, T => P = T
  | d + 1, P, T =>
      ∃ Q : Finset (MvPolynomial (Fin (k' + d)) K),
        IsFiniteMapping C P Q ∧ IsFiniteMappingChain C k' d Q T

@[simp] theorem isFiniteMappingChain_zero (C : Type*) [Field C] [Algebra K C] {k' : ℕ}
    (P : Finset (MvPolynomial (Fin (k' + 0)) K)) (T : Finset (MvPolynomial (Fin k') K)) :
    IsFiniteMappingChain C k' 0 P T ↔ P = T := Iff.rfl

theorem isFiniteMappingChain_succ (C : Type*) [Field C] [Algebra K C] {k' d : ℕ}
    (P : Finset (MvPolynomial (Fin (k' + (d + 1))) K))
    (T : Finset (MvPolynomial (Fin k') K)) :
    IsFiniteMappingChain C k' (d + 1) P T ↔
      ∃ Q : Finset (MvPolynomial (Fin (k' + d)) K),
        IsFiniteMapping C P Q ∧ IsFiniteMappingChain C k' d Q T := Iff.rfl

/-- A single-step finite mapping is a one-link composite finite mapping. -/
theorem IsFiniteMapping.isFiniteMappingChain {C : Type*} [Field C] [Algebra K C] {k' : ℕ}
    {P : Finset (MvPolynomial (Fin (k' + 1)) K)} {T : Finset (MvPolynomial (Fin k') K)}
    (h : IsFiniteMapping C P T) : IsFiniteMappingChain C k' 1 P T :=
  ⟨T, h, rfl⟩

end Azurite.BPR.Chapter4

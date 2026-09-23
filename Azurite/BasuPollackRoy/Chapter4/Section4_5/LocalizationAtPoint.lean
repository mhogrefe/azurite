import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# BPR §4.5: the localization `Ā_x` of `Ā` at a point

For `x ∈ Zer(𝒫, Cᵏ)`, the *localization of `Ā` at `x`*, denoted `Ā_x`, is the ring of fractions
associated to the multiplicative subset `S_x` of elements of `Ā` not vanishing at `x`
(`evalAtPointSubmonoid`, `mem_evalAtPointSubmonoid`). It is `Localization` of `Ā` at `S_x`
(`localizationAtPoint`).

The subset `S_x` is exactly the prime complement of the kernel of evaluation at `x`
(`evalBar`), the kernel being prime because `C` is a field. Hence `Ā_x` is a localization at a
prime ideal and is therefore a **local ring** (`isLocalRing_localizationAtPoint`): an element
`P/Q` is invertible iff `P(x) ≠ 0`, and either `P/Q` or `1 + P/Q = (Q + P)/Q` is invertible.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]
  (Ps : Finset (MvPolynomial (Fin k) K)) (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps)

/-- `S_x`: the multiplicative subset of `Ā` consisting of the elements not vanishing at `x` — that
is, the prime complement of the kernel of evaluation at `x` (prime because `C` is a field). -/
noncomputable def evalAtPointSubmonoid : Submonoid (quotPolysExt C Ps) :=
  letI := RingHom.ker_isPrime (evalBar C Ps x hx)
  (RingHom.ker (evalBar C Ps x hx)).primeCompl

/-- An element of `Ā` lies in `S_x` exactly when it does not vanish at `x`. -/
theorem mem_evalAtPointSubmonoid (Q : quotPolysExt C Ps) :
    Q ∈ evalAtPointSubmonoid C Ps x hx ↔ evalBar C Ps x hx Q ≠ 0 := by
  show Q ∉ RingHom.ker (evalBar C Ps x hx) ↔ evalBar C Ps x hx Q ≠ 0
  rw [RingHom.mem_ker]

/-- `Ā_x`: the localization of `Ā` at the multiplicative subset `S_x`. -/
noncomputable def localizationAtPoint : Type _ :=
  Localization (evalAtPointSubmonoid C Ps x hx)

noncomputable instance : CommRing (localizationAtPoint C Ps x hx) :=
  inferInstanceAs (CommRing (Localization _))

/-- The `Ā`-algebra structure on `Ā_x` (the localization map `Ā → Ā_x`). -/
noncomputable instance algebraQuotPolysExtLocalizationAtPoint :
    Algebra (quotPolysExt C Ps) (localizationAtPoint C Ps x hx) :=
  inferInstanceAs (Algebra (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)))

/-- **`Ā_x` is a local ring.** It is a localization of `Ā` at a prime ideal (the kernel of
evaluation at `x`). -/
theorem isLocalRing_localizationAtPoint : IsLocalRing (localizationAtPoint C Ps x hx) := by
  let := RingHom.ker_isPrime (evalBar C Ps x hx)
  show IsLocalRing (Localization (RingHom.ker (evalBar C Ps x hx)).primeCompl)
  infer_instance

end Azurite.BPR.Chapter4

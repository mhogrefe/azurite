import Azurite.BasuPollackRoy.Chapter2.Section2_5.Theorem_2_80
import Azurite.BasuPollackRoy.Chapter2.Section2_3.OrderedSentences
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealClosure
import Azurite.BasuPollackRoy.Chapter2.Section2_4.RealClosureEmbedding

/-! # BPR Theorem 2.81: truth of `ℚ`-sentences is independent of the real closed field

Every real closed field contains the real closure of `ℚ` (the real algebraic numbers), and
a sentence with coefficients in `ℚ` has the same truth value in every real closed field.
This is the absolute form of the transfer principle (Theorem~2.80): rather than comparing
truth across an inclusion `R ⊆ R'`, it compares truth across two *arbitrary* real closed
fields, using their common real closed subfield `RC = ` the real closure of `ℚ`.

The proof base-changes the `ℚ`-sentence to a sentence over a fixed real closure `RC` of
`ℚ` (`Formula.mapCoeffO`, which does not change the realization over a scalar tower), embeds
`RC` order-preservingly into any real closed field `S` (`exists_algHom`, since `RC` is
algebraic over `ℚ` and `ℚ` embeds order-preservingly into every ordered field via
`Rat.cast`), and applies Theorem~2.80 to the inclusion `RC ⊆ S`.
-/

open Azurite.BPR

namespace Azurite.BPR

/-- **Transfer of `ℚ`-sentence truth to a fixed real closure.** If `RC` is a real closed
field, algebraic over `ℚ`, with `ℚ` embedded order-preservingly, then any real closed field
`S` agrees with `RC` on the truth of a `ℚ`-sentence. -/
private theorem istrue_transfer_to_realClosure {k : ℕ}
    {RC : Type*} [Field RC] [LinearOrder RC] [IsStrictOrderedRing RC] [IsRealClosed RC]
      [Algebra ℚ RC] (halg : Algebra.IsAlgebraic ℚ RC) (hQRC : StrictMono (algebraMap ℚ RC))
    {S : Type*} [Field S] [LinearOrder S] [IsStrictOrderedRing S] [IsRealClosed S] [Algebra ℚ S]
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) ℚ)) (hΦ : Formula.isSentence Φ) :
    Φ.IsTrue (C := S) ↔ Φ.IsTrue (C := RC) := by
  have hQS : StrictMono (algebraMap ℚ S) := by
    have h : (algebraMap ℚ S) = (Rat.cast : ℚ → S) := by ext q; exact eq_ratCast _ q
    rw [h]; exact Rat.cast_strictMono
  -- An order-preserving `ℚ`-embedding `RC → S`, since `RC` is algebraic over `ℚ`.
  obtain ⟨φ⟩ := exists_algHom (F := ℚ) (R := RC) (R' := S)
    hasIVP_of_isRealClosed hasIVP_of_isRealClosed halg hQRC hQS
  letI : Algebra RC S := φ.toAlgebra
  haveI : IsScalarTower ℚ RC S := IsScalarTower.of_algebraMap_eq (fun q => (φ.commutes q).symm)
  -- Base-change `Φ` to `RC`; Theorem 2.80 transfers across `RC ⊆ S`.
  have hsent : Formula.isSentence (Φ.mapCoeffO (D' := RC)) := Formula.isSentence_mapCoeffO hΦ
  have h80 := theorem_2_80 (R := RC) (R' := S) (Φ.mapCoeffO (D' := RC)) hsent
  rw [Formula.IsTrue, Formula.IsTrue,
    ← Formula.realization_mapCoeffO (D' := RC) (S := S) Φ,
    ← Formula.realization_mapCoeffO (D' := RC) (S := RC) Φ]
  exact h80.symm

/-- **BPR Theorem 2.81.** Let `R` be a real closed field. A sentence in the language of
ordered fields with coefficients in `ℚ` is true in `R` if and only if it is true in any
real closed field.

Since every real closed field contains the real closure of `ℚ`
(`exists_orderCompatible_realClosure_algebraic`), both `R` and the comparison field agree
with that common real closure on the truth of the sentence
(`istrue_transfer_to_realClosure`), hence with each other. -/
theorem theorem_2_81 {k : ℕ}
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
    (Φ : Formula (Fin k) (OrderedFieldAtom (Fin k) ℚ)) (hΦ : Formula.isSentence Φ) :
    Φ.IsTrue (C := R) ↔ Φ.IsTrue (C := R') := by
  obtain ⟨RCif, hclosed, _⟩ := RealClosure.exists_orderCompatible_realClosure_algebraic ℚ
  letI : LinearOrder ↥RCif := IsRealClosed.toLinearOrder
  haveI : IsOrderedRing ↥RCif := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing ↥RCif := IsOrderedRing.toIsStrictOrderedRing _
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have halg : Algebra.IsAlgebraic ℚ ↥RCif :=
    Algebra.IsAlgebraic.tower_bot ℚ ↥RCif (AlgebraicClosure ℚ)
  have hQRC : StrictMono (algebraMap ℚ ↥RCif) := by
    have h : (algebraMap ℚ ↥RCif) = (Rat.cast : ℚ → ↥RCif) := by ext q; exact eq_ratCast _ q
    rw [h]; exact Rat.cast_strictMono
  exact (istrue_transfer_to_realClosure halg hQRC Φ hΦ (S := R)).trans
        (istrue_transfer_to_realClosure halg hQRC Φ hΦ (S := R')).symm

end Azurite.BPR

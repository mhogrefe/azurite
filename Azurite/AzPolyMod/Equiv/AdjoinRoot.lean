import Azurite.AzPolyMod.Basic
import Azurite.AzPolynomial.Equiv.DivModByMonic
import Azurite.AzPolynomial.Equiv.Pow
import Azurite.Algorithm.Equiv.SlidingWindowPowAzNat
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Ring.Equiv

set_option linter.unusedSectionVars false

/-!
# `AzPolyMod f ≃+* AdjoinRoot (toPoly f)` — correctness of `R[x]/(f)`

For a **monic** `f`, `AzPolyMod f` is the quotient ring `R[x]/(f)`.  This file proves it,
transporting the ring structure from Mathlib's `AdjoinRoot (toPoly f)` (`= R[X] ⧸ (toPoly f)`)
through the reduction map.

The bridge is
`toAdjoin a := AdjoinRoot.mk (toPoly f) (toPoly a.val)`.
Its key property is that **reduction preserves the residue class**
(`toAdjoin_ofPoly`): `toAdjoin (ofPoly p) = AdjoinRoot.mk (toPoly f) (toPoly p)`, which follows
directly from the reconstruction identity `toPoly_f_dvd_sub_modByMonic`.  From there `toAdjoin`
preserves every operation, is injective (degree `< deg f` + monic), and is surjective
(`AdjoinRoot.mk` is surjective), giving:

* `instance : CommRing (AzPolyMod f)` (gated on `[Nontrivial R] [Fact (toPoly f).Monic]`), and
* `ringEquivAdjoinRoot : AzPolyMod f ≃+* AdjoinRoot (toPoly f)`, the correctness anchor.
-/

namespace Azurite

namespace AzPolyMod

open Polynomial AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] {f : AzPolynomial R}

/-- Forward map to Mathlib's `R[x]/(f) = AdjoinRoot (toPoly f)`. -/
noncomputable def toAdjoin (a : AzPolyMod f) : AdjoinRoot (AzPolynomial.toPoly f) :=
  AdjoinRoot.mk (AzPolynomial.toPoly f) (AzPolynomial.toPoly a.val)

theorem toAdjoin_def (a : AzPolyMod f) :
    toAdjoin a = AdjoinRoot.mk (AzPolynomial.toPoly f) (AzPolynomial.toPoly a.val) := rfl

theorem toAdjoin_zero : toAdjoin (0 : AzPolyMod f) = 0 := by
  show AdjoinRoot.mk (AzPolynomial.toPoly f) (AzPolynomial.toPoly (0 : AzPolynomial R)) = 0
  rw [toPoly_zero, map_zero]

section Monic

variable (hf : (AzPolynomial.toPoly f).Monic) (hf0 : AzPolynomial.toPoly f ≠ 0)
include hf hf0

/-- **Reduction preserves the residue class.**  The heart of the correspondence: reducing a
polynomial `p` modulo `f` lands in the same `AdjoinRoot` class as `p`. -/
theorem toAdjoin_ofPoly (p : AzPolynomial R) :
    toAdjoin (ofPoly p : AzPolyMod f) = AdjoinRoot.mk (AzPolynomial.toPoly f) (AzPolynomial.toPoly p) := by
  show AdjoinRoot.mk (AzPolynomial.toPoly f) (AzPolynomial.toPoly (modByMonic p f)) = _
  rw [AdjoinRoot.mk_eq_mk]
  have h := toPoly_f_dvd_sub_modByMonic hf hf0 p
  rw [show AzPolynomial.toPoly (modByMonic p f) - AzPolynomial.toPoly p
      = -(AzPolynomial.toPoly p - AzPolynomial.toPoly (modByMonic p f)) by ring]
  exact dvd_neg.mpr h

/-- The coefficient inclusion agrees with `AdjoinRoot.of`. -/
theorem toAdjoin_ofCoeff (c : R) :
    toAdjoin (ofCoeff c : AzPolyMod f) = AdjoinRoot.of (AzPolynomial.toPoly f) c := by
  show toAdjoin (ofPoly (AzPolynomial.C c)) = _
  rw [toAdjoin_ofPoly hf hf0, toPoly_C]
  rfl

/-! ### Operation preservation -/

theorem toAdjoin_one : toAdjoin (1 : AzPolyMod f) = 1 := by
  show toAdjoin (ofPoly (1 : AzPolynomial R)) = 1
  rw [toAdjoin_ofPoly hf hf0, toPoly_one, map_one]

theorem toAdjoin_add (a b : AzPolyMod f) : toAdjoin (a + b) = toAdjoin a + toAdjoin b := by
  show toAdjoin (ofPoly (a.val + b.val)) = _
  rw [toAdjoin_ofPoly hf hf0, toPoly_add, map_add]; rfl

theorem toAdjoin_mul (a b : AzPolyMod f) : toAdjoin (a * b) = toAdjoin a * toAdjoin b := by
  show toAdjoin (ofPoly (a.val * b.val)) = _
  rw [toAdjoin_ofPoly hf hf0, toPoly_mul, map_mul]; rfl

theorem toAdjoin_neg (a : AzPolyMod f) : toAdjoin (-a) = -toAdjoin a := by
  show toAdjoin (ofPoly (-a.val)) = _
  rw [toAdjoin_ofPoly hf hf0, toPoly_neg, map_neg]; rfl

theorem toAdjoin_sub (a b : AzPolyMod f) : toAdjoin (a - b) = toAdjoin a - toAdjoin b := by
  show toAdjoin (ofPoly (a.val - b.val)) = _
  rw [toAdjoin_ofPoly hf hf0, toPoly_sub, map_sub]; rfl

theorem toAdjoin_pow (a : AzPolyMod f) (n : ℕ) : toAdjoin (a.pow n) = (toAdjoin a) ^ n := by
  show toAdjoin (Azurite.slidingWindowPow a n) = _
  rw [Azurite.map_slidingWindowPow toAdjoin (toAdjoin_one hf hf0) (toAdjoin_mul hf hf0) a n]

/-! ### Bijectivity -/

/-- The reduced representative of a class has Mathlib degree `< deg f`. -/
theorem degree_toPoly_val_lt (a : AzPolyMod f) :
    (AzPolynomial.toPoly a.val).degree < (AzPolynomial.toPoly f).degree := by
  have hfs : 0 < f.coeffs.size := by
    rcases Nat.eq_zero_or_pos f.coeffs.size with h | h
    · exfalso; apply hf0
      have : f = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h)
      rw [this]; exact toPoly_zero
    · exact h
  have hsz : a.val.coeffs.size < f.coeffs.size := by
    rcases a.isReduced with h | h
    · exact h
    · omega
  exact degree_toPoly_lt_of_size_lt hsz hf0

theorem toAdjoin_injective [Nontrivial R] : Function.Injective (toAdjoin (f := f)) := by
  intro a b hab
  rw [toAdjoin_def, toAdjoin_def, AdjoinRoot.mk_eq_mk] at hab
  -- `hab : toPoly f ∣ d`; with `deg d < deg f` and monic `f`, this forces `d = 0`
  -- (via `d %ₘ f = 0` from divisibility and `d %ₘ f = d` from the degree bound).
  set d := AzPolynomial.toPoly a.val - AzPolynomial.toPoly b.val with hd
  have hmod0 : d %ₘ (AzPolynomial.toPoly f) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hf).mpr hab
  have hdeg : d.degree < (AzPolynomial.toPoly f).degree :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (degree_toPoly_val_lt hf hf0 a) (degree_toPoly_val_lt hf hf0 b))
  have hself : d %ₘ (AzPolynomial.toPoly f) = d :=
    (Polynomial.modByMonic_eq_self_iff hf).mpr hdeg
  have hdiff : d = 0 := by rw [← hself, hmod0]
  exact AzPolyMod.ext (toPoly_inj.mp (sub_eq_zero.mp hdiff))

theorem toAdjoin_surjective : Function.Surjective (toAdjoin (f := f)) := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  exact ⟨ofPoly (AzPolynomial.ofPoly p), by rw [toAdjoin_ofPoly hf hf0, toPoly_ofPoly]⟩

end Monic

/-! ### Natural / integer casts (data for the `CommRing`) -/

instance : NatCast (AzPolyMod f) := ⟨fun n => ofPoly (AzPolynomial.C (n : R))⟩
instance : IntCast (AzPolyMod f) := ⟨fun n => ofPoly (AzPolynomial.C (n : R))⟩
instance : SMul ℕ (AzPolyMod f) := ⟨fun n a => (n : AzPolyMod f) * a⟩
instance : SMul ℤ (AzPolyMod f) := ⟨fun n a => (n : AzPolyMod f) * a⟩

section Monic

variable (hf : (AzPolynomial.toPoly f).Monic) (hf0 : AzPolynomial.toPoly f ≠ 0)
include hf hf0

theorem toAdjoin_natCast (n : ℕ) : toAdjoin ((n : AzPolyMod f)) = (n : AdjoinRoot (AzPolynomial.toPoly f)) := by
  show toAdjoin (ofPoly (AzPolynomial.C ((n : R)))) = _
  rw [toAdjoin_ofPoly hf hf0, toPoly_C]
  exact map_natCast ((AdjoinRoot.mk (AzPolynomial.toPoly f)).comp Polynomial.C) n

theorem toAdjoin_intCast (n : ℤ) : toAdjoin ((n : AzPolyMod f)) = (n : AdjoinRoot (AzPolynomial.toPoly f)) := by
  show toAdjoin (ofPoly (AzPolynomial.C ((n : R)))) = _
  rw [toAdjoin_ofPoly hf hf0, toPoly_C]
  exact map_intCast ((AdjoinRoot.mk (AzPolynomial.toPoly f)).comp Polynomial.C) n

end Monic

/-! ### The `CommRing` instance and the ring isomorphism -/

section Instance

variable [Nontrivial R] [hfact : Fact (AzPolynomial.toPoly f).Monic]

private theorem monic_f : (AzPolynomial.toPoly f).Monic := hfact.out
private theorem ne_zero_f : AzPolynomial.toPoly f ≠ 0 := hfact.out.ne_zero

/-- **`AzPolyMod f` is a commutative ring** for monic `f`: the ring structure is pulled back
from `AdjoinRoot (toPoly f)` through the injective, operation-preserving `toAdjoin`. -/
noncomputable instance instCommRing : CommRing (AzPolyMod f) :=
  Function.Injective.commRing (toAdjoin (f := f))
    (toAdjoin_injective (monic_f) (ne_zero_f))
    (toAdjoin_zero)
    (toAdjoin_one (monic_f) (ne_zero_f))
    (toAdjoin_add (monic_f) (ne_zero_f))
    (toAdjoin_mul (monic_f) (ne_zero_f))
    (toAdjoin_neg (monic_f) (ne_zero_f))
    (toAdjoin_sub (monic_f) (ne_zero_f))
    (fun n a => by
      show toAdjoin ((n : AzPolyMod f) * a) = n • toAdjoin a
      rw [toAdjoin_mul (monic_f) (ne_zero_f), toAdjoin_natCast (monic_f) (ne_zero_f), nsmul_eq_mul])
    (fun n a => by
      show toAdjoin ((n : AzPolyMod f) * a) = n • toAdjoin a
      rw [toAdjoin_mul (monic_f) (ne_zero_f), toAdjoin_intCast (monic_f) (ne_zero_f), zsmul_eq_mul])
    (fun a n => by
      show toAdjoin (a.pow n) = toAdjoin a ^ n
      rw [toAdjoin_pow (monic_f) (ne_zero_f)])
    (toAdjoin_natCast (monic_f) (ne_zero_f))
    (toAdjoin_intCast (monic_f) (ne_zero_f))

/-- `toAdjoin` bundled as a **ring homomorphism** `AzPolyMod f →+* AdjoinRoot (toPoly f)`. -/
noncomputable def toAdjoinRingHom : AzPolyMod f →+* AdjoinRoot (AzPolynomial.toPoly f) where
  toFun := toAdjoin
  map_one' := toAdjoin_one (monic_f) (ne_zero_f)
  map_mul' := toAdjoin_mul (monic_f) (ne_zero_f)
  map_zero' := toAdjoin_zero
  map_add' := toAdjoin_add (monic_f) (ne_zero_f)

/-- `toAdjoin` bundled as a **ring isomorphism** `AzPolyMod f ≃+* AdjoinRoot (toPoly f)`, the
correctness anchor identifying `AzPolyMod f` with Mathlib's `R[x]/(f)`. -/
noncomputable def ringEquivAdjoinRoot : AzPolyMod f ≃+* AdjoinRoot (AzPolynomial.toPoly f) :=
  RingEquiv.ofBijective toAdjoinRingHom (by
    refine ⟨?_, ?_⟩
    · exact toAdjoin_injective (monic_f) (ne_zero_f)
    · exact toAdjoin_surjective (monic_f) (ne_zero_f))

@[simp] theorem ringEquivAdjoinRoot_apply (a : AzPolyMod f) :
    ringEquivAdjoinRoot a = toAdjoin a := rfl

/-- **`powAzNat` computes the monoid power** `a ^ n.toNat` (for monic `f`, where `AzPolyMod f`
is a `Monoid`): the limb-level `AzNat`-exponent power agrees with the `ℕ` power. -/
theorem powAzNat_eq_pow (a : AzPolyMod f) (n : AzNat) : a.powAzNat n = a ^ n.toNat :=
  Azurite.slidingWindowPowAzNat_eq_pow a n

/-- The `AzNat`-exponent power transports through `ringEquivAdjoinRoot`:
`toAdjoin (a ^ (n : AzNat)) = (toAdjoin a) ^ n.toNat`. -/
theorem toAdjoin_powAzNat (a : AzPolyMod f) (n : AzNat) :
    toAdjoin (a ^ (n : AzNat)) = (toAdjoin a) ^ n.toNat := by
  show toAdjoin (a.powAzNat n) = _
  rw [powAzNat_eq_pow]
  exact toAdjoin_pow (monic_f) (ne_zero_f) a n.toNat

/-- Sanity: the transported `CommRing` is fully usable — `ring` discharges identities and
`pow` is the (sliding-window) monoid power. -/
example (a b c : AzPolyMod f) : (a + b) * c = a * c + b * c := by ring
example (a : AzPolyMod f) (n : ℕ) : a ^ n = a.pow n := rfl

end Instance

end AzPolyMod

end Azurite

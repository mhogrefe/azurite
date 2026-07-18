/-
  **The computable Gauss-sum tower IS the mod-`n` pair tower**: the
  ring isomorphism `CycPQModN n.toNat p q ≃+* GaussTowerPQ n p q`
  (`gaussTowerEquiv`), composed from
  * `adjoinRootCongr` — the generic `AdjoinRoot` congruence along a
    base ring equivalence (reusable),
  * `toPoly_cyclotomicPrime` — the all-ones `AzPolynomial` really is
    `Φ_p` for prime `p` (`Polynomial.cyclotomic_prime`),
  * `AzPolyMod.ringEquivAdjoinRoot` at both levels (now computable
    on the `AzPolyMod` side), and
  * `AzZMod.ringEquivZMod` at the base.

  The composite with the reduction of `CycPQModN.lean` gives the
  end-to-end map `reduceT : ℤ[ζ_p, ζ_q] →+* GaussTowerPQ n p q`
  into the COMPUTABLE tower, with the kernel theorem transported:

    `(n : ℤ[ζ_p, ζ_q]) ∣ x  ↔  reduceT x = 0`
    (`natCast_dvd_iff_reduceT`),

  and the generators corresponding (`reduceT_zetaP`,
  `reduceT_zetaQ`).  This is the semantic identity behind the
  checker: an equality test in `GaussTowerPQ` IS a congruence in
  `ℤ[ζ_p, ζ_q]`.
-/
import Azurite.AzPolyMod.GaussTower
import Azurite.CrandallPomerance.Chapter4.CycPQModN

namespace Azurite

open Polynomial

/-- A prime `Fact` supplies `Fact (1 < k)` (and thence `NeZero k`). -/
instance factOneLtOfPrime {k : ℕ} [hk : Fact k.Prime] : Fact (1 < k) :=
  ⟨hk.out.one_lt⟩

section AdjoinRootCongr

variable {R S : Type _} [CommRing R] [CommRing S]

/-- The forward homomorphism of the `AdjoinRoot` congruence: lift
along `of g ∘ e`, sending root to root. -/
noncomputable def adjoinRootCongrHom (e : R ≃+* S) {f : Polynomial R}
    {g : Polynomial S} (h : f.map (e : R →+* S) = g) :
    AdjoinRoot f →+* AdjoinRoot g :=
  AdjoinRoot.lift ((AdjoinRoot.of g).comp (e : R →+* S))
    (AdjoinRoot.root g) (by
      rw [← Polynomial.eval₂_map, h]
      exact AdjoinRoot.eval₂_root g)

@[simp] theorem adjoinRootCongrHom_root (e : R ≃+* S) {f : Polynomial R}
    {g : Polynomial S} (h : f.map (e : R →+* S) = g) :
    adjoinRootCongrHom e h (AdjoinRoot.root f) = AdjoinRoot.root g := by
  rw [adjoinRootCongrHom]
  exact AdjoinRoot.lift_root _

@[simp] theorem adjoinRootCongrHom_of (e : R ≃+* S) {f : Polynomial R}
    {g : Polynomial S} (h : f.map (e : R →+* S) = g) (r : R) :
    adjoinRootCongrHom e h (AdjoinRoot.of f r) = AdjoinRoot.of g (e r) := by
  rw [adjoinRootCongrHom]
  exact AdjoinRoot.lift_of _

private theorem map_symm_eq (e : R ≃+* S) {f : Polynomial R}
    {g : Polynomial S} (h : f.map (e : R →+* S) = g) :
    g.map (e.symm : S →+* R) = f := by
  rw [← h, Polynomial.map_map]
  simp

/-- **`AdjoinRoot` congruence along a base ring equivalence**: if
`e : R ≃+* S` carries `f` to `g`, then `R[x]/(f) ≃+* S[x]/(g)`. -/
noncomputable def adjoinRootCongr (e : R ≃+* S) {f : Polynomial R}
    {g : Polynomial S} (h : f.map (e : R →+* S) = g) :
    AdjoinRoot f ≃+* AdjoinRoot g := by
  refine RingEquiv.ofRingHom (adjoinRootCongrHom e h)
    (adjoinRootCongrHom e.symm (map_symm_eq e h)) ?_ ?_
  · refine AdjoinRoot.ringHom_ext (RingHom.ext fun r => ?_) ?_
    · simp
    · simp
  · refine AdjoinRoot.ringHom_ext (RingHom.ext fun r => ?_) ?_
    · simp
    · simp

@[simp] theorem adjoinRootCongr_apply (e : R ≃+* S) {f : Polynomial R}
    {g : Polynomial S} (h : f.map (e : R →+* S) = g) (x : AdjoinRoot f) :
    adjoinRootCongr e h x = adjoinRootCongrHom e h x := rfl

theorem adjoinRootCongr_root (e : R ≃+* S) {f : Polynomial R}
    {g : Polynomial S} (h : f.map (e : R →+* S) = g) :
    adjoinRootCongr e h (AdjoinRoot.root f) = AdjoinRoot.root g := by
  rw [adjoinRootCongr_apply, adjoinRootCongrHom_root]

theorem adjoinRootCongr_of (e : R ≃+* S) {f : Polynomial R}
    {g : Polynomial S} (h : f.map (e : R →+* S) = g) (r : R) :
    adjoinRootCongr e h (AdjoinRoot.of f r) = AdjoinRoot.of g (e r) := by
  rw [adjoinRootCongr_apply, adjoinRootCongrHom_of]

end AdjoinRootCongr

namespace AzPolynomial

/-- The all-ones `AzPolynomial` really is the `p`-th cyclotomic
polynomial for prime `p`. -/
theorem toPoly_cyclotomicPrime {R : Type _} [CommRing R] [DecidableEq R]
    [Nontrivial R] {k : ℕ} [Fact k.Prime] :
    AzPolynomial.toPoly (cyclotomicPrime R k) = cyclotomic k R := by
  rw [cyclotomic_prime R k]
  apply Polynomial.ext
  intro i
  rw [coeff_toPoly_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow, AzPolynomial.coeff, cyclotomicPrime,
    Array.getElem?_replicate]
  rw [Finset.sum_ite_eq (Finset.range k) i (fun _ => (1 : R))]
  by_cases hik : i < k
  · simp [hik, Finset.mem_range]
  · simp [hik, Finset.mem_range]

end AzPolynomial

namespace AzPolyMod

open AzPolynomial CP

variable (n : AzNat) (p q : ℕ) [Fact (1 < n.toNat)] [Fact p.Prime]
  [Fact q.Prime]

/-- Level 1 of the identification:
`(ℤ/n)[ζ_p] ≃+* (ℤ/n)[x]/(Φ_p)` computable. -/
noncomputable def gaussTowerPEquiv : CycPModN n.toNat p ≃+* GaussTowerP n p :=
  (adjoinRootCongr (AzZMod.ringEquivZMod (m := n)).symm (by
      rw [map_cyclotomic, toPoly_cyclotomicPrime])).trans
    (ringEquivAdjoinRoot (f := cyclotomicPrime (AzZMod n) p)).symm

@[simp] theorem gaussTowerPEquiv_root :
    gaussTowerPEquiv n p (AdjoinRoot.root (cyclotomic p (ZMod n.toNat)))
      = zetaPT n p := by
  rw [gaussTowerPEquiv, RingEquiv.trans_apply, adjoinRootCongr_root]
  rw [RingEquiv.symm_apply_eq, ringEquivAdjoinRoot_apply, zetaPT]
  rw [toAdjoin_ofPoly (monic_toPoly_cyclotomicPrime _ (NeZero.ne p))
    (monic_toPoly_cyclotomicPrime _ (NeZero.ne p)).ne_zero,
    AzPolynomial.toPoly_X, AdjoinRoot.mk_X]

/-- **The identification of the computable tower with the mod-`n`
pair tower**: `(ℤ/n)[ζ_p, ζ_q] ≃+* GaussTowerPQ n p q`. -/
noncomputable def gaussTowerEquiv : CycPQModN n.toNat p q ≃+* GaussTowerPQ n p q :=
  (adjoinRootCongr (gaussTowerPEquiv n p) (by
      rw [map_cyclotomic, toPoly_cyclotomicPrime])).trans
    (ringEquivAdjoinRoot (f := cyclotomicPrime (GaussTowerP n p) q)).symm

@[simp] theorem gaussTowerEquiv_zetaQ :
    gaussTowerEquiv n p q (zetaQModN n.toNat p q) = zetaQT n p q := by
  rw [gaussTowerEquiv, RingEquiv.trans_apply, zetaQModN,
    adjoinRootCongr_root]
  rw [RingEquiv.symm_apply_eq, ringEquivAdjoinRoot_apply, zetaQT]
  rw [toAdjoin_ofPoly (monic_toPoly_cyclotomicPrime _ (NeZero.ne q))
    (monic_toPoly_cyclotomicPrime _ (NeZero.ne q)).ne_zero,
    AzPolynomial.toPoly_X, AdjoinRoot.mk_X]

@[simp] theorem gaussTowerEquiv_zetaP :
    gaussTowerEquiv n p q (zetaPModN n.toNat p q)
      = constT n p q (zetaPT n p) := by
  rw [gaussTowerEquiv, RingEquiv.trans_apply, zetaPModN]
  rw [show (algebraMap (CycPModN n.toNat p) (CycPQModN n.toNat p q))
      (AdjoinRoot.root (cyclotomic p (ZMod n.toNat)))
      = AdjoinRoot.of _ (AdjoinRoot.root (cyclotomic p (ZMod n.toNat)))
      from rfl,
    adjoinRootCongr_of, gaussTowerPEquiv_root]
  rw [RingEquiv.symm_apply_eq, ringEquivAdjoinRoot_apply, constT, ofCoeff]
  rw [toAdjoin_ofPoly (monic_toPoly_cyclotomicPrime _ (NeZero.ne q))
    (monic_toPoly_cyclotomicPrime _ (NeZero.ne q)).ne_zero,
    toPoly_C, AdjoinRoot.mk_C]

/-- **The end-to-end reduction into the computable tower**:
`ℤ[ζ_p, ζ_q] →+* GaussTowerPQ n p q`. -/
noncomputable def reduceT : CycPQ p q →+* GaussTowerPQ n p q :=
  (gaussTowerEquiv n p q).toRingHom.comp (reduceModN n.toNat p q)

@[simp] theorem reduceT_zetaP :
    reduceT n p q (zetaP p q) = constT n p q (zetaPT n p) := by
  rw [reduceT, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, reduceModN_zetaP, gaussTowerEquiv_zetaP]

@[simp] theorem reduceT_zetaQ :
    reduceT n p q (zetaQ p q) = zetaQT n p q := by
  rw [reduceT, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, reduceModN_zetaQ, gaussTowerEquiv_zetaQ]

/-- **The kernel theorem, computable form**: `n` divides `x` in
`ℤ[ζ_p, ζ_q]` exactly when the image of `x` in the COMPUTABLE tower
vanishes — an equality test in `GaussTowerPQ` IS a congruence in
`ℤ[ζ_p, ζ_q]`. -/
theorem natCast_dvd_iff_reduceT (x : CycPQ p q) :
    ((n.toNat : ℕ) : CycPQ p q) ∣ x ↔ reduceT n p q x = 0 := by
  rw [natCast_dvd_iff_reduceModN n.toNat p q x, reduceT,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (EmbeddingLike.map_eq_zero_iff (f := gaussTowerEquiv n p q)).mp h

end AzPolyMod

end Azurite

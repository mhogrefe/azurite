/-
  **The step-5 content correspondence (soundness direction)**: a
  passing content-gcd check in the computable tower kills every
  common divisor of `n` and the symbolic element —

    `towerContentGcd n p q (reduceT x) = 1
       → ∀ d ∣ n, 1 < d → ¬ (d : ℤ[ζ_p, ζ_q]) ∣ x`
    (`not_dvd_of_towerContentGcd_eq_one`),

  which is exactly the shape the step-5 bridge
  (`h5_of_forall_coprime_content`-side) and the tower-form
  correctness theorem consume.

  The route avoids any representation-level induction through the
  division algorithm: multiplying by a CONSTANT never grows the
  degree, so no `modByMonic` reduction fires —
  `ofPoly` of an already-reduced polynomial is itself
  (`ofPoly_of_isReduced`, by `toAdjoin`-injectivity), the val of
  `ofCoeff d * S` is literally `C d * S.val`
  (`val_ofCoeff_mul`), and its coefficients are `d`-multiples
  (`coeff_C_mul`-semantics).  Applying this at both tower levels, a
  `d`-multiple (`d ∣ n`) has every flattened coefficient val
  divisible by `d`, hence `d` divides the seeded gcd fold
  (`dvd_towerContentGcd_of_grid`).
-/
import Azurite.AzPolyMod.Equiv.GaussSumT
import Azurite.AzNat.Equiv.Gcd

namespace Azurite

namespace AzPolyMod

open AzPolynomial

section Reduced

variable {R : Type _} [CommRing R] [DecidableEq R] [Nontrivial R]
  {f : AzPolynomial R} [hfact : Fact (AzPolynomial.toPoly f).Monic]

omit [DecidableEq R] [Nontrivial R] in
private theorem monic_f'' : (AzPolynomial.toPoly f).Monic := hfact.out

omit [DecidableEq R] in
private theorem ne_zero_f'' : AzPolynomial.toPoly f ≠ 0 := hfact.out.ne_zero

/-- `ofPoly` of an already-reduced polynomial is itself (canonicity,
by `toAdjoin`-injectivity — no division-algorithm induction). -/
theorem ofPoly_of_isReduced {P : AzPolynomial R}
    (hred : P.coeffs.size < f.coeffs.size ∨ f.coeffs.size = 0) :
    (ofPoly P : AzPolyMod f) = ⟨P, hred⟩ :=
  toAdjoin_injective monic_f'' ne_zero_f'' (by
    rw [toAdjoin_ofPoly monic_f'' ne_zero_f'']
    rfl)

omit [Nontrivial R] in
/-- The size of a constant multiple is bounded by the original. -/
theorem coeffs_size_C_mul_le (d : R) (P : AzPolynomial R) :
    (AzPolynomial.C d * P).coeffs.size ≤ P.coeffs.size := by
  by_cases h0 : (AzPolynomial.C d * P).coeffs.size = 0
  · omega
  · by_cases hP0 : P.coeffs.size = 0
    · exfalso
      have hP : P = 0 := by
        apply AzPolynomial.ext
        rw [show P.coeffs = #[] from Array.eq_empty_of_size_eq_zero hP0]
        rfl
      have hz : AzPolynomial.C d * P = 0 := by
        rw [← toPoly_inj, toPoly_mul, hP, toPoly_zero, mul_zero]
      rw [hz] at h0
      exact h0 rfl
    · have hdeg : (AzPolynomial.C d * P).natDegree ≤ P.natDegree := by
        rw [← AzPolynomial.natDegree_toPoly, ← AzPolynomial.natDegree_toPoly P,
          toPoly_mul, toPoly_C]
        exact Polynomial.natDegree_C_mul_le d (AzPolynomial.toPoly P)
      rw [AzPolynomial.natDegree, AzPolynomial.natDegree] at hdeg
      omega

/-- Constant multiplication acts on the reduced representative
literally: `(ofCoeff d * S).val = C d * S.val` (no reduction fires,
the degree does not grow). -/
theorem val_ofCoeff_mul (hf2 : 1 < f.coeffs.size) (d : R) (S : AzPolyMod f) :
    (ofCoeff d * S).val = AzPolynomial.C d * S.val := by
  have hCval : (ofCoeff d : AzPolyMod f).val = AzPolynomial.C d := by
    have hred : (AzPolynomial.C d).coeffs.size < f.coeffs.size
        ∨ f.coeffs.size = 0 := by
      left
      have hsize : (AzPolynomial.C d).coeffs.size ≤ 1 := by
        rw [AzPolynomial.C]
        split <;> simp
      omega
    rw [show (ofCoeff d : AzPolyMod f) = ofPoly (AzPolynomial.C d) from rfl,
      ofPoly_of_isReduced hred]
  have hmulred : (AzPolynomial.C d * S.val).coeffs.size < f.coeffs.size
      ∨ f.coeffs.size = 0 := by
    left
    rcases S.isReduced with h | h
    · exact lt_of_le_of_lt (coeffs_size_C_mul_le d S.val) h
    · omega
  have heq : ofCoeff d * S
      = (ofPoly (AzPolynomial.C d * S.val) : AzPolyMod f) := by
    apply toAdjoin_injective monic_f'' ne_zero_f''
    rw [toAdjoin_mul monic_f'' ne_zero_f'',
      toAdjoin_ofCoeff monic_f'' ne_zero_f'',
      toAdjoin_ofPoly monic_f'' ne_zero_f'', toPoly_mul, toPoly_C,
      map_mul, AdjoinRoot.mk_C]
    rfl
  rw [heq, ofPoly_of_isReduced hmulred]

omit [Nontrivial R] in
/-- The coefficients of a constant multiple are the scaled
coefficients. -/
theorem coeff_C_mul_az (d : R) (P : AzPolynomial R) (i : ℕ) :
    AzPolynomial.coeff (AzPolynomial.C d * P) i
      = d * AzPolynomial.coeff P i := by
  rw [← coeff_toPoly_eq, ← coeff_toPoly_eq, toPoly_mul, toPoly_C,
    Polynomial.coeff_C_mul]

omit [DecidableEq R] [Nontrivial R] in
/-- Every element of the coefficient array is a coefficient. -/
theorem mem_coeffs_eq_coeff {P : AzPolynomial R} {c : R}
    (hc : c ∈ P.coeffs) : ∃ i, c = AzPolynomial.coeff P i := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc
  refine ⟨i, ?_⟩
  rw [AzPolynomial.coeff, Array.getElem?_eq_getElem hi]
  rfl

end Reduced

section Content

variable (n : AzNat) (p q : ℕ) [Fact (1 < n.toNat)] [Fact p.Prime]
  [Fact q.Prime]

/-- Divisibility by `d` at the `AzZMod` level: a `(d : AzZMod n)`
multiple has `d`-divisible canonical residue, when `d ∣ n`. -/
private theorem dvd_val_natCast_mul {d : ℕ} (hdn : d ∣ n.toNat)
    (c : AzZMod n) : d ∣ (((d : ℕ) : AzZMod n) * c).val.toNat := by
  haveI : NeZero n.toNat :=
    ⟨by have := Fact.out (p := 1 < n.toNat); omega⟩
  have hval : (((d : ℕ) : AzZMod n) * c).val.toNat
      = (AzZMod.toZMod (((d : ℕ) : AzZMod n) * c)).val := by
    rw [AzZMod.toZMod, ZMod.val_natCast,
      Nat.mod_eq_of_lt (((d : ℕ) : AzZMod n) * c).isLt]
  rw [hval, AzZMod.toZMod_mul, AzZMod.toZMod_natCast, ZMod.val_mul,
    ZMod.val_natCast]
  exact (Nat.dvd_mod_iff hdn).mpr
    (Dvd.dvd.mul_right ((Nat.dvd_mod_iff hdn).mpr dvd_rfl) _)

/-- **The grid of a `d`-multiple is `d`-divisible** (`d ∣ n`): the
constant-multiplication analysis applied at both tower levels. -/
theorem grid_dvd_of_natCast_mul {d : ℕ} (hdn : d ∣ n.toNat)
    (S : GaussTowerPQ n p q) :
    ∀ c2 ∈ (((d : ℕ) : GaussTowerPQ n p q) * S).val.coeffs,
      ∀ c1 ∈ c2.val.coeffs, d ∣ c1.val.toNat := by
  have hq2 : 1 < (cyclotomicPrime (GaussTowerP n p) q).coeffs.size := by
    rw [cyclotomicPrime_coeffs_size]
    exact (Fact.out (p := q.Prime)).one_lt
  have hp2 : 1 < (cyclotomicPrime (AzZMod n) p).coeffs.size := by
    rw [cyclotomicPrime_coeffs_size]
    exact (Fact.out (p := p.Prime)).one_lt
  have hcast3 : ((d : ℕ) : GaussTowerPQ n p q)
      = ofCoeff ((d : ℕ) : GaussTowerP n p) := rfl
  intro c2 hc2 c1 hc1
  rw [hcast3, val_ofCoeff_mul hq2] at hc2
  obtain ⟨i, rfl⟩ := mem_coeffs_eq_coeff hc2
  rw [coeff_C_mul_az] at hc1
  have hcast2 : ((d : ℕ) : GaussTowerP n p)
      = ofCoeff ((d : ℕ) : AzZMod n) := rfl
  rw [hcast2, val_ofCoeff_mul hp2] at hc1
  obtain ⟨j, rfl⟩ := mem_coeffs_eq_coeff hc1
  rw [coeff_C_mul_az]
  exact dvd_val_natCast_mul n hdn _

omit [Fact q.Prime] in
/-- `d` divides the seeded gcd fold when it divides the seed and
every grid entry. -/
theorem dvd_towerContentGcd_of_grid {d : ℕ} (hdn : d ∣ n.toNat)
    (T : GaussTowerPQ n p q)
    (hgrid : ∀ c2 ∈ T.val.coeffs, ∀ c1 ∈ c2.val.coeffs,
      d ∣ c1.val.toNat) :
    d ∣ (towerContentGcd n p q T).toNat := by
  rw [towerContentGcd]
  have houter : ∀ (l : List (GaussTowerP n p)) (acc : AzNat),
      d ∣ acc.toNat →
      (∀ c2 ∈ l, ∀ c1 ∈ c2.val.coeffs, d ∣ c1.val.toNat) →
      d ∣ (l.foldl (fun acc' c2 =>
        c2.val.coeffs.foldl (fun acc'' c1 => AzNat.gcd acc'' c1.val)
          acc') acc).toNat := by
    intro l
    induction l with
    | nil => intro acc hacc _; simpa using hacc
    | cons c2 l ih =>
      intro acc hacc hl
      rw [List.foldl_cons]
      refine ih _ ?_ (fun c2' hc2' => hl c2' (List.mem_cons_of_mem _ hc2'))
      -- the inner fold over `c2.val.coeffs`
      have hinner : ∀ (l1 : List (AzZMod n)) (acc1 : AzNat),
          d ∣ acc1.toNat → (∀ c1 ∈ l1, d ∣ c1.val.toNat) →
          d ∣ (l1.foldl (fun acc'' c1 => AzNat.gcd acc'' c1.val)
            acc1).toNat := by
        intro l1
        induction l1 with
        | nil => intro acc1 hacc1 _; simpa using hacc1
        | cons c1 l1 ih1 =>
          intro acc1 hacc1 hl1
          rw [List.foldl_cons]
          refine ih1 _ ?_ (fun c hc => hl1 c (List.mem_cons_of_mem _ hc))
          rw [AzNat.toNat_gcd]
          exact Nat.dvd_gcd hacc1 (hl1 c1 List.mem_cons_self)
      rw [← Array.foldl_toList]
      refine hinner _ _ hacc ?_
      intro c1 hc1
      exact hl c2 List.mem_cons_self c1 (by simpa using hc1)
  rw [← Array.foldl_toList]
  refine houter _ _ hdn ?_
  intro c2 hc2
  exact hgrid c2 (by simpa using hc2)

/-- **Step-5 rail soundness**: a passing content-gcd check in the
computable tower kills every common divisor of `n` and the symbolic
element — the exact hypothesis shape of the step-5 bridge and the
tower-form correctness theorem. -/
theorem not_dvd_of_towerContentGcd_eq_one (x : CP.CycPQ p q)
    (hgcd : (towerContentGcd n p q (reduceT n p q x)).toNat = 1) :
    ∀ d, d ∣ n.toNat → 1 < d → ¬(d : CP.CycPQ p q) ∣ x := by
  intro d hdn hd1 hdvd
  obtain ⟨y, rfl⟩ := hdvd
  have hred : reduceT n p q ((d : CP.CycPQ p q) * y)
      = ((d : ℕ) : GaussTowerPQ n p q) * reduceT n p q y := by
    rw [map_mul, map_natCast]
  have hgrid := grid_dvd_of_natCast_mul n p q hdn (reduceT n p q y)
  rw [← hred] at hgrid
  have hdg := dvd_towerContentGcd_of_grid n p q hdn _ hgrid
  rw [hgcd] at hdg
  exact absurd (Nat.dvd_one.mp hdg) (by omega)

end Content

end AzPolyMod

end Azurite

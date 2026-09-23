/-
  Gathen–Gerhard, "Modern Computer Algebra", Theorem 14.2:

  For a finite field `F` with `q` elements and any `d ≥ 1`, the polynomial
  `X^(q^d) − X ∈ F[X]` is the product of all monic irreducible polynomials
  in `F[X]` whose degree divides `d`.

  The working form is the divisibility criterion (stated WITHOUT `d ≠ 0`,
  where both sides hold trivially): for irreducible `f`,

    `f ∣ X^(q^d) − X  ↔  natDegree f ∣ d`.

  The FORWARD direction is already in Mathlib
  (`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`, following the
  book's subfield argument through `FiniteField.Extension`). The REVERSE
  direction is the book's: with `n = deg f` dividing `d`, pass to
  `K = F[x]/⟨f⟩` (a field with `q^n` elements), where the root
  `a = x mod f` satisfies `a^(q^n) = a` by Fermat (GG 14.1 =
  `FiniteField.pow_card`), hence `a^(q^d) = a`; so `f`, being `a`'s minimal
  polynomial (up to the leading unit), divides `X^(q^d) − X`. Lean's
  `minpoly.dvd` absorbs the book's gcd-descent (Example 6.19 — "the gcd
  over `F_{q^n}` already has coefficients in `F_q`"): minimality over the
  BASE field is exactly what the gcd argument establishes.

  Squarefreeness is by separability (`galois_poly_separable`: the
  derivative is `−1` in characteristic `p ∣ q^d`), replacing the book's
  double-root argument. The product form then falls out of unique
  factorization: the normalized factors of a monic squarefree polynomial
  are duplicate-free, multiply to it, and are characterized by the
  divisibility criterion.
-/
import Mathlib.FieldTheory.Finite.Extension

namespace Azurite

namespace GG

open Polynomial FiniteField UniqueFactorizationMonoid

variable {F : Type*} [Field F] [Fintype F]

/-- The reverse direction of the criterion (GG's second half): an
irreducible polynomial whose degree divides `d` divides `X^(q^d) − X`.
Fermat's little theorem in `F[x]/⟨f⟩` plus minimality over the base
field. -/
theorem dvd_X_pow_card_pow_sub_X_of_natDegree_dvd {d : ℕ} {f : F[X]}
    (hf : Irreducible f) (hdvd : f.natDegree ∣ d) :
    f ∣ X ^ Fintype.card F ^ d - X := by
  have hf0 : f ≠ 0 := hf.ne_zero
  have : Fact (Irreducible f) := ⟨hf⟩
  -- `K = F[x]/⟨f⟩` is a field with `q ^ deg f` elements
  have : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have : Finite (AdjoinRoot f) := Module.finite_of_finite F
  have : Fintype (AdjoinRoot f) := Fintype.ofFinite (AdjoinRoot f)
  have hcard : Fintype.card (AdjoinRoot f) = Fintype.card F ^ f.natDegree := by
    rw [Module.card_eq_pow_finrank (K := F) (V := AdjoinRoot f),
      (AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim]
  obtain ⟨e, rfl⟩ := hdvd
  -- the root satisfies `a^(q^(n·e)) = a` by Fermat in `K`
  have haQ : AdjoinRoot.root f ^ Fintype.card F ^ (f.natDegree * e)
      = AdjoinRoot.root f := by
    rw [pow_mul, ← hcard]
    exact FiniteField.pow_card_pow e (AdjoinRoot.root f)
  have haeval : Polynomial.aeval (AdjoinRoot.root f)
      (X ^ Fintype.card F ^ (f.natDegree * e) - X : F[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, haQ, sub_self]
  -- so `a`'s minimal polynomial — `f` up to its leading unit — divides
  have hmin := minpoly.dvd F (AdjoinRoot.root f) haeval
  rw [AdjoinRoot.minpoly_root hf0] at hmin
  exact (dvd_mul_right f (C f.leadingCoeff⁻¹)).trans hmin

/-- **The divisibility criterion** (the working form of GG Theorem 14.2):
an irreducible `f` divides `X^(q^d) − X` exactly when `deg f` divides `d`.
(At `d = 0` both sides hold trivially: the polynomial is `0`.) -/
theorem irreducible_dvd_X_pow_card_pow_sub_X_iff {d : ℕ} {f : F[X]}
    (hf : Irreducible f) :
    f ∣ X ^ Fintype.card F ^ d - X ↔ f.natDegree ∣ d := by
  constructor
  · intro h
    exact hf.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
      (by rw [Nat.card_eq_fintype_card]; exact h)
  · exact dvd_X_pow_card_pow_sub_X_of_natDegree_dvd hf

/-- `X^(q^d) − X` is squarefree for `d ≥ 1`: it is separable (its
derivative is `−1` in characteristic `p ∣ q^d`). -/
theorem squarefree_X_pow_card_pow_sub_X {d : ℕ} (hd : d ≠ 0) :
    Squarefree (X ^ Fintype.card F ^ d - X : F[X]) := by
  obtain ⟨p, hchar⟩ := CharP.exists F
  have hp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨k, -, hcard⟩ := FiniteField.card F p
  refine (galois_poly_separable p (Fintype.card F ^ d) ?_).squarefree
  rw [hcard]
  exact dvd_pow (dvd_pow_self p k.2.ne') hd

/-- `X^(q^d) − X` is monic for `d ≥ 1`. -/
theorem monic_X_pow_card_pow_sub_X {d : ℕ} (hd : d ≠ 0) :
    (X ^ Fintype.card F ^ d - X : F[X]).Monic := by
  have h2 : 2 ≤ Fintype.card F ^ d :=
    le_trans Fintype.one_lt_card (Nat.le_self_pow hd (Fintype.card F))
  refine Polynomial.monic_X_pow_sub (R := F) (p := X) ?_
  rw [Polynomial.degree_X]
  exact_mod_cast h2

/-- The factor set of GG Theorem 14.2: membership in the (duplicate-free)
factor multiset of `X^(q^d) − X` is exactly "monic, irreducible, degree
dividing `d`". -/
theorem mem_normalizedFactors_X_pow_card_pow_sub_X_iff [DecidableEq F]
    {d : ℕ} (hd : d ≠ 0) {f : F[X]} :
    f ∈ normalizedFactors (X ^ Fintype.card F ^ d - X : F[X])
      ↔ f.Monic ∧ Irreducible f ∧ f.natDegree ∣ d := by
  classical
  have h0 : (X ^ Fintype.card F ^ d - X : F[X]) ≠ 0 :=
    (monic_X_pow_card_pow_sub_X hd).ne_zero
  rw [mem_normalizedFactors_iff' h0]
  constructor
  · rintro ⟨hirr, hnorm, hdvd⟩
    exact ⟨(Polynomial.normalize_eq_self_iff_monic hirr.ne_zero).mp hnorm, hirr,
      (irreducible_dvd_X_pow_card_pow_sub_X_iff hirr).mp hdvd⟩
  · rintro ⟨hmonic, hirr, hdeg⟩
    exact ⟨hirr, hmonic.normalize_eq_self,
      (irreducible_dvd_X_pow_card_pow_sub_X_iff hirr).mpr hdeg⟩

/-- The factor multiset is duplicate-free (squarefreeness), so it is
honestly a SET of polynomials. -/
theorem nodup_normalizedFactors_X_pow_card_pow_sub_X [DecidableEq F] {d : ℕ}
    (hd : d ≠ 0) :
    (normalizedFactors (X ^ Fintype.card F ^ d - X : F[X])).Nodup :=
  (squarefree_iff_nodup_normalizedFactors
    (monic_X_pow_card_pow_sub_X hd).ne_zero).mp
    (squarefree_X_pow_card_pow_sub_X hd)

/-- **GG Theorem 14.2.** For `d ≥ 1`, `X^(q^d) − X` is the product of all
monic irreducible polynomials over `F` whose degree divides `d` — stated as
the product over its (duplicate-free) factor set, whose membership is
characterized by `mem_normalizedFactors_X_pow_card_pow_sub_X_iff`. -/
theorem X_pow_card_pow_sub_X_eq_prod [DecidableEq F] {d : ℕ} (hd : d ≠ 0) :
    (X ^ Fintype.card F ^ d - X : F[X])
      = (normalizedFactors (X ^ Fintype.card F ^ d - X : F[X])).toFinset.prod id := by
  classical
  have hmonic := monic_X_pow_card_pow_sub_X (F := F) (d := d) hd
  have h0 : (X ^ Fintype.card F ^ d - X : F[X]) ≠ 0 := hmonic.ne_zero
  have hnodup := nodup_normalizedFactors_X_pow_card_pow_sub_X (F := F) (d := d) hd
  -- the Finset product is the multiset product (no duplicates)
  have hfin : (normalizedFactors (X ^ Fintype.card F ^ d - X : F[X])).toFinset.prod id
      = (normalizedFactors (X ^ Fintype.card F ^ d - X : F[X])).prod := by
    rw [Finset.prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup,
      Multiset.map_id]
  rw [hfin]
  -- the multiset product is associated to the polynomial; both are monic
  have hassoc := prod_normalizedFactors h0
  have hprodmonic : (normalizedFactors (X ^ Fintype.card F ^ d - X : F[X])).prod.Monic := by
    refine Polynomial.monic_multiset_prod_of_monic _ _ ?_
    intro g hg
    exact Polynomial.monic_normalize (irreducible_of_factor g hg).ne_zero
  exact (Polynomial.eq_of_monic_of_associated hprodmonic hmonic hassoc).symm

/-- **The Ben-Or irreducibility criterion** (the mathematics of the
distinct-degree irreducibility test; Crandall–Pomerance Algorithm
2.2.9): a monic `f` of positive degree over a finite field is
irreducible exactly when `X^(q^i) − X` is coprime to `f` for every
`i` up to half the degree.  A reducible `f` has an irreducible factor
`g` of degree at most `(deg f)/2`, which divides both `f` and
`X^(q^(deg g)) − X`; conversely an irreducible `f` divides no
`X^(q^i) − X` with `0 < i < deg f`. -/
theorem irreducible_iff_isCoprime_X_pow_card_pow_sub_X {f : F[X]}
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Irreducible f ↔ ∀ i : ℕ, 1 ≤ i → 2 * i ≤ f.natDegree →
      IsCoprime (X ^ Fintype.card F ^ i - X) f := by
  constructor
  · intro hirr i hi1 hi2
    have hnd : ¬f ∣ X ^ Fintype.card F ^ i - X := by
      intro hdvd
      have hdvd' := (irreducible_dvd_X_pow_card_pow_sub_X_iff hirr).mp hdvd
      have := Nat.le_of_dvd hi1 hdvd'
      omega
    exact ((hirr.coprime_iff_not_dvd).mpr hnd).symm
  · intro hall
    by_contra hnirr
    have hfu : ¬IsUnit f := by
      intro hu
      have := natDegree_eq_zero_of_isUnit hu
      omega
    -- a nonunit nonzero polynomial over a field has positive degree
    have hdeg_pos : ∀ c : F[X], c ≠ 0 → ¬IsUnit c → 0 < c.natDegree := by
      intro c hc0 hcu
      rcases Nat.eq_zero_or_pos c.natDegree with h0 | h
      · obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.mp h0
        refine absurd (isUnit_C.mpr (isUnit_iff_ne_zero.mpr fun hx0 => ?_)) (hx ▸ hcu)
        rw [← hx, hx0, C_0] at hc0
        exact hc0 rfl
      · exact h
    -- split off two nonunit factors and keep the smaller
    rw [irreducible_iff] at hnirr
    push Not at hnirr
    obtain ⟨a, b, hab, hau, hbu⟩ := hnirr hfu
    have ha0 : a ≠ 0 := fun h => hf.ne_zero (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hf.ne_zero (by rw [hab, h, mul_zero])
    have hadeg := hdeg_pos a ha0 hau
    have hbdeg := hdeg_pos b hb0 hbu
    have hsum : a.natDegree + b.natDegree = f.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha0 hb0]
    obtain ⟨c, hc0, hcu, hcdvd, hcdeg⟩ :
        ∃ c : F[X], c ≠ 0 ∧ ¬IsUnit c ∧ c ∣ f ∧
          2 * c.natDegree ≤ f.natDegree := by
      rcases Nat.le_total a.natDegree b.natDegree with h | h
      · exact ⟨a, ha0, hau, ⟨b, hab⟩, by omega⟩
      · exact ⟨b, hb0, hbu, ⟨a, by rw [hab, mul_comm]⟩, by omega⟩
    -- an irreducible factor of the smaller piece is caught by the sweep
    obtain ⟨g, hgirr, hgdvd⟩ := WfDvdMonoid.exists_irreducible_factor hcu hc0
    have hgdeg : g.natDegree ≤ c.natDegree :=
      Polynomial.natDegree_le_of_dvd hgdvd hc0
    have hg1 : 1 ≤ g.natDegree := hdeg_pos g hgirr.ne_zero hgirr.not_isUnit
    have hgX : g ∣ X ^ Fintype.card F ^ g.natDegree - X :=
      dvd_X_pow_card_pow_sub_X_of_natDegree_dvd hgirr dvd_rfl
    have hcop := hall g.natDegree hg1 (by omega)
    exact hgirr.not_isUnit (hcop.isUnit_of_dvd' hgX (hgdvd.trans hcdvd))

end GG

end Azurite

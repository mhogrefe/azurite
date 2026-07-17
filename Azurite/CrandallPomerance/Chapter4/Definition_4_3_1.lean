/-
  Crandall–Pomerance, Definition 4.3.1 and its accompanying remark
  (corrected).

  The DEFINITION — `f, g ∈ Z_n[x]` are coprime when the ideal they
  generate is all of `Z_n[x]`, i.e. `af + bg = 1` for some `a, b` —
  is verbatim Mathlib's `IsCoprime`, instantiated at
  `Polynomial (ZMod n)`; the ideal-language reading is
  `Ideal.sup_eq_top_iff_isCoprime`.  Nothing to add.

  The REMARK — "it is not so hard to prove that every ideal in
  `Z_n[x]` is principally generated if and only if `n` is prime" — is
  FALSE as printed (the fifth erratum caught in this chapter): for
  `n = 6`, CRT gives `Z_6[x] ≅ Z_2[x] × Z_3[x]`, and a product of
  principal ideal rings is a principal ideal ring.  Concretely, the
  suspect ideal `(2, x) ⊆ Z_6[x]` equals `(3x + 4)`:
  `2·(3x + 4) = 2`, `(4x + 3)(3x + 4) = x`, `3x + 4 = 3·x + 2·2`.

  The CORRECT statement, proven below
  (`polynomial_zmod_isPrincipalIdealRing_iff`):

    `Z_n[x]` is a principal ideal ring  ⟺  `n` is squarefree.

  Forward: if `R[X]` is a principal ideal ring then `R` is REDUCED
  (`isReduced_of_polynomial_isPrincipalIdealRing`, valid over any
  commutative ring): a square-zero `ε ≠ 0` makes the ideal `(ε, x)`
  non-principal, by a four-line computation with the constant and
  linear coefficients of a putative generator.  Then Mathlib's
  `isReduced_zmod : IsReduced (ZMod n) ↔ Squarefree n ∨ n = 0`
  finishes (the case `n = 0` — `Z[x]` — dies by
  `Ideal.IsField.of_isPrincipalIdealRing_polynomial`, since `ℤ` is
  not a field).  Backward: strong induction splitting off the least
  prime factor; squarefreeness makes the split coprime, CRT and the
  splitting `(R × S)[X] ≅ R[X] × S[X]` reduce to the field case.
-/
import Mathlib.RingTheory.ZMod
import Mathlib.RingTheory.Ideal.Prod
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum.GCD

namespace Azurite

namespace CP

open Polynomial

/-! ### A non-reduced coefficient ring kills principality -/

/-- A non-reduced commutative ring contains a nonzero square-zero
element. -/
private theorem exists_sq_eq_zero {R : Type*} [CommRing R]
    (h : ¬IsReduced R) : ∃ ε : R, ε ≠ 0 ∧ ε * ε = 0 := by
  have haux : ∀ m (x : R), x ^ m = 0 → x ≠ 0 →
      ∃ ε : R, ε ≠ 0 ∧ ε * ε = 0 := by
    intro m
    induction m with
    | zero =>
      intro x h0 hx
      rw [pow_zero] at h0
      exact absurd (by rw [← mul_one x, h0, mul_zero]) hx
    | succ m ih =>
      intro x h0 hx
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [pow_one] at h0
        exact absurd h0 hx
      by_cases hxm : x ^ m = 0
      · exact ih x hxm hx
      · refine ⟨x ^ m, hxm, ?_⟩
        calc x ^ m * x ^ m = x ^ (m + 1) * x ^ (m - 1) := by
              rw [← pow_add, ← pow_add]
              congr 1
              omega
        _ = 0 := by rw [h0, zero_mul]
  rw [isReduced_iff] at h
  push Not at h
  obtain ⟨x, ⟨m, hm⟩, hx⟩ := h
  exact haux m x hm hx

/-- If `R[X]` is a principal ideal ring then `R` is reduced: for a
square-zero `ε ≠ 0` the ideal `(ε, X)` cannot be principal.  (This is
the mathematical content behind the corrected book remark, over an
arbitrary commutative ring.) -/
theorem isReduced_of_polynomial_isPrincipalIdealRing (R : Type*)
    [CommRing R] [IsPrincipalIdealRing R[X]] : IsReduced R := by
  by_contra hred
  obtain ⟨ε, hε0, hsq⟩ := exists_sq_eq_zero hred
  obtain ⟨h, hI⟩ :=
    (IsPrincipalIdealRing.principal (Ideal.span {C ε, X})).principal
  have hI' : Ideal.span {C ε, X} = Ideal.span ({h} : Set R[X]) := hI
  -- the three memberships
  have hmemh : h ∈ Ideal.span ({C ε, X} : Set R[X]) := by
    rw [hI']
    exact Ideal.mem_span_singleton_self h
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmemh
  have hmemC : C ε ∈ Ideal.span ({h} : Set R[X]) := by
    rw [← hI']
    exact Ideal.subset_span (by simp)
  obtain ⟨g, hgc⟩ := Ideal.mem_span_singleton'.mp hmemC
  have hmemX : (X : R[X]) ∈ Ideal.span ({h} : Set R[X]) := by
    rw [← hI']
    exact Ideal.subset_span (by simp)
  obtain ⟨f, hfc⟩ := Ideal.mem_span_singleton'.mp hmemX
  -- constant and linear coefficients
  have h0 : h.coeff 0 = a.coeff 0 * ε := by
    have hc := congrArg (fun q : R[X] => q.coeff 0) hab
    simpa [mul_coeff_zero] using hc.symm
  have hC0 : g.coeff 0 * h.coeff 0 = ε := by
    have hc := congrArg (fun q : R[X] => q.coeff 0) hgc
    simpa [mul_coeff_zero] using hc
  have hX0 : f.coeff 0 * h.coeff 0 = 0 := by
    have hc := congrArg (fun q : R[X] => q.coeff 0) hfc
    simpa [mul_coeff_zero] using hc
  have hX1 : f.coeff 0 * h.coeff 1 + f.coeff 1 * h.coeff 0 = 1 := by
    have hc := congrArg (fun q : R[X] => q.coeff 1) hfc
    rw [coeff_X_one, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
    simpa [Finset.sum_range_succ] using hc
  -- the four-line contradiction
  have hεf0 : ε * f.coeff 0 = 0 := by
    linear_combination (-(f.coeff 0)) * hC0 + g.coeff 0 * hX0
  have hεh0 : ε * h.coeff 0 = 0 := by
    linear_combination ε * h0 + a.coeff 0 * hsq
  have : ε = 0 := by
    linear_combination (-ε) * hX1 + h.coeff 1 * hεf0 + f.coeff 1 * hεh0
  exact hε0 this

/-! ### Products of principal ideal rings -/

/-- A product of two principal ideal rings is a principal ideal ring:
each ideal is a product of ideals, generated by the pair of
generators. -/
private theorem isPrincipalIdealRing_prod (R S : Type*) [CommRing R]
    [CommRing S] [IsPrincipalIdealRing R] [IsPrincipalIdealRing S] :
    IsPrincipalIdealRing (R × S) := by
  refine ⟨fun I => ?_⟩
  obtain ⟨g₁, hg₁⟩ :=
    (IsPrincipalIdealRing.principal (I.map (RingHom.fst R S))).principal
  obtain ⟨g₂, hg₂⟩ :=
    (IsPrincipalIdealRing.principal (I.map (RingHom.snd R S))).principal
  refine ⟨⟨(g₁, g₂), ?_⟩⟩
  conv_lhs => rw [Ideal.ideal_prod_eq I]
  rw [hg₁, hg₂]
  ext x
  rw [Ideal.mem_prod, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨⟨c₁, hc₁⟩, c₂, hc₂⟩
    exact ⟨(c₁, c₂), Prod.ext hc₁ hc₂⟩
  · rintro ⟨⟨c₁, c₂⟩, hc⟩
    exact ⟨⟨c₁, congrArg Prod.fst hc⟩, ⟨c₂, congrArg Prod.snd hc⟩⟩

/-- Polynomials over a product split: the coefficientwise projection
pair `(R × S)[X] → R[X] × S[X]` is bijective. -/
private theorem polynomial_prod_bijective (R S : Type*) [CommRing R]
    [CommRing S] :
    Function.Bijective ⇑((mapRingHom (RingHom.fst R S)).prod
      (mapRingHom (RingHom.snd R S))) := by
  constructor
  · intro p q hpq
    simp only [RingHom.prod_apply, Prod.mk.injEq, coe_mapRingHom] at hpq
    obtain ⟨h1, h2⟩ := hpq
    refine Polynomial.ext fun k => ?_
    have e1 := congrArg (fun q : Polynomial R => q.coeff k) h1
    have e2 := congrArg (fun q : Polynomial S => q.coeff k) h2
    simp only [coeff_map, RingHom.coe_fst, RingHom.coe_snd] at e1 e2
    exact Prod.ext e1 e2
  · rintro ⟨q, r⟩
    refine ⟨q.sum (fun k a => C ((a, (0 : S)) : R × S) * X ^ k)
      + r.sum (fun k b => C (((0 : R), b) : R × S) * X ^ k), ?_⟩
    have hqfst : Polynomial.map (RingHom.fst R S)
        (q.sum (fun k a => C ((a, (0 : S)) : R × S) * X ^ k)) = q := by
      rw [Polynomial.sum_def, Polynomial.map_sum]
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        Polynomial.map_X, RingHom.coe_fst]
      exact Polynomial.sum_C_mul_X_pow_eq q
    have hrfst : Polynomial.map (RingHom.fst R S)
        (r.sum (fun k b => C (((0 : R), b) : R × S) * X ^ k)) = 0 := by
      rw [Polynomial.sum_def, Polynomial.map_sum]
      simp
    have hqsnd : Polynomial.map (RingHom.snd R S)
        (q.sum (fun k a => C ((a, (0 : S)) : R × S) * X ^ k)) = 0 := by
      rw [Polynomial.sum_def, Polynomial.map_sum]
      simp
    have hrsnd : Polynomial.map (RingHom.snd R S)
        (r.sum (fun k b => C (((0 : R), b) : R × S) * X ^ k)) = r := by
      rw [Polynomial.sum_def, Polynomial.map_sum]
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        Polynomial.map_X, RingHom.coe_snd]
      exact Polynomial.sum_C_mul_X_pow_eq r
    simp only [RingHom.prod_apply, coe_mapRingHom, Prod.mk.injEq]
    constructor
    · rw [Polynomial.map_add, hqfst, hrfst, add_zero]
    · rw [Polynomial.map_add, hqsnd, hrsnd, zero_add]

/-- The splitting `(R × S)[X] ≃+* R[X] × S[X]`. -/
private noncomputable def polynomialProdEquiv (R S : Type*) [CommRing R]
    [CommRing S] : Polynomial (R × S) ≃+* Polynomial R × Polynomial S :=
  RingEquiv.ofBijective _ (polynomial_prod_bijective R S)

/-! ### The corrected remark -/

/-- Squarefree `n` makes `Z_n[x]` a principal ideal ring: strong
induction splitting off the least prime factor, CRT, and the
polynomial product splitting reduce to the field case. -/
private theorem pir_of_squarefree :
    ∀ n : ℕ, Squarefree n → IsPrincipalIdealRing (Polynomial (ZMod n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hsf
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact not_squarefree_zero hsf
    rcases eq_or_ne n 1 with rfl | hn1
    · -- the zero ring: the unique ideal is `span {0}`
      refine ⟨fun I => ⟨0, ?_⟩⟩
      ext p
      have hp0 : p = 0 := Subsingleton.elim p 0
      subst hp0
      simp
    by_cases hp : n.Prime
    · haveI := Fact.mk hp
      exact inferInstance
    · obtain ⟨p, hpp, m, hm⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m :=
        ⟨n.minFac, Nat.minFac_prime hn1, n / n.minFac,
          (Nat.mul_div_cancel' n.minFac_dvd).symm⟩
      subst hm
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hn0
        exact hn0 rfl
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [mul_one] at hp
        exact hp hpp
      have hmlt : m < p * m := by
        have h2m : 2 * m ≤ p * m := Nat.mul_le_mul_right m hpp.two_le
        omega
      have hco : Nat.Coprime p m := by
        rw [Nat.Prime.coprime_iff_not_dvd hpp]
        intro hdvd
        have hsq : p * p ∣ p * m := mul_dvd_mul_left p hdvd
        exact hpp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p hsq))
      have hmsf : Squarefree m := hsf.squarefree_of_dvd ⟨p, by ring⟩
      haveI hP1 : IsPrincipalIdealRing (Polynomial (ZMod p)) := by
        haveI := Fact.mk hpp
        exact inferInstance
      haveI hP2 : IsPrincipalIdealRing (Polynomial (ZMod m)) :=
        ih m hmlt hmsf
      haveI : IsPrincipalIdealRing (Polynomial (ZMod p) × Polynomial (ZMod m)) :=
        isPrincipalIdealRing_prod _ _
      have e : Polynomial (ZMod (p * m))
          ≃+* Polynomial (ZMod p) × Polynomial (ZMod m) :=
        (Polynomial.mapEquiv (ZMod.chineseRemainder hco)).trans
          (polynomialProdEquiv _ _)
      exact IsPrincipalIdealRing.of_surjective e.symm.toRingHom
        e.symm.surjective

/-- **The corrected remark accompanying Definition 4.3.1**: `Z_n[x]`
is a principal ideal ring IF AND ONLY IF `n` is squarefree — not, as
the book states, iff `n` is prime (`Z_6[x]` is a principal ideal
ring: `(2, x) = (3x + 4)`).  Compare Mathlib's
`isReduced_zmod : IsReduced (ZMod n) ↔ Squarefree n ∨ n = 0`. -/
theorem polynomial_zmod_isPrincipalIdealRing_iff (n : ℕ) :
    IsPrincipalIdealRing (Polynomial (ZMod n)) ↔ Squarefree n := by
  constructor
  · intro hpir
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- `Z[x]` is not a principal ideal ring, since `ℤ` is not a field
      exfalso
      have hfield : IsField (ZMod 0) :=
        Ideal.IsField.of_isPrincipalIdealRing_polynomial
      obtain ⟨b, hb⟩ := hfield.mul_inv_cancel
        (show (2 : ZMod 0) ≠ 0 by decide)
      have hu : IsUnit (2 : ZMod 0) := IsUnit.of_mul_eq_one b hb
      have hu' : IsUnit (2 : ℤ) := hu
      rcases Int.isUnit_iff.mp hu' with h | h <;> norm_num at h
    · have hred : IsReduced (ZMod n) :=
        isReduced_of_polynomial_isPrincipalIdealRing _
      rcases isReduced_zmod.mp hred with h | h
      · exact h
      · omega
  · exact pir_of_squarefree n

section Examples

-- the book's claimed equivalence fails already at `n = 6`:
example : IsPrincipalIdealRing (Polynomial (ZMod 6)) :=
  (polynomial_zmod_isPrincipalIdealRing_iff 6).mpr (by
    rw [show (6 : ℕ) = 2 * 3 by norm_num,
      Nat.squarefree_mul (by norm_num)]
    exact ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩)

-- while non-squarefree moduli genuinely fail:
example : ¬IsPrincipalIdealRing (Polynomial (ZMod 4)) := fun h => by
  have hsf := (polynomial_zmod_isPrincipalIdealRing_iff 4).mp h
  have h2 := Nat.isUnit_iff.mp (hsf 2 (by norm_num))
  norm_num at h2

example : ¬IsPrincipalIdealRing (Polynomial (ZMod 12)) := fun h => by
  have hsf := (polynomial_zmod_isPrincipalIdealRing_iff 12).mp h
  have h2 := Nat.isUnit_iff.mp (hsf 2 (by norm_num))
  norm_num at h2

end Examples

end CP

end Azurite
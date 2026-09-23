/-
  Crandall–Pomerance, Theorem 4.2.2: with `f(x) = x² − ax + b`,
  `Δ = a² − 4b`, and `p` a prime not dividing `2bΔ`,

    `r_f(p) ∣ p − (Δ/p)`,

  where `(Δ/p)` is the Legendre symbol.

  The engine is the book's Theorem 3.6.3, the Lucas analogue of
  Fermat's little theorem: `p ∣ U_{p − (Δ/p)}`.  Two cases:

  * `(Δ/p) = 1`: `f` splits mod `p` with distinct roots
    `α, β = (a ± √Δ)/2 ∈ ZMod p`, both nonzero (their product is
    `b ≢ 0`); Fermat gives `α^(p−1) = β^(p−1) = 1`, so
    `U_{p−1}·(α − β) = 0` with `α − β = √Δ ≠ 0`, whence `p ∣ U_{p−1}`.

  * `(Δ/p) = −1`: `f` has no root mod `p` (a root `γ` would give
    `(2γ − a)² = Δ`), hence is irreducible, and `K = ZMod p[x]/(f)` is
    the field `GF(p²)`.  The Frobenius `x ↦ x^p` maps the root `α` to a
    root of `f`; it cannot fix `α` (the fixed points of Frobenius are
    the `p` roots of `X^p − X`, which the prime field already
    exhausts), so `α^p = β` and symmetrically `β^p = α`.  Then
    `α^(p+1) = βα = b = αβ = β^(p+1)`, so `U_{p+1}·(α − β) = 0` with
    `(α − β)² = Δ ≠ 0`, whence `p ∣ U_{p+1}`.

  Theorem 4.2.2 follows by the rank-divisibility characterization:
  `p ∣ U_j ↔ r_f(p) ∣ j`.
-/
import Azurite.CrandallPomerance.Chapter4.LucasSequences
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.CharP.Algebra

namespace Azurite

namespace CP

open Polynomial

variable {a b : ℤ} {p : ℕ} [Fact p.Prime]

/-- **The split case of Theorem 3.6.3**: if `Δ` is a nonzero square
mod `p` (and `p ∤ 2b`), then `p ∣ U_{p−1}`. -/
theorem lucasU_card_sub_one (hp2 : p ≠ 2) (hb : ¬(p : ℤ) ∣ b)
    (hsq : IsSquare ((a ^ 2 - 4 * b : ℤ) : ZMod p))
    (hΔ0 : ((a ^ 2 - 4 * b : ℤ) : ZMod p) ≠ 0) :
    (p : ℤ) ∣ lucasU a b (p - 1) := by
  obtain ⟨s, hs⟩ := hsq
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring,
      ZMod.natCast_eq_zero_iff] at h
    have h1 := Nat.le_of_dvd (by norm_num) h
    have h2 := (Fact.out (p := p.Prime)).two_le
    exact hp2 (by omega)
  set α : ZMod p := (((a : ℤ) : ZMod p) + s) * (2 : ZMod p)⁻¹ with hα
  set β : ZMod p := (((a : ℤ) : ZMod p) - s) * (2 : ZMod p)⁻¹ with hβ
  have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ h2
  have hsum : α + β = ((a : ℤ) : ZMod p) := by
    rw [hα, hβ]
    field_simp
    ring
  have hprod : α * β = ((b : ℤ) : ZMod p) := by
    rw [hα, hβ]
    have hΔ : ((a : ℤ) : ZMod p) ^ 2 - s * s
        = 4 * ((b : ℤ) : ZMod p) := by
      push_cast at hs
      linear_combination hs
    field_simp
    linear_combination hΔ
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hb
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hprod, h0, mul_zero]
  have hα0 : α ≠ 0 := by
    intro h0
    apply hb
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hprod, h0, zero_mul]
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs
    exact hΔ0 hs
  have hαβ : α - β ≠ 0 := by
    intro h0
    apply hs0
    have h1 : (α - β) * 2 = 2 * s * ((2 : ZMod p)⁻¹ * 2) := by
      rw [hα, hβ]
      ring
    rw [h0, zero_mul, mul_comm ((2 : ZMod p))⁻¹ 2, h2inv, mul_one] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h h2
    · exact h
  have hU := lucasU_spec hsum hprod (p - 1)
  rw [ZMod.pow_card_sub_one_eq_one hα0, ZMod.pow_card_sub_one_eq_one hβ0,
    sub_self] at hU
  rcases mul_eq_zero.mp hU with h0 | h0
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  · exact absurd h0 hαβ

/-- **The inert case of Theorem 3.6.3**: if `Δ` is not a square mod `p`
(and `p ∤ 2b`), then `p ∣ U_{p+1}` — via Frobenius in `GF(p²)`. -/
theorem lucasU_card_add_one
    (hnsq : ¬IsSquare ((a ^ 2 - 4 * b : ℤ) : ZMod p)) :
    (p : ℤ) ∣ lucasU a b (p + 1) := by
  set A : ZMod p := ((a : ℤ) : ZMod p) with hA
  set B : ZMod p := ((b : ℤ) : ZMod p) with hB
  -- `f` has no root mod `p`
  set g : (ZMod p)[X] := X ^ 2 - C A * X + C B with hg
  have hnoroot : ∀ γ : ZMod p, ¬IsRoot g γ := by
    intro γ hγ
    rw [hg, IsRoot] at hγ
    simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C,
      eval_X] at hγ
    apply hnsq
    refine ⟨2 * γ - A, ?_⟩
    push_cast
    rw [hA] at hγ ⊢
    rw [hB] at hγ
    linear_combination -4 * hγ
  -- hence irreducible, and `K` is a field
  have hgeq : g = C 1 * X ^ 2 + C (-A) * X + C B := by
    rw [hg, map_one, map_neg]
    ring
  have hgdeg : g.natDegree = 2 := by
    rw [hgeq]
    exact natDegree_quadratic one_ne_zero
  have hirr : Irreducible g :=
    irreducible_of_degree_le_three_of_not_isRoot
      (by rw [hgdeg]; decide) hnoroot
  have : Fact (Irreducible g) := ⟨hirr⟩
  set K := AdjoinRoot g with hK
  have : CharP K p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  set α : K := AdjoinRoot.root g with hαdef
  set β : K := ((a : ℤ) : K) - α with hβdef
  have hsum : α + β = ((a : ℤ) : K) := by
    rw [hβdef]
    ring
  -- the root identity, with `ℤ`-cast coefficients
  have hAcast : algebraMap (ZMod p) K A = ((a : ℤ) : K) := by
    rw [hA, map_intCast]
  have hBcast : algebraMap (ZMod p) K B = ((b : ℤ) : K) := by
    rw [hB, map_intCast]
  have hroot : α ^ 2 - ((a : ℤ) : K) * α + ((b : ℤ) : K) = 0 := by
    have h0 : AdjoinRoot.mk g (X ^ 2 - C A * X + C B) = 0 := by
      rw [← hg]
      exact AdjoinRoot.mk_self
    simp only [map_add, map_sub, map_pow, map_mul, AdjoinRoot.mk_X,
      AdjoinRoot.mk_C] at h0
    rw [show ((A : K)) = algebraMap (ZMod p) K A from rfl,
      show ((B : K)) = algebraMap (ZMod p) K B from rfl,
      hAcast, hBcast] at h0
    exact h0
  have hprod : α * β = ((b : ℤ) : K) := by
    rw [hβdef]
    linear_combination -hroot
  -- the quadratic factors through its two roots
  have hquad : ∀ γ : K, γ ^ 2 - ((a : ℤ) : K) * γ + ((b : ℤ) : K)
      = (γ - α) * (γ - β) := by
    intro γ
    linear_combination γ * hsum - hprod
  -- Frobenius sends `α` to a root of the quadratic
  have hfrobroot : (α ^ p) ^ 2 - ((a : ℤ) : K) * α ^ p + ((b : ℤ) : K)
      = 0 := by
    have hfr := congrArg (frobenius K p) hroot
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hfr
    rw [map_intCast, map_intCast] at hfr
    simp only [frobenius_def] at hfr
    exact hfr
  have hcases : (α ^ p - α) * (α ^ p - β) = 0 := by
    rw [← hquad (α ^ p)]
    exact hfrobroot
  -- `α^p = α` is impossible: Frobenius fixes only the prime field
  have hnotfix : α ^ p ≠ α := by
    intro hfix
    -- `α` is not in the image of `ZMod p`
    have hnotin : ∀ c : ZMod p, algebraMap (ZMod p) K c ≠ α := by
      intro c hc
      apply hnoroot c
      have h0 : (algebraMap (ZMod p) K c) ^ 2
          - ((a : ℤ) : K) * (algebraMap (ZMod p) K c) + ((b : ℤ) : K)
          = 0 := by
        rw [hquad, hc]
        ring
      rw [← hAcast, ← hBcast, ← map_pow, ← map_mul, ← map_sub,
        ← map_add] at h0
      have h1 : c ^ 2 - A * c + B = 0 :=
        (algebraMap (ZMod p) K).injective (by rw [h0, map_zero])
      rw [hg, IsRoot]
      simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X]
      exact h1
    -- root counting for `X^p − X`
    set gp : K[X] := X ^ p - X with hgp
    have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
    have hgp0 : gp ≠ 0 := by
      intro h0
      have hc : gp.coeff p = 1 := by
        rw [hgp, coeff_sub, coeff_X_pow, ite_eq_left rfl, coeff_X]
        rw [ite_eq_right (by omega : ¬(1 : ℕ) = p)]
        ring
      rw [h0, coeff_zero] at hc
      exact one_ne_zero hc.symm
    have hgpdeg : gp.natDegree ≤ p := by
      rw [hgp]
      refine le_trans (natDegree_sub_le _ _) ?_
      simp only [natDegree_X_pow, natDegree_X]
      omega
    have hmem : ∀ c : ZMod p, algebraMap (ZMod p) K c ∈ gp.roots := by
      intro c
      rw [mem_roots hgp0]
      simp only [hgp, IsRoot, eval_sub, eval_pow, eval_X]
      rw [← map_pow, ZMod.pow_card, sub_self]
    have hαmem : α ∈ gp.roots := by
      rw [mem_roots hgp0]
      simp only [hgp, IsRoot, eval_sub, eval_pow, eval_X]
      rw [hfix, sub_self]
    set S : Finset K :=
      insert α ((Finset.univ : Finset (ZMod p)).image
        (algebraMap (ZMod p) K)) with hS
    have hScard : S.card = p + 1 := by
      rw [hS, Finset.card_insert_of_notMem (by
        rw [Finset.mem_image]
        rintro ⟨c, -, hc⟩
        exact hnotin c hc),
        Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective,
        Finset.card_univ, ZMod.card]
    have hSsub : S ⊆ gp.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset]
      rw [hS, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hαmem
      · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
        exact hmem c
    have h1 := Finset.card_le_card hSsub
    have h2 := Multiset.toFinset_card_le gp.roots
    have h3 := Polynomial.card_roots' gp
    omega
  -- so `α^p = β`, and symmetrically `β^p = α`
  have hfrob : α ^ p = β := by
    rcases mul_eq_zero.mp hcases with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hnotfix
    · exact sub_eq_zero.mp h0
  have hβfrob : β ^ p = α := by
    have hchar : β ^ p = (((a : ℤ) : K)) ^ p - α ^ p := by
      rw [hβdef]
      exact sub_pow_char _ _
    have hint : (((a : ℤ) : K)) ^ p = ((a : ℤ) : K) := by
      have := map_intCast (frobenius K p) a
      rwa [frobenius_def] at this
    rw [hchar, hint, hfrob, hβdef]
    ring
  -- both `(p+1)`-th powers are `b`
  have hαp1 : α ^ (p + 1) = ((b : ℤ) : K) := by
    rw [pow_succ, hfrob, ← hprod]
    ring
  have hβp1 : β ^ (p + 1) = ((b : ℤ) : K) := by
    rw [pow_succ, hβfrob, ← hprod]
  -- `α ≠ β`, since `(α − β)² = Δ ≠ 0`
  have hΔ0 : ((a ^ 2 - 4 * b : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    exact hnsq ⟨0, by rw [h0, zero_mul]⟩
  have hαβ : α - β ≠ 0 := by
    intro h0
    apply hΔ0
    have hdisc := sub_sq_eq_disc hsum hprod
    rw [h0] at hdisc
    have : ((a ^ 2 - 4 * b : ℤ) : K) = 0 := by
      rw [← hdisc]
      ring
    rw [show ((a ^ 2 - 4 * b : ℤ) : K)
        = algebraMap (ZMod p) K ((a ^ 2 - 4 * b : ℤ) : ZMod p) from
        (map_intCast _ _).symm] at this
    exact (algebraMap (ZMod p) K).injective (by rw [this, map_zero])
  -- assemble
  have hU := lucasU_spec hsum hprod (p + 1)
  rw [hαp1, hβp1, sub_self] at hU
  rcases mul_eq_zero.mp hU with h0 | h0
  · have : ((lucasU a b (p + 1) : ℤ) : ZMod p) = 0 := by
      rw [show ((lucasU a b (p + 1) : ℤ) : K)
          = algebraMap (ZMod p) K ((lucasU a b (p + 1) : ℤ) : ZMod p)
          from (map_intCast _ _).symm] at h0
      exact (algebraMap (ZMod p) K).injective (by rw [h0, map_zero])
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  · exact absurd h0 hαβ

/-- **Crandall–Pomerance Theorem 3.6.3** (the Lucas analogue of Fermat's
little theorem): for a prime `p` not dividing `2bΔ`,
`p ∣ U_{p − (Δ/p)}`. -/
theorem theorem_3_6_3 (h : ¬(p : ℤ) ∣ 2 * b * (a ^ 2 - 4 * b)) :
    (p : ℤ) ∣
      lucasU a b ((p : ℤ) - legendreSym p (a ^ 2 - 4 * b)).toNat := by
  have h2 : ¬(p : ℤ) ∣ 2 := fun hd => h ((hd.mul_right b).mul_right _)
  have hb : ¬(p : ℤ) ∣ b := fun hd => h ((hd.mul_left 2).mul_right _)
  have hΔ : ¬(p : ℤ) ∣ (a ^ 2 - 4 * b) := fun hd => h (hd.mul_left _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 (by norm_num)
  have hΔ0 : ((a ^ 2 - 4 * b : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hΔ
  rcases legendreSym.eq_one_or_neg_one (p := p) hΔ0 with h1 | h1 <;>
    rw [h1]
  · rw [show ((p : ℤ) - 1).toNat = p - 1 by omega]
    exact lucasU_card_sub_one hp2 hb
      ((legendreSym.eq_one_iff (p := p) hΔ0).mp h1) hΔ0
  · rw [show ((p : ℤ) - (-1)).toNat = p + 1 by omega]
    refine lucasU_card_add_one ?_
    intro hsq
    have := (legendreSym.eq_one_iff (p := p) hΔ0).mpr hsq
    omega

/-- **Crandall–Pomerance Theorem 4.2.2**: with `f, Δ` as in (4.12) and
`p` a prime not dividing `2bΔ`, the rank of appearance satisfies
`r_f(p) ∣ p − (Δ/p)`. -/
theorem theorem_4_2_2 (h : ¬(p : ℤ) ∣ 2 * b * (a ^ 2 - 4 * b)) :
    ((rankApp a b p : ℕ) : ℤ)
      ∣ (p : ℤ) - legendreSym p (a ^ 2 - 4 * b) := by
  have h363 := theorem_3_6_3 h
  have h2 : ¬(p : ℤ) ∣ 2 := fun hd => h ((hd.mul_right b).mul_right _)
  have hb : ¬(p : ℤ) ∣ b := fun hd => h ((hd.mul_left 2).mul_right _)
  have hΔ : ¬(p : ℤ) ∣ (a ^ 2 - 4 * b) := fun hd => h (hd.mul_left _)
  have hp := Fact.out (p := p.Prime)
  have hΔ0 : ((a ^ 2 - 4 * b : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hΔ
  have hleg := legendreSym.eq_one_or_neg_one (p := p) hΔ0
  have hp3 : 2 ≤ p := hp.two_le
  have hNpos : 0 < ((p : ℤ) - legendreSym p (a ^ 2 - 4 * b)).toNat := by
    rcases hleg with h1 | h1 <;> rw [h1] <;> omega
  -- `p` is coprime to `b` over `ℤ`
  have hbcop : IsCoprime ((p : ℕ) : ℤ) b := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hnd : ¬p ∣ b.natAbs := fun hd =>
      hb (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd))
    have hcop := (hp.coprime_iff_not_dvd).mpr hnd
    simpa [Int.gcd, Int.natAbs_natCast] using hcop
  -- rank divides the index
  have hex : ∃ r : ℕ, 0 < r ∧ ((p : ℕ) : ℤ) ∣ lucasU a b r :=
    ⟨_, hNpos, h363⟩
  have hrank := (dvd_lucasU_iff_rankApp_dvd hbcop hex _).mp h363
  have hcast : ((((p : ℤ) - legendreSym p (a ^ 2 - 4 * b)).toNat : ℕ) : ℤ)
      = (p : ℤ) - legendreSym p (a ^ 2 - 4 * b) := by
    rcases hleg with h1 | h1 <;> rw [h1] <;> omega
  rw [← hcast]
  exact_mod_cast hrank

end CP



end Azurite

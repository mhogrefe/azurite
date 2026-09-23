/-
  **The Lucas–Lehmer divisor confinement (5.3), part 1: the structure
  of `A_r = (ℤ/rℤ)[T]/(T² − uT − a)` for a prime `r`.**

  For a prime divisor `r` of `n`, the ring `A = (ℤ/nℤ)[T]/(T² − uT − a)`
  of Test (4.3) reduces to `A_r` (`quadCast`), coordinates going to
  coordinates (`quadCast_quadElt`), and a unit coordinate stays nonzero
  (`quadElt_cast_ne_zero`).  In `A_r` the discriminant `Δ = u² + 4a`
  decides the arithmetic:

  * **inert** (`Δ` a nonsquare): `A_r = 𝔽_{r²}` and `x^(r+1) = N(x)`
    (`pow_card_succ_eq_quadNorm`, Test (4.3));
  * **split** (`Δ = δ²`, `δ ≠ 0`): the two roots `α₁ ≠ α₂` give
    evaluation maps `evAt` to `𝔽_r`, jointly injective, with
    `ev₁(x)·ev₂(x) = N(x)`; a norm-one `x` has `x^(r−1) = 1`;
  * **ramified** (`Δ = 0`): `ε = α − u/2` is nilpotent, a norm-one `x`
    is `±1 + dε`, and `x^(2r) = 1`.

  `normOne_pow_cases` packages the trichotomy; part 2 (`Impl_5_3b`) turns
  it into the confinement `r ≡ n^(ε(r)) (mod p^(v_p(n+1)))` for odd
  `p ∣ f⁺`, with `ε(r) = [Δ inert mod r]` the same for every `p`.
-/
import Azurite.CohenLenstra.Impl_4_9
import Azurite.CrandallPomerance.Chapter4.Theorem_4_3_3

namespace Azurite

namespace CL

open Polynomial

/-! ### Reduction `A_n → A_r` -/

section Cast

variable {n r : ℕ} (hrn : r ∣ n) (u a : ZMod n) (u' a' : ZMod r)
  (hu : ZMod.castHom hrn (ZMod r) u = u') (ha : ZMod.castHom hrn (ZMod r) a = a')

/-- **Reduction modulo `r ∣ n`** of the quadratic ring, `α ↦ α`, into
`A_r` with the given parameters `u' = ū`, `a' = ā`. -/
noncomputable def quadCast : QuadRing (ZMod n) u a →+* QuadRing (ZMod r) u' a' :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp (ZMod.castHom hrn (ZMod r))) (AdjoinRoot.root _) (by
    rw [← Polynomial.eval₂_map]
    have hmap : (X ^ 2 - C u * X - C a : (ZMod n)[X]).map (ZMod.castHom hrn (ZMod r))
        = X ^ 2 - C u' * X - C a' := by
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, hu, ha]
    rw [hmap]
    exact AdjoinRoot.eval₂_root _)

theorem quadCast_quadElt (x₀ x₁ : ZMod n) :
    quadCast hrn u a u' a' hu ha (quadElt u a x₀ x₁)
      = quadElt u' a' (ZMod.castHom hrn (ZMod r) x₀) (ZMod.castHom hrn (ZMod r) x₁) := by
  simp only [quadElt, map_add, map_mul, quadCast, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.lift_of, RingHom.comp_apply]

omit hu ha in
/-- **A unit coordinate survives reduction**: for prime `r ∣ n`, if `x₀`
or `x₁` is a unit of `ℤ/nℤ` then `x₀ + x₁α ≠ 0` in `A_r`. -/
theorem quadElt_cast_ne_zero [Fact r.Prime] {x₀ x₁ : ZMod n} (hunit : IsUnit x₀ ∨ IsUnit x₁) :
    quadElt u' a' (ZMod.castHom hrn (ZMod r) x₀) (ZMod.castHom hrn (ZMod r) x₁) ≠ 0 := by
  intro h0
  have h0' : quadElt u' a' (ZMod.castHom hrn (ZMod r) x₀) (ZMod.castHom hrn (ZMod r) x₁)
      = quadElt u' a' 0 0 := by
    rw [h0]
    simp only [quadElt, map_zero, zero_mul, add_zero]
  obtain ⟨h0, h1⟩ := quadElt_injective _ _ h0'
  rcases hunit with hu | hu
  · exact (hu.map (ZMod.castHom hrn (ZMod r))).ne_zero h0
  · exact (hu.map (ZMod.castHom hrn (ZMod r))).ne_zero h1

end Cast

/-! ### The structure of `A_r` -/

section Field

variable {r : ℕ} [hr : Fact r.Prime] (u a : ZMod r)

/-- Every element of `A_r` is `x₀ + x₁α`. -/
theorem exists_quadElt (y : QuadRing (ZMod r) u a) :
    ∃ x₀ x₁ : ZMod r, y = quadElt u a x₀ x₁ := by
  induction y using AdjoinRoot.induction_on with
  | ih g =>
    have hmonic : (X ^ 2 - C u * X - C a : (ZMod r)[X]).Monic := by
      rw [show (X ^ 2 - C u * X - C a : (ZMod r)[X]) = X ^ 2 - (C u * X + C a) by ring]
      exact monic_X_pow_sub (lt_of_le_of_lt degree_linear_le
        (by exact_mod_cast (by norm_num : (1 : ℕ) < 2)))
    have h2 : (X ^ 2 - C u * X - C a : (ZMod r)[X]).degree = 2 := by
      rw [show (X ^ 2 - C u * X - C a : (ZMod r)[X]) = X ^ 2 - (C u * X + C a) by ring,
        degree_sub_eq_left_of_degree_lt]
      · simp
      · rw [degree_X_pow]
        exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast (by norm_num : (1 : ℕ) < 2))
    have hdeg : (g %ₘ (X ^ 2 - C u * X - C a)).degree ≤ 1 := by
      by_cases h0 : g %ₘ (X ^ 2 - C u * X - C a) = 0
      · rw [h0, degree_zero]
        exact bot_le
      · have h := degree_modByMonic_lt g hmonic
        rw [h2] at h
        have h' : (g %ₘ (X ^ 2 - C u * X - C a)).natDegree < 2 :=
          (natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast h)
        exact degree_le_of_natDegree_le (n := 1) (by omega)
    refine ⟨(g %ₘ (X ^ 2 - C u * X - C a)).coeff 0, (g %ₘ (X ^ 2 - C u * X - C a)).coeff 1, ?_⟩
    have hrep := eq_X_add_C_of_degree_le_one hdeg
    have hmk : AdjoinRoot.mk (X ^ 2 - C u * X - C a) g
        = AdjoinRoot.mk (X ^ 2 - C u * X - C a) (g %ₘ (X ^ 2 - C u * X - C a)) := by
      conv_lhs => rw [← modByMonic_add_div g (X ^ 2 - C u * X - C a)]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    have hrep' : AdjoinRoot.mk (X ^ 2 - C u * X - C a) (g %ₘ (X ^ 2 - C u * X - C a))
        = AdjoinRoot.of _ ((g %ₘ (X ^ 2 - C u * X - C a)).coeff 1) * AdjoinRoot.root _
          + AdjoinRoot.of _ ((g %ₘ (X ^ 2 - C u * X - C a)).coeff 0) := by
      conv_lhs => rw [hrep]
      rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rw [hmk, hrep', quadElt, AdjoinRoot.algebraMap_eq]
    ring

/-- `algebraMap` is injective, so `A_r` has characteristic `r`. -/
theorem algebraMap_quadRing_injective :
    Function.Injective (algebraMap (ZMod r) (QuadRing (ZMod r) u a)) := by
  intro c d h
  have h' : quadElt u a c 0 = quadElt u a d 0 := by
    simp only [quadElt, map_zero, zero_mul, add_zero]
    exact h
  exact (quadElt_injective u a h').1

instance instCharPQuadRing : CharP (QuadRing (ZMod r) u a) r :=
  charP_of_injective_algebraMap (algebraMap_quadRing_injective u a) r

/-! #### The split case -/

/-- **Evaluation at a root `c` of `T² − uT − a`**: `A_r → 𝔽_r`, `α ↦ c`. -/
noncomputable def evAt {c : ZMod r} (hc : c ^ 2 - u * c - a = 0) :
    QuadRing (ZMod r) u a →+* ZMod r :=
  AdjoinRoot.lift (RingHom.id _) c (by
    simp only [eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, RingHom.id_apply]
    exact hc)

theorem evAt_quadElt {c : ZMod r} (hc : c ^ 2 - u * c - a = 0) (x₀ x₁ : ZMod r) :
    evAt u a hc (quadElt u a x₀ x₁) = x₀ + x₁ * c := by
  simp only [quadElt, map_add, map_mul, evAt, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.lift_of, RingHom.id_apply]

/-- **Joint injectivity of the two evaluations** at distinct roots. -/
theorem eq_zero_of_evAt_eq_zero {c₁ c₂ : ZMod r} (hc₁ : c₁ ^ 2 - u * c₁ - a = 0)
    (hc₂ : c₂ ^ 2 - u * c₂ - a = 0) (hne : c₁ ≠ c₂) {y : QuadRing (ZMod r) u a}
    (h₁ : evAt u a hc₁ y = 0) (h₂ : evAt u a hc₂ y = 0) : y = 0 := by
  obtain ⟨x₀, x₁, rfl⟩ := exists_quadElt u a y
  rw [evAt_quadElt] at h₁ h₂
  have hx₁ : x₁ = 0 := by
    have h : x₁ * (c₁ - c₂) = 0 := by linear_combination h₁ - h₂
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hx₀ : x₀ = 0 := by
    rw [hx₁, zero_mul, add_zero] at h₁
    exact h₁
  rw [hx₀, hx₁]
  simp [quadElt]

/-- **The product of the two evaluations is the norm** when the roots are
`α₁, α₂` with `α₁ + α₂ = u`, `α₁α₂ = −a`. -/
theorem evAt_mul_evAt {c₁ c₂ : ZMod r} (hc₁ : c₁ ^ 2 - u * c₁ - a = 0)
    (hc₂ : c₂ ^ 2 - u * c₂ - a = 0) (hsum : c₁ + c₂ = u) (hprod : c₁ * c₂ = -a) (x₀ x₁ : ZMod r) :
    evAt u a hc₁ (quadElt u a x₀ x₁) * evAt u a hc₂ (quadElt u a x₀ x₁) = quadNorm u a x₀ x₁ := by
  rw [evAt_quadElt, evAt_quadElt, quadNorm]
  linear_combination (x₀ * x₁) * hsum + (x₁ ^ 2) * hprod

/-- **Split case**: a norm-one element satisfies `x^(r−1) = 1`. -/
theorem quadElt_pow_card_sub_one_eq_one {c₁ c₂ : ZMod r} (hc₁ : c₁ ^ 2 - u * c₁ - a = 0)
    (hc₂ : c₂ ^ 2 - u * c₂ - a = 0) (hsum : c₁ + c₂ = u) (hprod : c₁ * c₂ = -a) (hne : c₁ ≠ c₂)
    {x₀ x₁ : ZMod r} (hN : quadNorm u a x₀ x₁ = 1) :
    quadElt u a x₀ x₁ ^ (r - 1) = 1 := by
  have hmul := evAt_mul_evAt u a hc₁ hc₂ hsum hprod x₀ x₁
  rw [hN] at hmul
  have h₁ : evAt u a hc₁ (quadElt u a x₀ x₁) ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have h₂ : evAt u a hc₂ (quadElt u a x₀ x₁) ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  rw [← sub_eq_zero]
  refine eq_zero_of_evAt_eq_zero u a hc₁ hc₂ hne ?_ ?_
  · rw [map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one h₁, sub_self]
  · rw [map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one h₂, sub_self]

/-- `2 ≠ 0` in `𝔽_r` for an odd prime `r`. -/
theorem two_ne_zero_zmod (hr2 : r ≠ 2) : (2 : ZMod r) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
  have := (CharP.cast_eq_zero_iff (ZMod r) r 2).mp h'
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).mp this)

theorem four_ne_zero_zmod (hr2 : r ≠ 2) : (4 : ZMod r) ≠ 0 := by
  rw [show (4 : ZMod r) = 2 * 2 by norm_num]
  exact mul_ne_zero (two_ne_zero_zmod hr2) (two_ne_zero_zmod hr2)

/-! #### The ramified case -/

/-- **Ramified case** (`u² + 4a = 0`, `r` odd): with `ε = α − u/2` nilpotent,
`x = c + dε` with `c = x₀ + x₁·u/2`, and `x^r = c^r = c` in characteristic `r`. -/
theorem quadElt_pow_card_ramified (hr2 : r ≠ 2) (hΔ : u ^ 2 + 4 * a = 0) (x₀ x₁ : ZMod r) :
    quadElt u a x₀ x₁ ^ r = algebraMap (ZMod r) (QuadRing (ZMod r) u a) (x₀ + x₁ * (u / 2)) := by
  have hr' := hr.out
  have h2 : (2 : ZMod r) ≠ 0 := two_ne_zero_zmod hr2
  have h4' : (4 : ZMod r) ≠ 0 := four_ne_zero_zmod hr2
  set ι := algebraMap (ZMod r) (QuadRing (ZMod r) u a) with hι
  set ξ := AdjoinRoot.root (X ^ 2 - C u * X - C a : (ZMod r)[X]) with hξ
  set c : ZMod r := x₀ + x₁ * (u / 2) with hc
  set ε : QuadRing (ZMod r) u a := ξ - ι (u / 2) with hε
  have hrel : ξ ^ 2 = ι u * ξ + ι a := quadRing_root_sq u a
  have hε2 : ε ^ 2 = 0 := by
    have h4 : ι (u / 2) * ι (u / 2) = ι (u ^ 2 / 4) := by
      rw [← map_mul]
      congr 1
      field_simp
      ring
    have hΔ' : ι a + ι (u ^ 2 / 4) = 0 := by
      rw [← map_add]
      have : a + u ^ 2 / 4 = 0 := by
        field_simp
        linear_combination hΔ
      rw [this, map_zero]
    rw [hε, sub_sq, hrel, sq (ι (u / 2)), h4]
    have hu2 : ι u = 2 * ι (u / 2) := by
      rw [← map_ofNat ι 2, ← map_mul]
      congr 1
      field_simp
    rw [hu2]
    linear_combination hΔ'
  have hx : quadElt u a x₀ x₁ = ι c + ι x₁ * ε := by
    rw [quadElt, hε, hc, map_add, map_mul]
    ring
  rw [hx, add_pow_char, mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card]
  have hεr : ε ^ r = 0 := pow_eq_zero_of_le hr'.two_le hε2
  rw [hεr, mul_zero, add_zero]

/-- In the ramified case `N(x) = (x₀ + x₁·u/2)²`. -/
theorem quadNorm_ramified (hr2 : r ≠ 2) (hΔ : u ^ 2 + 4 * a = 0) (x₀ x₁ : ZMod r) :
    quadNorm u a x₀ x₁ = (x₀ + x₁ * (u / 2)) ^ 2 := by
  have h2 : (2 : ZMod r) ≠ 0 := two_ne_zero_zmod hr2
  have h4' : (4 : ZMod r) ≠ 0 := four_ne_zero_zmod hr2
  rw [quadNorm]
  have : (x₀ + x₁ * (u / 2)) ^ 2
      = x₀ ^ 2 + u * x₀ * x₁ - a * x₁ ^ 2 + x₁ ^ 2 * (u ^ 2 + 4 * a) / 4 := by
    field_simp
    ring
  rw [this, hΔ]
  ring

/-- **Ramified case**: `x^(2r) = N(x)`. -/
theorem quadElt_pow_two_mul_card_eq_norm (hr2 : r ≠ 2) (hΔ : u ^ 2 + 4 * a = 0)
    (x₀ x₁ : ZMod r) :
    quadElt u a x₀ x₁ ^ (2 * r) = algebraMap (ZMod r) (QuadRing (ZMod r) u a) (quadNorm u a x₀ x₁) := by
  rw [pow_mul', quadElt_pow_card_ramified u a hr2 hΔ, ← map_pow, quadNorm_ramified u a hr2 hΔ]

/-- **Ramified case**: a norm-one element satisfies `x^(2r) = 1`. -/
theorem quadElt_pow_two_mul_card_eq_one (hr2 : r ≠ 2) (hΔ : u ^ 2 + 4 * a = 0)
    {x₀ x₁ : ZMod r} (hN : quadNorm u a x₀ x₁ = 1) :
    quadElt u a x₀ x₁ ^ (2 * r) = 1 := by
  rw [quadElt_pow_two_mul_card_eq_norm u a hr2 hΔ, hN, map_one]

/-! #### The trichotomy -/

/-- **The structure theorem for norm-one elements of `A_r`** (`r` an odd
prime): according to the discriminant `Δ = u² + 4a`,
`x^(r+1) = 1` (inert), `x^(r−1) = 1` (split), or `x^(2r) = 1` (ramified). -/
theorem normOne_pow_cases (hr2 : r ≠ 2) {x₀ x₁ : ZMod r} (hN : quadNorm u a x₀ x₁ = 1) :
    (¬ IsSquare (u ^ 2 + 4 * a) ∧ quadElt u a x₀ x₁ ^ (r + 1) = 1)
      ∨ (IsSquare (u ^ 2 + 4 * a) ∧ u ^ 2 + 4 * a ≠ 0 ∧ quadElt u a x₀ x₁ ^ (r - 1) = 1)
      ∨ (u ^ 2 + 4 * a = 0 ∧ quadElt u a x₀ x₁ ^ (2 * r) = 1) := by
  have hr' := hr.out
  by_cases hΔ : u ^ 2 + 4 * a = 0
  · exact Or.inr (Or.inr ⟨hΔ, quadElt_pow_two_mul_card_eq_one u a hr2 hΔ hN⟩)
  by_cases hsq : IsSquare (u ^ 2 + 4 * a)
  · obtain ⟨δ, hδ⟩ := hsq
    have h2 : (2 : ZMod r) ≠ 0 := two_ne_zero_zmod hr2
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      exact hΔ (by rw [hδ, mul_zero])
    refine Or.inr (Or.inl ⟨⟨δ, hδ⟩, hΔ, ?_⟩)
    set t : ZMod r := (2 : ZMod r)⁻¹ with ht_def
    have ht : 2 * t = 1 := mul_inv_cancel₀ h2
    refine quadElt_pow_card_sub_one_eq_one u a (c₁ := (u + δ) * t) (c₂ := (u - δ) * t)
      ?_ ?_ ?_ ?_ ?_ hN
    · linear_combination (u * (u + δ) * t + a * (2 * t + 1)) * ht + (-t ^ 2) * hδ
    · linear_combination (u * (u - δ) * t + a * (2 * t + 1)) * ht + (-t ^ 2) * hδ
    · linear_combination u * ht
    · linear_combination (-a * (2 * t + 1)) * ht + t ^ 2 * hδ
    · intro h
      apply hδ0
      linear_combination h - δ * ht
  · exact Or.inl ⟨hsq, quadNorm_one_pow_eq_one hr' hsq hN⟩

end Field

/-! ### The confinement -/

section Confinement

variable {n r p : ℕ}

/-- `castHom` carries the norm form. -/
theorem castHom_quadNorm (hrn : r ∣ n) (u a x₀ x₁ : ZMod n) :
    ZMod.castHom hrn (ZMod r) (quadNorm u a x₀ x₁)
      = quadNorm (ZMod.castHom hrn (ZMod r) u) (ZMod.castHom hrn (ZMod r) a)
          (ZMod.castHom hrn (ZMod r) x₀) (ZMod.castHom hrn (ZMod r) x₁) := by
  simp only [quadNorm, map_add, map_sub, map_mul, map_pow]

open Classical in
/-- **Test (4.3) confines the prime divisors of `n`** (the odd-`p` part of
Remark (4.5) and of (5.3)).  For a prime `r ∣ n` (`n` odd), an odd prime
`p` with `p^v ∣ n + 1`, and a norm-one `x = x₀ + x₁α ∈ A` with
`x^(n+1) = 1` and a *unit coordinate* in `x^((n+1)/p) − 1` (the
`prod`-certificate of (4.4)(f)):

  `r ≡ n^(ε(r))  (mod p^v)`,  `ε(r) = 0` if `Δ = u² + 4a` is a square mod `r`,
  `ε(r) = 1` otherwise

— the exponent depends on `r` alone, not on `p`.  Proof: in
`A_r = (ℤ/rℤ)[T]/(T² − uT − a)` the image `x̄` still has norm one,
`x̄^(n+1) = 1`, and `x̄^((n+1)/p) ≠ 1`, so `p^v ∣ ord(x̄)`; by
`normOne_pow_cases`, `ord(x̄)` divides `r + 1` (inert: `r ≡ −1 ≡ n`),
`r − 1` (split: `r ≡ 1`), or `2r` (ramified: then `p ∣ r`, impossible as
`p ∣ n + 1`). -/
theorem test_4_3_confinement (hn2 : ¬ 2 ∣ n) (hr : r.Prime) (hrn : r ∣ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {v : ℕ} (hv : 0 < v) (hpv : p ^ v ∣ n + 1) {u a x₀ x₁ : ZMod n}
    (hN : quadNorm u a x₀ x₁ = 1) (hx1 : quadElt u a x₀ x₁ ^ (n + 1) = 1)
    (hunit : ∃ c₀ c₁ : ZMod n, quadElt u a x₀ x₁ ^ ((n + 1) / p) - 1 = quadElt u a c₀ c₁
      ∧ (IsUnit c₀ ∨ IsUnit c₁)) :
    r ≡ n ^ (if IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4 * ZMod.castHom hrn (ZMod r) a)
      then 0 else 1) [MOD p ^ v] := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hn2 hrn
  have hn1 : 1 < n := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn2 (dvd_zero 2)
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact hr.one_lt.ne' (Nat.dvd_one.mp hrn)
    omega
  -- the image in `A_r`
  set y := quadCast hrn u a _ _ rfl rfl (quadElt u a x₀ x₁) with hy
  have hyE : y = quadElt (ZMod.castHom hrn (ZMod r) u) (ZMod.castHom hrn (ZMod r) a)
      (ZMod.castHom hrn (ZMod r) x₀) (ZMod.castHom hrn (ZMod r) x₁) :=
    quadCast_quadElt hrn u a _ _ rfl rfl x₀ x₁
  have hNr : quadNorm (ZMod.castHom hrn (ZMod r) u) (ZMod.castHom hrn (ZMod r) a)
      (ZMod.castHom hrn (ZMod r) x₀) (ZMod.castHom hrn (ZMod r) x₁) = 1 := by
    rw [← castHom_quadNorm, hN, map_one]
  have hy1 : y ^ (n + 1) = 1 := by
    rw [hy, ← map_pow, hx1, map_one]
  have hyp : y ^ ((n + 1) / p) ≠ 1 := by
    obtain ⟨c₀, c₁, hc, hcu⟩ := hunit
    intro h
    have h' : y ^ ((n + 1) / p) - 1 = 0 := sub_eq_zero.mpr h
    rw [hy, ← map_pow, ← map_one (quadCast hrn u a _ _ rfl rfl), ← map_sub, hc,
      quadCast_quadElt] at h'
    exact quadElt_cast_ne_zero hrn _ _ hcu h'
  -- `p^v` divides the order of `y`
  have hord : p ^ v ∣ orderOf y := by
    refine CP.dvd_orderOf_of_pow_eq_one (by omega) (pow_pos hp.pos v) hpv hy1 ?_
    intro q hq hqF hcon
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqF)
    subst hqp
    exact hyp hcon
  have hpn1 : (p ^ v : ℕ) ∣ n + 1 := hpv
  -- the three cases
  rcases normOne_pow_cases (ZMod.castHom hrn (ZMod r) u) (ZMod.castHom hrn (ZMod r) a) hr2 hNr
    with ⟨hns, hpow⟩ | ⟨hsq, -, hpow⟩ | ⟨hΔ, hpow⟩
  · -- inert: `ord ∣ r + 1`, so `p^v ∣ r + 1` and `r ≡ n`
    rw [ite_eq_right hns, pow_one]
    rw [← hyE] at hpow
    have h1 : p ^ v ∣ r + 1 := hord.trans (orderOf_dvd_of_pow_eq_one hpow)
    have h2 : r + 1 ≡ n + 1 [MOD p ^ v] :=
      (Nat.modEq_zero_iff_dvd.mpr h1).trans (Nat.modEq_zero_iff_dvd.mpr hpn1).symm
    exact Nat.ModEq.add_right_cancel' 1 h2
  · -- split: `ord ∣ r − 1`, so `r ≡ 1`
    rw [ite_eq_left hsq, pow_zero]
    rw [← hyE] at hpow
    have h1 : p ^ v ∣ r - 1 := hord.trans (orderOf_dvd_of_pow_eq_one hpow)
    exact ((Nat.modEq_iff_dvd' hr.one_lt.le).mpr h1).symm
  · -- ramified: `ord ∣ 2r`, so `p ∣ r`, contradicting `p ∣ n + 1`
    exfalso
    rw [← hyE] at hpow
    have h1 : p ^ v ∣ 2 * r := hord.trans (orderOf_dvd_of_pow_eq_one hpow)
    have h2 : p ∣ 2 * r := (dvd_pow_self p hv.ne').trans h1
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp h
      subst hpr
      have hpn : p ∣ n + 1 := (dvd_pow_self p hv.ne').trans hpv
      have h1' : p ∣ (n + 1) - n := Nat.dvd_sub hpn hrn
      rw [Nat.add_sub_cancel_left] at h1'
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1')

end Confinement

/-! ### The `2`-adic side: the splitting type is the parity -/

section TwoAdic

variable {n r : ℕ}

/-- `IsSquare (4a) ↔ IsSquare a` in `𝔽_r`, `r` odd. -/
theorem isSquare_four_mul_iff {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (a : ZMod r) :
    IsSquare (4 * a) ↔ IsSquare a := by
  have h2 : (2 : ZMod r) ≠ 0 := two_ne_zero_zmod hr2
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d / 2, ?_⟩
    field_simp
    linear_combination hd
  · rintro ⟨d, hd⟩
    exact ⟨2 * d, by rw [hd]; ring⟩

/-- **(c1) and the splitting type** (`u = 0`, `Δ = 4a`): for prime `n ≡ 1 (mod 4)`,
`a^((n−1)/2) ≡ −1` and `r ∣ n` prime, `2^v ∣ r − 1` with `v = v₂(n − 1)`, and
`r ≢ 1 (mod 2^(v+1))` exactly when `T² − a` is inert modulo `r`. -/
theorem c1_two_adic (hn : Odd n) (hr : r.Prime) (hrn : r ∣ n) {a : ℤ}
    (ha : Int.ModEq (n : ℤ) (a ^ ((n - 1) / 2)) (-1)) :
    2 ^ (n - 1).factorization 2 ∣ r - 1
      ∧ (¬ 2 ^ ((n - 1).factorization 2 + 1) ∣ r - 1
          ↔ ¬ IsSquare ((ZMod.castHom hrn (ZMod r) (0 : ZMod n)) ^ 2
              + 4 * ZMod.castHom hrn (ZMod r) ((a : ℤ) : ZMod n))) := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hrn)
  obtain ⟨h1, h2⟩ := lemma_7_23 hn ha hrn
  refine ⟨h1, h2.trans ?_⟩
  rw [legendreSym.eq_neg_one_iff, map_zero, map_intCast, zero_pow (by norm_num), zero_add,
    isSquare_four_mul_iff hr2]

open Classical in
/-- **(c2) and the splitting type** (`a = 1`): for `n ≡ 3 (mod 4)`, `α^(n+1) = −1`
in `A`, and `r ∣ n` prime, with `2^v ∣ n + 1`, `v ≥ 2`:
`r ≡ n^(ε(r)) (mod 2^v)`; moreover in the split case `r ≡ 1 (mod 2^(v+1))`. -/
theorem c2_two_adic (hn3 : n % 4 = 3) (hr : r.Prime) (hrn : r ∣ n) {u : ZMod n}
    (hα : (AdjoinRoot.root (X ^ 2 - C u * X - C (1 : ZMod n) : Polynomial (ZMod n))) ^ (n + 1)
      = -1) {v : ℕ} (hv : 2 ≤ v) (h2v : 2 ^ v ∣ n + 1) :
    r ≡ n ^ (if IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4) then 0 else 1) [MOD 2 ^ v]
      ∧ (IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4) → 2 ^ (v + 1) ∣ r - 1)
      ∧ (¬ IsSquare ((ZMod.castHom hrn (ZMod r) u) ^ 2 + 4) → r ≡ n [MOD 2 ^ (v + 1)]) := by
  have : Fact r.Prime := ⟨hr⟩
  have hn2 : ¬ 2 ∣ n := by omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hn2 hrn
  have hn1 : 1 < n := by omega
  set ū := ZMod.castHom hrn (ZMod r) u with hū
  set ψ := ZMod.castHom hrn (ZMod r) with hψ
  have hψ1 : ψ 1 = 1 := ψ.map_one
  -- the image of `α`
  set φ := quadCast hrn u 1 ū 1 rfl hψ1 with hφ
  set y := φ (AdjoinRoot.root _) with hy
  have hyE : y = quadElt ū 1 0 1 := by
    have h := quadCast_quadElt hrn u 1 ū 1 rfl hψ1 0 1
    rw [ψ.map_zero, hψ1] at h
    rw [hy, ← h]
    congr 1
    simp [quadElt]
  have hy1 : y ^ (n + 1) = -1 := by
    rw [hy, ← φ.map_pow, hα, φ.map_neg, φ.map_one]
  have hyne : y ^ (n + 1) ≠ 1 := by
    rw [hy1]
    intro h
    have h' : (-1 : ZMod r) = 1 := algebraMap_quadRing_injective ū 1 (by
      rw [(algebraMap (ZMod r) (QuadRing (ZMod r) ū 1)).map_neg,
        (algebraMap (ZMod r) (QuadRing (ZMod r) ū 1)).map_one]
      exact h)
    have h2 : (2 : ZMod r) = 0 := by linear_combination -h'
    exact two_ne_zero_zmod hr2 h2
  have hy2 : y ^ (2 * (n + 1)) = 1 := by
    rw [pow_mul', hy1]
    ring
  -- `2^(v+1)` divides the order of `y`
  have hord : 2 ^ (v + 1) ∣ orderOf y := by
    refine CP.dvd_orderOf_of_pow_eq_one (by omega) (pow_pos (by norm_num) _)
      (by rw [pow_succ, mul_comm]; exact Nat.mul_dvd_mul_left 2 h2v) hy2 ?_
    intro q hq hqF hcon
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqF)
    subst hq2
    rw [Nat.mul_div_cancel_left _ (by norm_num)] at hcon
    exact hyne hcon
  by_cases hΔ : ū ^ 2 + 4 = 0
  · -- ramified: `y^(2r) = N(α) = −1`, so `ord ∣ 4r` and `2^(v+1) ∣ 4`, contradicting `v ≥ 2`
    exfalso
    have hΔ' : ū ^ 2 + 4 * 1 = 0 := by rw [mul_one]; exact hΔ
    have hpow : y ^ (2 * r) = -1 := by
      rw [hyE, quadElt_pow_two_mul_card_eq_norm ū 1 hr2 hΔ', quadNorm]
      simp
    have hpow4 : y ^ (4 * r) = 1 := by
      rw [show 4 * r = 2 * r * 2 by ring, pow_mul, hpow]
      ring
    have h1 := hord.trans (orderOf_dvd_of_pow_eq_one hpow4)
    have hodd : Nat.Coprime (2 ^ (v + 1)) r :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hr).mpr hr2.symm)
    have h4 : 2 ^ (v + 1) ∣ 4 := hodd.dvd_of_dvd_mul_right h1
    have h8 : 2 ^ 3 ∣ 4 := (pow_dvd_pow 2 (by omega : 3 ≤ v + 1)).trans h4
    norm_num at h8
  by_cases hsq : IsSquare (ū ^ 2 + 4)
  · -- split: `y^(r−1) = 1`, so `2^(v+1) ∣ r − 1`
    obtain ⟨δ, hδ⟩ := hsq
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      exact hΔ (by rw [hδ, mul_zero])
    have h2 : (2 : ZMod r) ≠ 0 := two_ne_zero_zmod hr2
    set t : ZMod r := (2 : ZMod r)⁻¹ with ht_def
    have ht : 2 * t = 1 := mul_inv_cancel₀ h2
    have hc₁ : ((ū + δ) * t) ^ 2 - ū * ((ū + δ) * t) - 1 = 0 := by
      linear_combination (ū * (ū + δ) * t + 1 * (2 * t + 1)) * ht + (-t ^ 2) * hδ
    have hc₂ : ((ū - δ) * t) ^ 2 - ū * ((ū - δ) * t) - 1 = 0 := by
      linear_combination (ū * (ū - δ) * t + 1 * (2 * t + 1)) * ht + (-t ^ 2) * hδ
    have hne : (ū + δ) * t ≠ (ū - δ) * t := by
      intro h
      apply hδ0
      linear_combination h - δ * ht
    -- both evaluations of `α` are nonzero (their product is `−1`)
    have hprod : (ū + δ) * t * ((ū - δ) * t) = -1 := by
      linear_combination (-1 * (2 * t + 1)) * ht + t ^ 2 * hδ
    have hprod' : ((ū + δ) * t) * (-((ū - δ) * t)) = 1 := by
      rw [mul_neg, hprod, neg_neg]
    have hc₁0 : (ū + δ) * t ≠ 0 := left_ne_zero_of_mul_eq_one hprod'
    have hc₂0 : (ū - δ) * t ≠ 0 := by
      intro h
      rw [h, mul_zero] at hprod
      exact zero_ne_one (by linear_combination -hprod : (0 : ZMod r) = 1)
    set e₁ := evAt ū 1 hc₁ with he₁
    set e₂ := evAt ū 1 hc₂ with he₂
    have hpow : y ^ (r - 1) = 1 := by
      rw [hyE, ← sub_eq_zero]
      refine eq_zero_of_evAt_eq_zero ū 1 hc₁ hc₂ hne ?_ ?_
      · rw [e₁.map_sub, e₁.map_pow, e₁.map_one, he₁, evAt_quadElt, zero_add, one_mul,
          ZMod.pow_card_sub_one_eq_one hc₁0, sub_self]
      · rw [e₂.map_sub, e₂.map_pow, e₂.map_one, he₂, evAt_quadElt, zero_add, one_mul,
          ZMod.pow_card_sub_one_eq_one hc₂0, sub_self]
    have h1 : 2 ^ (v + 1) ∣ r - 1 := hord.trans (orderOf_dvd_of_pow_eq_one hpow)
    refine ⟨?_, fun _ => h1, fun h => absurd ⟨δ, hδ⟩ h⟩
    rw [ite_eq_left ⟨δ, hδ⟩, pow_zero]
    exact ((Nat.modEq_iff_dvd' hr.one_lt.le).mpr ((pow_dvd_pow 2 (by omega)).trans h1)).symm
  · -- inert: `y^(r+1) = −1`, so `y^(2(r+1)) = 1` and `2^v ∣ r + 1`
    have hsq' : ¬ IsSquare (ū ^ 2 + 4 * 1) := by rw [mul_one]; exact hsq
    have hpow : y ^ (r + 1) = -1 := by
      rw [hyE, quadElt, (algebraMap (ZMod r) (QuadRing (ZMod r) ū 1)).map_zero, zero_add,
        (algebraMap (ZMod r) (QuadRing (ZMod r) ū 1)).map_one, one_mul,
        root_pow_card_succ_eq_neg hr hsq', (algebraMap (ZMod r) (QuadRing (ZMod r) ū 1)).map_one]
    have hpow2 : y ^ (2 * (r + 1)) = 1 := by
      rw [pow_mul', hpow]
      ring
    have h1 := hord.trans (orderOf_dvd_of_pow_eq_one hpow2)
    have h2 : 2 ^ v ∣ r + 1 := by
      rw [pow_succ, mul_comm] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    refine ⟨?_, fun h => absurd h hsq, fun _ => ?_⟩
    · rw [ite_eq_right hsq, pow_one]
      have h3 : r + 1 ≡ n + 1 [MOD 2 ^ v] :=
        (Nat.modEq_zero_iff_dvd.mpr h2).trans (Nat.modEq_zero_iff_dvd.mpr h2v).symm
      exact Nat.ModEq.add_right_cancel' 1 h3
    · -- `y^(n+1) = −1 = y^(r+1)`, so `ord(y) ∣ n − r`
      have hrn' : r ≤ n := Nat.le_of_dvd (by omega) hrn
      have hy3 : y ^ (n - r) = 1 := by
        have h4 : y ^ (n + 1) = y ^ (n - r) * y ^ (r + 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hy1, hpow, mul_neg_one] at h4
        exact (neg_inj.mp h4).symm
      have h5 : 2 ^ (v + 1) ∣ n - r := hord.trans (orderOf_dvd_of_pow_eq_one hy3)
      exact (Nat.modEq_iff_dvd' hrn').mpr h5

end TwoAdic

end CL

end Azurite

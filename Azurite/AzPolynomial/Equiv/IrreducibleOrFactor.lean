/-
  Correctness of the optimistic irreducibility test
  (`Azurite.AzPolynomial.irreducibleOrFactor`).

  Three verdicts, three theorems:
  * `irreducibleOrFactor_factor` — a `.inl d` verdict is a nontrivial
    factor of `m`, UNCONDITIONALLY (each `.inl` comes from a
    `gcdOrFactor` call, whose factor verdicts are sound over any
    modulus).
  * `irreducibleOrFactor_ne_inl_of_prime` — over a prime modulus the
    test never reports a factor.
  * `irreducibleOrFactor_eq_inr_true_iff` — over a prime modulus, for
    monic `f` of positive degree, the `.inr true` verdict holds IFF
    the transported polynomial is irreducible over `ZMod m.toNat`.

  The iff transports the Ben-Or criterion
  (`GG.irreducible_iff_isCoprime_X_pow_card_pow_sub_X`): the loop
  invariant is the `AdjoinRoot`-level congruence
  `mk fZ (toZModPoly h) = (mk fZ X)^(m^i)`, maintained through
  `powModByMonic` by the GG power bridge (`GG.toPoly_powModByMonic`,
  instantiated at the field `AzZMod m` — available exactly under the
  primality hypothesis) followed by the coefficient transport; each
  `gcdOrFactor` check equals coprimality of `X^(m^i) − X` with `fZ`
  by `isCoprime_iff_of_gcdOrFactor` (a monic generator is a unit iff
  it is `1`) and congruence-invariance of coprimality.
-/
import Azurite.AzPolynomial.IrreducibleOrFactor
import Azurite.AzPolynomial.Equiv.GcdOrFactor
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.GathenGerhard.Chapter14.Algorithm_14_3
import Azurite.GathenGerhard.Chapter14.Theorem_14_2
import Azurite.AzZMod.Field

namespace Azurite.AzPolynomial

open Polynomial

variable {m : AzNat} [NeZero m.toNat]

/-! ### Transport plumbing -/

omit [NeZero m.toNat] in
/-- `AdjoinRoot.mk` is blind to reduction mod its modulus. -/
theorem mk_modByMonic {fZ : Polynomial (ZMod m.toNat)}
    (p : Polynomial (ZMod m.toNat)) :
    AdjoinRoot.mk fZ (p %ₘ fZ) = AdjoinRoot.mk fZ p := by
  rw [AdjoinRoot.mk_eq_mk]
  exact ⟨-(p /ₘ fZ), by linear_combination modByMonic_add_div p fZ⟩

omit [NeZero m.toNat] in
/-- Coprimality with the modulus only depends on the residue class. -/
theorem isCoprime_congr {fZ p q : Polynomial (ZMod m.toNat)}
    (hcong : AdjoinRoot.mk fZ p = AdjoinRoot.mk fZ q) :
    IsCoprime p fZ ↔ IsCoprime q fZ := by
  obtain ⟨c, hc⟩ := AdjoinRoot.mk_eq_mk.mp hcong
  rw [show p = q + fZ * c by linear_combination hc,
    IsCoprime.add_mul_left_left_iff]

/-! ### The factor verdict, unconditionally -/

private theorem benOrLoop_factor (hm : 1 < m.toNat)
    {f : AzPolynomial (AzZMod m)} {d : AzNat} :
    ∀ (steps : ℕ) (h : AzPolynomial (AzZMod m)),
      benOrLoop m f steps h = .inl d →
      d.toNat ∣ m.toNat ∧ 1 < d.toNat ∧ d.toNat < m.toNat := by
  intro steps
  induction steps with
  | zero =>
    intro h hd
    exact absurd hd (by simp [benOrLoop])
  | succ steps ih =>
    intro h hd
    rw [benOrLoop] at hd
    cases hgo : gcdOrFactor m (h - X) f with
    | inl d' =>
      rw [hgo] at hd
      dsimp only at hd
      obtain rfl : d' = d := by simpa using hd
      exact gcdOrFactor_factor hm hgo
    | inr w =>
      rw [hgo] at hd
      dsimp only at hd
      by_cases hw : w = 1
      · rw [ite_eq_left hw] at hd
        exact ih _ hd
      · rw [ite_eq_right hw] at hd
        exact absurd hd (by simp)

/-- **A factor verdict of the irreducibility test is a nontrivial
divisor of `m`** — no primality assumption. -/
theorem irreducibleOrFactor_factor (hm : 1 < m.toNat)
    {f : AzPolynomial (AzZMod m)} {d : AzNat}
    (hd : irreducibleOrFactor m f = .inl d) :
    d.toNat ∣ m.toNat ∧ 1 < d.toNat ∧ d.toNat < m.toNat := by
  rw [irreducibleOrFactor] at hd
  by_cases h0 : f.natDegree = 0
  · rw [ite_eq_left h0] at hd
    exact absurd hd (by simp)
  · rw [ite_eq_right h0] at hd
    exact benOrLoop_factor hm _ _ hd

/-- **Over a prime modulus the test never reports a factor.** -/
theorem irreducibleOrFactor_ne_inl_of_prime (hm : Nat.Prime m.toNat)
    (f : AzPolynomial (AzZMod m)) (d : AzNat) :
    irreducibleOrFactor m f ≠ .inl d := by
  rw [irreducibleOrFactor]
  by_cases h0 : f.natDegree = 0
  · rw [ite_eq_left h0]
    simp
  · rw [ite_eq_right h0]
    generalize powModByMonic X m f = h
    generalize f.natDegree / 2 = steps
    induction steps generalizing h with
    | zero => simp [benOrLoop]
    | succ steps ih =>
      rw [benOrLoop]
      cases hgo : gcdOrFactor m (h - X) f with
      | inl d' => exact absurd hgo (gcdOrFactor_ne_inl_of_prime hm _ _ _)
      | inr w =>
        dsimp only
        by_cases hw : w = 1
        · rw [ite_eq_left hw]
          exact ih _
        · rw [ite_eq_right hw]
          simp

/-! ### The irreducibility verdict, over a prime modulus -/

section Prime

variable {f : AzPolynomial (AzZMod m)}

/-- The `powModByMonic` bridge at the `ZMod` level: available exactly
when `m` is prime (the GG power bridge runs over the field
`AzZMod m`). -/
private theorem toZModPoly_powModByMonic (hm : Nat.Prime m.toNat)
    (hf : f.Monic) (a : AzPolynomial (AzZMod m)) (q : AzNat) :
    toZModPoly (powModByMonic a q f)
      = (toZModPoly a %ₘ toZModPoly f) ^ q.toNat %ₘ toZModPoly f := by
  have := Fact.mk hm
  have h1 := GG.toPoly_powModByMonic (K := AzZMod m)
    ((Monic_toPoly f).mpr hf) a q
  unfold toZModPoly
  rw [h1, Polynomial.map_modByMonic _ ((Monic_toPoly f).mpr hf),
    Polynomial.map_pow, Polynomial.map_modByMonic _ ((Monic_toPoly f).mpr hf)]

/-- The invariant step: an `m`-th modular power is an `m.toNat`-th
power of the residue class. -/
private theorem mk_toZModPoly_powModByMonic (hm : Nat.Prime m.toNat)
    (hf : f.Monic) (a : AzPolynomial (AzZMod m)) (q : AzNat) :
    AdjoinRoot.mk (toZModPoly f) (toZModPoly (powModByMonic a q f))
      = AdjoinRoot.mk (toZModPoly f) (toZModPoly a) ^ q.toNat := by
  rw [toZModPoly_powModByMonic hm hf, mk_modByMonic, map_pow,
    mk_modByMonic]

/-- A `gcdOrFactor` generator is `1` exactly when the transported
inputs are coprime (a monic generator is a unit iff it is `1`). -/
theorem gcd_eq_one_iff (hf : f.Monic)
    {a w : AzPolynomial (AzZMod m)} (hg : gcdOrFactor m a f = .inr w) :
    w = 1 ↔ IsCoprime (toZModPoly a) (toZModPoly f) := by
  rw [isCoprime_iff_of_gcdOrFactor hf hg]
  constructor
  · rintro rfl
    rw [toZModPoly_one]
    exact isUnit_one
  · intro hu
    have h1 : toZModPoly w = 1 :=
      (Monic_toZModPoly.mpr (gcdOrFactor_gcd hf hg).1).eq_one_of_isUnit hu
    exact toZModPoly_injective (h1.trans toZModPoly_one.symm)

/-- The loop computes the conjunction of the coprimality checks over
its index window. -/
private theorem benOrLoop_eq_inr_true_iff (hm : Nat.Prime m.toNat)
    (hf : f.Monic) :
    ∀ (steps i : ℕ) (h : AzPolynomial (AzZMod m)), 0 < i →
      AdjoinRoot.mk (toZModPoly f) (toZModPoly h)
        = AdjoinRoot.mk (toZModPoly f) Polynomial.X ^ m.toNat ^ i →
      (benOrLoop m f steps h = .inr true ↔
        ∀ k, i ≤ k → k < i + steps →
          IsCoprime (Polynomial.X ^ m.toNat ^ k - Polynomial.X)
            (toZModPoly f)) := by
  have := Fact.mk hm
  intro steps
  induction steps with
  | zero =>
    intro i h hi hinv
    constructor
    · intro _ k hk1 hk2
      exact absurd hk2 (by omega)
    · intro _
      rfl
  | succ steps ih =>
    intro i h hi hinv
    rw [benOrLoop]
    cases hgo : gcdOrFactor m (h - X) f with
    | inl d => exact absurd hgo (gcdOrFactor_ne_inl_of_prime hm _ _ _)
    | inr w =>
      dsimp only
      -- the check at index `i` is coprimality of `X^(m^i) − X` with `fZ`
      have hcong : AdjoinRoot.mk (toZModPoly f)
          (toZModPoly h - Polynomial.X)
          = AdjoinRoot.mk (toZModPoly f)
            (Polynomial.X ^ m.toNat ^ i - Polynomial.X) := by
        simp only [map_sub, map_pow]
        rw [hinv]
      have hcheck : w = 1
          ↔ IsCoprime (Polynomial.X ^ m.toNat ^ i - Polynomial.X)
            (toZModPoly f) := by
        rw [gcd_eq_one_iff hf hgo, toZModPoly_sub, toZModPoly_X]
        exact isCoprime_congr hcong
      -- the invariant advances by an `m.toNat`-th power
      have hnext : AdjoinRoot.mk (toZModPoly f)
          (toZModPoly (powModByMonic h m f))
          = AdjoinRoot.mk (toZModPoly f) Polynomial.X ^ m.toNat ^ (i + 1) := by
        rw [mk_toZModPoly_powModByMonic hm hf, hinv, ← pow_mul, ← pow_succ]
      by_cases hw : w = 1
      · rw [ite_eq_left hw, ih (i + 1) _ (by omega) hnext]
        constructor
        · intro hall k hk1 hk2
          rcases Nat.eq_or_lt_of_le hk1 with rfl | hklt
          · exact hcheck.mp hw
          · exact hall k (by omega) (by omega)
        · intro hall k hk1 hk2
          exact hall k (by omega) (by omega)
      · rw [ite_eq_right hw]
        constructor
        · intro habs
          simp at habs
        · intro hall
          exact absurd (hcheck.mpr (hall i le_rfl (by omega))) hw

/-- **The irreducibility verdict is exact over a prime modulus**: for
monic `f` of positive degree, `.inr true` holds iff the transported
polynomial is irreducible over `ZMod m.toNat` — the Ben-Or criterion,
computed by the sweep. -/
theorem irreducibleOrFactor_eq_inr_true_iff (hm : Nat.Prime m.toNat)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    irreducibleOrFactor m f = .inr true ↔ Irreducible (toZModPoly f) := by
  have := Fact.mk hm
  rw [irreducibleOrFactor, ite_eq_right hdeg.ne']
  have hinit : AdjoinRoot.mk (toZModPoly f)
      (toZModPoly (powModByMonic X m f))
      = AdjoinRoot.mk (toZModPoly f) Polynomial.X ^ m.toNat ^ 1 := by
    rw [mk_toZModPoly_powModByMonic hm hf, toZModPoly_X, pow_one]
  rw [benOrLoop_eq_inr_true_iff hm hf (f.natDegree / 2) 1 _ one_pos hinit]
  have hfZm : (toZModPoly f).Monic := Monic_toZModPoly.mpr hf
  have hdegZ : (toZModPoly f).natDegree = f.natDegree := by
    unfold toZModPoly
    rw [((Monic_toPoly f).mpr hf).natDegree_map]
    exact AzPolynomial.natDegree_toPoly f
  rw [GG.irreducible_iff_isCoprime_X_pow_card_pow_sub_X hfZm (by omega)]
  simp only [ZMod.card, hdegZ]
  constructor
  · intro hall i hi1 hi2
    have hle : i ≤ f.natDegree / 2 :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    exact hall i hi1 (by omega)
  · intro hall k hk1 hk2
    have hle : k * 2 ≤ f.natDegree :=
      (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
    exact hall k hk1 (by omega)

end Prime

end Azurite.AzPolynomial

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **From the per-`(p, q)` character equations to the clauses of Theorem (6.3).**

  * The common-ring characters are transported into `ℂ` along the embedding
    `ℤ[ζ_{q·p^k}] → ℂ`, `ζ ↦ exp(2πi/(q·p^k))` (`embC`, `Yc`); this is the
    character family `Y q p` that `theorem_6_3_LL` consumes, with the exact
    order `p^k` (`orderOf_Yc`).
  * For a fixed prime `p ∣ t`, a (6.4) source (`∀ D, ∃ l, …`) and the chain
    results for all `q` with `p ∣ q − 1` are aligned at one common level `D`
    into a single exponent `l` per prime factor `r` of `n`
    (`clause_odd`, `clause_two`), via the alignment lemma `chi_eq_chi_pow`.
-/
import Azurite.APRCL.Equiv.JacobiChain
import Azurite.CohenLenstra.Alignment
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace Azurite

namespace APRCL

open CL CP Finset Polynomial

section ToComplex

variable {q p k : ℕ} [hqF : Fact q.Prime] (hp : p.Prime) (hpk : p ^ k ∣ q - 1)
  {gu : (ZMod q)ˣ} (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu)

/-- The primitive `q·p^k`-th root `exp(2πi/(q·p^k))`. -/
noncomputable def zetaC (q p k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (q * p ^ k : ℕ))

include hp in
theorem isPrimitiveRoot_zetaC : IsPrimitiveRoot (zetaC q p k) (q * p ^ k) :=
  Complex.isPrimitiveRoot_exp _ (cr_pos hp).ne'

/-- **The embedding `ℤ[ζ_{q·p^k}] → ℂ`.** -/
noncomputable def embC (hp : p.Prime) : CR q p k →+* ℂ :=
  AdjoinRoot.lift (Int.castRingHom ℂ) (zetaC q p k) (by
    have : NeZero ((q * p ^ k : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr (cr_pos hp).ne'⟩
    have hroot : IsRoot (cyclotomic (q * p ^ k) ℂ) (zetaC q p k) :=
      isRoot_cyclotomic_iff.mpr (isPrimitiveRoot_zetaC hp)
    rw [eval₂_eq_eval_map, map_cyclotomic]
    exact hroot)

include hp in
theorem embC_zetaM : embC (q := q) (k := k) hp (zetaM (q * p ^ k)) = zetaC q p k :=
  AdjoinRoot.lift_root _

include hp in
theorem isPrimitiveRoot_embC_zP : IsPrimitiveRoot (embC hp (zP q p k)) (p ^ k) := by
  rw [zP, map_pow, embC_zetaM]
  exact (isPrimitiveRoot_zetaC hp).pow (cr_pos hp) rfl

/-- **The complex character `Y_{q,p}`**: `χ_R` transported into `ℂ`. -/
noncomputable def Yc (hp : p.Prime) (hpk : p ^ k ∣ q - 1)
    (hg : ∀ u : (ZMod q)ˣ, u ∈ Subgroup.zpowers gu) : MulChar (ZMod q) ℂ :=
  (chiR hp hpk hg).ringHomComp (embC hp)

include hp hpk hg in
theorem Yc_apply (a : ZMod q) : Yc hp hpk hg a = embC hp (chiR hp hpk hg a) :=
  MulChar.ringHomComp_apply _ _ _

include hp hpk hg in
theorem Yc_gen : Yc hp hpk hg gu = embC hp (zP q p k) := by
  rw [Yc_apply, chiR_gen]

include hp hpk hg in
/-- **`Y_{q,p}` has exact order `p^k`.** -/
theorem orderOf_Yc : orderOf (Yc hp hpk hg) = p ^ k := by
  have hζ := isPrimitiveRoot_embC_zP (q := q) (k := k) hp
  have hu : IsPrimitiveRoot ((hζ.isUnit (pow_pos hp.pos k).ne').unit) (p ^ k) :=
    hζ.isUnit_unit (pow_pos hp.pos k).ne'
  have hmem := mem_rootsOfUnity_card_units_of_dvd hu.pow_eq_one hpk
  have heq : Yc hp hpk hg = MulChar.ofRootOfUnity hmem hg := by
    rw [MulChar.eq_iff hg, Yc_gen, MulChar.ofRootOfUnity_spec]
    rfl
  rw [heq]
  exact orderOf_ofRootOfUnity_eq hu hmem hg

include hp hpk hg in
/-- Transport of a chain result into `ℂ`. -/
theorem Yc_eq_of_chiR {r e : ℕ} (h : chiR hp hpk hg r = zP q p k ^ e) :
    Yc hp hpk hg r = embC hp (zP q p k) ^ e := by
  rw [Yc_apply, h, map_pow]

end ToComplex

/-! ### Alignment at a common level -/

/-- Fermat: `n^(p−1) ≡ 1 (mod p)` for `p ∤ n`. -/
theorem pow_sub_one_modEq_one_of_not_dvd {N p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ N) :
    N ^ (p - 1) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h : ((N : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpn
  have := ZMod.pow_card_sub_one_eq_one h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by push_cast; exact this)

/-- The level-`D` congruence as the integer divisibility of Theorem (7.8). -/
theorem int_dvd_of_modEq {N p r m D L : ℕ} (hLD : L ≤ D)
    (h : r ^ (p - 1) ≡ (N ^ (p - 1)) ^ m [MOD p ^ D]) :
    (p : ℤ) ^ L ∣ (r : ℤ) ^ (p - 1) - (N : ℤ) ^ ((p - 1) * m) := by
  have h1 := (Nat.modEq_iff_dvd.mp h.symm)
  push_cast at h1
  rw [← pow_mul] at h1
  exact (pow_dvd_pow (p : ℤ) hLD).trans h1

/-- **The odd-`p` clause of Theorem (6.3)**: one exponent `l` per prime factor `r`
serving all `q` with `p ∣ q − 1` and the `p`-adic congruence at level `E`. -/
theorem clause_odd {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn1 : 1 < N) (hpn : ¬ p ∣ N)
    (S64 : ∀ r, r.Prime → r ∣ N → ∀ D, ∃ l, r ^ (p - 1) ≡ (N ^ (p - 1)) ^ l [MOD p ^ D])
    (Qs : List ℕ) (hQ : ∀ q ∈ Qs, q.Prime) (kq : ℕ → ℕ) (hkq : ∀ q ∈ Qs, 0 < kq q)
    (Y : (q : ℕ) → MulChar (ZMod q) ℂ) (ζc : ℕ → ℂ)
    (hζ : ∀ q ∈ Qs, IsPrimitiveRoot (ζc q) (p ^ kq q))
    (hchain : ∀ q ∈ Qs, ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((p : ℤ) ^ ((N ^ ((p - 1) * p ^ kq q) - 1).factorization p)
        ∣ (r : ℤ) ^ (p - 1) - (N : ℤ) ^ ((p - 1) * m)) →
      Y q r = ζc q ^ (f₀ * m))
    (E : ℕ) :
    ∀ r ∈ N.primeFactors, ∃ l, (∀ q ∈ Qs, Y q r = Y q N ^ l) ∧
      r ^ (p - 1) ≡ (N ^ (p - 1)) ^ l [MOD p ^ E] := by
  classical
  have hchain' : ∀ q : ℕ, ∃ f₀ : ℕ, q ∈ Qs → ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((p : ℤ) ^ ((N ^ ((p - 1) * p ^ kq q) - 1).factorization p)
        ∣ (r : ℤ) ^ (p - 1) - (N : ℤ) ^ ((p - 1) * m)) →
      Y q r = ζc q ^ (f₀ * m) := fun q => by
    by_cases hq : q ∈ Qs
    · obtain ⟨f₀, hf₀⟩ := hchain q hq
      exact ⟨f₀, fun _ => hf₀⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose f₀ hchain using hchain'
  set D : ℕ := E + padicValNat p (N ^ (p - 1) - 1)
    + (Qs.map fun q => (N ^ ((p - 1) * p ^ kq q) - 1).factorization p + kq q).sum with hD
  have hED : E ≤ D := by omega
  have hqS : ∀ q ∈ Qs, (N ^ ((p - 1) * p ^ kq q) - 1).factorization p + kq q
      ≤ (Qs.map fun q => (N ^ ((p - 1) * p ^ kq q) - 1).factorization p + kq q).sum := fun q hq =>
    List.le_sum_of_mem (List.mem_map_of_mem hq)
  have hqD : ∀ q ∈ Qs, (N ^ ((p - 1) * p ^ kq q) - 1).factorization p + kq q ≤ D := fun q hq => by
    have := hqS q hq
    omega
  -- the common exponent function
  have hm' : ∀ r : ℕ, ∃ l : ℕ, r.Prime → r ∣ N → r ^ (p - 1) ≡ (N ^ (p - 1)) ^ l [MOD p ^ D] := by
    intro r
    by_cases h : r.Prime ∧ r ∣ N
    · obtain ⟨l, hl⟩ := S64 r h.1 h.2 D
      exact ⟨l, fun _ _ => hl⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose m hm using hm'
  have hmF : ∀ r ∈ N.primeFactors, r ^ (p - 1) ≡ (N ^ (p - 1)) ^ m r [MOD p ^ D] := fun r hr =>
    hm r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  have hx1 : 1 < N ^ (p - 1) := Nat.one_lt_pow (by have := hp.two_le; omega) hn1
  -- per `q`: the alignment
  have hal : ∀ q ∈ Qs, ∀ r ∈ N.primeFactors, Y q r = Y q N ^ m r := fun q hq => by
    have : Fact q.Prime := ⟨hQ q hq⟩
    refine chi_eq_chi_pow (hkq q hq) hn1 hpn hp (hζ q hq) ?_ (f := f₀ q) hmF fun r hr => ?_
    · intro j hj
      exact pow_dvd_of_pow_modEq_one_odd hp hp2 hx1 (pow_sub_one_modEq_one_of_not_dvd hp hpn)
        (by have := hqS q hq; omega) hj
    · exact hchain q hq r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr) (m r)
        (int_dvd_of_modEq (by have := hqD q hq; omega) (hmF r hr))
  intro r hr
  exact ⟨m r, fun q hq => hal q hq r hr, Nat.ModEq.of_dvd (pow_dvd_pow p hED) (hmF r hr)⟩

/-- **The `p = 2` clause of Theorem (6.3)**: additionally the parity of `l` is the
Lucas–Lehmer `ε(r)`, read off at level `v + 1`. -/
theorem clause_two {N : ℕ} (hn1 : 1 < N) (hodd : N % 2 = 1)
    (S64 : ∀ r, r.Prime → r ∣ N → ∀ D, ∃ l, r ≡ N ^ l [MOD 2 ^ D])
    (ε : ℕ → ℕ) (v : ℕ)
    (hpar : ∀ r, r.Prime → r ∣ N → ∀ l, r ≡ N ^ l [MOD 2 ^ (v + 1)] → l % 2 = ε r)
    (Qs : List ℕ) (hQ : ∀ q ∈ Qs, q.Prime) (kq : ℕ → ℕ) (hkq : ∀ q ∈ Qs, 0 < kq q)
    (Y : (q : ℕ) → MulChar (ZMod q) ℂ) (ζc : ℕ → ℂ)
    (hζ : ∀ q ∈ Qs, IsPrimitiveRoot (ζc q) (2 ^ kq q))
    (hchain : ∀ q ∈ Qs, ∃ f₀ : ℕ, ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((2 : ℤ) ^ ((N ^ ((2 - 1) * 2 ^ kq q) - 1).factorization 2)
        ∣ (r : ℤ) ^ (2 - 1) - (N : ℤ) ^ ((2 - 1) * m)) →
      Y q r = ζc q ^ (f₀ * m))
    (E : ℕ) :
    ∀ r ∈ N.primeFactors, ∃ l, l % 2 = ε r ∧ (∀ q ∈ Qs, Y q r = Y q N ^ l) ∧
      r ^ (2 - 1) ≡ (N ^ (2 - 1)) ^ l [MOD 2 ^ E] := by
  classical
  have hchain' : ∀ q : ℕ, ∃ f₀ : ℕ, q ∈ Qs → ∀ r, r.Prime → r ∣ N → ∀ m : ℕ,
      ((2 : ℤ) ^ ((N ^ ((2 - 1) * 2 ^ kq q) - 1).factorization 2)
        ∣ (r : ℤ) ^ (2 - 1) - (N : ℤ) ^ ((2 - 1) * m)) →
      Y q r = ζc q ^ (f₀ * m) := fun q => by
    by_cases hq : q ∈ Qs
    · obtain ⟨f₀, hf₀⟩ := hchain q hq
      exact ⟨f₀, fun _ => hf₀⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose f₀ hchain using hchain'
  set D : ℕ := E + (v + 1) + padicValNat 2 (N + 1) + padicValNat 2 (N - 1)
    + (Qs.map fun q => (N ^ ((2 - 1) * 2 ^ kq q) - 1).factorization 2 + kq q).sum with hD
  have hED : E ≤ D := by omega
  have hvD : v + 1 ≤ D := by omega
  have hqS : ∀ q ∈ Qs, (N ^ ((2 - 1) * 2 ^ kq q) - 1).factorization 2 + kq q
      ≤ (Qs.map fun q => (N ^ ((2 - 1) * 2 ^ kq q) - 1).factorization 2 + kq q).sum := fun q hq =>
    List.le_sum_of_mem (List.mem_map_of_mem hq)
  have hqD : ∀ q ∈ Qs, (N ^ ((2 - 1) * 2 ^ kq q) - 1).factorization 2 + kq q ≤ D := fun q hq => by
    have := hqS q hq
    omega
  have hm' : ∀ r : ℕ, ∃ l : ℕ, r.Prime → r ∣ N → r ≡ N ^ l [MOD 2 ^ D] := by
    intro r
    by_cases h : r.Prime ∧ r ∣ N
    · obtain ⟨l, hl⟩ := S64 r h.1 h.2 D
      exact ⟨l, fun _ _ => hl⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose m hm using hm'
  have hmF : ∀ r ∈ N.primeFactors, r ^ (2 - 1) ≡ (N ^ (2 - 1)) ^ m r [MOD 2 ^ D] := fun r hr => by
    simpa using hm r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  have hal : ∀ q ∈ Qs, ∀ r ∈ N.primeFactors, Y q r = Y q N ^ m r := fun q hq => by
    have : Fact q.Prime := ⟨hQ q hq⟩
    refine chi_eq_chi_pow (hkq q hq) hn1 (by omega) Nat.prime_two (hζ q hq) ?_ (f := f₀ q) hmF
      fun r hr => ?_
    · intro j hj
      norm_num at hj
      exact pow_dvd_of_pow_modEq_one_two hn1 hodd (by have := hqS q hq; omega) hj
    · exact hchain q hq r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr) (m r)
        (int_dvd_of_modEq (by have := hqD q hq; omega) (hmF r hr))
  intro r hr
  refine ⟨m r, ?_, fun q hq => hal q hq r hr, Nat.ModEq.of_dvd (pow_dvd_pow 2 hED) (hmF r hr)⟩
  exact hpar r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr) (m r)
    (Nat.ModEq.of_dvd (pow_dvd_pow 2 hvD)
      (hm r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)))

end APRCL

end Azurite

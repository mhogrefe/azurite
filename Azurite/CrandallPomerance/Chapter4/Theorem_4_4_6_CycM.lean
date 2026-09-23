/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Theorem 4.4.6, the composite direction, INSTANTIATED at the
  concrete common-ring model: for each prime `q ∣ F` the ring is
  `ℤ[ζ_((q−1)q)]` (`CycM ((q−1)q)`), the `q`-th root is
  `ζ^(q−1)` (`zetaQFam`), and the `p`-th roots for `p ∣ q − 1` are
  `ζ^((q−1)q/p)` (`zetaPFam`; junk indices get `1`, keeping the
  unrestricted membership hypothesis of the abstract theorem
  satisfiable).  The model discharges every ring-side hypothesis of
  `theorem_4_4_6_composite` — domain (`isDomain_cycM`), membership
  (`zetaPFam_mem`, via `mem_rootsOfUnity_card_units_of_dvd`),
  primitivity (`isPrimitiveRoot_zetaPFam`/`isPrimitiveRoot_zetaQFam`
  via `IsPrimitiveRoot.pow`), and ℤ-faithfulness
  (`natCast_dvd_natCast_iff_cycM`) — leaving
  `theorem_4_4_6_composite_cycM` with only the algorithm's OWN data:
  the generator `g_q`, the step-3/4 congruences, the step-5 coprime
  check, and the step-6 tables, all stated in `ℤ[ζ_((q−1)q)]`.
  (The checker's per-pair computations live in the `CycPQ` tower;
  the tower-to-`CycM` transfer hom is the remaining bridge.)
-/
import Azurite.CrandallPomerance.Chapter4.CycM
import Azurite.CrandallPomerance.Chapter4.Theorem_4_4_6

namespace Azurite

namespace CP

open Polynomial

/-- The `p`-th root family in the common ring `ℤ[ζ_((q−1)q)]`:
`ζ_p = ζ^((q−1)q/p)` for `p ∣ q − 1`; junk indices get `1`. -/
noncomputable def zetaPFam (q p : ℕ) : (CycM ((q - 1) * q))ˣ :=
  if hm : 0 < (q - 1) * q then
    if p ∣ q - 1 then zetaMUnit hm ^ ((q - 1) * q / p) else 1
  else 1

/-- The `q`-th root in the common ring: `ζ_q = ζ^(q−1)`. -/
noncomputable def zetaQFam (q : ℕ) : CycM ((q - 1) * q) :=
  zetaM ((q - 1) * q) ^ (q - 1)

section Prime

variable {q : ℕ} [Fact q.Prime]

private theorem hm_pos : 0 < (q - 1) * q := by
  have := (Fact.out (p := q.Prime)).two_le
  exact Nat.mul_pos (by omega) (by omega)

/-- `ζ_q` is a genuine primitive `q`-th root in the common ring. -/
theorem isPrimitiveRoot_zetaQFam : IsPrimitiveRoot (zetaQFam q) q :=
  (isPrimitiveRoot_zetaM hm_pos).pow hm_pos rfl

/-- The whole family lies in the `(q−1)`-th roots of unity — the
membership hypothesis of the character construction. -/
theorem zetaPFam_mem (p : ℕ) :
    zetaPFam q p ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ)
      (CycM ((q - 1) * q)) := by
  rw [zetaPFam, dite_eq_left hm_pos]
  by_cases hd : p ∣ q - 1
  · rw [ite_eq_left hd]
    refine mem_rootsOfUnity_card_units_of_dvd ?_ hd
    rw [← pow_mul, Nat.div_mul_cancel (hd.mul_right q),
      zetaMUnit_pow_eq_one]
  · rw [ite_eq_right hd]
    exact mem_rootsOfUnity_card_units_of_dvd (one_pow 1) (one_dvd _)

/-- The family members at prime factors of `q − 1` are genuine
primitive `p`-th roots. -/
theorem isPrimitiveRoot_zetaPFam {p : ℕ} (hp : p ∈ (q - 1).primeFactors) :
    IsPrimitiveRoot (zetaPFam q p) p := by
  have hd : p ∣ q - 1 := Nat.dvd_of_mem_primeFactors hp
  rw [zetaPFam, dite_eq_left hm_pos, ite_eq_left hd, ← IsPrimitiveRoot.coe_units_iff,
    Units.val_pow_eq_pow_val, val_zetaMUnit]
  exact (isPrimitiveRoot_zetaM hm_pos).pow hm_pos
    (Nat.div_mul_cancel (hd.mul_right q)).symm

end Prime

/-- **Theorem 4.4.6, composite direction, at the concrete model**:
the abstract certificate hypotheses discharged at `ℤ[ζ_((q−1)q)]`,
leaving only the algorithm's own data — the generator `g_q`, the
step-3/4 congruences, the step-5 coprime check at `q₀(p)`, and the
step-6 tables. -/
theorem theorem_4_4_6_composite_cycM
    {n I F : ℕ} (hn1 : 1 < n) (hncomp : ¬n.Prime)
    (hI : Squarefree I) (hF : Squarefree F)
    (hqI : ∀ q ∈ F.primeFactors, (q - 1) ∣ I)
    (hgcd : Nat.Coprime (I * F) n) (hnF : n < F ^ 2)
    {w u : ℕ → ℕ}
    (hw : ∀ p ∈ I.primeFactors, 0 < w p)
    (hu : ∀ p ∈ I.primeFactors, ¬p ∣ u p)
    {lTab : ℕ → ℕ → ℕ} {lq : ℕ → ℕ} {l : ℕ} {q₀ : ℕ → ℕ}
    (hq₀ : ∀ p ∈ I.primeFactors, q₀ p ∈ F.primeFactors ∧ p ∣ q₀ p - 1)
    {g : (q : ℕ) → (ZMod q)ˣ}
    (hgen : ∀ q, q ∈ F.primeFactors → ∀ x, x ∈ Subgroup.zpowers (g q))
    (hstep : ∀ q (hq : q ∈ F.primeFactors) [Fact q.Prime],
      ∀ p ∈ (q - 1).primeFactors,
      (n : CycM ((q - 1) * q))
        ∣ gaussSum (MulChar.ofRootOfUnity (zetaPFam_mem p) (hgen q hq))
            (AddChar.zmodChar q isPrimitiveRoot_zetaQFam.pow_eq_one)
            ^ (p ^ w p * u p)
          - (zetaPFam q p : CycM ((q - 1) * q)) ^ lTab p q)
    (h5 : ∀ q (hq : q ∈ F.primeFactors) [Fact q.Prime],
      ∀ p ∈ (q - 1).primeFactors, q₀ p = q →
      ∀ d, d ∣ n → 1 < d → ∀ j,
      ¬(d : CycM ((q - 1) * q))
        ∣ gaussSum (MulChar.ofRootOfUnity (zetaPFam_mem p) (hgen q hq))
            (AddChar.zmodChar q isPrimitiveRoot_zetaQFam.pow_eq_one)
            ^ (p ^ (w p - 1) * u p)
          - (zetaPFam q p : CycM ((q - 1) * q)) ^ j)
    (hlq : ∀ q ∈ F.primeFactors, ∀ p ∈ (q - 1).primeFactors,
      lq q ≡ lTab p q [MOD p])
    (hl : ∀ q ∈ F.primeFactors,
      ((l : ℕ) : ZMod q) = ((g q ^ lq q : (ZMod q)ˣ) : ZMod q)) :
    ∃ j, 0 < j ∧ j < I ∧ l ^ j % F ∣ n ∧ 1 < l ^ j % F ∧ l ^ j % F < n := by
  refine theorem_4_4_6_composite hn1 hncomp hI hF hqI hgcd hnF hw hu
    (lTab := lTab) (lq := lq) hq₀
    (R := fun q => CycM ((q - 1) * q)) (ζP := zetaPFam) (ζQ := zetaQFam)
    (g := g) ?_ ?_
  · intro q hq
    have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    exact isDomain_cycM hm_pos
  · intro q hq inst
    exact ⟨isPrimitiveRoot_zetaQFam, zetaPFam_mem, hgen q hq,
      fun p hp => isPrimitiveRoot_zetaPFam hp,
      fun x y => natCast_dvd_natCast_iff_cycM hm_pos x y,
      hstep q hq, h5 q hq, hlq q hq, hl q hq⟩

end CP

end Azurite

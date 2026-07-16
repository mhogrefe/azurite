/-
  **Correctness of the limb-level Algorithm 4.2.11**: the `AzNat`
  divisors-in-residue-classes list maps under `toNat` to the proven
  reference list `Azurite.CP.lenstraDivisors`
  (`map_toNat_lenstraDivisors`), so the reference specification
  transfers: under the hypotheses of Theorem 4.2.12,
  `d ∈ lenstraDivisors n r s rs ↔ d.toNat ∣ n.toNat ∧
  d.toNat % s.toNat = r.toNat` (`mem_lenstraDivisors`).

  The bridge is the usual two-rail pattern, component by component:
  a state-transport `stateBridge` commutes with the double-step
  (`toNat`/`toInt` on every field), the fuel search and the chain
  sequences transport indexwise, and each stage of the solver
  (square-root test, candidate verification, window enumeration)
  matches the reference definition branch by branch.
-/
import Azurite.AzNat.LenstraDivisors
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_12
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.SqrtRem
import Azurite.AzInt.Equiv.DivMod
import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Compare
import Azurite.AzInt.Equiv.Conversion
import Azurite.AzInt.Equiv.Pow
import Azurite.AzInt.Equiv.RingEquiv

namespace Azurite

namespace AzNat

open Azurite.AzInt (toInt_sub toInt_mul toInt_add lt_iff_toInt_lt
  le_iff_toInt_le)

/-! ### Small bridges -/

private theorem toInt_zero : ((0 : AzInt)).toInt = 0 := rfl

private theorem toInt_one : ((1 : AzInt)).toInt = 1 := rfl

private theorem toInt_two : ((2 : AzInt)).toInt = 2 :=
  map_ofNat AzInt.toIntRingHom 2

private theorem toInt_four : ((4 : AzInt)).toInt = 4 :=
  map_ofNat AzInt.toIntRingHom 4

private theorem azint_eq_iff {a b : AzInt} : a = b ↔ a.toInt = b.toInt :=
  ⟨congrArg _, fun h => AzInt.ringEquivInt.injective h⟩

private theorem toInt_hPow (z : AzInt) (k : ℕ) :
    (z ^ k).toInt = z.toInt ^ k :=
  map_pow AzInt.toIntRingHom z k

private theorem aznat_eq_iff {a b : AzNat} : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg _, fun h => toNat_injective h⟩

private theorem eq_zero_iff (a : AzNat) : a = 0 ↔ a.toNat = 0 := by
  rw [aznat_eq_iff, toNat_zero]

private theorem azint_eq_zero_iff (a : AzInt) : a = 0 ↔ a.toInt = 0 := by
  rw [azint_eq_iff, toInt_zero]

private theorem azint_lt_zero_iff (a : AzInt) : a < 0 ↔ a.toInt < 0 := by
  rw [lt_iff_toInt_lt, toInt_zero]

private theorem azint_pos_iff (a : AzInt) : 0 < a ↔ 0 < a.toInt := by
  rw [lt_iff_toInt_lt, toInt_zero]

private theorem azint_nonneg_iff (a : AzInt) : 0 ≤ a ↔ 0 ≤ a.toInt := by
  rw [le_iff_toInt_le, toInt_zero]

/-! ### The chain bridge -/

/-- Transport of the chain state to the reference state. -/
private def stateBridge (σ : LenstraState) : CP.LenstraState :=
  ⟨σ.a0.toNat, σ.a1.toNat, σ.b0.toInt, σ.b1.toInt, σ.c0.toInt, σ.c1.toInt⟩

private theorem stateBridge_lstep (σ : LenstraState) :
    stateBridge (lstep σ) = CP.lstep (stateBridge σ) := by
  rw [lstep, CP.lstep]
  by_cases h0 : σ.a0 = 0
  · rw [if_pos h0, if_pos (show (stateBridge σ).a0 = 0 from
      (eq_zero_iff _).mp h0)]
  · rw [if_neg h0, if_neg (show ¬(stateBridge σ).a0 = 0 from
      fun h => h0 ((eq_zero_iff _).mpr h))]
    have hmodb : (σ.a0 % σ.a1).toNat
        = (stateBridge σ).a0 % (stateBridge σ).a1 := toNat_mod _ _
    by_cases hγ : σ.a0 % σ.a1 = 0
    · rw [if_pos hγ, if_pos (show (stateBridge σ).a0 % (stateBridge σ).a1
          = 0 from by rw [← hmodb]; exact (eq_zero_iff _).mp hγ)]
      simp only [stateBridge, toNat_zero, toInt_zero, toInt_sub,
        toInt_mul, AzNat.toInt_toAzInt, toNat_div]
    · rw [if_neg hγ, if_neg (show ¬(stateBridge σ).a0 % (stateBridge σ).a1
          = 0 from by rw [← hmodb]; exact fun h => hγ ((eq_zero_iff _).mpr h))]
      simp only [stateBridge, toNat_mod, toNat_mul, toNat_sub,
        toNat_div, toNat_one, toInt_sub, toInt_mul, AzNat.toInt_toAzInt]

private theorem stateBridge_lchain (s a₁ : AzNat) (c₁ : AzInt) (k : ℕ) :
    stateBridge (lchain s a₁ c₁ k)
      = CP.lchain s.toNat a₁.toNat c₁.toInt k := by
  induction k with
  | zero =>
    rw [lchain, CP.lchain]
    rfl
  | succ k ih =>
    rw [lchain, CP.lchain, ← ih, stateBridge_lstep]

private theorem lchain_a0_bridge (s a₁ : AzNat) (c₁ : AzInt) (k : ℕ) :
    (lchain s a₁ c₁ k).a0.toNat
      = (CP.lchain s.toNat a₁.toNat c₁.toInt k).a0 := by
  rw [← stateBridge_lchain]
  rfl

private theorem lKAux_bridge (s a₁ : AzNat) (c₁ : AzInt) :
    ∀ fuel k, lKAux s a₁ c₁ fuel k
      = CP.lKAux s.toNat a₁.toNat c₁.toInt fuel k := by
  intro fuel
  induction fuel with
  | zero =>
    intro k
    rw [lKAux, CP.lKAux]
  | succ fuel ih =>
    intro k
    rw [lKAux, CP.lKAux]
    by_cases h : (lchain s a₁ c₁ k).a0 = 0
    · rw [if_pos h, if_pos (by
        rw [← lchain_a0_bridge]
        exact (eq_zero_iff _).mp h)]
    · rw [if_neg h, if_neg (by
        rw [← lchain_a0_bridge]
        exact fun hc => h ((eq_zero_iff _).mpr hc)), ih]

private theorem lT_bridge (s a₁ : AzNat) (c₁ : AzInt) :
    lT s a₁ c₁ = CP.lT s.toNat a₁.toNat c₁.toInt := by
  rw [lT, CP.lT, lK, CP.lK, lKAux_bridge]

private theorem toInt_lA (s a₁ : AzNat) (c₁ : AzInt) (i : ℕ) :
    (lA s a₁ c₁ i).toInt = CP.lA s.toNat a₁.toNat c₁.toInt i := by
  rw [lA, CP.lA]
  by_cases h : i % 2 = 0
  · rw [if_pos h, if_pos h, AzNat.toInt_toAzInt, lchain_a0_bridge]
  · rw [if_neg h, if_neg h, AzNat.toInt_toAzInt,
      show (lchain s a₁ c₁ (i / 2)).a1.toNat
        = (CP.lchain s.toNat a₁.toNat c₁.toInt (i / 2)).a1 from by
        rw [← stateBridge_lchain]; rfl]

private theorem toInt_lB (s a₁ : AzNat) (c₁ : AzInt) (i : ℕ) :
    (lB s a₁ c₁ i).toInt = CP.lB s.toNat a₁.toNat c₁.toInt i := by
  rw [lB, CP.lB]
  by_cases h : i % 2 = 0
  · rw [if_pos h, if_pos h, show (lchain s a₁ c₁ (i / 2)).b0.toInt
      = (CP.lchain s.toNat a₁.toNat c₁.toInt (i / 2)).b0 from by
      rw [← stateBridge_lchain]; rfl]
  · rw [if_neg h, if_neg h, show (lchain s a₁ c₁ (i / 2)).b1.toInt
      = (CP.lchain s.toNat a₁.toNat c₁.toInt (i / 2)).b1 from by
      rw [← stateBridge_lchain]; rfl]

private theorem toInt_lC (s a₁ : AzNat) (c₁ : AzInt) (i : ℕ) :
    (lC s a₁ c₁ i).toInt = CP.lC s.toNat a₁.toNat c₁.toInt i := by
  rw [lC, CP.lC]
  by_cases h : i % 2 = 0
  · rw [if_pos h, if_pos h, show (lchain s a₁ c₁ (i / 2)).c0.toInt
      = (CP.lchain s.toNat a₁.toNat c₁.toInt (i / 2)).c0 from by
      rw [← stateBridge_lchain]; rfl]
  · rw [if_neg h, if_neg h, show (lchain s a₁ c₁ (i / 2)).c1.toInt
      = (CP.lchain s.toNat a₁.toNat c₁.toInt (i / 2)).c1 from by
      rw [← stateBridge_lchain]; rfl]

/-! ### The solver bridge -/

private theorem toNat_natAbs_of_pos {u : AzInt} (hu : 0 < u) :
    u.natAbs.toNat = u.toInt.toNat := by
  have h1 := AzInt.toNat_natAbs u
  have h2 : 0 < u.toInt := (azint_pos_iff u).mp hu
  omega

private theorem intSqrt?_bridge (D : AzInt) :
    Option.map AzInt.toInt (intSqrt? D) = CP.intSqrt? D.toInt := by
  rw [intSqrt?, CP.intSqrt?]
  by_cases hneg : D < 0
  · rw [if_pos hneg, if_pos ((azint_lt_zero_iff D).mp hneg)]
    rfl
  · rw [if_neg hneg, if_neg (fun h => hneg ((azint_lt_zero_iff D).mpr h))]
    have hDt : D.natAbs.toNat = D.toInt.toNat := by
      have h1 := AzInt.toNat_natAbs D
      have h2 : ¬D.toInt < 0 := fun h => hneg ((azint_lt_zero_iff D).mpr h)
      omega
    have hsq_le : Nat.sqrt D.natAbs.toNat * Nat.sqrt D.natAbs.toNat
        ≤ D.natAbs.toNat := by
      have h := Nat.sqrt_le' D.natAbs.toNat
      rw [Nat.pow_two] at h
      exact h
    by_cases hrem : (sqrtRem D.natAbs).2 = 0
    · have hrem' : D.natAbs.toNat
          - Nat.sqrt D.natAbs.toNat * Nat.sqrt D.natAbs.toNat = 0 := by
        rw [← toNat_sqrtRem_snd]
        exact (eq_zero_iff _).mp hrem
      rw [if_pos hrem, if_pos (by rw [← hDt]; omega)]
      rw [Option.map_some]
      congr 1
      rw [AzNat.toInt_toAzInt, toNat_sqrtRem_fst, hDt]
    · have hrem' : ¬(D.natAbs.toNat
          - Nat.sqrt D.natAbs.toNat * Nat.sqrt D.natAbs.toNat = 0) := by
        rw [← toNat_sqrtRem_snd]
        exact fun h => hrem ((eq_zero_iff _).mpr h)
      rw [if_neg hrem, if_neg (by rw [← hDt]; omega)]
      rfl

private theorem map_toNat_reportIfDivisor (n r s : AzNat) (u : AzInt) :
    (reportIfDivisor n r s u).map toNat
      = CP.reportIfDivisor n.toNat r.toNat s.toNat u.toInt := by
  rw [reportIfDivisor, CP.reportIfDivisor]
  by_cases hpos : 0 < u
  · have hpos' : 0 < u.toInt := (azint_pos_iff u).mp hpos
    have hna : u.natAbs.toNat = u.toInt.toNat := toNat_natAbs_of_pos hpos
    have hne : 0 < u.toInt.toNat := by omega
    have hciff : (n % u.natAbs = 0 ∧ u.natAbs % s = r)
        ↔ (u.toInt.toNat ∣ n.toNat
          ∧ u.toInt.toNat % s.toNat = r.toNat) := by
      constructor
      · rintro ⟨h1, h2⟩
        have h1' := (eq_zero_iff _).mp h1
        rw [toNat_mod, hna] at h1'
        have h2' := aznat_eq_iff.mp h2
        rw [toNat_mod, hna] at h2'
        exact ⟨Nat.dvd_of_mod_eq_zero h1', h2'⟩
      · rintro ⟨h1, h2⟩
        refine ⟨(eq_zero_iff _).mpr ?_, aznat_eq_iff.mpr ?_⟩
        · rw [toNat_mod, hna]
          exact Nat.mod_eq_zero_of_dvd h1
        · rw [toNat_mod, hna]
          exact h2
    by_cases hc : n % u.natAbs = 0 ∧ u.natAbs % s = r
    · rw [if_pos ⟨hpos, hc.1, hc.2⟩,
        if_pos ⟨hpos', (hciff.mp hc).1, (hciff.mp hc).2⟩,
        List.map_cons, List.map_nil, hna]
    · rw [if_neg (fun h => hc ⟨h.2.1, h.2.2⟩),
        if_neg (fun h => hc (hciff.mpr ⟨h.2.1, h.2.2⟩))]
      rfl
  · rw [if_neg (fun h => hpos h.1),
      if_neg (fun h => hpos ((azint_pos_iff u).mpr h.1))]
    rfl

private theorem map_toNat_solveSystem (n r r' s : AzNat) (a b c : AzInt) :
    (solveSystem n r r' s a b c).map toNat
      = CP.solveSystem n.toNat r.toNat r'.toNat s.toNat
          a.toInt b.toInt c.toInt := by
  rw [solveSystem, CP.solveSystem]
  by_cases ha : a = 0
  · rw [if_pos ha, if_pos ((azint_eq_zero_iff a).mp ha)]
    by_cases hb : b = 0
    · rw [if_pos hb, if_pos ((azint_eq_zero_iff b).mp hb)]
      rfl
    · rw [if_neg hb, if_neg (fun h => hb ((azint_eq_zero_iff b).mpr h))]
      have hcond1 : (c % b = 0 ∧ 0 ≤ c / b)
          ↔ (b.toInt ∣ c.toInt ∧ 0 ≤ c.toInt / b.toInt) := by
        rw [azint_eq_zero_iff, AzInt.toInt_hMod, azint_nonneg_iff,
          AzInt.toInt_hDiv, Int.dvd_iff_emod_eq_zero]
      by_cases hc1 : c % b = 0 ∧ 0 ≤ c / b
      · rw [if_pos hc1, if_pos (hcond1.mp hc1)]
        have hvz : (c / b * s.toAzInt + r'.toAzInt).toInt
            = c.toInt / b.toInt * (s.toNat : ℤ) + (r'.toNat : ℤ) := by
          rw [toInt_add, toInt_mul, AzInt.toInt_hDiv,
            AzNat.toInt_toAzInt, AzNat.toInt_toAzInt]
        have hposiff : (0 < c / b * s.toAzInt + r'.toAzInt)
            ↔ (0 < c.toInt / b.toInt * (s.toNat : ℤ) + (r'.toNat : ℤ)) := by
          rw [azint_pos_iff, hvz]
        by_cases hv : 0 < c / b * s.toAzInt + r'.toAzInt
        · have hv' := hposiff.mp hv
          have hna : (c / b * s.toAzInt + r'.toAzInt).natAbs.toNat
              = (c.toInt / b.toInt * (s.toNat : ℤ)
                + (r'.toNat : ℤ)).toNat := by
            rw [toNat_natAbs_of_pos hv, hvz]
          have hdvdiff : (n % (c / b * s.toAzInt + r'.toAzInt).natAbs = 0)
              ↔ ((c.toInt / b.toInt * (s.toNat : ℤ)
                + (r'.toNat : ℤ)).toNat ∣ n.toNat) := by
            rw [eq_zero_iff, toNat_mod, hna]
            exact ⟨Nat.dvd_of_mod_eq_zero, Nat.mod_eq_zero_of_dvd⟩
          by_cases hd : n % (c / b * s.toAzInt + r'.toAzInt).natAbs = 0
          · rw [if_pos ⟨hv, hd⟩, if_pos ⟨hv', hdvdiff.mp hd⟩,
              map_toNat_reportIfDivisor]
            congr 1
            rw [AzNat.toInt_toAzInt, toNat_div, hna]
          · rw [if_neg (fun h => hd h.2),
              if_neg (fun h => hd (hdvdiff.mpr h.2))]
            rfl
        · rw [if_neg (fun h => hv h.1),
            if_neg (fun h => hv (hposiff.mpr h.1))]
          rfl
      · rw [if_neg hc1, if_neg (fun h => hc1 (hcond1.mpr h))]
        rfl
  · rw [if_neg ha, if_neg (fun h => ha ((azint_eq_zero_iff a).mpr h))]
    have hR : (c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt).toInt
        = c.toInt * (s.toNat : ℤ) + a.toInt * (r.toNat : ℤ)
          + b.toInt * (r'.toNat : ℤ) := by
      rw [toInt_add, toInt_add, toInt_mul, toInt_mul, toInt_mul,
        AzNat.toInt_toAzInt, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt]
    have hDz : ((c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt) ^ 2
        - 4 * a * b * n.toAzInt).toInt
        = (c.toInt * (s.toNat : ℤ) + a.toInt * (r.toNat : ℤ)
            + b.toInt * (r'.toNat : ℤ)) ^ 2
          - 4 * a.toInt * b.toInt * (n.toNat : ℤ) := by
      rw [toInt_sub, toInt_hPow, hR, toInt_mul, toInt_mul, toInt_mul,
        toInt_four, AzNat.toInt_toAzInt]
    have hsq := intSqrt?_bridge ((c * s.toAzInt + a * r.toAzInt
      + b * r'.toAzInt) ^ 2 - 4 * a * b * n.toAzInt)
    rw [hDz] at hsq
    rcases hmatch : intSqrt? ((c * s.toAzInt + a * r.toAzInt
        + b * r'.toAzInt) ^ 2 - 4 * a * b * n.toAzInt) with - | w
    · have hcp : CP.intSqrt? ((c.toInt * (s.toNat : ℤ)
          + a.toInt * (r.toNat : ℤ) + b.toInt * (r'.toNat : ℤ)) ^ 2
          - 4 * a.toInt * b.toInt * (n.toNat : ℤ)) = none := by
        rw [← hsq, hmatch]
        rfl
      rw [hcp]
      rfl
    · have hcp : CP.intSqrt? ((c.toInt * (s.toNat : ℤ)
          + a.toInt * (r.toNat : ℤ) + b.toInt * (r'.toNat : ℤ)) ^ 2
          - 4 * a.toInt * b.toInt * (n.toNat : ℤ)) = some w.toInt := by
        rw [← hsq, hmatch]
        rfl
      rw [hcp]
      dsimp only
      rw [List.map_append]
      have h2a : ((2 : AzInt) * a).toInt = 2 * a.toInt := by
        rw [toInt_mul, toInt_two]
      have hbr1 : ((c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt
          + w) % (2 * a) = 0)
          ↔ (2 * a.toInt ∣ c.toInt * (s.toNat : ℤ)
            + a.toInt * (r.toNat : ℤ) + b.toInt * (r'.toNat : ℤ)
            + w.toInt) := by
        rw [azint_eq_zero_iff, AzInt.toInt_hMod, toInt_add, hR, h2a,
          Int.dvd_iff_emod_eq_zero]
      have hbr2 : ((c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt
          - w) % (2 * a) = 0)
          ↔ (2 * a.toInt ∣ c.toInt * (s.toNat : ℤ)
            + a.toInt * (r.toNat : ℤ) + b.toInt * (r'.toNat : ℤ)
            - w.toInt) := by
        rw [azint_eq_zero_iff, AzInt.toInt_hMod, toInt_sub, hR, h2a,
          Int.dvd_iff_emod_eq_zero]
      congr 1
      · by_cases h1 : (c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt
            + w) % (2 * a) = 0
        · rw [if_pos h1, if_pos (hbr1.mp h1), map_toNat_reportIfDivisor]
          congr 1
          rw [AzInt.toInt_hDiv, toInt_add, hR, h2a]
        · rw [if_neg h1, if_neg (fun h => h1 (hbr1.mpr h))]
          rfl
      · by_cases h2 : (c * s.toAzInt + a * r.toAzInt + b * r'.toAzInt
            - w) % (2 * a) = 0
        · rw [if_pos h2, if_pos (hbr2.mp h2), map_toNat_reportIfDivisor]
          congr 1
          rw [AzInt.toInt_hDiv, toInt_sub, hR, h2a]
        · rw [if_neg h2, if_neg (fun h => h2 (hbr2.mpr h))]
          rfl

/-! ### The window bridges -/

private theorem map_toInt_evenWindow (s : AzNat) (cᵢ : AzInt) :
    (evenWindow s cᵢ).map AzInt.toInt
      = CP.evenWindow s.toNat cᵢ.toInt := by
  rw [evenWindow, CP.evenWindow]
  have hm : (cᵢ % s.toAzInt).toInt = cᵢ.toInt % (s.toNat : ℤ) := by
    rw [AzInt.toInt_hMod, AzNat.toInt_toAzInt]
  by_cases h : cᵢ % s.toAzInt = 0
  · rw [if_pos h, if_pos (by rw [← hm]; exact (azint_eq_zero_iff _).mp h)]
    rfl
  · rw [if_neg h, if_neg (by
      rw [← hm]
      exact fun hc => h ((azint_eq_zero_iff _).mpr hc))]
    rw [List.map_cons, List.map_cons, List.map_nil, hm, toInt_sub, hm,
      AzNat.toInt_toAzInt]

private theorem map_toInt_oddWindow (n s : AzNat) (a b cᵢ : AzInt) :
    (oddWindow n s a b cᵢ).map AzInt.toInt
      = CP.oddWindow n.toNat s.toNat a.toInt b.toInt cᵢ.toInt := by
  rw [oddWindow, CP.oddWindow, List.map_filterMap]
  have hcount : (n / s.pow 3).toNat + 1 = n.toNat / s.toNat ^ 3 + 1 := by
    rw [toNat_div, toNat_pow]
  rw [hcount]
  refine List.filterMap_congr ?_
  intro j _
  have hcexp : (2 * (a * b) + (cᵢ - 2 * (a * b)) % s.toAzInt
      + (ofNat j).toAzInt * s.toAzInt).toInt
      = 2 * (a.toInt * b.toInt)
        + (cᵢ.toInt - 2 * (a.toInt * b.toInt)) % (s.toNat : ℤ)
        + (j : ℤ) * (s.toNat : ℤ) := by
    simp only [toInt_add, toInt_mul, toInt_sub, toInt_two,
      AzInt.toInt_hMod, AzNat.toInt_toAzInt, toNat_ofNat]
  have hciff : (s.toAzInt ^ 2 * ((2 * (a * b)
      + (cᵢ - 2 * (a * b)) % s.toAzInt + (ofNat j).toAzInt * s.toAzInt)
        - a * b) < n.toAzInt)
      ↔ ((s.toNat : ℤ) ^ 2 * ((2 * (a.toInt * b.toInt)
        + (cᵢ.toInt - 2 * (a.toInt * b.toInt)) % (s.toNat : ℤ)
        + (j : ℤ) * (s.toNat : ℤ)) - a.toInt * b.toInt)
          < (n.toNat : ℤ)) := by
    rw [lt_iff_toInt_lt, toInt_mul, toInt_hPow, toInt_sub, hcexp,
      toInt_mul, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt]
  by_cases hcond : s.toAzInt ^ 2 * ((2 * (a * b)
      + (cᵢ - 2 * (a * b)) % s.toAzInt + (ofNat j).toAzInt * s.toAzInt)
        - a * b) < n.toAzInt
  · rw [if_pos hcond, if_pos (hciff.mp hcond), Option.map_some, hcexp]
  · rw [if_neg hcond, if_neg (fun h => hcond (hciff.mpr h))]
    rfl

/-! ### The main bridge and the transported specification -/

/-- The limb-level list maps under `toNat` to the proven reference
list of Algorithm 4.2.11. -/
theorem map_toNat_lenstraDivisors (n r s rs : AzNat) :
    (lenstraDivisors n r s rs).map toNat
      = CP.lenstraDivisors n.toNat r.toNat s.toNat rs.toNat := by
  rw [lenstraDivisors, CP.lenstraDivisors, List.map_flatMap]
  have hargs1 : (lenstraChainArgs n r s rs).1.toNat
      = (CP.lenstraChainArgs n.toNat r.toNat s.toNat rs.toNat).1 := by
    rw [lenstraChainArgs, CP.lenstraChainArgs]
    simp only [toNat_mod, toNat_mul]
  have hargs2 : (lenstraChainArgs n r s rs).2.toInt
      = (CP.lenstraChainArgs n.toNat r.toNat s.toNat rs.toNat).2 := by
    rw [lenstraChainArgs, CP.lenstraChainArgs]
    simp only [toInt_mul, AzInt.toInt_hDiv, toInt_sub,
      AzNat.toInt_toAzInt, toNat_mod, toNat_mul]
  have hT : lT s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2
      = CP.lT s.toNat (CP.lenstraChainArgs n.toNat r.toNat s.toNat rs.toNat).1
          (CP.lenstraChainArgs n.toNat r.toNat s.toNat rs.toNat).2 := by
    rw [lT_bridge, hargs1, hargs2]
  rw [hT]
  refine List.flatMap_congr ?_
  intro i _
  rw [List.map_flatMap]
  have hsolve : ∀ cz : AzInt, (solveSystem n r (n * rs % s) s
      (lA s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
      (lB s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
      cz).map toNat
      = CP.solveSystem n.toNat r.toNat (n.toNat * rs.toNat % s.toNat)
          s.toNat
          (CP.lA s.toNat
            (CP.lenstraChainArgs n.toNat r.toNat s.toNat rs.toNat).1
            (CP.lenstraChainArgs n.toNat r.toNat s.toNat rs.toNat).2 i)
          (CP.lB s.toNat
            (CP.lenstraChainArgs n.toNat r.toNat s.toNat rs.toNat).1
            (CP.lenstraChainArgs n.toNat r.toNat s.toNat rs.toNat).2 i)
          cz.toInt := by
    intro cz
    rw [map_toNat_solveSystem, toNat_mod, toNat_mul, toInt_lA, toInt_lB,
      hargs1, hargs2]
  by_cases hpar : i % 2 = 0
  · rw [if_pos hpar, if_pos hpar,
      List.flatMap_congr (fun cz _ => hsolve cz), ← List.flatMap_map,
      map_toInt_evenWindow, toInt_lC, hargs1, hargs2]
  · rw [if_neg hpar, if_neg hpar,
      List.flatMap_congr (fun cz _ => hsolve cz), ← List.flatMap_map,
      map_toInt_oddWindow, toInt_lA, toInt_lB, toInt_lC, hargs1, hargs2]

/-- **The transported specification**: under the hypotheses of
Theorem 4.2.12 (on the `toNat` values), the limb-level list contains
exactly the divisors of `n` congruent to `r (mod s)`. -/
theorem mem_lenstraDivisors {n r s rs : AzNat} (hr : 0 < r.toNat)
    (hrs : r.toNat < s.toNat) (hsn : s.toNat < n.toNat)
    (hinv : r.toNat * rs.toNat % s.toNat = 1) (hns : ¬s.toNat ∣ n.toNat)
    {d : AzNat} :
    d ∈ lenstraDivisors n r s rs ↔
      d.toNat ∣ n.toNat ∧ d.toNat % s.toNat = r.toNat := by
  rw [← CP.mem_lenstraDivisors hr hrs hsn hinv hns,
    ← map_toNat_lenstraDivisors]
  constructor
  · intro hd
    exact List.mem_map_of_mem hd
  · intro hd
    obtain ⟨d', hd', he⟩ := List.mem_map.mp hd
    rwa [show d = d' from toNat_injective he.symm]

end AzNat

end Azurite
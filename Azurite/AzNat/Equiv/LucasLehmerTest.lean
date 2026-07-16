/-
  **Correctness of the Lucas–Lehmer test** (Algorithm 4.2.7):

  * `lucasLehmerTest_eq_true_iff`: for an odd prime `p`,
    `lucasLehmerTest p = true ↔ (mersenne p).Prime` — BOTH verdicts
    are proofs, by the full iff of Theorem 4.2.6.

  The bridge is the usual two-rail pattern: `toNat_*` lemmas transport
  the limb-level loop onto Mathlib's `LucasLehmer.norm_num_ext.sModNat`
  (the recurrences agree on the nose), `sModNat_eq_sMod` and
  `residue_eq_zero_iff_sMod_eq_zero` convert the final residue to
  `(2^p − 1 : ℤ) ∣ s (p − 2)`, and `Azurite.CP.theorem_4_2_6` supplies
  the equivalence with primality.
-/
import Azurite.AzNat.LucasLehmerTest
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Pow2
import Azurite.AzNat.Equiv.Square.ToomCook3
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_6

namespace Azurite

namespace AzNat

open LucasLehmer.norm_num_ext

private lemma beq_iff_toNat_eq {a b : AzNat} :
    (a == b) = true ↔ a.toNat = b.toNat := by
  rw [beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, fun h => toNat_injective h⟩

/-- The limb-level Lucas–Lehmer loop computes Mathlib's `sModNat`. -/
theorem toNat_lucasLehmerLoop (M : AzNat) (k : ℕ) :
    (lucasLehmerLoop M (M - ofNat 2) k).toNat = sModNat M.toNat k := by
  induction k with
  | zero =>
    rw [lucasLehmerLoop, sModNat, toNat_mod, toNat_ofNat]
  | succ k ih =>
    rw [lucasLehmerLoop, sModNat, toNat_mod, toNat_add, toNat_square,
      toNat_sub, toNat_ofNat, ih]

/-- **Correctness of Algorithm 4.2.7**: for an odd prime `p`, the
limb-level Lucas–Lehmer test answers `true` exactly when
`M_p = 2^p − 1` is prime.  Both directions are Theorem 4.2.6 — in
particular a `false` verdict PROVES compositeness. -/
theorem lucasLehmerTest_eq_true_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    lucasLehmerTest p = true ↔ (mersenne p).Prime := by
  rw [CP.theorem_4_2_6 hp hp2, lucasLehmerTest, beq_iff_toNat_eq,
    toNat_lucasLehmerLoop, toNat_sub, toNat_pow2, toNat_one, toNat_zero]
  have hcast := sModNat_eq_sMod p (p - 2) hp.two_le
  have hchain : LucasLehmer.sMod p (p - 2) = 0
      ↔ (mersenne p : ℤ) ∣ LucasLehmer.s (p - 2) := by
    rw [← LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp.one_lt]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 :=
      ⟨p - 2, by have := hp.two_le; omega⟩
    rw [LucasLehmer.lucasLehmerResidue, LucasLehmer.sZMod_eq_s]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [show ((mersenne (p' + 2) : ℕ) : ℤ) = ((2 ^ (p' + 2) - 1 : ℕ) : ℤ)
      from rfl]
  rw [← hchain, ← hcast]
  exact ⟨fun h => by rw [h]; rfl, fun h => Int.natCast_eq_zero.mp h⟩

/-- The `false` half, stated separately for symmetry with the other
verdict theorems. -/
theorem lucasLehmerTest_eq_false_iff {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : lucasLehmerTest p = false ↔ ¬(mersenne p).Prime := by
  rw [← lucasLehmerTest_eq_true_iff hp hp2, Bool.eq_false_iff]

end AzNat

end Azurite

import Azurite.AzPolynomial.DivModByMonic
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Add
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Monomial
import Mathlib.Algebra.Polynomial.Div

/-!
# Correctness of `AzPolynomial.divModByMonic` (division by a monic polynomial)

For a **monic** `f`, the fuel-driven algorithm `divModByMonic` computes the genuine
Euclidean division: this file proves the **reconstruction identity**

`toPoly (divByMonic P f) * toPoly f + toPoly (modByMonic P f) = toPoly P`

and, together with the (unconditional) degree bound `divModByMonicAux_rem_size`, ties
`modByMonic`/`divByMonic` to Mathlib's `%ₘ` / `/ₘ`.

The proof is a fuel induction on `divModByMonicAux`:

* Each loop step subtracts `c • X^k · f` where `c` is the running leading coefficient;
  the trivial identity `rem = c•X^k·f + (rem − c•X^k·f)` gives the per-step
  reconstruction **unconditionally**.
* The only branch that would break reconstruction is the fuel-out reset-to-`0`; for
  monic `f` each step strictly drops the remainder's degree (`modStep_size_lt`, the one
  place monic-ness is used), so with fuel `P.coeffs.size + 1` that branch is never hit.
-/

namespace Azurite.AzPolynomial

open Polynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-! ### Size / coefficient helpers -/

omit [DecidableEq R] in
private theorem coeff_last_ne_zero (p : AzPolynomial R) (hp : p.coeffs.size ≠ 0) :
    p.coeff (p.coeffs.size - 1) ≠ 0 := by
  intro h
  apply p.last_ne_zero
  show p.coeffs[p.coeffs.size - 1]? = some 0
  rw [Array.getElem?_eq_getElem (by omega)]
  congr 1
  rw [show p.coeff (p.coeffs.size - 1) = (p.coeffs[p.coeffs.size - 1]?).getD 0 from rfl,
    Array.getElem?_eq_getElem (by omega)] at h
  exact h

omit [DecidableEq R] in
/-- If every coefficient from index `N` upward vanishes, the dense size is `≤ N`. -/
private theorem size_le_of_coeff_zero_above (P : AzPolynomial R) (N : ℕ)
    (h : ∀ i, i ≥ N → P.coeff i = 0) : P.coeffs.size ≤ N := by
  by_contra hlt
  have hlt' : N < P.coeffs.size := by omega
  exact coeff_last_ne_zero P (by omega) (h _ (by omega))

/-- A nonzero-size polynomial maps to a nonzero Mathlib polynomial. -/
private theorem toPoly_ne_zero_of_size_pos {P : AzPolynomial R} (hP : 0 < P.coeffs.size) :
    AzPolynomial.toPoly P ≠ 0 := by
  intro h
  have : P = 0 := toPoly_inj.mp (h.trans toPoly_zero.symm)
  rw [this, coeffs_zero] at hP
  simp at hP

/-- Monic (hence nonzero) divisor has positive dense size. -/
private theorem size_pos_of_toPoly_ne_zero {f : AzPolynomial R} (hf0 : AzPolynomial.toPoly f ≠ 0) :
    0 < f.coeffs.size := by
  rcases Nat.eq_zero_or_pos f.coeffs.size with h | h
  · exfalso; apply hf0
    have : f = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h)
    rw [this]; exact toPoly_zero
  · exact h

/-! ### Per-step degree drop (the only use of monic-ness) -/

/-- Subtracting `c • X^k · f` (with `c` the leading coefficient and `k` the degree gap)
from a remainder of degree `≥ deg f` strictly decreases its dense size, because for
**monic** `f` the leading terms cancel exactly. -/
private theorem modStep_size_lt {f : AzPolynomial R} (hf : (AzPolynomial.toPoly f).Monic)
    (hf0 : AzPolynomial.toPoly f ≠ 0)
    (rem : AzPolynomial R) (hge : f.coeffs.size ≤ rem.coeffs.size) :
    (rem - mulBasecaseFold (monomial (rem.natDegree - f.natDegree) rem.leadingCoeff) f).coeffs.size
      < rem.coeffs.size := by
  have hfs : 0 < f.coeffs.size := size_pos_of_toPoly_ne_zero hf0
  have hrs : 0 < rem.coeffs.size := lt_of_lt_of_le hfs hge
  set c := rem.leadingCoeff with hc
  set k := rem.natDegree - f.natDegree with hk
  have hrem0 : AzPolynomial.toPoly rem ≠ 0 := toPoly_ne_zero_of_size_pos hrs
  have hc_ne : c ≠ 0 := coeff_last_ne_zero rem (by omega)
  have hdeg_rem : (AzPolynomial.toPoly rem).degree = (rem.natDegree : WithBot ℕ) := by
    rw [AzPolynomial.degree_toPoly]
    show (if rem.coeffs = #[] then (⊥ : WithBot ℕ) else ↑rem.natDegree) = ↑rem.natDegree
    rw [ite_eq_right (by intro h; rw [h] at hrs; simp at hrs)]
  have hdeg_f : (AzPolynomial.toPoly f).degree = (f.natDegree : WithBot ℕ) := by
    rw [AzPolynomial.degree_toPoly]
    show (if f.coeffs = #[] then (⊥ : WithBot ℕ) else ↑f.natDegree) = ↑f.natDegree
    rw [ite_eq_right (by intro h; rw [h] at hfs; simp at hfs)]
  have hdeg_prod : (Polynomial.monomial k c * AzPolynomial.toPoly f).degree
      = (rem.natDegree : WithBot ℕ) := by
    rw [hf.degree_mul, Polynomial.degree_monomial k hc_ne, hdeg_f, ← Nat.cast_add]
    congr 1
    show k + f.natDegree = rem.natDegree
    have : f.natDegree ≤ rem.natDegree := by
      show f.coeffs.size - 1 ≤ rem.coeffs.size - 1; omega
    omega
  have hlc_prod : (Polynomial.monomial k c * AzPolynomial.toPoly f).leadingCoeff = c := by
    rw [Polynomial.leadingCoeff_mul_monic hf, Polynomial.leadingCoeff_monomial]
  have hd := Polynomial.degree_sub_lt_left (hdeg_rem.trans hdeg_prod.symm) hrem0
    (by rw [leadingCoeff_toPoly, ← hc, hlc_prod])
  have key : ∀ i, i ≥ rem.natDegree →
      (AzPolynomial.toPoly rem - Polynomial.monomial k c * AzPolynomial.toPoly f).coeff i = 0 := by
    intro i hi
    apply Polynomial.coeff_eq_zero_of_degree_lt
    calc (AzPolynomial.toPoly rem - Polynomial.monomial k c * AzPolynomial.toPoly f).degree
        < (AzPolynomial.toPoly rem).degree := hd
      _ = (rem.natDegree : WithBot ℕ) := hdeg_rem
      _ ≤ (i : WithBot ℕ) := by exact_mod_cast hi
  have hbridge : ∀ i, (rem - mulBasecaseFold (monomial k c) f).coeff i
      = (AzPolynomial.toPoly rem - Polynomial.monomial k c * AzPolynomial.toPoly f).coeff i := by
    intro i
    rw [← coeff_toPoly_eq, toPoly_sub, toPoly_mulBasecaseFold, toPoly_monomial]
  have hsz := size_le_of_coeff_zero_above (rem - mulBasecaseFold (monomial k c) f) rem.natDegree
    (fun i hi => by rw [hbridge]; exact key i hi)
  have hnd : rem.natDegree = rem.coeffs.size - 1 := rfl
  omega

/-! ### Reconstruction identity -/

/-- **Fuel-driven reconstruction.**  As long as the fuel is at least the remainder's
size (which holds for monic `f`, since the degree strictly drops each step), the
algorithm's quotient/remainder satisfy `rem = quo · f + rem'`. -/
private theorem divModByMonicAux_reconstruct {f : AzPolynomial R}
    (hf : (AzPolynomial.toPoly f).Monic) (hf0 : AzPolynomial.toPoly f ≠ 0) :
    ∀ (fuel : ℕ) (rem : AzPolynomial R), rem.coeffs.size ≤ fuel →
      AzPolynomial.toPoly rem = AzPolynomial.toPoly (divModByMonicAux f fuel rem).1
          * AzPolynomial.toPoly f
        + AzPolynomial.toPoly (divModByMonicAux f fuel rem).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro rem hrem
    have hsz0 : rem.coeffs.size = 0 := by omega
    have hrem0 : rem = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero hsz0)
    subst hrem0
    simp [divModByMonicAux, toPoly_zero]
  | succ n ih =>
    intro rem hrem
    simp only [divModByMonicAux]
    split
    · simp
    · rename_i hge
      have hge' : f.coeffs.size ≤ rem.coeffs.size := by omega
      set m := monomial (rem.natDegree - f.natDegree) rem.leadingCoeff with hm
      set rem' := rem - mulBasecaseFold m f with hrem'
      have hstep : rem'.coeffs.size < rem.coeffs.size := modStep_size_lt hf hf0 rem hge'
      have ihr := ih rem' (by omega)
      have htr : AzPolynomial.toPoly rem' = AzPolynomial.toPoly rem - AzPolynomial.toPoly m
          * AzPolynomial.toPoly f := by
        rw [hrem', toPoly_sub, toPoly_mulBasecaseFold]
      rw [htr] at ihr
      dsimp only
      rw [toPoly_add]
      linear_combination ihr

/-- **Reconstruction identity for `modByMonic`/`divByMonic`.**  For a monic divisor `f`,
`toPoly (divByMonic P f) · toPoly f + toPoly (modByMonic P f) = toPoly P`. -/
theorem toPoly_divByMonic_mul_add_modByMonic {f : AzPolynomial R}
    (hf : (AzPolynomial.toPoly f).Monic) (hf0 : AzPolynomial.toPoly f ≠ 0) (P : AzPolynomial R) :
    AzPolynomial.toPoly (divByMonic P f) * AzPolynomial.toPoly f
      + AzPolynomial.toPoly (modByMonic P f) = AzPolynomial.toPoly P := by
  exact (divModByMonicAux_reconstruct hf hf0 (P.coeffs.size + 1) P (by omega)).symm

/-- The residue `toPoly P − toPoly (modByMonic P f)` is a multiple of `toPoly f`. -/
theorem toPoly_f_dvd_sub_modByMonic {f : AzPolynomial R} (hf : (AzPolynomial.toPoly f).Monic)
    (hf0 : AzPolynomial.toPoly f ≠ 0) (P : AzPolynomial R) :
    AzPolynomial.toPoly f ∣ (AzPolynomial.toPoly P - AzPolynomial.toPoly (modByMonic P f)) := by
  refine ⟨AzPolynomial.toPoly (divByMonic P f), ?_⟩
  have h := toPoly_divByMonic_mul_add_modByMonic hf hf0 P
  linear_combination -h

/-- Strictly smaller dense size implies strictly smaller Mathlib degree (given the larger
one is nonzero). -/
theorem degree_toPoly_lt_of_size_lt {P Q : AzPolynomial R} (h : P.coeffs.size < Q.coeffs.size)
    (hQ0 : AzPolynomial.toPoly Q ≠ 0) :
    (AzPolynomial.toPoly P).degree < (AzPolynomial.toPoly Q).degree := by
  have hqs : 0 < Q.coeffs.size := size_pos_of_toPoly_ne_zero hQ0
  rw [AzPolynomial.degree_toPoly, AzPolynomial.degree_toPoly]
  simp only [AzPolynomial.degree]
  rw [ite_eq_right (show Q.coeffs ≠ #[] by intro hh; rw [hh] at hqs; simp at hqs)]
  by_cases hP : P.coeffs = #[]
  · rw [ite_eq_left hP]; exact WithBot.bot_lt_coe _
  · rw [ite_eq_right hP]
    have hPs : 0 < P.coeffs.size := by
      rcases Nat.eq_zero_or_pos P.coeffs.size with h' | h'
      · exact absurd (Array.eq_empty_of_size_eq_zero h') hP
      · exact h'
    have hlt : P.natDegree < Q.natDegree := by
      show P.coeffs.size - 1 < Q.coeffs.size - 1; omega
    exact_mod_cast hlt

/-- The degree bound restated in `Polynomial` terms: `deg (modByMonic P f) < deg f`. -/
theorem degree_toPoly_modByMonic_lt {f : AzPolynomial R} (hf0 : AzPolynomial.toPoly f ≠ 0)
    (P : AzPolynomial R) :
    (AzPolynomial.toPoly (modByMonic P f)).degree < (AzPolynomial.toPoly f).degree :=
  degree_toPoly_lt_of_size_lt (modByMonic_coeffs_size_lt P f (size_pos_of_toPoly_ne_zero hf0)) hf0

/-! ### Agreement with Mathlib's `%ₘ` / `/ₘ`

The reconstruction identity + degree bound are exactly the hypotheses of the uniqueness of monic
division (`Polynomial.div_modByMonic_unique`), pinning `modByMonic`/`divByMonic` to Mathlib's
`Polynomial.modByMonic` / `Polynomial.divByMonic`. -/

/-- **`modByMonic` computes Mathlib's `%ₘ`.**  For a monic divisor `f`,
`toPoly (modByMonic P f) = toPoly P %ₘ toPoly f`. -/
theorem toPoly_modByMonic {f : AzPolynomial R} (hf : (AzPolynomial.toPoly f).Monic)
    (hf0 : AzPolynomial.toPoly f ≠ 0) (P : AzPolynomial R) :
    AzPolynomial.toPoly (modByMonic P f)
      = AzPolynomial.toPoly P %ₘ AzPolynomial.toPoly f :=
  (Polynomial.div_modByMonic_unique (AzPolynomial.toPoly (divByMonic P f))
    (AzPolynomial.toPoly (modByMonic P f)) hf
    ⟨by linear_combination toPoly_divByMonic_mul_add_modByMonic hf hf0 P,
      degree_toPoly_modByMonic_lt hf0 P⟩).2.symm

/-- **`divByMonic` computes Mathlib's `/ₘ`.**  For a monic divisor `f`,
`toPoly (divByMonic P f) = toPoly P /ₘ toPoly f`. -/
theorem toPoly_divByMonic {f : AzPolynomial R} (hf : (AzPolynomial.toPoly f).Monic)
    (hf0 : AzPolynomial.toPoly f ≠ 0) (P : AzPolynomial R) :
    AzPolynomial.toPoly (divByMonic P f)
      = AzPolynomial.toPoly P /ₘ AzPolynomial.toPoly f :=
  (Polynomial.div_modByMonic_unique (AzPolynomial.toPoly (divByMonic P f))
    (AzPolynomial.toPoly (modByMonic P f)) hf
    ⟨by linear_combination toPoly_divByMonic_mul_add_modByMonic hf hf0 P,
      degree_toPoly_modByMonic_lt hf0 P⟩).1.symm

end Azurite.AzPolynomial

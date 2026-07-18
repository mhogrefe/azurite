/-
  Crandall–Pomerance, Theorem 2.1.6 (Chinese remainder theorem): for
  positive, pairwise coprime moduli `m_0, …, m_(r−1)` with product `M`
  and given residues `n_i`, the system

    `n ≡ n_i (mod m_i)`,  `0 ≤ n < M`

  has a unique solution, given explicitly by the least nonnegative
  residue mod `M` of `∑ n_i v_i M_i`, where `M_i = M / m_i` and the
  `v_i` are inverses with `v_i M_i ≡ 1 (mod m_i)`.

  Mathlib carries list-iterated two-moduli CRT
  (`Nat.chineseRemainderOfList`); what is formalized here is the
  book's statement — the `Fin`-indexed system with the EXPLICIT
  interpolation formula (the CRT analogue of Lagrange interpolation),
  which is what Algorithm 2.1.7 (Garner) is measured against.  The
  inverses exist (`exists_crt_inverse`) because `M_i` is the product
  of the moduli other than `m_i`, each coprime to `m_i`.
-/
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Azurite

namespace CP

open Finset
open scoped Function

variable {r : ℕ} (m n : Fin r → ℕ)

/-- Congruence modulo the product of pairwise coprime moduli is
congruence modulo each of them. -/
theorem modEq_prod_iff {x y : ℕ} (hco : Pairwise (Nat.Coprime on m)) :
    x ≡ y [MOD ∏ i, m i] ↔ ∀ i, x ≡ y [MOD m i] := by
  have hl : (List.finRange r).Pairwise (Nat.Coprime on m) :=
    List.Pairwise.imp (fun h => hco h.ne) (List.pairwise_lt_finRange _)
  rw [← List.prod_ofFn (f := m), List.ofFn_eq_map,
    Nat.modEq_list_map_prod_iff hl]
  simp

/-- `M / m i` is the product of the moduli other than `m i`. -/
theorem prod_div_eq_prod_erase (hm : ∀ i, 0 < m i) (i : Fin r) :
    (∏ j, m j) / m i = ∏ j ∈ univ.erase i, m j := by
  rw [← Finset.mul_prod_erase univ m (mem_univ i),
    Nat.mul_div_cancel_left _ (hm i)]

/-- The inverses `v_i` of Theorem 2.1.6 exist: `M_i = M / m_i` is
invertible mod `m_i`. -/
theorem exists_crt_inverse (hm : ∀ i, 0 < m i)
    (hco : Pairwise (Nat.Coprime on m)) (i : Fin r) :
    ∃ v, v * ((∏ j, m j) / m i) ≡ 1 [MOD m i] := by
  by_cases h1 : m i = 1
  · exact ⟨0, h1 ▸ Nat.modEq_one⟩
  · have h1 : 1 < m i := by have := hm i; omega
    have hcop : Nat.Coprime ((∏ j, m j) / m i) (m i) := by
      rw [prod_div_eq_prod_erase m hm i]
      exact Nat.Coprime.prod_left fun j hj => hco (ne_of_mem_erase hj)
    obtain ⟨v, -, hv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    refine ⟨v, ?_⟩
    rw [Nat.ModEq, Nat.mul_comm, hv, Nat.mod_eq_of_lt h1]

/-- **Theorem 2.1.6, the explicit formula**: the least nonnegative
residue mod `M` of `∑ n_i v_i M_i` solves the system. -/
theorem theorem_2_1_6_explicit (hm : ∀ i, 0 < m i) (v : Fin r → ℕ)
    (hv : ∀ i, v i * ((∏ j, m j) / m i) ≡ 1 [MOD m i]) :
    (∑ i, n i * v i * ((∏ j, m j) / m i)) % ∏ j, m j < ∏ j, m j ∧
      ∀ i, (∑ i, n i * v i * ((∏ j, m j) / m i)) % ∏ j, m j
        ≡ n i [MOD m i] := by
  have hM : 0 < ∏ j, m j := Finset.prod_pos fun j _ => hm j
  refine ⟨Nat.mod_lt _ hM, fun i => ?_⟩
  have hmod : (∑ i, n i * v i * ((∏ j, m j) / m i)) % ∏ j, m j
      ≡ ∑ i, n i * v i * ((∏ j, m j) / m i) [MOD m i] :=
    (Nat.mod_modEq _ _).of_dvd (dvd_prod_of_mem m (mem_univ i))
  refine hmod.trans ?_
  rw [← Finset.add_sum_erase univ _ (mem_univ i)]
  have hhead : n i * v i * ((∏ j, m j) / m i) ≡ n i [MOD m i] := by
    have := ((hv i).mul_left (n i)).trans (by rw [Nat.mul_one])
    rwa [← Nat.mul_assoc] at this
  have htail : (∑ j ∈ univ.erase i, n j * v j * ((∏ k, m k) / m j))
      ≡ 0 [MOD m i] := by
    rw [Nat.modEq_zero_iff_dvd]
    refine Finset.dvd_sum fun j hj => Dvd.dvd.mul_left ?_ _
    rw [prod_div_eq_prod_erase m hm j]
    exact dvd_prod_of_mem m (mem_erase.mpr ⟨(ne_of_mem_erase hj).symm, mem_univ i⟩)
  simpa using hhead.add htail

/-- **Theorem 2.1.6 (Chinese remainder theorem)**: the system
`n ≡ n_i (mod m_i)`, `0 ≤ n < M` has a unique solution. -/
theorem theorem_2_1_6 (hm : ∀ i, 0 < m i)
    (hco : Pairwise (Nat.Coprime on m)) :
    ∃! x, x < ∏ i, m i ∧ ∀ i, x ≡ n i [MOD m i] := by
  choose v hv using exists_crt_inverse m hm hco
  obtain ⟨hlt, hsol⟩ := theorem_2_1_6_explicit m n hm v hv
  refine ⟨_, ⟨hlt, hsol⟩, fun y ⟨hylt, hy⟩ => ?_⟩
  have hxy : y ≡ (∑ i, n i * v i * ((∏ j, m j) / m i)) % ∏ j, m j
      [MOD ∏ i, m i] :=
    (modEq_prod_iff m hco).mpr fun i => (hy i).trans (hsol i).symm
  rw [Nat.ModEq, Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt hlt] at hxy
  exact hxy

end CP

end Azurite

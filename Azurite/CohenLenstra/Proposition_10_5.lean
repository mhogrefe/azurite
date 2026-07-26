/-
  **Cohen–Lenstra Proposition (10.5): every (10.1)-ideal has
  quotient of size at least `n^f`.**

  If `𝔪 ⊆ ℤ[ζ_m]` satisfies `𝔪 ∩ ℤ = nℤ` and `σ_n[𝔪] = 𝔪`, then
  `1, ζ̄, …, ζ̄^(f−1)` are independent over `ℤ/nℤ` in `ℤ[ζ_m]/𝔪`,
  where `f` is the order of `n` mod `m` — so the quotient has at
  least `n^f` elements, and the ideals produced by Methods (10.2)
  and (10.3) (with quotient exactly `n^f`) are largest possible,
  even for composite `n`.

  We formalize the independence statement (`proposition_10_5`): an
  integer combination `Σ a_i ζ^i ∈ 𝔪` with `i < f` forces
  `n ∣ a_i` for all `i`.  The cardinality reading, the surjectivity
  of (10.3)'s `λ`, and `ℤ[ζ_{p^k}]/𝔪 ≅ F` are display-level
  consequences (counting on top of the independence) and are
  recorded in the blueprint.

  Proof, following the paper: applying `σ_n^j` to the relation
  gives `Σ_i a_i ζ̄^(i·n^j) = 0` for `j < f` (their (10.6)).  From
  `∏_{0<x<m} (1 − ζ^x) = m` (the identity of (7.17)'s proof;
  Mathlib's `IsPrimitiveRoot.prod_one_sub_pow_eq_order`) and
  `gcd(m, n) = 1`, every `1 − ζ̄^x` with `m ∤ x` is a *unit* in the
  quotient (`isUnit_one_sub_zetaBar_pow`).  Hence the Vandermonde
  determinant `det(ζ̄^(i n^j)) = ∏_{i<j} (ζ̄^(n^j) − ζ̄^(n^i))` is a
  unit — the differences factor as `ζ̄^(n^i)·(ζ̄^(n^j−n^i) − 1)`,
  with exponent nonzero mod `m` because the powers `n^j`, `j < f`,
  are distinct mod `m` — and the linear system kills the
  coefficients via the adjugate (`Matrix.adjugate_mul`).
-/
import Azurite.CohenLenstra.Method_10_2
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace Azurite

namespace CL

open Polynomial Azurite.CP

variable {m n : ℕ}

/-- The `hIZ`-condition extends from `ℕ` to `ℤ`. -/
theorem intCast_mem_imp_dvd {𝔪 : Ideal (CycM m)}
    (hIZ : ∀ a : ℕ, ((a : ℕ) : CycM m) ∈ 𝔪 → n ∣ a) :
    ∀ b : ℤ, ((b : ℤ) : CycM m) ∈ 𝔪 → (n : ℤ) ∣ b := by
  intro b hb
  rcases Int.natAbs_eq b with he | he
  · rw [he] at hb ⊢
    rw [Int.cast_natCast] at hb
    exact_mod_cast hIZ b.natAbs hb
  · rw [he] at hb ⊢
    rw [Int.cast_neg, Int.cast_natCast] at hb
    have hb' : ((b.natAbs : ℕ) : CycM m) ∈ 𝔪 := by
      simpa using 𝔪.neg_mem hb
    exact (Int.natCast_dvd_natCast.mpr (hIZ b.natAbs hb')).neg_right

/-- **`1 − ζ̄^x` is a unit mod `𝔪` for `m ∤ x`** — from
`∏_{0<x<m} (1 − ζ^x) = m` and the invertibility of `m` mod `n`. -/
theorem isUnit_one_sub_zetaBar_pow (hm : 0 < m) (hco : Nat.Coprime n m)
    (hn1 : 1 < n) {𝔪 : Ideal (CycM m)}
    (hnI : ((n : ℕ) : CycM m) ∈ 𝔪) {x : ℕ} (hx : ¬ m ∣ x) :
    IsUnit (1 - Ideal.Quotient.mk 𝔪 (zetaM m) ^ x) := by
  haveI := isDomain_cycM hm
  set π := Ideal.Quotient.mk 𝔪 with hπ
  set z := π (zetaM m) with hzdef
  -- `(m : Q)` is a unit
  have hmunit : IsUnit ((m : ℕ) : CycM m ⧸ 𝔪) := by
    obtain ⟨y, hy⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco.symm hn1
    obtain ⟨t, ht⟩ : ∃ t, m * y = n * t + 1 := by
      refine ⟨m * y / n, ?_⟩
      have := Nat.div_add_mod (m * y) n
      omega
    refine IsUnit.of_mul_eq_one ((y : ℕ) : CycM m ⧸ 𝔪) ?_
    have hcast : ((m : ℕ) : CycM m ⧸ 𝔪) * ((y : ℕ) : CycM m ⧸ 𝔪)
        = ((n : ℕ) : CycM m ⧸ 𝔪) * ((t : ℕ) : CycM m ⧸ 𝔪) + 1 := by
      have hc := congrArg (Nat.cast : ℕ → CycM m ⧸ 𝔪) ht
      push_cast at hc
      exact hc
    have hn0 : ((n : ℕ) : CycM m ⧸ 𝔪) = 0 := by
      rw [show ((n : ℕ) : CycM m ⧸ 𝔪) = π ((n : ℕ) : CycM m) from
        (map_natCast π n).symm, hπ, Ideal.Quotient.eq_zero_iff_mem]
      exact hnI
    rw [hcast, hn0, zero_mul, zero_add]
  -- the product identity, pushed to the quotient
  have hζ := isPrimitiveRoot_zetaM hm
  have hprod : ∏ k ∈ Finset.range (m - 1), (1 - z ^ (k + 1))
      = ((m : ℕ) : CycM m ⧸ 𝔪) := by
    have hζ' : IsPrimitiveRoot (zetaM m) ((m - 1) + 1) := by
      rwa [show m - 1 + 1 = m from by omega]
    have hup : ∏ k ∈ Finset.range (m - 1), (1 - zetaM m ^ (k + 1))
        = ((m : ℕ) : CycM m) := by
      rw [hζ'.prod_one_sub_pow_eq_order]
      have h1 : ((m - 1 + 1 : ℕ) : CycM m) = ((m : ℕ) : CycM m) := by
        rw [show m - 1 + 1 = m from by omega]
      push_cast at h1 ⊢
      exact h1
    have hπup := congrArg π hup
    rw [map_prod, map_natCast] at hπup
    rw [← hπup]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_sub, map_one, map_pow]
  -- `1 − z^x = 1 − z^(x % m)` is one of the factors
  have hzm : z ^ m = 1 := by
    rw [hzdef, ← map_pow, hζ.pow_eq_one, map_one]
  have hred : z ^ x = z ^ (x % m) := by
    conv_lhs => rw [← Nat.div_add_mod x m]
    rw [pow_add, pow_mul, hzm, one_pow, one_mul]
  have hxm1 : 1 ≤ x % m := by
    rcases Nat.eq_zero_or_pos (x % m) with h0 | h1
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) hx
    · exact h1
  have hxmlt : x % m < m := Nat.mod_lt _ hm
  have hdvd : (1 - z ^ (x % m))
      ∣ ∏ k ∈ Finset.range (m - 1), (1 - z ^ (k + 1)) := by
    have hmem : x % m - 1 ∈ Finset.range (m - 1) :=
      Finset.mem_range.mpr (by omega)
    have hd := Finset.dvd_prod_of_mem (fun k => 1 - z ^ (k + 1)) hmem
    rwa [show x % m - 1 + 1 = x % m from by omega] at hd
  rw [hred]
  exact isUnit_of_dvd_unit hdvd (hprod ▸ hmunit)

/-- **Cohen–Lenstra Proposition (10.5)** (independence form): for
an ideal `𝔪` of `ℤ[ζ_m]` satisfying the (10.1)-conditions, the
powers `1, ζ̄, …, ζ̄^(f−1)` are independent over `ℤ/nℤ` in the
quotient, where the powers `n^j`, `j < f`, are distinct mod `m`
(e.g. `f` = the order of `n` mod `m`): an integer combination
`Σ_{i<f} a_i ζ^i ∈ 𝔪` forces `n ∣ a_i` for all `i`.  Hence
`#(ℤ[ζ_m]/𝔪) ≥ n^f`, and the ideals of Methods (10.2)/(10.3) are
largest possible. -/
theorem proposition_10_5 (hm : 0 < m) (hco : Nat.Coprime n m)
    (hn1 : 1 < n) {𝔪 : Ideal (CycM m)}
    (hnI : ((n : ℕ) : CycM m) ∈ 𝔪)
    (hIZ : ∀ a : ℕ, ((a : ℕ) : CycM m) ∈ 𝔪 → n ∣ a)
    (hσ : ∀ x ∈ 𝔪, sigmaN hm hco x ∈ 𝔪)
    {f : ℕ}
    (hdist : ∀ i j : ℕ, i < f → j < f → n ^ i ≡ n ^ j [MOD m] → i = j)
    (a : Fin f → ℤ)
    (hsum : (∑ i : Fin f, ((a i : ℤ) : CycM m) * zetaM m ^ (i : ℕ)) ∈ 𝔪) :
    ∀ i, (n : ℤ) ∣ a i := by
  set π := Ideal.Quotient.mk 𝔪 with hπ
  set z := π (zetaM m) with hzdef
  -- (10.6): the `σ^j`-translates of the relation
  have hmem : ∀ j : ℕ,
      (∑ i : Fin f, ((a i : ℤ) : CycM m) * zetaM m ^ ((i : ℕ) * n ^ j))
        ∈ 𝔪 := by
    intro j
    induction j with
    | zero =>
      have he : ∀ i : Fin f, (i : ℕ) * n ^ 0 = (i : ℕ) := fun i => by
        rw [pow_zero, mul_one]
      rw [Finset.sum_congr rfl fun i _ => by rw [he i]]
      exact hsum
    | succ j ih =>
      have hσsum : sigmaN hm hco
          (∑ i : Fin f, ((a i : ℤ) : CycM m) * zetaM m ^ ((i : ℕ) * n ^ j))
          = ∑ i : Fin f,
              ((a i : ℤ) : CycM m) * zetaM m ^ ((i : ℕ) * n ^ (j + 1)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_intCast, map_pow, sigmaN_zetaM, ← pow_mul]
        have he : n * ((i : ℕ) * n ^ j) = (i : ℕ) * n ^ (j + 1) := by
          rw [pow_succ]
          ring
        rw [he]
      exact hσsum ▸ hσ _ ih
  -- push to the quotient
  have h106 : ∀ j : ℕ,
      (∑ i : Fin f, ((a i : ℤ) : CycM m ⧸ 𝔪) * z ^ ((i : ℕ) * n ^ j))
        = 0 := by
    intro j
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hmem j)
    rw [map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, map_pow]
  -- the Vandermonde system
  set v : Fin f → CycM m ⧸ 𝔪 := fun j => z ^ n ^ (j : ℕ) with hv
  set M := Matrix.vandermonde v with hM
  set av : Fin f → CycM m ⧸ 𝔪 := fun i => ((a i : ℤ) : CycM m ⧸ 𝔪)
    with hav
  have hMv : M.mulVec av = 0 := by
    funext j
    have hrow : M.mulVec av j
        = ∑ i : Fin f, ((a i : ℤ) : CycM m ⧸ 𝔪) * z ^ ((i : ℕ) * n ^ (j : ℕ)) := by
      simp only [hM, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
        hv, hav]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (z ^ n ^ (j : ℕ)) ^ (i : ℕ) * ((a i : ℤ) : CycM m ⧸ 𝔪)
          = ((a i : ℤ) : CycM m ⧸ 𝔪) * z ^ ((i : ℕ) * n ^ (j : ℕ))
      rw [← pow_mul, mul_comm (n ^ (j : ℕ)) (i : ℕ), mul_comm]
    rw [hrow, h106]
    rfl
  -- the determinant is a unit
  have hzunit : IsUnit z := by
    have hzm : z * z ^ (m - 1) = 1 := by
      rw [← pow_succ', show m - 1 + 1 = m from by omega, hzdef,
        ← map_pow, (isPrimitiveRoot_zetaM hm).pow_eq_one, map_one]
    exact IsUnit.of_mul_eq_one _ hzm
  have hdet : IsUnit M.det := by
    rw [hM, Matrix.det_vandermonde]
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul)
      isUnit_one fun i _ => ?_
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul)
      isUnit_one fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hle : n ^ (i : ℕ) ≤ n ^ (j : ℕ) :=
      Nat.pow_le_pow_right (by omega) (le_of_lt hij)
    have hfactor : v j - v i
        = z ^ n ^ (i : ℕ) * (z ^ (n ^ (j : ℕ) - n ^ (i : ℕ)) - 1) := by
      rw [hv, mul_sub, mul_one, ← pow_add,
        show n ^ (i : ℕ) + (n ^ (j : ℕ) - n ^ (i : ℕ)) = n ^ (j : ℕ)
          from by omega]
    rw [hfactor]
    refine IsUnit.mul (hzunit.pow _) ?_
    have hnd : ¬ m ∣ n ^ (j : ℕ) - n ^ (i : ℕ) := by
      intro hd
      have hmodeq : n ^ (i : ℕ) ≡ n ^ (j : ℕ) [MOD m] :=
        (Nat.modEq_iff_dvd' hle).mpr hd
      have := hdist (i : ℕ) (j : ℕ) i.isLt j.isLt hmodeq
      exact absurd (Fin.ext this) hij.ne
    have hone := isUnit_one_sub_zetaBar_pow hm hco hn1 hnI hnd
    rw [← hπ, ← hzdef] at hone
    have hneg : z ^ (n ^ (j : ℕ) - n ^ (i : ℕ)) - 1
        = -(1 - z ^ (n ^ (j : ℕ) - n ^ (i : ℕ))) := by ring
    rw [hneg]
    exact hone.neg
  -- cancel via the adjugate
  have hda : M.det • av = 0 := by
    calc M.det • av
        = (M.det • (1 : Matrix (Fin f) (Fin f) (CycM m ⧸ 𝔪))).mulVec av := by
          rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (M.adjugate * M).mulVec av := by rw [Matrix.adjugate_mul]
      _ = M.adjugate.mulVec (M.mulVec av) := by
          rw [← Matrix.mulVec_mulVec]
      _ = M.adjugate.mulVec 0 := by rw [hMv]
      _ = 0 := Matrix.mulVec_zero _
  intro i
  have hzero : ((a i : ℤ) : CycM m ⧸ 𝔪) = 0 := by
    have h1 := congrFun hda i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hav] at h1
    exact (hdet.mul_right_eq_zero).mp h1
  have hmemi : ((a i : ℤ) : CycM m) ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [show Ideal.Quotient.mk 𝔪 ((a i : ℤ) : CycM m)
      = ((a i : ℤ) : CycM m ⧸ 𝔪) from map_intCast _ _]
    exact hzero
  exact intCast_mem_imp_dvd hIZ _ hmemi

end CL

end Azurite

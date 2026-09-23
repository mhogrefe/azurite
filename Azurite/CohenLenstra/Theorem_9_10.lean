/-
  **Cohen–Lenstra Theorem (9.10): the triple-Jacobi-sum test for
  `p = 2`, `k ≥ 3`.**

  The triple Jacobi sum is `j(χ,χ,χ) = j(χ,χ)·j(χ,χ²)` (their
  (9.7)), satisfying `j(χ,χ,χ) = τ(χ)³/τ(χ³) = τ(χ)^(3−σ₃)` (their
  (9.8), two applications of (8.2)).  The index set is

    `M = {x : 1 ≤ x ≤ 2^k, x ≡ 1 or 3 (mod 8)}`  (their (9.9)),

  a subgroup of `(ℤ/2^k)^*` mod `2^k`.  Theorem (9.10): for
  `n ≡ 1, 3 (mod 8)` and `α = Σ_{x ∈ M} [nx/2^k]σ_x⁻¹`, the test
  (9.11) `j(χ,χ,χ)^α ≡ ζ (mod 𝔪)` implies (7.9) — with
  `β = Σ_{x ∈ M} [3x/2^k]σ_x⁻¹`, via the group-ring identity
  `(n−σ_n)β = (3−σ₃)α` (their (9.13), the θ-argument (9.15)/(9.16)
  of Lemma (8.12)'s pattern) and condition (7.6) for `β` (their
  (9.14), from the explicit sum `Σ_{x ∈ M} [3x/2^k] = 2^(k−2) − 1`,
  their (9.17)/(9.18), which is odd).

  The formalization mirrors `Theorem_8_5.lean` exactly, with the
  arithmetic simpler in two respects: the coefficient-wise (9.13)
  needs only two Euclidean decompositions and no subtraction guards
  (`eq_9_13_coeff`), and the (7.6)-condition is a closed-form
  computation rather than a valuation argument (`eq_9_18`,
  `eq_9_14`).  The conclusion `theorem_9_10` is the
  (7.9)-hypothesis of Theorem (7.8) at `p = 2` for the family
  `(S, ν) = (M2set k, [3·minv(·)/2^k])`; `eq_9_14` is its
  `hβ`-hypothesis, and the elements of `M2set` are odd (`M2_odd`),
  its `hSp`.  Failure of the test proves `n` composite by (7.5)
  (assembled with the algorithm in the later sections).
-/
import Azurite.CohenLenstra.Theorem_8_5

namespace Azurite

namespace CL

open Finset

/-- **The paper's (9.9)**: the index set
`M = {x : 1 ≤ x < 2^k, x ≡ 1 or 3 (mod 8)}` (the representative
`2^k` itself is even, so the paper's `1 ≤ x ≤ 2^k` gives the same
set). -/
def M2set (k : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (2 ^ k)).filter (fun x => x % 8 = 1 ∨ x % 8 = 3)

section M2Arithmetic

variable {k : ℕ} (hk3 : 3 ≤ k)

theorem mem_M2set {x : ℕ} :
    x ∈ M2set k ↔ (1 ≤ x ∧ x < 2 ^ k) ∧ (x % 8 = 1 ∨ x % 8 = 3) := by
  simp [M2set, Finset.mem_filter, Finset.mem_Ico]

theorem M2_odd {x : ℕ} (hx : x ∈ M2set k) : ¬ 2 ∣ x := by
  obtain ⟨_, h8⟩ := mem_M2set.mp hx
  omega

/-- `M2set k` sits inside the (8.4)-set at `p = 2`; this transports
the `Mset`-toolkit (`minv_mem`, `minv_invol`, …). -/
theorem M2_subset_Mset {x : ℕ} (hx : x ∈ M2set k) : x ∈ Mset 2 k := by
  obtain ⟨hb, h8⟩ := mem_M2set.mp hx
  exact mem_Mset.mpr ⟨hb, by omega⟩

include hk3 in
theorem eight_dvd_pow : (8 : ℕ) ∣ 2 ^ k := by
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8]
  exact pow_dvd_pow 2 hk3

include hk3 in
/-- `M2set` (mod `2^k`) is closed under multiplication by
`c ≡ 1, 3 (mod 8)` — the subgroup remark under (9.9). -/
theorem mAct2_mem {c x : ℕ} (hc : c % 8 = 1 ∨ c % 8 = 3)
    (hx : x ∈ M2set k) : mAct 2 k c x ∈ M2set k := by
  have : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  obtain ⟨⟨hx1, hxlt⟩, hx8⟩ := mem_M2set.mp hx
  have hval : mAct 2 k c x = (c * x) % 2 ^ k := by
    rw [mAct]
    exact ZMod.val_natCast (n := 2 ^ k) _
  have hmod8 : ((c * x) % 2 ^ k) % 8 = (c * x) % 8 :=
    Nat.mod_mod_of_dvd _ (eight_dvd_pow hk3)
  have hcx8 : (c * x) % 8 = 1 ∨ (c * x) % 8 = 3 := by
    have := Nat.mul_mod c x 8
    rcases hc with h | h <;> rcases hx8 with h' | h' <;>
      rw [h, h'] at this <;> omega
  refine mem_M2set.mpr ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hval]
    omega
  · rw [hval]
    exact Nat.mod_lt _ (pow_pos (by norm_num) k)
  · rw [hval, hmod8]
    exact hcx8

include hk3 in
/-- The residue class mod `8` of the mod-`2^k` inverse of
`c ≡ 1, 3 (mod 8)` is again `1` or `3` (`{1, 3}` is a subgroup of
`(ℤ/8)^*`, each element its own inverse). -/
theorem minv2_residue {c : ℕ} (hc : c % 8 = 1 ∨ c % 8 = 3) :
    minv 2 k c % 8 = 1 ∨ minv 2 k c % 8 = 3 := by
  have hc2 : ¬ 2 ∣ c := by omega
  have hspec := minv_spec (k := k) Nat.prime_two hc2
  have hmod8 : c * minv 2 k c ≡ 1 [MOD 8] :=
    Nat.ModEq.of_dvd (eight_dvd_pow hk3) hspec
  have h1 : (c * minv 2 k c) % 8 = 1 % 8 := hmod8
  have := Nat.mul_mod c (minv 2 k c) 8
  rcases hc with h | h <;> rw [h] at this <;> omega

include hk3 in
theorem minv2_mem {x : ℕ} (hx : x ∈ M2set k) : minv 2 k x ∈ M2set k := by
  have hres := minv2_residue hk3 (mem_M2set.mp hx).2
  have hM := minv_mem Nat.prime_two (by omega) (M2_subset_Mset hx)
  obtain ⟨hb, _⟩ := mem_Mset.mp hM
  exact mem_M2set.mpr ⟨hb, hres⟩

/-- **The coefficient-wise form of (9.13)**:
`(n − σ_n)β = (3 − σ₃)α`, read off at the coefficient of `σ_y⁻¹` —
two Euclidean decompositions, no guards. -/
theorem eq_9_13_coeff {n y : ℕ} :
    n * αc 3 2 k y + αc n 2 k (mAct 2 k 3 y)
      = 3 * αc n 2 k y + αc 3 2 k (mAct 2 k n y) := by
  have : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hN0 : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
  have hact : ∀ c z : ℕ, mAct 2 k c z = (c * z) % 2 ^ k := fun c z => by
    rw [mAct]
    exact ZMod.val_natCast (n := 2 ^ k) _
  simp only [αc, hact]
  have h1 := div_shift hN0 n (3 * y)
  have h2 := div_shift hN0 3 (n * y)
  have h3 : n * (3 * y) = 3 * (n * y) := by ring
  rw [h3] at h1
  omega

end M2Arithmetic

/-! ### The sums (9.17)/(9.18) and condition (7.6) for `β` -/

section SumComputation

variable {k : ℕ} (hk3 : 3 ≤ k)

include hk3 in
/-- The enumeration of `M2set` by blocks of eight. -/
theorem M2set_eq_biUnion :
    M2set k = (Finset.range (2 ^ (k - 3))).biUnion
      (fun j => {8 * j + 1, 8 * j + 3}) := by
  have hpow : (2 : ℕ) ^ k = 8 * 2 ^ (k - 3) := by
    conv_lhs => rw [show k = 3 + (k - 3) from by omega]
    rw [pow_add]
    norm_num
  ext x
  simp only [mem_M2set, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h8⟩
    refine ⟨x / 8, ?_, ?_⟩ <;> omega
  · rintro ⟨j, hj, hx | hx⟩ <;> subst hx <;>
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

include hk3 in
/-- `Σ_{x ∈ M} x = 2^(k−1)·(2^(k−2) − 1)` — the explicit sum behind
(9.17)/(9.18). -/
theorem sum_M2 : ∑ x ∈ M2set k, x = 2 ^ (k - 1) * (2 ^ (k - 2) - 1) := by
  rw [M2set_eq_biUnion hk3, Finset.sum_biUnion ?_]
  · have hinner : ∀ j : ℕ, ∑ x ∈ ({8 * j + 1, 8 * j + 3} : Finset ℕ), x
        = 16 * j + 4 := by
      intro j
      rw [Finset.sum_insert (by simp), Finset.sum_singleton]
      ring
    rw [Finset.sum_congr rfl fun j _ => hinner j]
    set t := (2 : ℕ) ^ (k - 3) with ht
    have hsplit : ∑ j ∈ Finset.range t, (16 * j + 4)
        = 16 * (∑ j ∈ Finset.range t, j) + 4 * t := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, smul_eq_mul, mul_comm t 4]
    rw [hsplit]
    have hgauss : (∑ j ∈ Finset.range t, j) * 2 = t * (t - 1) :=
      Finset.sum_range_id_mul_two t
    have ht1 : 1 ≤ t := Nat.one_le_two_pow
    have hp1 : (2 : ℕ) ^ (k - 1) = 4 * t := by
      rw [ht, show k - 1 = 2 + (k - 3) from by omega, pow_add]
      norm_num
    have hp2 : (2 : ℕ) ^ (k - 2) = 2 * t := by
      rw [ht, show k - 2 = 1 + (k - 3) from by omega, pow_add]
      norm_num
    rw [hp1, hp2]
    have htt : t * (t - 1) = t * t - t := by
      rw [Nat.mul_sub, mul_one]
    have hexp : 4 * t * (2 * t - 1) = 4 * (t * (2 * t - 1)) := by ring
    have hexp2 : t * (2 * t - 1) = 2 * (t * t) - t := by
      rw [Nat.mul_sub, mul_one, show t * (2 * t) = 2 * (t * t) from by
        ring]
    have htt2 : t ≤ t * t := Nat.le_mul_of_pos_left t ht1
    omega
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert,
      Finset.mem_singleton]
    rintro a (ha | ha) <;> subst ha <;> rintro (h | h) <;> omega

include hk3 in
/-- **The paper's (9.17)/(9.18)**:
`Σ_{x ∈ M} [3x/2^k] = 2^(k−2) − 1` — obtained by summing the
Euclidean decompositions `3x = 2^k·[3x/2^k] + (3x mod 2^k)` over
`M` and reindexing `Σ (3x mod 2^k) = Σ x` along the action of `3`
(the paper's homomorphism `σ_x ↦ 1` applied to (9.16)). -/
theorem eq_9_18 : ∑ x ∈ M2set k, αc 3 2 k x = 2 ^ (k - 2) - 1 := by
  have : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hact : ∀ z : ℕ, mAct 2 k 3 z = (3 * z) % 2 ^ k := fun z => by
    rw [mAct]
    exact ZMod.val_natCast (n := 2 ^ k) _
  -- the summed Euclidean decompositions
  have hsplit : ∀ x : ℕ, 3 * x = 2 ^ k * αc 3 2 k x + mAct 2 k 3 x := by
    intro x
    rw [hact, αc]
    exact (Nat.div_add_mod (3 * x) (2 ^ k)).symm
  have hsum : 3 * (∑ x ∈ M2set k, x)
      = 2 ^ k * (∑ x ∈ M2set k, αc 3 2 k x)
        + ∑ x ∈ M2set k, mAct 2 k 3 x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hsplit x
  -- `mAct 3` permutes `M`, so the last sum is `Σ x`
  have h38 : (3 : ℕ) % 8 = 1 ∨ (3 : ℕ) % 8 = 3 := Or.inr (by norm_num)
  have h32 : ¬ (2 : ℕ) ∣ 3 := by omega
  have hreidx : ∑ x ∈ M2set k, mAct 2 k 3 x = ∑ y ∈ M2set k, y := by
    refine Finset.sum_nbij' (fun x => mAct 2 k 3 x)
      (fun y => mAct 2 k (minv 2 k 3) y)
      (fun x hx => mAct2_mem hk3 h38 hx)
      (fun y hy => mAct2_mem hk3 (minv2_residue hk3 h38) hy)
      (fun x hx => mAct_mAct_one Nat.prime_two
        (by
          have := minv_spec (k := k) Nat.prime_two h32
          rwa [mul_comm] at this) (mem_M2set.mp hx).1.2)
      (fun y hy => mAct_mAct_one Nat.prime_two
        (minv_spec (k := k) Nat.prime_two h32) (mem_M2set.mp hy).1.2)
      (fun x _ => rfl)
  rw [hreidx] at hsum
  -- `2·Σx = 2^k·Σαc`, then cancel `2^k`
  have h2S : 2 * (∑ x ∈ M2set k, x)
      = 2 ^ k * (∑ x ∈ M2set k, αc 3 2 k x) := by
    omega
  have hkk : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = 1 + (k - 1) from by omega]
    rw [pow_add, pow_one]
  have hLHS : 2 * (∑ x ∈ M2set k, x) = 2 ^ k * (2 ^ (k - 2) - 1) := by
    rw [sum_M2 hk3, hkk, mul_assoc]
  rw [hLHS] at h2S
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) k) h2S).symm

include hk3 in
/-- **The paper's (9.14)**, in the form of condition (7.6) (the
`hβ`-hypothesis of Theorem (7.8)) for the family
`(M2set k, [3·minv(·)/2^k])`: the coefficient sum is
`2^(k−2) − 1` by (9.18), which is odd, and the weights `y` are all
odd. -/
theorem eq_9_14 :
    ¬ 2 ∣ ∑ y ∈ M2set k, αc 3 2 k (minv 2 k y) * y := by
  have hk : 0 < k := by omega
  -- drop the odd weights mod 2
  have h1 : ∑ y ∈ M2set k, αc 3 2 k (minv 2 k y) * y
      ≡ ∑ y ∈ M2set k, αc 3 2 k (minv 2 k y) [MOD 2] :=
    modEq_sum fun y hy => by
      have hodd := M2_odd hy
      have hy1 : y ≡ 1 [MOD 2] := by
        unfold Nat.ModEq
        omega
      calc αc 3 2 k (minv 2 k y) * y
          ≡ αc 3 2 k (minv 2 k y) * 1 [MOD 2] := hy1.mul_left _
        _ = αc 3 2 k (minv 2 k y) := mul_one _
  -- reindex along `minv`
  have h2 : ∑ y ∈ M2set k, αc 3 2 k (minv 2 k y)
      = ∑ x ∈ M2set k, αc 3 2 k x := by
    refine Finset.sum_nbij' (fun y => minv 2 k y) (fun x => minv 2 k x)
      (fun y hy => minv2_mem hk3 hy) (fun x hx => minv2_mem hk3 hx)
      (fun y hy => minv_invol Nat.prime_two hk (M2_subset_Mset hy))
      (fun x hx => minv_invol Nat.prime_two hk (M2_subset_Mset hx))
      (fun y _ => rfl)
  rw [h2, eq_9_18 hk3] at h1
  -- `2^(k−2) − 1` is odd
  have h22 : (2 : ℕ) ^ (k - 2) = 2 * 2 ^ (k - 3) := by
    conv_lhs => rw [show k - 2 = 1 + (k - 3) from by omega]
    rw [pow_add, pow_one]
  have h13 := Nat.one_le_two_pow (n := k - 3)
  intro hd
  unfold Nat.ModEq at h1
  omega

end SumComputation

/-! ### The product identities and Theorem (9.10) -/

section NineTen

variable {R : Type _} [CommRing R] [IsDomain R] {q n k : ℕ}
variable [Fact q.Prime]
variable {χ : MulChar (ZMod q) R} {ψ : AddChar (ZMod q) R}
variable {σ : R →+* R} {I : Ideal R}

omit [IsDomain R] in
/-- Reindexing a Gauss-sum product over `M2set` along the
multiplication action by `c ≡ 1, 3 (mod 8)`. -/
theorem Pprod_reindex_M2 (hk3 : 3 ≤ k) (hord : orderOf χ = 2 ^ k)
    {c : ℕ} (hc : c % 8 = 1 ∨ c % 8 = 3) (f : ℕ → ℕ) :
    ∏ x ∈ M2set k, gaussSum (χ ^ (c * minv 2 k x)) ψ ^ f x
      = ∏ y ∈ M2set k, gaussSum (χ ^ minv 2 k y) ψ ^ f (mAct 2 k c y) := by
  have hk : 0 < k := by omega
  have hc2 : ¬ 2 ∣ c := by omega
  have hchpow : ∀ {A B : ℕ}, A ≡ B [MOD 2 ^ k] → χ ^ A = χ ^ B :=
    fun hAB => pow_eq_pow_iff_modEq.mpr (hord ▸ hAB)
  refine Finset.prod_nbij' (fun x => mAct 2 k (minv 2 k c) x)
    (fun y => mAct 2 k c y)
    (fun x hx => mAct2_mem hk3 (minv2_residue hk3 hc) hx)
    (fun y hy => mAct2_mem hk3 hc hy)
    (fun x hx => mAct_mAct_one Nat.prime_two
      (minv_spec (k := k) Nat.prime_two hc2) (mem_M2set.mp hx).1.2)
    (fun y hy => mAct_mAct_one Nat.prime_two
      (by
        have := minv_spec (k := k) Nat.prime_two hc2
        rwa [mul_comm] at this) (mem_M2set.mp hy).1.2)
    (fun x hx => ?_)
  have hcongr := minv_mAct_congr' Nat.prime_two hk hc2 (M2_odd hx)
  have hfx : mAct 2 k c (mAct 2 k (minv 2 k c) x) = x :=
    mAct_mAct_one Nat.prime_two
      (minv_spec (k := k) Nat.prime_two hc2) (mem_M2set.mp hx).1.2
  rw [hfx, hchpow hcongr.symm]

/-- **The paper's (9.8), per exponent, unit-free**: for odd `m`,

`τ(χ^(3m))·(j(χ^m,χ^m)·j(χ^m,χ^(2m))) = τ(χ^m)³`,

i.e. `j(χ,χ,χ) = τ(χ)^(3−σ₃)` after division by the unit
`τ(χ³)` — two applications of (8.2), with (9.7)'s
`j(χ,χ,χ) = j(χ,χ)·j(χ,χ²)` inlined as the product of the two
Jacobi sums. -/
theorem eq_9_8 (hk3 : 3 ≤ k) (hord : orderOf χ = 2 ^ k)
    (ψ : AddChar (ZMod q) R) {m : ℕ} (hm : ¬ 2 ∣ m) :
    gaussSum (χ ^ (3 * m)) ψ
      * (jacobiSum (χ ^ m) (χ ^ m) * jacobiSum (χ ^ m) (χ ^ (2 * m)))
    = gaussSum (χ ^ m) ψ ^ 3 := by
  have hd1 : ¬ (2 : ℕ) ^ k ∣ m + m := by
    intro hd
    have h2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = 1 + (k - 1) from by omega]
      rw [pow_add, pow_one]
    rw [h2, show m + m = 2 * m from by ring] at hd
    have hdm : (2 : ℕ) ^ (k - 1) ∣ m :=
      (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 2)).mp hd
    exact hm (dvd_trans (dvd_pow_self 2 (by omega : k - 1 ≠ 0)) hdm)
  have hd2 : ¬ (2 : ℕ) ^ k ∣ m + 2 * m := by
    intro hd
    have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
    have := dvd_trans h2 hd
    omega
  have h1 := eq_8_2 (p := 2) (k := k) hord ψ (a := m) (b := m) hd1
  have h2 := eq_8_2 (p := 2) (k := k) hord ψ (a := m) (b := 2 * m) hd2
  rw [show m + m = 2 * m from by ring] at h1
  rw [show m + 2 * m = 3 * m from by ring] at h2
  calc gaussSum (χ ^ (3 * m)) ψ
        * (jacobiSum (χ ^ m) (χ ^ m) * jacobiSum (χ ^ m) (χ ^ (2 * m)))
      = (gaussSum (χ ^ (3 * m)) ψ * jacobiSum (χ ^ m) (χ ^ (2 * m)))
        * jacobiSum (χ ^ m) (χ ^ m) := by ring
    _ = (gaussSum (χ ^ m) ψ * gaussSum (χ ^ (2 * m)) ψ)
        * jacobiSum (χ ^ m) (χ ^ m) := by rw [h2]
    _ = gaussSum (χ ^ m) ψ
        * (gaussSum (χ ^ (2 * m)) ψ * jacobiSum (χ ^ m) (χ ^ m)) := by
        ring
    _ = gaussSum (χ ^ m) ψ
        * (gaussSum (χ ^ m) ψ * gaussSum (χ ^ m) ψ) := by rw [h1]
    _ = gaussSum (χ ^ m) ψ ^ 3 := by ring

omit [IsDomain R] in
/-- **The `(n−σ_n)β = (3−σ₃)α` identity at the Gauss-sum-product
level** — the (9.13)-half of (9.10)'s proof, assembled from the
coefficient-wise `eq_9_13_coeff`. -/
theorem tau_product_identity_M2 (hk3 : 3 ≤ k)
    (hord : orderOf χ = 2 ^ k) (hn8 : n % 8 = 1 ∨ n % 8 = 3) :
    (∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x) ^ n
      * ∏ x ∈ M2set k,
          gaussSum (χ ^ (3 * minv 2 k x)) ψ ^ αc n 2 k x
    = (∏ x ∈ M2set k, gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x)
      * ∏ x ∈ M2set k,
          gaussSum (χ ^ minv 2 k x) ψ ^ (3 * αc n 2 k x) := by
  rw [Pprod_reindex_M2 hk3 hord (c := 3) (Or.inr (by norm_num))
      (αc n 2 k),
    Pprod_reindex_M2 hk3 hord (c := n) hn8 (αc 3 2 k),
    ← Finset.prod_pow]
  simp only [← pow_mul]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [← pow_add, ← pow_add]
  congr 1
  rw [mul_comm (αc 3 2 k y) n]
  have h913 := eq_9_13_coeff (k := k) (n := n) (y := y)
  omega

/-- **The paper's chain `j(χ,χ,χ)^α = τ(χ)^((n−σ_n)β)`**, as the
unit-free ring identity `j^α · σ(u_β) = u_β^n`. -/
theorem jacobi_tau_identity_M2 (hk3 : 3 ≤ k)
    (hord : orderOf χ = 2 ^ k) (hψ : ψ.IsPrimitive)
    (hq0 : ((q : ℕ) : R) ≠ 0) (hn8 : n % 8 = 1 ∨ n % 8 = 3) :
    (∏ x ∈ M2set k,
        (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
          * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
          ^ αc n 2 k x)
      * ∏ x ∈ M2set k,
          gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x
    = (∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x) ^ n := by
  have hk : 0 < k := by omega
  have hchne : ∀ x ∈ M2set k, χ ^ (3 * minv 2 k x) ≠ 1 := by
    intro x hx h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hd
    have h2d : (2 : ℕ) ∣ 3 * minv 2 k x :=
      dvd_trans (dvd_pow_self 2 hk.ne') hd
    have hodd := minv_not_dvd Nat.prime_two hk (M2_odd hx)
    omega
  -- step A: the per-`x` instances of (9.8), multiplied
  have hA : (∏ x ∈ M2set k,
        (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
          * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
          ^ αc n 2 k x)
      * ∏ x ∈ M2set k,
          gaussSum (χ ^ (3 * minv 2 k x)) ψ ^ αc n 2 k x
    = ∏ x ∈ M2set k,
        gaussSum (χ ^ minv 2 k x) ψ ^ (3 * αc n 2 k x) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [← mul_pow, mul_comm
      (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
        * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
      (gaussSum (χ ^ (3 * minv 2 k x)) ψ),
      eq_9_8 hk3 hord ψ (minv_not_dvd Nat.prime_two hk (M2_odd hx)),
      ← pow_mul]
  have hB := tau_product_identity_M2 (ψ := ψ) hk3 hord hn8
  -- cancel the common factor `∏ τ(χ^(3·x*))^(αc)`
  have hPs : (∏ x ∈ M2set k,
      gaussSum (χ ^ (3 * minv 2 k x)) ψ ^ αc n 2 k x) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun x hx => ?_
    refine pow_ne_zero _ ?_
    refine gaussSum_ne_zero_of_nontrivial ?_ (hchne x hx) hψ
    rw [ZMod.card]
    exact hq0
  refine mul_right_cancel₀ hPs ?_
  calc (∏ x ∈ M2set k,
        (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
          * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
          ^ αc n 2 k x)
      * (∏ x ∈ M2set k,
          gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x)
      * (∏ x ∈ M2set k,
          gaussSum (χ ^ (3 * minv 2 k x)) ψ ^ αc n 2 k x)
      = ((∏ x ∈ M2set k,
            (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
              * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
              ^ αc n 2 k x)
          * ∏ x ∈ M2set k,
              gaussSum (χ ^ (3 * minv 2 k x)) ψ ^ αc n 2 k x)
        * ∏ x ∈ M2set k,
            gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x := by
        ring
    _ = (∏ x ∈ M2set k,
          gaussSum (χ ^ minv 2 k x) ψ ^ (3 * αc n 2 k x))
        * ∏ x ∈ M2set k,
            gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x := by
        rw [hA]
    _ = (∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x) ^ n
        * ∏ x ∈ M2set k,
            gaussSum (χ ^ (3 * minv 2 k x)) ψ ^ αc n 2 k x := by
        rw [hB]
        ring

/-- **Cohen–Lenstra Theorem (9.10)** (soundness direction,
abstract): if the triple-Jacobi-sum congruence (9.11) holds —
`∏_{x ∈ M} (j(χ^(x*),χ^(x*))·j(χ^(x*),χ^(2x*)))^(αc x) ≡ ζ'
(mod I)` — then the (7.9)-hypothesis of Theorem (7.8) holds at
`p = 2` for the family `(M2set k, [3·minv(·)/2^k])`, with the
*same* `ζ'`.  The `hβ`-hypothesis for this family is `eq_9_14`;
its `hSp` is `M2_odd`.  As in (8.5), the second assertion of the
paper's theorem (a prime `n` passes the test) is completeness,
assembled with the algorithm in the later sections. -/
theorem theorem_9_10 (hk3 : 3 ≤ k) (hn0 : n ≠ 0)
    (hord : orderOf χ = 2 ^ k) (hψ : ψ.IsPrimitive)
    (hq0 : ((q : ℕ) : R) ≠ 0) (hn8 : n % 8 = 1 ∨ n % 8 = 3)
    (hσχ : ∀ c : ZMod q, σ (χ c) = χ c ^ n)
    (hσψ : ∀ c : ZMod q, σ (ψ c) = ψ c)
    {ζ' : R}
    (h911 : (∏ x ∈ M2set k,
        (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
          * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
          ^ αc n 2 k x) - ζ' ∈ I) :
    (∏ y ∈ M2set k, gaussSum (χ ^ y) ψ ^ αc 3 2 k (minv 2 k y)) ^ n
      - ζ' * σ (∏ y ∈ M2set k,
          gaussSum (χ ^ y) ψ ^ αc 3 2 k (minv 2 k y)) ∈ I := by
  have hk : 0 < k := by omega
  -- the `y`-indexed family is the `minv`-reindexing of the
  -- `x`-indexed one
  have hreidx : (∏ y ∈ M2set k,
        gaussSum (χ ^ y) ψ ^ αc 3 2 k (minv 2 k y))
      = ∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x := by
    refine Finset.prod_nbij' (fun y => minv 2 k y) (fun x => minv 2 k x)
      (fun y hy => minv2_mem hk3 hy) (fun x hx => minv2_mem hk3 hx)
      (fun y hy => minv_invol Nat.prime_two hk (M2_subset_Mset hy))
      (fun x hx => minv_invol Nat.prime_two hk (M2_subset_Mset hx))
      (fun y hy => ?_)
    rw [minv_invol Nat.prime_two hk (M2_subset_Mset hy)]
  -- σ of the product is the `n`-shifted product
  have hσprod : σ (∏ x ∈ M2set k,
        gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x)
      = ∏ x ∈ M2set k,
          gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [map_pow, sigma_gaussSum hσχ hσψ hn0 ?_]
    · rw [mul_comm]
    · intro h0
      exact minv_not_dvd Nat.prime_two hk (M2_odd hx)
        (h0 ▸ dvd_zero 2)
  rw [hreidx, hσprod]
  have hid := jacobi_tau_identity_M2 (ψ := ψ) hk3 hord hψ hq0 hn8
  have heq : (∏ x ∈ M2set k,
        gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x) ^ n
      - ζ' * ∏ x ∈ M2set k,
          gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x
      = ((∏ x ∈ M2set k,
            (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
              * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
              ^ αc n 2 k x) - ζ')
        * ∏ x ∈ M2set k,
            gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x := by
    rw [← hid]
    ring
  rw [heq]
  exact Ideal.mul_mem_right _ I h911

end NineTen

end CL

end Azurite

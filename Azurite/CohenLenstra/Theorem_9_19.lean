/-
  **Cohen–Lenstra Theorem (9.19): the triple-Jacobi-sum test for
  `p = 2`, `k ≥ 3`, `n ≡ 5, 7 (mod 8)`.**

  The companion of Theorem (9.10) for the residues where `mAct n`
  does *not* preserve the index set `M`.  With
  `φ = χ^(2^(k−3))` (of order `8` at every level) the test (9.20) is

    `j(χ,χ,χ)^α · j(φ,φ³)² ≡ ζ (mod 𝔪)`,

  and its verification implies (7.9) for the same family
  `(M, β)` as in (9.10), with the root `χ(−1)·ζ`.

  The proof follows the paper.  (9.15) applied to `m = −n` (allowed
  since `−n ≡ 1, 3 (mod 8)`) combines with (9.16) into

    `(n + σ_{−n})β = (3 − σ₃)α + 2·Σ_{x ∈ M} σ_x⁻¹`,

  rendered coefficient-wise as the floor identity
  `eq_9_13_coeff_neg` (with `nneg` a positive representative of
  `−n` mod `2^k`; two Euclidean decompositions plus the two
  "negation" identities `[A/N] + [B/N] + 1 = m` for `A + B = mN`,
  `N ∤ A`).  The pairing `σ_n(u)·σ_{−n}(u)` collapses by (7.2)
  (`tau_mul_tau_inv`) and (9.18) to `χ(−1)·q^(2^(k−2)−1)`
  (`sigma_pair_M2`).  Finally (9.22),

    `(∏_{x ∈ M} τ(χ^x))² = q^(2^(k−2)−1) · j(φ,φ³)²`,

  is proved by induction on `k`: the base `k = 3` is (8.2) plus
  `τ(χ⁴)² = q`; the step pairs `τ(χ^x)` with `τ(χ^(yx))`
  (`y = 1 + 2^(k−1)`, so `χ^y = χψ` for the quadratic `ψ`) via the
  Hasse–Davenport special case (9.23)

    `χ(4)·τ(χ)·τ(χψ) = τ(χ²)·τ(ψ)`,

  and the `τ(χ²)`-product doubles down one level (`M2set_succ`).
  (9.23) reduces via (8.2) to `j(χ,ψ) = χ(4)·j(χ,χ)`, proved by
  the direct counting argument of [5, §20.4]:
  `#{s : s² = w} = 1 + ψ(w)` — our abstract order-2 character is
  identified with Mathlib's `quadraticChar` on a generator of
  `(ℤ/q)ˣ` (`psi_eq_quadraticChar`), unlocking Mathlib's
  `quadraticChar_card_sqrts`.

  Condition (7.6) for `β` is (9.14) — `eq_9_14`, unchanged from
  Theorem (9.10).  Remarks (9.24a) (the root of (7.9) is `±ζ`,
  and `±ζ` is primitive iff `ζ` is — feeding the
  (7.26)-discussion) and (9.24b) (`χ(−1) = −1` iff
  `k = v₂(q−1)`) are prose-level observations recorded in the
  blueprint.
-/
import Azurite.CohenLenstra.Theorem_9_1
import Azurite.CohenLenstra.Theorem_9_10
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace Azurite

namespace CL

open Finset

/-! ### Floor arithmetic: the coefficient-wise (9.13)-analogue -/

/-- If `A + B = m·N` with `N ∤ A`, the floors satisfy
`[A/N] + [B/N] + 1 = m` — the "negation" identity behind
`[−a/N] = −[a/N] − 1`. -/
theorem div_add_div_of_add_eq {N A B m : ℕ} (hN : 0 < N)
    (hAB : A + B = m * N) (hA : ¬ N ∣ A) :
    A / N + B / N + 1 = m := by
  have hmod : A % N + B % N = N := by
    have hd : N ∣ A % N + B % N := by
      have h1 : A + B ≡ 0 [MOD N] :=
        (Nat.modEq_zero_iff_dvd).mpr ⟨m, by rw [hAB, mul_comm]⟩
      have h2 : A % N + B % N ≡ A + B [MOD N] :=
        (Nat.mod_modEq A N).add (Nat.mod_modEq B N)
      exact (Nat.modEq_zero_iff_dvd).mp (h2.trans h1)
    have hAm : A % N < N := Nat.mod_lt _ hN
    have hBm : B % N < N := Nat.mod_lt _ hN
    have hA0 : A % N ≠ 0 := fun h => hA (Nat.dvd_of_mod_eq_zero h)
    obtain ⟨j, hj⟩ := hd
    match j, hj with
    | 0, hj => omega
    | 1, hj => omega
    | (j + 2), hj =>
      have h2N : N * 2 ≤ N * (j + 2) := Nat.mul_le_mul_left N (by omega)
      omega
  have hdiv : (A + B) / N = m := by
    rw [hAB, Nat.mul_div_cancel _ hN]
  rw [Nat.add_div hN, hmod, ite_eq_left le_rfl] at hdiv
  omega

/-- **The coefficient-wise form of the (9.13)-analogue for
`n ≡ 5, 7 (mod 8)`**: with `nneg` a representative of `−n` mod
`2^k`, the group-ring identity
`(n + σ_{−n})β = (3 − σ₃)α + 2Σσ_x⁻¹` reads off at `σ_y⁻¹` as a
floor identity in ℕ. -/
theorem eq_9_13_coeff_neg {k n nneg y : ℕ} (hk : 0 < k)
    (hy : ¬ 2 ∣ y) (hn : ¬ 2 ∣ n) (hnn : 2 ^ k ∣ n + nneg) :
    n * αc 3 2 k y + αc 3 2 k (mAct 2 k nneg y)
        + αc n 2 k (mAct 2 k 3 y)
      = 3 * αc n 2 k y + 2 := by
  have : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hN0 : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
  have hact : ∀ c z : ℕ, mAct 2 k c z = (c * z) % 2 ^ k := fun c z => by
    rw [mAct]
    exact ZMod.val_natCast (n := 2 ^ k) _
  simp only [αc, hact]
  obtain ⟨c, hc⟩ := hnn
  have h2N : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
  have hnyodd : ¬ 2 ^ k ∣ n * y := fun hd => by
    have := dvd_trans h2N hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h
    · exact hn h
    · exact hy h
  have h3nyodd : ¬ 2 ^ k ∣ 3 * (n * y) := fun hd => by
    have := dvd_trans h2N hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h
    · omega
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
      · exact hn h'
      · exact hy h'
  -- the two Euclidean decompositions
  have h1 := div_shift hN0 n (3 * y)
  have h2 := div_shift hN0 3 (nneg * y)
  have h3 : n * (3 * y) = 3 * (n * y) := by ring
  rw [h3] at h1
  -- the two negation identities
  have hf1 : n * y / 2 ^ k + nneg * y / 2 ^ k + 1 = c * y :=
    div_add_div_of_add_eq hN0
      (by rw [show n * y + nneg * y = (n + nneg) * y from by ring, hc]
          ring) hnyodd
  have hf2 : 3 * (n * y) / 2 ^ k + 3 * (nneg * y) / 2 ^ k + 1
      = 3 * (c * y) :=
    div_add_div_of_add_eq hN0
      (by rw [show 3 * (n * y) + 3 * (nneg * y)
            = 3 * ((n + nneg) * y) from by ring, hc]
          ring) h3nyodd
  omega

/-! ### Character-theoretic preliminaries -/

section CharPrelims

variable {R : Type _} [CommRing R] [IsDomain R] {q : ℕ} [Fact q.Prime]

omit [IsDomain R] in
/-- A character of `2`-power order `> 1` forces `q ≠ 2` (the unit
group of `ℤ/2` is trivial). -/
theorem q_ne_two {χ : MulChar (ZMod q) R} {k : ℕ}
    (hord : orderOf χ = 2 ^ k) (hk : 0 < k) : q ≠ 2 := by
  rintro rfl
  have hχ1 : χ = 1 := by
    refine MulChar.ext fun u => ?_
    have hu : u = 1 := by revert u; decide
    rw [hu]
    simp
  rw [hχ1, orderOf_one] at hord
  have : (1 : ℕ) < 2 ^ k := Nat.one_lt_two_pow_iff.mpr hk.ne'
  omega

omit [IsDomain R] in
/-- `χ(−1)` to an odd power is `χ(−1)`. -/
theorem chi_neg_one_pow_odd (χ : MulChar (ZMod q) R) {m : ℕ}
    (hm : ¬ 2 ∣ m) : χ (-1) ^ m = χ (-1) := by
  have hsq : χ (-1) ^ 2 = 1 := by
    rw [pow_two]
    exact chi_neg_one_sq χ
  obtain ⟨j, hj⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
  rw [hj, pow_succ, pow_mul, hsq, one_pow, one_mul]

/-- Powers by odd exponents preserve the (2-power) order. -/
theorem orderOf_pow_odd {M : Type _} [Monoid M] {a : M} {K x : ℕ}
    (hord : orderOf a = 2 ^ K) (hx : ¬ 2 ∣ x) :
    orderOf (a ^ x) = 2 ^ K := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (dvd_zero 2)
  rw [orderOf_pow' a hx0, hord]
  have hco : Nat.gcd (2 ^ K) x = 1 :=
    Nat.Coprime.pow_left K
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx)
  rw [hco, Nat.div_one]

/-- An abstract order-2 character into a domain *is* Mathlib's
quadratic character (composed into `R`): both send a generator of
the cyclic unit group to `−1`. -/
theorem psi_eq_quadraticChar (hq2 : q ≠ 2)
    {ψq : MulChar (ZMod q) R} (hψ2 : orderOf ψq = 2) (a : ZMod q) :
    ψq a = ((quadraticChar (ZMod q) a : ℤ) : R) := by
  have hq := Fact.out (p := q.Prime)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  -- `ψq ↑g = −1`
  have hgsq : ψq ↑g * ψq ↑g = 1 := by
    have h1 : (ψq ^ 2) ↑g = 1 := by
      rw [← hψ2, pow_orderOf_eq_one]
      exact MulChar.one_apply_coe g
    rw [MulChar.pow_apply_coe, pow_two] at h1
    exact h1
  have hψg : ψq ↑g = -1 := by
    rcases mul_self_eq_one_iff.mp hgsq with h | h
    · exfalso
      have hone : ψq = 1 := by
        refine MulChar.ext fun u => ?_
        rw [MulChar.one_apply_coe]
        obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (hg u)
        have hn' : g ^ n = u := hn
        rw [← hn', Units.val_pow_eq_pow_val, map_pow, h, one_pow]
      rw [hone, orderOf_one] at hψ2
      exact absurd hψ2 (by norm_num)
    · exact h
  -- the generator is not a square, so `quadraticChar ↑g = −1`
  have hq2le : 2 ≤ q := hq.two_le
  have hqodd : q % 2 = 1 :=
    Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hgord : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, ZMod.card_units]
  have hgns : ¬ IsSquare (↑g : ZMod q) := by
    rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hb
      exact g.ne_zero hb
    have hbu : IsUnit b := isUnit_iff_ne_zero.mpr hb0
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (hg hbu.unit)
    have hn' : g ^ n = hbu.unit := hn
    have hgu : g = hbu.unit * hbu.unit := by
      refine Units.ext ?_
      rw [Units.val_mul, hbu.unit_spec]
      exact hb
    have hg2n : g ^ (2 * n) = g ^ 1 := by
      rw [two_mul, pow_add, hn', pow_one, ← hgu]
    have hmod := pow_eq_pow_iff_modEq.mp hg2n
    rw [hgord] at hmod
    have h2d : (2 : ℕ) ∣ q - 1 := by omega
    have hfin := Nat.ModEq.of_dvd h2d hmod
    have : (2 * n) % 2 = 1 % 2 := hfin
    omega
  have hqcg : quadraticChar (ZMod q) ↑g = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hgns
  -- pointwise comparison
  by_cases hua : IsUnit a
  · obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (hg hua.unit)
    have hn' : g ^ n = hua.unit := hn
    have ha : a = ↑(g ^ n) := by rw [hn', hua.unit_spec]
    rw [ha, Units.val_pow_eq_pow_val, map_pow, map_pow, hψg, hqcg]
    push_cast
    ring
  · rw [MulChar.map_nonunit _ hua, MulChar.map_nonunit _ hua]
    simp

/-- The number of square roots of `w` in `ℤ/q`, counted in `R`, is
`1 + ψ(w)` for an(y) order-2 character `ψ`. -/
theorem card_sq_fiber (hq2 : q ≠ 2)
    {ψq : MulChar (ZMod q) R} (hψ2 : orderOf ψq = 2) (w : ZMod q) :
    (((Finset.univ.filter fun s : ZMod q => s ^ 2 = w).card : ℕ) : R)
      = 1 + ψq w := by
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  have hcount := quadraticChar_card_sqrts hchar w
  have hset : ({x : ZMod q | x ^ 2 = w} : Set (ZMod q)).toFinset
      = Finset.univ.filter fun s : ZMod q => s ^ 2 = w := by
    ext s
    simp
  rw [hset] at hcount
  have : (((Finset.univ.filter fun s : ZMod q => s ^ 2 = w).card : ℤ) : R)
      = ((quadraticChar (ZMod q) w + 1 : ℤ) : R) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : R)) hcount
  push_cast at this
  rw [this, psi_eq_quadraticChar hq2 hψ2 w]
  ring

/-- **The counting computation of [5, §20.4]**:
`j(χ, ψ) = χ(4)·j(χ, χ)` for any nontrivial `χ` and an(y) order-2
character `ψ` — the Hasse–Davenport product relation at the
quadratic character, in Jacobi-sum form. -/
theorem jacobiSum_quadratic (hq2 : q ≠ 2)
    {η ψq : MulChar (ZMod q) R} (hη1 : η ≠ 1) (hψ2 : orderOf ψq = 2) :
    jacobiSum η ψq = η 4 * jacobiSum η η := by
  have hq := Fact.out (p := q.Prime)
  have hu2 : IsUnit ((2 : ℕ) : ZMod q) := by
    refine (ZMod.isUnit_iff_coprime 2 q).mpr ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      fun hd => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
        hd).symm
  have h20 : (2 : ZMod q) ≠ 0 := by
    have hcast : ((2 : ℕ) : ZMod q) = (2 : ZMod q) := by push_cast; rfl
    rw [← hcast]
    exact hu2.ne_zero
  -- step 1: absorb `η 4` into the sum
  have h1 : η 4 * jacobiSum η η
      = ∑ x : ZMod q, η (4 * (x * (1 - x))) := by
    rw [jacobiSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, map_mul]
  -- step 2: substitute `s = 1 − 2x`, using `4x(1−x) = 1 − (1−2x)²`
  have hbij : Function.Bijective (fun x : ZMod q => 1 - 2 * x) := by
    refine Finite.injective_iff_bijective.mp fun a b hab => ?_
    have h2 : (2 : ZMod q) * a = 2 * b := sub_right_injective hab
    exact mul_left_cancel₀ h20 h2
  have h2 : ∑ x : ZMod q, η (4 * (x * (1 - x)))
      = ∑ s : ZMod q, η (1 - s ^ 2) := by
    refine Fintype.sum_bijective _ hbij _ _ fun x => ?_
    congr 1
    ring
  -- step 3: fiberwise over `w = s²`
  have h3 : ∑ s : ZMod q, η (1 - s ^ 2)
      = ∑ w : ZMod q,
          (((Finset.univ.filter fun s : ZMod q => s ^ 2 = w).card : ℕ) : R)
            * η (1 - w) := by
    rw [Finset.sum_comp (fun w => η (1 - w)) (fun s : ZMod q => s ^ 2)]
    rw [Finset.sum_subset (Finset.subset_univ _)]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [nsmul_eq_mul]
    · intro w _ hw
      have hempty : (Finset.univ.filter
          fun s : ZMod q => s ^ 2 = w) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun s _ hs => ?_
        exact hw (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, hs⟩)
      rw [hempty]
      simp
  -- step 4: the counting identity + splitting the sum
  have h4 : ∑ w : ZMod q,
        (((Finset.univ.filter fun s : ZMod q => s ^ 2 = w).card : ℕ) : R)
          * η (1 - w)
      = (∑ w : ZMod q, η (1 - w))
        + ∑ w : ZMod q, ψq w * η (1 - w) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [card_sq_fiber hq2 hψ2 w, add_mul, one_mul]
  -- the plain character sum vanishes
  have h5 : ∑ w : ZMod q, η (1 - w) = 0 := by
    have hre : ∑ w : ZMod q, η (1 - w) = ∑ v : ZMod q, η v := by
      refine Fintype.sum_bijective (fun w : ZMod q => 1 - w)
        (Function.Involutive.bijective fun w => by ring) _ _
        fun w => rfl
    rw [hre]
    exact MulChar.sum_eq_zero_of_ne_one hη1
  -- assemble
  have h7 : ∑ w : ZMod q, ψq w * η (1 - w) = jacobiSum η ψq := by
    rw [← jacobiSum]
    exact jacobiSum_comm ψq η
  rw [h1, h2, h3, h4, h5, zero_add, h7]

end CharPrelims

/-! ### The Hasse–Davenport identity (9.23) and the induction (9.22) -/

section NineTwentyTwo

variable {R : Type _} [CommRing R] [IsDomain R] {q : ℕ} [Fact q.Prime]
variable {ψ : AddChar (ZMod q) R}

/-- **The paper's (9.23), unit-free**: for `η` of order `2^K`
(`K ≥ 2`), with `ψ_η = η^(2^(K−1))` the quadratic character,

`η(4)·τ(η)·τ(η·ψ_η) = τ(η²)·τ(ψ_η)`

(the special case of the Hasse–Davenport product relation, proved
via `jacobiSum_quadratic` and two applications of (8.2)). -/
theorem eq_9_23 {K : ℕ} (hK : 2 ≤ K) {η : MulChar (ZMod q) R}
    (hord : orderOf η = 2 ^ K) (hψ : ψ.IsPrimitive)
    (hq0 : ((q : ℕ) : R) ≠ 0) :
    η 4 * (gaussSum η ψ * gaussSum (η ^ (1 + 2 ^ (K - 1))) ψ)
      = gaussSum (η ^ 2) ψ * gaussSum (η ^ 2 ^ (K - 1)) ψ := by
  have hq2 : q ≠ 2 := q_ne_two hord (by omega)
  have hη1 : η ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    have : (1 : ℕ) < 2 ^ K := Nat.one_lt_two_pow_iff.mpr (by omega)
    omega
  have hψ2 : orderOf (η ^ 2 ^ (K - 1)) = 2 := by
    rw [orderOf_pow, hord]
    have hgcd : Nat.gcd (2 ^ K) (2 ^ (K - 1)) = 2 ^ (K - 1) := by
      refine Nat.gcd_eq_right ?_
      exact pow_dvd_pow 2 (by omega)
    rw [hgcd, Nat.pow_div (by omega) (by norm_num),
      show K - (K - 1) = 1 from by omega, pow_one]
  have hHD := jacobiSum_quadratic hq2 hη1 hψ2
  -- the two (8.2)-instances
  have h82a := eq_8_2 (p := 2) (k := K) hord ψ (a := 1) (b := 1)
    (by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      have : (2 : ℕ) ^ 2 ≤ 2 ^ K :=
        Nat.pow_le_pow_right (by norm_num) hK
      omega)
  have h82b := eq_8_2 (p := 2) (k := K) hord ψ (a := 1)
    (b := 2 ^ (K - 1))
    (by
      intro hd
      have h2e : (2 : ℕ) ∣ 2 ^ (K - 1) :=
        dvd_pow_self 2 (by omega : K - 1 ≠ 0)
      have h2K : (2 : ℕ) ∣ 2 ^ K := dvd_pow_self 2 (by omega : K ≠ 0)
      have := dvd_trans h2K hd
      omega)
  rw [pow_one] at h82a h82b
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h82a
  -- cancel `τ(η)` from the multiplied-out chain
  have hτη : gaussSum η ψ ≠ 0 := by
    refine gaussSum_ne_zero_of_nontrivial ?_ hη1 hψ
    rw [ZMod.card]
    exact hq0
  refine mul_right_cancel₀ hτη ?_
  calc η 4 * (gaussSum η ψ * gaussSum (η ^ (1 + 2 ^ (K - 1))) ψ)
        * gaussSum η ψ
      = gaussSum (η ^ (1 + 2 ^ (K - 1))) ψ
          * (η 4 * (gaussSum η ψ * gaussSum η ψ)) := by ring
    _ = gaussSum (η ^ (1 + 2 ^ (K - 1))) ψ
          * (η 4 * (gaussSum (η ^ 2) ψ * jacobiSum η η)) := by
        rw [h82a]
    _ = gaussSum (η ^ 2) ψ
          * (gaussSum (η ^ (1 + 2 ^ (K - 1))) ψ
            * (η 4 * jacobiSum η η)) := by ring
    _ = gaussSum (η ^ 2) ψ
          * (gaussSum (η ^ (1 + 2 ^ (K - 1))) ψ
            * jacobiSum η (η ^ 2 ^ (K - 1))) := by rw [← hHD]
    _ = gaussSum (η ^ 2) ψ
          * (gaussSum η ψ * gaussSum (η ^ 2 ^ (K - 1)) ψ) := by
        rw [h82b]
    _ = gaussSum (η ^ 2) ψ * gaussSum (η ^ 2 ^ (K - 1)) ψ
          * gaussSum η ψ := by ring

/-- The level-`(k+1)` index set is the level-`k` one plus its
translate by `2^k` — the double cover behind the (9.22)
induction step. -/
theorem M2set_succ {k : ℕ} (hk3 : 3 ≤ k) :
    M2set (k + 1) = M2set k ∪ (M2set k).image (· + 2 ^ k) := by
  obtain ⟨c, hc⟩ := eight_dvd_pow hk3
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ]
    ring
  ext x
  simp only [mem_M2set, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨⟨hx1, hxlt⟩, hx8⟩
    by_cases hlt : x < 2 ^ k
    · exact Or.inl ⟨⟨hx1, hlt⟩, hx8⟩
    · refine Or.inr ⟨x - 2 ^ k, ⟨⟨by omega, by omega⟩, by omega⟩,
        by omega⟩
  · rintro (⟨⟨h1, h2⟩, h8⟩ | ⟨a, ⟨⟨ha1, ha2⟩, ha8⟩, rfl⟩) <;>
      exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem card_M2set {k : ℕ} (hk3 : 3 ≤ k) :
    (M2set k).card = 2 ^ (k - 2) := by
  rw [M2set_eq_biUnion hk3, Finset.card_biUnion ?_]
  · have hpair : ∀ j : ℕ,
        ({8 * j + 1, 8 * j + 3} : Finset ℕ).card = 2 := by
      intro j
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    rw [Finset.sum_congr rfl fun j _ => hpair j, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    rw [show k - 2 = (k - 3) + 1 from by omega, pow_succ]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_insert,
      Finset.mem_singleton]
    rintro a (ha | ha) <;> subst ha <;> rintro (h | h) <;> omega

/-- **The paper's (9.22)**:
`(∏_{x ∈ M} τ(χ^x))² = q^(2^(k−2)−1)·j(φ,φ³)²` with
`φ = χ^(2^(k−3))`, by induction on `k` via (9.23). -/
theorem eq_9_22 (hψ : ψ.IsPrimitive) (hq0 : ((q : ℕ) : R) ≠ 0)
    {k : ℕ} (hk3 : 3 ≤ k) :
    ∀ χ : MulChar (ZMod q) R, orderOf χ = 2 ^ k →
      (∏ x ∈ M2set k, gaussSum (χ ^ x) ψ) ^ 2
        = ((q : ℕ) : R) ^ (2 ^ (k - 2) - 1)
          * jacobiSum (χ ^ 2 ^ (k - 3)) ((χ ^ 2 ^ (k - 3)) ^ 3) ^ 2 := by
  induction k, hk3 using Nat.le_induction with
  | base =>
    intro χ hord
    -- `M = {1, 3}`, `φ = χ`
    have hM3 : M2set 3 = {1, 3} := by
      ext x
      simp only [mem_M2set, show (2 : ℕ) ^ 3 = 8 from by norm_num,
        Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hM3, Finset.prod_insert (by simp), Finset.prod_singleton]
    simp only [show (3 : ℕ) - 2 = 1 from rfl,
      show (3 : ℕ) - 3 = 0 from rfl, pow_zero, pow_one]
    have h82 := eq_8_2 (p := 2) (k := 3) hord ψ (a := 1) (b := 3)
      (by norm_num)
    rw [pow_one, show (1 : ℕ) + 3 = 4 from rfl] at h82
    have hord4 : orderOf (χ ^ 4) = 2 := by
      rw [orderOf_pow, hord]
      decide
    have hχ41 : χ ^ 4 ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord4
      exact absurd hord4 (by norm_num)
    have hsq : gaussSum (χ ^ 4) ψ ^ 2 = ((q : ℕ) : R) := by
      rw [gaussSum_sq hχ41 (isQuadratic_of_orderOf hord4) hψ, ZMod.card]
      have hneg : (χ ^ 4) (-1) = 1 := by
        rw [MulChar.pow_apply' χ (by norm_num) (-1)]
        have := chi_neg_one_sq χ
        calc χ (-1) ^ 4 = (χ (-1) * χ (-1)) * (χ (-1) * χ (-1)) := by
              ring
          _ = 1 := by rw [this, one_mul]
      rw [hneg, one_mul]
    calc (gaussSum χ ψ * gaussSum (χ ^ 3) ψ) ^ 2
        = (gaussSum (χ ^ 4) ψ * jacobiSum χ (χ ^ 3)) ^ 2 := by
          rw [h82]
      _ = gaussSum (χ ^ 4) ψ ^ 2 * jacobiSum χ (χ ^ 3) ^ 2 := by
          ring
      _ = ((q : ℕ) : R) * jacobiSum χ (χ ^ 3) ^ 2 := by
          rw [hsq]
  | succ k hk ih =>
    intro χ hord
    have hk31 : 3 ≤ k + 1 := by omega
    have hkpos : 0 < k + 1 := by omega
    obtain ⟨c8, hc8⟩ := eight_dvd_pow hk
    -- the quadratic character `ψχ = χ^(2^k)` and the shift `y`
    set ψχ := χ ^ 2 ^ k with hψχdef
    have hordψχ : orderOf ψχ = 2 := by
      rw [hψχdef, orderOf_pow, hord]
      have hgcd : Nat.gcd (2 ^ (k + 1)) (2 ^ k) = 2 ^ k :=
        Nat.gcd_eq_right (pow_dvd_pow 2 (by omega))
      rw [hgcd, pow_succ, Nat.mul_div_cancel_left _
        (pow_pos (by norm_num) _)]
    have hord2 : orderOf (χ ^ 2) = 2 ^ k := by
      rw [orderOf_pow, hord]
      have hgcd : Nat.gcd (2 ^ (k + 1)) 2 = 2 := by
        refine Nat.gcd_eq_right ?_
        exact dvd_pow_self 2 (by omega)
      rw [hgcd, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    set y := 1 + 2 ^ k with hydef
    have hy8 : y % 8 = 1 := by omega
    have hyodd : ¬ 2 ∣ y := by omega
    -- reindexing `x ↦ y·x` fixes the product
    have hchpow : ∀ {A B : ℕ}, A ≡ B [MOD 2 ^ (k + 1)] →
        χ ^ A = χ ^ B :=
      fun hAB => pow_eq_pow_iff_modEq.mpr (hord ▸ hAB)
    have hsub1 : ∏ x ∈ M2set (k + 1), gaussSum (χ ^ (y * x)) ψ
        = ∏ x ∈ M2set (k + 1), gaussSum (χ ^ x) ψ := by
      refine Finset.prod_nbij' (fun x => mAct 2 (k + 1) y x)
        (fun x => mAct 2 (k + 1) (minv 2 (k + 1) y) x)
        (fun x hx => mAct2_mem hk31 (Or.inl hy8) hx)
        (fun x hx => mAct2_mem hk31
          (minv2_residue hk31 (Or.inl hy8)) hx)
        (fun x hx => mAct_mAct_one Nat.prime_two
          (by
            have := minv_spec (k := k + 1) Nat.prime_two hyodd
            rwa [mul_comm] at this) (mem_M2set.mp hx).1.2)
        (fun x hx => mAct_mAct_one Nat.prime_two
          (minv_spec (k := k + 1) Nat.prime_two hyodd)
          (mem_M2set.mp hx).1.2)
        (fun x hx => ?_)
      have hcong : mAct 2 (k + 1) y x ≡ y * x [MOD 2 ^ (k + 1)] := by
        have : NeZero ((2 : ℕ) ^ (k + 1)) :=
          ⟨pow_ne_zero _ two_ne_zero⟩
        rw [mAct, ZMod.val_natCast]
        exact Nat.mod_modEq _ _
      rw [hchpow hcong.symm]
    -- the per-`x` (9.23)-instances
    have hper : ∀ x ∈ M2set (k + 1),
        χ 4 ^ x * (gaussSum (χ ^ x) ψ * gaussSum (χ ^ (y * x)) ψ)
          = gaussSum ψχ ψ * gaussSum (χ ^ (2 * x)) ψ := by
      intro x hx
      have hxodd : ¬ 2 ∣ x := M2_odd hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hxodd (dvd_zero 2)
      have hordx : orderOf (χ ^ x) = 2 ^ (k + 1) :=
        orderOf_pow_odd hord hxodd
      have h923 := eq_9_23 (K := k + 1) (by omega) hordx hψ hq0
      rw [show k + 1 - 1 = k from rfl] at h923
      -- convert the four `(χ^x)`-powers
      have hc1 : (χ ^ x) 4 = χ 4 ^ x := MulChar.pow_apply' χ hx0 4
      have hc2 : (χ ^ x) ^ (1 + 2 ^ k) = χ ^ (y * x) := by
        rw [← pow_mul, hydef]
        rw [mul_comm x (1 + 2 ^ k)]
      have hc3 : (χ ^ x) ^ 2 = χ ^ (2 * x) := by
        rw [← pow_mul, mul_comm x 2]
      have hc4 : (χ ^ x) ^ 2 ^ k = ψχ := by
        rw [← pow_mul, hψχdef]
        refine hchpow ?_
        have hx1 : x ≡ 1 [MOD 2] := by
          unfold Nat.ModEq
          omega
        have := Nat.ModEq.mul_right' (c := 2 ^ k) hx1
        rw [one_mul, ← pow_succ'] at this
        exact this
      rw [hc1, hc2, hc3, hc4] at h923
      rw [h923]
      exact mul_comm _ _
    -- multiply the instances over `M`
    have hbig := Finset.prod_congr rfl hper
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_const, hsub1] at hbig
    -- the `χ(4)`-factor is 1 via (9.17)
    have hu2 : IsUnit ((2 : ℕ) : ZMod q) := by
      have hq2 : q ≠ 2 := q_ne_two hord (by omega)
      refine (ZMod.isUnit_iff_coprime 2 q).mpr ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        fun hd => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two
          (Fact.out (p := q.Prime))).mp hd).symm
    have hchi4 : ∏ x ∈ M2set (k + 1), χ 4 ^ x = 1 := by
      rw [Finset.prod_pow_eq_pow_sum, sum_M2 hk31,
        show k + 1 - 1 = k from rfl, show k + 1 - 2 = k - 1 from rfl]
      have h42 : (4 : ZMod q) = 2 * 2 := by norm_num
      have hkill : χ 4 ^ (2 ^ k * (2 ^ (k - 1) - 1)) = 1 := by
        rw [h42, map_mul]
        have : (χ 2 * χ 2) ^ (2 ^ k * (2 ^ (k - 1) - 1))
            = (χ 2 ^ 2 ^ (k + 1)) ^ (2 ^ (k - 1) - 1) := by
          calc (χ 2 * χ 2) ^ (2 ^ k * (2 ^ (k - 1) - 1))
              = (χ 2 ^ 2) ^ (2 ^ k * (2 ^ (k - 1) - 1)) := by
                rw [← pow_two]
            _ = χ 2 ^ (2 * (2 ^ k * (2 ^ (k - 1) - 1))) := by
                rw [← pow_mul]
            _ = χ 2 ^ (2 ^ (k + 1) * (2 ^ (k - 1) - 1)) := by
                congr 1
                rw [pow_succ]
                ring
            _ = (χ 2 ^ 2 ^ (k + 1)) ^ (2 ^ (k - 1) - 1) := by
                rw [← pow_mul]
        rw [this]
        have hχ2 : χ 2 ^ 2 ^ (k + 1) = 1 := by
          have h1 : χ 2 ^ 2 ^ (k + 1) = (χ ^ 2 ^ (k + 1)) 2 :=
            (MulChar.pow_apply' χ (pow_ne_zero _ two_ne_zero) 2).symm
          rw [h1, ← hord, pow_orderOf_eq_one]
          have h2u : ((2 : ℕ) : ZMod q) = ↑hu2.unit :=
            hu2.unit_spec.symm
          have : ((2 : ℕ) : ZMod q) = (2 : ZMod q) := by push_cast; rfl
          rw [← this, h2u]
          exact MulChar.one_apply_coe hu2.unit
        rw [hχ2, one_pow]
      exact hkill
    rw [hchi4, one_mul] at hbig
    -- the `τ(ψχ)`-factor is a `q`-power
    have hψχ1 : ψχ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hordψχ
      exact absurd hordψχ (by norm_num)
    have hτψsq : gaussSum ψχ ψ ^ 2 = ((q : ℕ) : R) := by
      rw [gaussSum_sq hψχ1 (isQuadratic_of_orderOf hordψχ) hψ,
        ZMod.card]
      have hneg : ψχ (-1) = 1 := by
        rw [hψχdef, MulChar.pow_apply' χ (pow_ne_zero _ two_ne_zero)]
        have h2k : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [h2k, pow_mul, pow_two, chi_neg_one_sq, one_pow]
      rw [hneg, one_mul]
    have hcard : (M2set (k + 1)).card = 2 ^ (k - 1) := by
      rw [card_M2set hk31]
      congr 1
    have hτψpow : gaussSum ψχ ψ ^ (M2set (k + 1)).card
        = ((q : ℕ) : R) ^ 2 ^ (k - 2) := by
      rw [hcard, show (2 : ℕ) ^ (k - 1) = 2 * 2 ^ (k - 2) from by
        rw [← pow_succ']
        congr 1
        omega]
      rw [pow_mul, hτψsq]
    rw [hτψpow] at hbig
    -- the doubled product at level `k`
    have hsplit : ∏ x ∈ M2set (k + 1), gaussSum (χ ^ (2 * x)) ψ
        = (∏ x ∈ M2set k, gaussSum ((χ ^ 2) ^ x) ψ) ^ 2 := by
      have hconv : ∀ x : ℕ, χ ^ (2 * x) = (χ ^ 2) ^ x := fun x => by
        rw [← pow_mul]
      have hdisj : Disjoint (M2set k) ((M2set k).image (· + 2 ^ k)) := by
        simp only [Finset.disjoint_left, Finset.mem_image]
        rintro a ha ⟨b, hb, rfl⟩
        have h1 := (mem_M2set.mp ha).1.2
        have h2 := (mem_M2set.mp hb).1.1
        omega
      have hcv : ∏ x ∈ M2set (k + 1), gaussSum (χ ^ (2 * x)) ψ
          = ∏ x ∈ M2set (k + 1), gaussSum ((χ ^ 2) ^ x) ψ :=
        Finset.prod_congr rfl fun x _ => by rw [hconv x]
      rw [hcv, M2set_succ hk, Finset.prod_union hdisj,
        Finset.prod_image (fun a _ b _ h => by omega)]
      have hshift : ∀ a : ℕ, (χ ^ 2) ^ (a + 2 ^ k) = (χ ^ 2) ^ a := by
        intro a
        rw [pow_add, ← hord2, pow_orderOf_eq_one, mul_one]
      have hsh : ∏ a ∈ M2set k, gaussSum ((χ ^ 2) ^ (a + 2 ^ k)) ψ
          = ∏ a ∈ M2set k, gaussSum ((χ ^ 2) ^ a) ψ :=
        Finset.prod_congr rfl fun a _ => by rw [hshift a]
      rw [hsh]
      exact (pow_two _).symm
    rw [hsplit, ih (χ ^ 2) hord2] at hbig
    -- assemble, aligning `φ` and the exponent
    have hφ : (χ ^ 2) ^ 2 ^ (k - 3) = χ ^ 2 ^ (k + 1 - 3) := by
      rw [← pow_mul]
      congr 1
      rw [← pow_succ']
      congr 1
      omega
    rw [hφ] at hbig
    have hexp : ((q : ℕ) : R) ^ 2 ^ (k - 2)
        * (((q : ℕ) : R) ^ (2 ^ (k - 2) - 1)
          * jacobiSum (χ ^ 2 ^ (k + 1 - 3))
              ((χ ^ 2 ^ (k + 1 - 3)) ^ 3) ^ 2)
        = ((q : ℕ) : R) ^ (2 ^ (k + 1 - 2) - 1)
          * jacobiSum (χ ^ 2 ^ (k + 1 - 3))
              ((χ ^ 2 ^ (k + 1 - 3)) ^ 3) ^ 2 := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      have h1 : (2 : ℕ) ^ (k + 1 - 2) = 2 * 2 ^ (k - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      have h2 : (1 : ℕ) ≤ 2 ^ (k - 2) := Nat.one_le_two_pow
      omega
    rw [hexp] at hbig
    rw [← hbig, pow_two]

end NineTwentyTwo

/-! ### The product identities and Theorem (9.19) -/

section NineNineteen

variable {R : Type _} [CommRing R] [IsDomain R] {q n k : ℕ}
variable [Fact q.Prime]
variable {χ : MulChar (ZMod q) R} {ψ : AddChar (ZMod q) R}
variable {σ : R →+* R} {I : Ideal R}

omit [IsDomain R] in
/-- **The `(n + σ_{−n})β = (3 − σ₃)α + 2Σσ_x⁻¹` identity at the
Gauss-sum-product level** — assembled from the coefficient-wise
`eq_9_13_coeff_neg`. -/
theorem tau_product_identity_M2_neg (hk3 : 3 ≤ k)
    (hord : orderOf χ = 2 ^ k) {nneg : ℕ}
    (hnn : 2 ^ k ∣ n + nneg)
    (hnneg8 : nneg % 8 = 1 ∨ nneg % 8 = 3) (hn2 : ¬ 2 ∣ n) :
    (∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x) ^ n
      * (∏ x ∈ M2set k,
          gaussSum (χ ^ (nneg * minv 2 k x)) ψ ^ αc 3 2 k x)
      * ∏ x ∈ M2set k,
          gaussSum (χ ^ (3 * minv 2 k x)) ψ ^ αc n 2 k x
    = (∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ (3 * αc n 2 k x))
      * (∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ) ^ 2 := by
  have hk : 0 < k := by omega
  rw [Pprod_reindex_M2 hk3 hord (c := nneg) hnneg8 (αc 3 2 k),
    Pprod_reindex_M2 hk3 hord (c := 3) (Or.inr (by norm_num))
      (αc n 2 k),
    ← Finset.prod_pow, ← Finset.prod_pow]
  simp only [← pow_mul]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  have h913 := eq_9_13_coeff_neg (k := k) (n := n) (nneg := nneg)
    (y := y) hk (M2_odd hy) hn2 hnn
  have hcomm : αc 3 2 k y * n = n * αc 3 2 k y := mul_comm _ _
  omega

/-- **The (7.2)-pairing**: `σ_n(u_β)·σ_{−n}(u_β) = χ(−1)·q^T` with
`T = Σβ = 2^(k−2) − 1` (which is odd), via `tau_mul_tau_inv` per
factor and (9.18). -/
theorem sigma_pair_M2 (hk3 : 3 ≤ k) (hord : orderOf χ = 2 ^ k)
    (hψ : ψ.IsPrimitive) {nneg : ℕ} (hnn : 2 ^ k ∣ n + nneg)
    (hn2 : ¬ 2 ∣ n) :
    (∏ x ∈ M2set k, gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x)
      * ∏ x ∈ M2set k,
          gaussSum (χ ^ (nneg * minv 2 k x)) ψ ^ αc 3 2 k x
    = χ (-1) ^ (2 ^ (k - 2) - 1)
      * ((q : ℕ) : R) ^ (2 ^ (k - 2) - 1) := by
  have hk : 0 < k := by omega
  have hpair : ∀ x ∈ M2set k,
      gaussSum (χ ^ (n * minv 2 k x)) ψ
        * gaussSum (χ ^ (nneg * minv 2 k x)) ψ
      = χ (-1) * ((q : ℕ) : R) := by
    intro x hx
    have hxodd := minv_not_dvd Nat.prime_two hk (M2_odd hx)
    have hnxodd : ¬ 2 ∣ n * minv 2 k x := fun hd => by
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
      · exact hn2 h
      · exact hxodd h
    have hne1 : χ ^ (n * minv 2 k x) ≠ 1 := by
      intro h1
      have hd := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at hd
      exact hnxodd (dvd_trans (dvd_pow_self 2 hk.ne') hd)
    have hinv : χ ^ (nneg * minv 2 k x) = (χ ^ (n * minv 2 k x))⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← pow_add]
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      rw [hord]
      rw [show n * minv 2 k x + nneg * minv 2 k x
          = (n + nneg) * minv 2 k x from by ring]
      exact Dvd.dvd.mul_right hnn _
    rw [hinv, tau_mul_tau_inv hne1 hψ]
    congr 1
    rw [MulChar.pow_apply' χ (by
      rintro h0
      rw [h0] at hnxodd
      exact hnxodd (dvd_zero 2)) (-1)]
    exact chi_neg_one_pow_odd χ hnxodd
  calc (∏ x ∈ M2set k, gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x)
        * ∏ x ∈ M2set k,
            gaussSum (χ ^ (nneg * minv 2 k x)) ψ ^ αc 3 2 k x
      = ∏ x ∈ M2set k,
          (gaussSum (χ ^ (n * minv 2 k x)) ψ
            * gaussSum (χ ^ (nneg * minv 2 k x)) ψ) ^ αc 3 2 k x := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun x _ => (mul_pow _ _ _).symm
    _ = ∏ x ∈ M2set k, (χ (-1) * ((q : ℕ) : R)) ^ αc 3 2 k x :=
        Finset.prod_congr rfl fun x hx => by rw [hpair x hx]
    _ = (χ (-1) * ((q : ℕ) : R)) ^ ∑ x ∈ M2set k, αc 3 2 k x :=
        Finset.prod_pow_eq_pow_sum _ _ _
    _ = χ (-1) ^ (2 ^ (k - 2) - 1)
          * ((q : ℕ) : R) ^ (2 ^ (k - 2) - 1) := by
        rw [eq_9_18 hk3, mul_pow]

/-- **The paper's (9.21)**, as the unit-free ring identity
`u_β^n = χ(−1)·j(χ,χ,χ)^α·j(φ,φ³)²·σ(u_β)`. -/
theorem jacobi_tau_identity_M2_neg (hk3 : 3 ≤ k)
    (hord : orderOf χ = 2 ^ k) (hψ : ψ.IsPrimitive)
    (hq0 : ((q : ℕ) : R) ≠ 0) (hn8 : n % 8 = 5 ∨ n % 8 = 7) :
    χ (-1) * ((∏ x ∈ M2set k,
        (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
          * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
          ^ αc n 2 k x)
        * jacobiSum (χ ^ 2 ^ (k - 3)) ((χ ^ 2 ^ (k - 3)) ^ 3) ^ 2)
      * ∏ x ∈ M2set k,
          gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x
    = (∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x) ^ n := by
  have hk : 0 < k := by omega
  have hn2 : ¬ 2 ∣ n := by omega
  -- the representative of `−n` mod `2^k`
  have hNpos : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
  have hnmodpos : n % 2 ^ k ≠ 0 := by
    intro h
    have hd : 2 ^ k ∣ n := Nat.dvd_of_mod_eq_zero h
    exact hn2 (dvd_trans (dvd_pow_self 2 hk.ne') hd)
  set nneg := 2 ^ k - n % 2 ^ k with hnnegdef
  have hnmodlt : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ hNpos
  have hnn : 2 ^ k ∣ n + nneg := by
    refine ⟨n / 2 ^ k + 1, ?_⟩
    have := Nat.div_add_mod n (2 ^ k)
    rw [Nat.mul_add, mul_one]
    omega
  have hnneg8 : nneg % 8 = 1 ∨ nneg % 8 = 3 := by
    obtain ⟨c8, hc8⟩ := eight_dvd_pow hk3
    obtain ⟨d, hd⟩ := hnn
    have hd8 : n + nneg = 8 * (c8 * d) := by
      rw [hd, hc8]
      ring
    omega
  -- the five product objects
  set u := ∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x
    with hu
  set su := ∏ x ∈ M2set k,
    gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x with hsu
  set v := ∏ x ∈ M2set k,
    gaussSum (χ ^ (nneg * minv 2 k x)) ψ ^ αc 3 2 k x with hv
  set P3 := ∏ x ∈ M2set k,
    gaussSum (χ ^ (3 * minv 2 k x)) ψ ^ αc n 2 k x with hP3
  set Q := ∏ x ∈ M2set k,
    gaussSum (χ ^ minv 2 k x) ψ ^ (3 * αc n 2 k x) with hQ
  set Ja := ∏ x ∈ M2set k,
    (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
      * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
      ^ αc n 2 k x with hJa
  set W := ∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ with hW
  set jphi := jacobiSum (χ ^ 2 ^ (k - 3)) ((χ ^ 2 ^ (k - 3)) ^ 3)
    with hjphi
  set E := 2 ^ (k - 2) - 1 with hE
  -- (A): the group-ring identity at the τ-level
  have hAneg : u ^ n * v * P3 = Q * W ^ 2 :=
    tau_product_identity_M2_neg hk3 hord hnn hnneg8 hn2
  -- (B): the (7.2)-pairing
  have hB : su * v = χ (-1) ^ E * ((q : ℕ) : R) ^ E :=
    sigma_pair_M2 hk3 hord hψ hnn hn2
  -- the (9.8)-products: `Ja·P3 = Q`
  have hchne : ∀ x ∈ M2set k, χ ^ (3 * minv 2 k x) ≠ 1 := by
    intro x hx h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hd
    have h2d : (2 : ℕ) ∣ 3 * minv 2 k x :=
      dvd_trans (dvd_pow_self 2 hk.ne') hd
    have hodd := minv_not_dvd Nat.prime_two hk (M2_odd hx)
    omega
  have hA : Ja * P3 = Q := by
    rw [hJa, hP3, hQ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [← mul_pow, mul_comm
      (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
        * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
      (gaussSum (χ ^ (3 * minv 2 k x)) ψ),
      eq_9_8 hk3 hord ψ (minv_not_dvd Nat.prime_two hk (M2_odd hx)),
      ← pow_mul]
  -- (9.22): `W² = q^E · j(φ,φ³)²`
  have hWx : W = ∏ x ∈ M2set k, gaussSum (χ ^ x) ψ := by
    rw [hW]
    refine Finset.prod_nbij' (fun y => minv 2 k y) (fun x => minv 2 k x)
      (fun y hy => minv2_mem hk3 hy) (fun x hx => minv2_mem hk3 hx)
      (fun y hy => minv_invol Nat.prime_two hk (M2_subset_Mset hy))
      (fun x hx => minv_invol Nat.prime_two hk (M2_subset_Mset hx))
      (fun y _ => rfl)
  have h922 : W ^ 2 = ((q : ℕ) : R) ^ E * jphi ^ 2 := by
    rw [hWx, hE, hjphi]
    exact eq_9_22 hψ hq0 hk3 χ hord
  -- nonvanishing for the cancellations
  have hP3ne : P3 ≠ 0 := by
    rw [hP3]
    refine Finset.prod_ne_zero_iff.mpr fun x hx => ?_
    refine pow_ne_zero _ ?_
    refine gaussSum_ne_zero_of_nontrivial ?_ (hchne x hx) hψ
    rw [ZMod.card]
    exact hq0
  have hqE : ((q : ℕ) : R) ^ E ≠ 0 := pow_ne_zero _ hq0
  -- `E` is odd
  have hEodd : ¬ 2 ∣ E := by
    rw [hE]
    have h22 : (2 : ℕ) ^ (k - 2) = 2 * 2 ^ (k - 3) := by
      rw [← pow_succ']
      congr 1
      omega
    have := Nat.one_le_two_pow (n := k - 3)
    omega
  -- assemble: `u^n·χ(−1)^E·q^E·P3 = Ja·q^E·jφ²·su·P3`
  have hmain : u ^ n * (χ (-1) ^ E * ((q : ℕ) : R) ^ E) * P3
      = Ja * (((q : ℕ) : R) ^ E * jphi ^ 2) * su * P3 := by
    calc u ^ n * (χ (-1) ^ E * ((q : ℕ) : R) ^ E) * P3
        = u ^ n * (su * v) * P3 := by rw [hB]
      _ = (u ^ n * v * P3) * su := by ring
      _ = Q * W ^ 2 * su := by rw [hAneg]
      _ = (Ja * P3) * W ^ 2 * su := by rw [hA]
      _ = (Ja * P3) * (((q : ℕ) : R) ^ E * jphi ^ 2) * su := by
          rw [h922]
      _ = Ja * (((q : ℕ) : R) ^ E * jphi ^ 2) * su * P3 := by ring
  have hcancel : u ^ n * χ (-1) ^ E = Ja * jphi ^ 2 * su := by
    have h1 := mul_right_cancel₀ hP3ne hmain
    have h2 : ((q : ℕ) : R) ^ E * (u ^ n * χ (-1) ^ E)
        = ((q : ℕ) : R) ^ E * (Ja * jphi ^ 2 * su) := by
      calc ((q : ℕ) : R) ^ E * (u ^ n * χ (-1) ^ E)
          = u ^ n * (χ (-1) ^ E * ((q : ℕ) : R) ^ E) := by ring
        _ = Ja * (((q : ℕ) : R) ^ E * jphi ^ 2) * su := h1
        _ = ((q : ℕ) : R) ^ E * (Ja * jphi ^ 2 * su) := by ring
    exact mul_left_cancel₀ hqE h2
  -- multiply by `χ(−1)^E` and collapse the sign
  have hsqE : χ (-1) ^ E * χ (-1) ^ E = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, pow_two, chi_neg_one_sq,
      one_pow]
  have hEneg : χ (-1) ^ E = χ (-1) := chi_neg_one_pow_odd χ hEodd
  calc χ (-1) * (Ja * jphi ^ 2) * su
      = χ (-1) ^ E * (Ja * jphi ^ 2 * su) := by rw [hEneg]; ring
    _ = χ (-1) ^ E * (u ^ n * χ (-1) ^ E) := by rw [← hcancel]
    _ = u ^ n * (χ (-1) ^ E * χ (-1) ^ E) := by ring
    _ = u ^ n := by rw [hsqE, mul_one]

/-- **Cohen–Lenstra Theorem (9.19)** (soundness direction,
abstract): for `n ≡ 5, 7 (mod 8)`, if the congruence (9.20) holds —
`∏_{x ∈ M} (j(χ^(x*),χ^(x*))·j(χ^(x*),χ^(2x*)))^(αc x)
  · j(φ,φ³)² ≡ ζ' (mod I)` with `φ = χ^(2^(k−3))` —
then the (7.9)-hypothesis of Theorem (7.8) holds at `p = 2` for
the family `(M2set k, [3·minv(·)/2^k])`, with root `χ(−1)·ζ'`
(Remark (9.24a): a `±ζ'`, primitive iff `ζ'` is).  The
`hβ`-hypothesis for this family is `eq_9_14`; its `hSp` is
`M2_odd`.  Failure of the test proves `n` composite. -/
theorem theorem_9_19 (hk3 : 3 ≤ k)
    (hord : orderOf χ = 2 ^ k) (hψ : ψ.IsPrimitive)
    (hq0 : ((q : ℕ) : R) ≠ 0) (hn8 : n % 8 = 5 ∨ n % 8 = 7)
    (hσχ : ∀ c : ZMod q, σ (χ c) = χ c ^ n)
    (hσψ : ∀ c : ZMod q, σ (ψ c) = ψ c)
    {ζ' : R}
    (h920 : (∏ x ∈ M2set k,
        (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
          * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
          ^ αc n 2 k x)
        * jacobiSum (χ ^ 2 ^ (k - 3)) ((χ ^ 2 ^ (k - 3)) ^ 3) ^ 2
        - ζ' ∈ I) :
    (∏ y ∈ M2set k, gaussSum (χ ^ y) ψ ^ αc 3 2 k (minv 2 k y)) ^ n
      - (χ (-1) * ζ') * σ (∏ y ∈ M2set k,
          gaussSum (χ ^ y) ψ ^ αc 3 2 k (minv 2 k y)) ∈ I := by
  have hk : 0 < k := by omega
  have hn0 : n ≠ 0 := by omega
  have hreidx : (∏ y ∈ M2set k,
        gaussSum (χ ^ y) ψ ^ αc 3 2 k (minv 2 k y))
      = ∏ x ∈ M2set k, gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x := by
    refine Finset.prod_nbij' (fun y => minv 2 k y) (fun x => minv 2 k x)
      (fun y hy => minv2_mem hk3 hy) (fun x hx => minv2_mem hk3 hx)
      (fun y hy => minv_invol Nat.prime_two hk (M2_subset_Mset hy))
      (fun x hx => minv_invol Nat.prime_two hk (M2_subset_Mset hx))
      (fun y hy => ?_)
    rw [minv_invol Nat.prime_two hk (M2_subset_Mset hy)]
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
  have hid := jacobi_tau_identity_M2_neg (ψ := ψ) hk3 hord hψ hq0 hn8
  have heq : (∏ x ∈ M2set k,
        gaussSum (χ ^ minv 2 k x) ψ ^ αc 3 2 k x) ^ n
      - (χ (-1) * ζ') * ∏ x ∈ M2set k,
          gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x
      = ((∏ x ∈ M2set k,
            (jacobiSum (χ ^ minv 2 k x) (χ ^ minv 2 k x)
              * jacobiSum (χ ^ minv 2 k x) (χ ^ (2 * minv 2 k x)))
              ^ αc n 2 k x)
          * jacobiSum (χ ^ 2 ^ (k - 3)) ((χ ^ 2 ^ (k - 3)) ^ 3) ^ 2
          - ζ')
        * (χ (-1) * ∏ x ∈ M2set k,
            gaussSum (χ ^ (n * minv 2 k x)) ψ ^ αc 3 2 k x) := by
    rw [← hid]
    ring
  rw [heq]
  exact Ideal.mul_mem_right _ I h920

end NineNineteen

end CL

end Azurite

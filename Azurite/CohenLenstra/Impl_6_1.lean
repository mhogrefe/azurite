/-
  **Implementation paper, §6 (continued): the Karatsuba identity,
  the inverse of `σ_x` (6.1), the determination of `h` (6.2), and
  the `λ`-route of (1.3)(i2a).**

  **The Appendix identity.**  All Appendix formulae come from
  recursive use of

    `(A₁X + A₀)(B₁X + B₀) = A₁B₁X² + ((A₁+A₀)(B₁+B₀) − A₁B₁ − A₀B₀)X + A₀B₀`

  (`karatsuba_identity`; three multiplications instead of four — the
  scheme of Remark (4.9)), combined with trial and error; the authors
  suspect the `p = 7` squaring (14 multiplications) can drop to 12 as
  for `p^k = 9`, and that the `p = 11` squaring count is too high.

  **(6.1) Computation of `σ_x⁻¹`.**  For `a = (a_i)_{i<m}` (with
  `a_i = 0` for `i ≥ m`) put `b_i = a_{xi mod p^k}` for `i < m`, then
  for `i = m, …, p^k − 1` and `1 ≤ j < p` replace `b_{i − jp^(k−1)}`
  by `b_{i − jp^(k−1)} − a_{xi mod p^k}`.  Then `σ_x(b) = a`.  Each
  position `t < m` receives exactly one correction, from
  `i = m + (t mod p^(k−1))`, so the output is
  `b_t = a_{xt mod p^k} − a_{x(m + t mod p^(k−1)) mod p^k}`
  (`sigmaInvCoeff`), and the certificate is `sigmaInv_spec`:
  `Σ_{t<m} b_t z^(xt) = Σ_{i<m} a_i z^i` for any root `z` of
  `Φ_{p^k}` in any commutative ring — proved by folding the
  corrections back into a sum over `i < p^k` (the vanishing
  `Σ_{l<p} z^(c + xl·p^(k−1)) = 0`, `sum_pow_root_cyclotomic_eq_zero`),
  reducing exponents mod `p^k`, and reindexing `i ↦ xi mod p^k`
  (`sum_range_mul_mod`).  In the model, `sigmaN_sigmaInv` states it
  as `σ_x(b) = a` for `σ_x = sigmaN`.

  The small powers of (1.3)(i1) are computed by repeated
  multiplication inside the `j`-loop; the `u`-th power of (i2b) by
  the `2^m`-ary method (3.6) with the ring operations of §6 (prose).

  **(6.2) Determination of `h`.**  Given `a = (a_i)_{i<m}`, find
  `h < p^k` with `a = ζ^h` if it exists: if `a` is the unit vector at
  `l < m`, then `h = l` (`unitVec_sum`); if `a_{l + jp^(k−1)} ≡ −1`
  for `0 ≤ j < p − 1` (some `l < p^(k−1)`) and all other `a_i = 0`,
  then — **erratum**: the paper says `h = l`, but
  `−Σ_{j<p−1} ζ^(l + jp^(k−1)) = ζ^(l + (p−1)p^(k−1))`, so
  `h = l + m` (`negPattern_sum`; e.g. `p^k = 4`: the vector `(−1, 0)`
  is `ζ² = −1`, not `ζ⁰`).  Since `h` feeds the `λ_p`-test (i3)
  through `h mod p`, and `m ≡ −1 (mod p)` when `k = 1`, the misprint
  would matter in an implementation.  The computable search
  `findH` uses the corrected value, and `findH_spec` certifies
  `a = z^h` whenever it returns `some h`.  Otherwise `h` does not
  exist and `n` is composite — the completeness half, which for
  prime `n` follows from uniqueness of coordinates in the power
  basis (`cycModN_dim`); deferred with the other completeness halves.

  **(1.3)(i2a), the `λ`-route.**  When `flag_{p^k}` holds,
  `λ(a) = Σ_{i<m} a_i β^i ∈ ℤ/nℤ` is computed by Horner's scheme or
  from the stored powers `β^i` of (1.3)(e) — the ring-hom identity
  `lambdaHom_sum`; `λ(j₀)^u` by (3.6) in `ℤ/nℤ`; and `h` by comparing
  `λ(j₀)^u·λ(j_v)` with `β^i`, `i < p^k`, modulo `n` — equality after
  `λ` is congruence modulo `𝔪 = ker λ` (`sub_mem_mKernel_iff`), which
  is exactly the (10.3)-form of the test.
-/
import Azurite.CohenLenstra.Impl_6
import Azurite.CohenLenstra.Method_10_2

namespace Azurite

namespace CL

open Polynomial Finset

/-- **The Appendix identity** (Karatsuba): three multiplications
`A₁B₁`, `A₀B₀`, `(A₁+A₀)(B₁+B₀)` instead of four. -/
theorem karatsuba_identity {R : Type _} [CommRing R] (A₁ A₀ B₁ B₀ X : R) :
    (A₁ * X + A₀) * (B₁ * X + B₀)
      = A₁ * B₁ * X ^ 2 + ((A₁ + A₀) * (B₁ + B₀) - A₁ * B₁ - A₀ * B₀) * X
        + A₀ * B₀ := by
  ring

/-! ### Support: sums over `range` -/

/-- Splitting `range (q·P)` as `r + l·P` with `r < P`, `l < q`. -/
theorem sum_range_mul_eq_double {M : Type _} [AddCommMonoid M] (P : ℕ) (g : ℕ → M) :
    ∀ q : ℕ, ∑ i ∈ range (q * P), g i = ∑ r ∈ range P, ∑ l ∈ range q, g (r + l * P)
  | 0 => by simp
  | q + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul_eq_double P g q,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_range_succ, add_comm (q * P) r]

/-- Reindexing `range N` by `i ↦ xi mod N` for `x` coprime to `N`. -/
theorem sum_range_mul_mod {M : Type _} [AddCommMonoid M] {x N : ℕ} (hN : 0 < N)
    (hx : Nat.Coprime x N) (f : ℕ → M) :
    ∑ i ∈ range N, f (x * i % N) = ∑ j ∈ range N, f j := by
  rcases Nat.lt_or_ge N 2 with h | h
  · have : N = 1 := by omega
    subst this
    simp
  · obtain ⟨y, -, hy⟩ := Nat.exists_mul_mod_eq_one_of_coprime hx h
    refine Finset.sum_nbij' (fun i => x * i % N) (fun j => y * j % N) ?_ ?_ ?_ ?_ ?_
    · intro i _
      exact mem_range.mpr (Nat.mod_lt _ hN)
    · intro j _
      exact mem_range.mpr (Nat.mod_lt _ hN)
    · intro i hi
      have hi' := mem_range.mp hi
      show y * (x * i % N) % N = i
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, mul_comm y x,
        Nat.mul_mod, hy, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hi']
    · intro j hj
      have hj' := mem_range.mp hj
      show x * (y * j % N) % N = j
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, hy,
        one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hj']
    · intro i _
      rfl

/-! ### Roots of `Φ_{p^k}` -/

/-- A root of `Φ_N` is an `N`-th root of unity. -/
theorem pow_eq_one_of_cyclotomic {R : Type _} [CommRing R] {N : ℕ} {z : R}
    (hz : eval₂ (Int.castRingHom R) z (cyclotomic N ℤ) = 0) : z ^ N = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one N ℤ
  have h := congrArg (eval₂ (Int.castRingHom R) z) hg
  rw [eval₂_sub, eval₂_X_pow, eval₂_one, eval₂_mul, hz, zero_mul] at h
  exact sub_eq_zero.mp h

/-- **The vanishing identity**: for a root `z` of `Φ_{p^k}` and
`p ∤ x`, `Σ_{l<p} z^(c + xl·p^(k−1)) = 0` — the `p`-th roots of unity
`z^(xl·p^(k−1))` sum to zero. -/
theorem sum_pow_root_cyclotomic_eq_zero {R : Type _} [CommRing R] {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) {z : R}
    (hz : eval₂ (Int.castRingHom R) z (cyclotomic (p ^ k) ℤ) = 0)
    {x : ℕ} (hx : ¬ p ∣ x) (c : ℕ) :
    ∑ l ∈ range p, z ^ (c + x * l * p ^ (k - 1)) = 0 := by
  have hz1 : z ^ p ^ k = 1 := pow_eq_one_of_cyclotomic hz
  have hΦ : ∑ i ∈ range p, z ^ (i * p ^ (k - 1)) = 0 := by
    rw [cyclotomic_prime_pow_eq_sum hp hk, eval₂_finsetSum] at hz
    simpa only [eval₂_X_pow] using hz
  have hω : (z ^ p ^ (k - 1)) ^ p = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hk]
    exact hz1
  have hcop : Nat.Coprime x p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hx).symm
  have hre : ∀ l, z ^ (c + x * l * p ^ (k - 1))
      = z ^ c * (z ^ p ^ (k - 1)) ^ (x * l % p) := by
    intro l
    rw [pow_add, mul_comm (x * l) (p ^ (k - 1)), pow_mul]
    congr 1
    exact pow_eq_pow_of_modEq hω (Nat.mod_modEq _ _).symm
  simp_rw [hre]
  rw [← Finset.mul_sum]
  have hre2 : ∑ l ∈ range p, (z ^ p ^ (k - 1)) ^ (x * l % p)
      = ∑ j ∈ range p, (z ^ p ^ (k - 1)) ^ j :=
    sum_range_mul_mod hp.pos hcop _
  have hzero : ∑ j ∈ range p, (z ^ p ^ (k - 1)) ^ j = 0 := by
    rw [← hΦ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_comm]
  rw [hre2, hzero, mul_zero]

/-! ### (6.1) The inverse of `σ_x` -/

/-- **The (6.1) output**: `b_t = a_{xt mod p^k} − a_{x(m + t mod p^(k−1)) mod p^k}`
with `m = (p−1)p^(k−1)`. -/
def sigmaInvCoeff {R : Type _} [Sub R] (p k x : ℕ) (a : ℕ → R) (i : ℕ) : R :=
  a (x * i % p ^ k) - a (x * ((p - 1) * p ^ (k - 1) + i % p ^ (k - 1)) % p ^ k)

/-- **(6.1) is correct**: `σ_x(b) = a`, i.e. `Σ_t b_t z^(xt) = Σ_i a_i z^i`,
for any root `z` of `Φ_{p^k}` and `a` vanishing from `m` on. -/
theorem sigmaInv_spec {R : Type _} [CommRing R] {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {z : R} (hz : eval₂ (Int.castRingHom R) z (cyclotomic (p ^ k) ℤ) = 0)
    {x : ℕ} (hx : ¬ p ∣ x) (a : ℕ → R)
    (ha : ∀ i, (p - 1) * p ^ (k - 1) ≤ i → a i = 0) :
    ∑ i ∈ range ((p - 1) * p ^ (k - 1)), sigmaInvCoeff p k x a i * z ^ (x * i)
      = ∑ i ∈ range ((p - 1) * p ^ (k - 1)), a i * z ^ i := by
  have hz1 : z ^ p ^ k = 1 := pow_eq_one_of_cyclotomic hz
  have hzN : ∀ e, z ^ e = z ^ (e % p ^ k) := fun e =>
    pow_eq_pow_of_modEq hz1 (Nat.mod_modEq e _).symm
  have hcop : Nat.Coprime x (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hx).symm
  have hN : p ^ k = (p - 1) * p ^ (k - 1) + p ^ (k - 1) := by
    have h1 : p ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hk]
    have h2 : (p - 1) * p ^ (k - 1) = p * p ^ (k - 1) - p ^ (k - 1) :=
      Nat.sub_one_mul _ _
    have h3 : p ^ (k - 1) ≤ p * p ^ (k - 1) := Nat.le_mul_of_pos_left _ hp.pos
    omega
  -- the vanishing identity, split at `p − 1`
  have hsum : ∀ r, ∑ l ∈ range (p - 1), z ^ (x * (r + l * p ^ (k - 1)))
      = - z ^ (x * ((p - 1) * p ^ (k - 1) + r)) := by
    intro r
    have hvan := sum_pow_root_cyclotomic_eq_zero hp hk hz hx (x * r)
    have hsplit := Finset.sum_range_succ
      (fun l => z ^ (x * r + x * l * p ^ (k - 1))) (p - 1)
    rw [Nat.sub_add_cancel hp.one_lt.le] at hsplit
    have h1 : ∀ l, x * (r + l * p ^ (k - 1)) = x * r + x * l * p ^ (k - 1) :=
      fun l => by ring
    have h2 : x * ((p - 1) * p ^ (k - 1) + r) = x * r + x * (p - 1) * p ^ (k - 1) := by
      ring
    simp_rw [h1]
    rw [h2]
    linear_combination hvan - hsplit
  -- the correction sum, folded
  have hS2 : ∑ i ∈ range ((p - 1) * p ^ (k - 1)),
        a (x * ((p - 1) * p ^ (k - 1) + i % p ^ (k - 1)) % p ^ k) * z ^ (x * i)
      = - ∑ r ∈ range (p ^ (k - 1)),
          a (x * ((p - 1) * p ^ (k - 1) + r) % p ^ k)
            * z ^ (x * ((p - 1) * p ^ (k - 1) + r)) := by
    rw [sum_range_mul_eq_double, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := mem_range.mp hr
    have hmod : ∀ l, (r + l * p ^ (k - 1)) % p ^ (k - 1) = r := fun l => by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr']
    simp_rw [hmod]
    rw [← Finset.mul_sum, hsum r, mul_neg]
  calc ∑ i ∈ range ((p - 1) * p ^ (k - 1)), sigmaInvCoeff p k x a i * z ^ (x * i)
      = ∑ i ∈ range ((p - 1) * p ^ (k - 1)), a (x * i % p ^ k) * z ^ (x * i)
        - ∑ i ∈ range ((p - 1) * p ^ (k - 1)),
            a (x * ((p - 1) * p ^ (k - 1) + i % p ^ (k - 1)) % p ^ k) * z ^ (x * i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sigmaInvCoeff, sub_mul]
    _ = ∑ i ∈ range ((p - 1) * p ^ (k - 1)), a (x * i % p ^ k) * z ^ (x * i)
        + ∑ r ∈ range (p ^ (k - 1)),
            a (x * ((p - 1) * p ^ (k - 1) + r) % p ^ k)
              * z ^ (x * ((p - 1) * p ^ (k - 1) + r)) := by
        rw [hS2, sub_neg_eq_add]
    _ = ∑ i ∈ range ((p - 1) * p ^ (k - 1) + p ^ (k - 1)),
          a (x * i % p ^ k) * z ^ (x * i) :=
        (Finset.sum_range_add _ _ _).symm
    _ = ∑ i ∈ range (p ^ k), a (x * i % p ^ k) * z ^ (x * i % p ^ k) := by
        rw [← hN]
        exact Finset.sum_congr rfl fun i _ => by rw [← hzN]
    _ = ∑ j ∈ range (p ^ k), a j * z ^ j :=
        sum_range_mul_mod (pow_pos hp.pos k) hcop (fun j => a j * z ^ j)
    _ = ∑ j ∈ range ((p - 1) * p ^ (k - 1)), a j * z ^ j
        + ∑ r ∈ range (p ^ (k - 1)),
            a ((p - 1) * p ^ (k - 1) + r) * z ^ ((p - 1) * p ^ (k - 1) + r) := by
        rw [hN]
        exact Finset.sum_range_add _ _ _
    _ = ∑ j ∈ range ((p - 1) * p ^ (k - 1)), a j * z ^ j := by
        have h0 : ∑ r ∈ range (p ^ (k - 1)),
            a ((p - 1) * p ^ (k - 1) + r) * z ^ ((p - 1) * p ^ (k - 1) + r) = 0 :=
          Finset.sum_eq_zero fun r _ => by
            rw [ha _ (Nat.le_add_right _ _), zero_mul]
        rw [h0, add_zero]

/-- **(6.1) in the model**: for `b` the (6.1) output, `σ_x(b) = a` in
`ℤ[ζ_{p^k}]`. -/
theorem sigmaN_sigmaInv {p k x : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hcop : Nat.Coprime x (p ^ k)) (a : ℕ → ℤ)
    (ha : ∀ i, (p - 1) * p ^ (k - 1) ≤ i → a i = 0) :
    sigmaN (pow_pos hp.pos k) hcop
        (∑ i ∈ range ((p - 1) * p ^ (k - 1)),
          ((sigmaInvCoeff p k x a i : ℤ) : CP.CycM (p ^ k)) * CP.zetaM (p ^ k) ^ i)
      = ∑ i ∈ range ((p - 1) * p ^ (k - 1)),
          (a i : CP.CycM (p ^ k)) * CP.zetaM (p ^ k) ^ i := by
  have hx : ¬ p ∣ x := by
    intro h
    have h1 := Nat.Coprime.coprime_dvd_left h hcop
    rw [Nat.coprime_pow_right_iff hk] at h1
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1 dvd_rfl)
  have hz : eval₂ (Int.castRingHom (CP.CycM (p ^ k))) (CP.zetaM (p ^ k))
      (cyclotomic (p ^ k) ℤ) = 0 := by
    rw [RingHom.ext_int (Int.castRingHom _) (AdjoinRoot.of _)]
    exact AdjoinRoot.eval₂_root _
  simp only [map_sum, map_mul, map_intCast, map_pow, sigmaN_zetaM, ← pow_mul]
  have hcast : ∀ i, ((sigmaInvCoeff p k x a i : ℤ) : CP.CycM (p ^ k))
      = sigmaInvCoeff p k x (fun j => (a j : CP.CycM (p ^ k))) i := fun i => by
    simp only [sigmaInvCoeff, Int.cast_sub]
  simp_rw [hcast]
  exact sigmaInv_spec hp hk hz hx _ (fun i hi => by rw [ha i hi, Int.cast_zero])

/-! ### (6.2) Determination of `h` -/

/-- **(6.2), first case**: the unit vector at `l < m` is `z^l`. -/
theorem unitVec_sum {R : Type _} [CommRing R] (z : R) {m l : ℕ} (hl : l < m) :
    ∑ i ∈ range m, (if i = l then (1 : R) else 0) * z ^ i = z ^ l := by
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hbl
    simp [hbl]
  · intro h
    exact absurd (mem_range.mpr hl) h

/-- **(6.2), second case (corrected)**: `−1` at the positions
`l + j·p^(k−1)`, `j < p − 1`, zero elsewhere, is `z^(l + (p−1)p^(k−1))`
— **not** `z^l` as printed. -/
theorem negPattern_sum {R : Type _} [CommRing R] {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {z : R} (hz : eval₂ (Int.castRingHom R) z (cyclotomic (p ^ k) ℤ) = 0)
    {l : ℕ} (hl : l < p ^ (k - 1)) :
    ∑ i ∈ range ((p - 1) * p ^ (k - 1)),
        (if i % p ^ (k - 1) = l then (-1 : R) else 0) * z ^ i
      = z ^ (l + (p - 1) * p ^ (k - 1)) := by
  rw [sum_range_mul_eq_double]
  have hmod : ∀ r j, (r + j * p ^ (k - 1)) % p ^ (k - 1) = r % p ^ (k - 1) :=
    fun r j => Nat.add_mul_mod_self_right _ _ _
  simp_rw [hmod]
  rw [Finset.sum_eq_single l]
  · rw [Nat.mod_eq_of_lt hl]
    simp only [if_true, neg_one_mul, Finset.sum_neg_distrib]
    have hvan := sum_pow_root_cyclotomic_eq_zero hp hk hz hp.not_dvd_one l
    have hsplit := Finset.sum_range_succ
      (fun j => z ^ (l + 1 * j * p ^ (k - 1))) (p - 1)
    rw [Nat.sub_add_cancel hp.one_lt.le] at hsplit
    simp only [one_mul] at hvan hsplit
    linear_combination hsplit - hvan
  · intro r hr hrl
    rw [Nat.mod_eq_of_lt (mem_range.mp hr), if_neg hrl]
    simp
  · intro h
    exact absurd (mem_range.mpr hl) h

/-- **(6.2) as a computable search** (corrected second case): returns
`some h` with `a = ζ^h`, or `none`. -/
def findH {R : Type _} [CommRing R] [DecidableEq R] (p k : ℕ) (a : ℕ → R) : Option ℕ :=
  match (List.range ((p - 1) * p ^ (k - 1))).find?
      (fun l => (List.range ((p - 1) * p ^ (k - 1))).all
        fun i => decide (a i = if i = l then 1 else 0)) with
  | some l => some l
  | none =>
    ((List.range (p ^ (k - 1))).find?
      (fun l => (List.range ((p - 1) * p ^ (k - 1))).all
        fun i => decide (a i = if i % p ^ (k - 1) = l then -1 else 0))).map
      (fun l => l + (p - 1) * p ^ (k - 1))

/-- **(6.2) is sound**: `findH p k a = some h` ⟹ `Σ_i a_i z^i = z^h`
for any root `z` of `Φ_{p^k}`. -/
theorem findH_spec {R : Type _} [CommRing R] [DecidableEq R] {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) {z : R}
    (hz : eval₂ (Int.castRingHom R) z (cyclotomic (p ^ k) ℤ) = 0)
    (a : ℕ → R) {h : ℕ} (hfind : findH p k a = some h) :
    ∑ i ∈ range ((p - 1) * p ^ (k - 1)), a i * z ^ i = z ^ h := by
  unfold findH at hfind
  split at hfind
  · rename_i l hl
    obtain rfl : l = h := Option.some.inj hfind
    have hprop0 := List.find?_some hl
    have hprop := List.all_eq_true.mp hprop0
    have hlm : l < (p - 1) * p ^ (k - 1) :=
      List.mem_range.mp (List.mem_of_find?_eq_some hl)
    have hsum : ∑ i ∈ range ((p - 1) * p ^ (k - 1)), a i * z ^ i
        = ∑ i ∈ range ((p - 1) * p ^ (k - 1)),
            (if i = l then (1 : R) else 0) * z ^ i :=
      Finset.sum_congr rfl fun i hi => by
        rw [of_decide_eq_true (hprop i (List.mem_range.mpr (mem_range.mp hi)))]
    rw [hsum]
    exact unitVec_sum z hlm
  · rw [Option.map_eq_some_iff] at hfind
    obtain ⟨l, hl, rfl⟩ := hfind
    have hprop0 := List.find?_some hl
    have hprop := List.all_eq_true.mp hprop0
    have hlP : l < p ^ (k - 1) :=
      List.mem_range.mp (List.mem_of_find?_eq_some hl)
    have hsum : ∑ i ∈ range ((p - 1) * p ^ (k - 1)), a i * z ^ i
        = ∑ i ∈ range ((p - 1) * p ^ (k - 1)),
            (if i % p ^ (k - 1) = l then (-1 : R) else 0) * z ^ i :=
      Finset.sum_congr rfl fun i hi => by
        rw [of_decide_eq_true (hprop i (List.mem_range.mpr (mem_range.mp hi)))]
    rw [hsum]
    exact negPattern_sum hp hk hz hlP

/-- **(6.2) is sound, mapped form**: the coordinates `a : ℕ → R` may live in
the coefficient ring while the sum is taken in `S` along `φ : R →+* S`. -/
theorem findH_spec_map {R S : Type _} [CommRing R] [DecidableEq R] [CommRing S]
    (φ : R →+* S) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) {z : S}
    (hz : eval₂ (Int.castRingHom S) z (cyclotomic (p ^ k) ℤ) = 0)
    (a : ℕ → R) {h : ℕ} (hfind : findH p k a = some h) :
    ∑ i ∈ range ((p - 1) * p ^ (k - 1)), φ (a i) * z ^ i = z ^ h := by
  unfold findH at hfind
  split at hfind
  · rename_i l hl
    obtain rfl : l = h := Option.some.inj hfind
    have hprop0 := List.find?_some hl
    have hprop := List.all_eq_true.mp hprop0
    have hlm : l < (p - 1) * p ^ (k - 1) :=
      List.mem_range.mp (List.mem_of_find?_eq_some hl)
    have hsum : ∑ i ∈ range ((p - 1) * p ^ (k - 1)), φ (a i) * z ^ i
        = ∑ i ∈ range ((p - 1) * p ^ (k - 1)),
            (if i = l then (1 : S) else 0) * z ^ i :=
      Finset.sum_congr rfl fun i hi => by
        rw [of_decide_eq_true (hprop i (List.mem_range.mpr (mem_range.mp hi)))]
        split_ifs <;> simp
    rw [hsum]
    exact unitVec_sum z hlm
  · rw [Option.map_eq_some_iff] at hfind
    obtain ⟨l, hl, rfl⟩ := hfind
    have hprop0 := List.find?_some hl
    have hprop := List.all_eq_true.mp hprop0
    have hlP : l < p ^ (k - 1) :=
      List.mem_range.mp (List.mem_of_find?_eq_some hl)
    have hsum : ∑ i ∈ range ((p - 1) * p ^ (k - 1)), φ (a i) * z ^ i
        = ∑ i ∈ range ((p - 1) * p ^ (k - 1)),
            (if i % p ^ (k - 1) = l then (-1 : S) else 0) * z ^ i :=
      Finset.sum_congr rfl fun i hi => by
        rw [of_decide_eq_true (hprop i (List.mem_range.mpr (mem_range.mp hi)))]
        split_ifs <;> simp
    rw [hsum]
    exact negPattern_sum hp hk hz hlP

-- `p^k = 4`, `m = 2`: `(−1, 0)` is `ζ² = −1`, so `h = 2` (the paper's `h = l` would give `0`);
-- `(0, 1)` is `ζ`; `(1, 1)` is no power of `ζ`.
#guard findH (R := ℤ) 2 2 (fun i => if i = 0 then -1 else 0) = some 2
#guard findH (R := ℤ) 2 2 (fun i => if i = 1 then 1 else 0) = some 1
#guard findH (R := ℤ) 2 2 (fun i => if i < 2 then 1 else 0) = none
-- `p^k = 9`, `m = 6`: `−1` at positions `1, 4` is `ζ^(1 + 6) = ζ^7`.
#guard findH (R := ℤ) 3 2 (fun i => if i = 1 ∨ i = 4 then -1 else 0) = some 7

/-! ### (1.3)(i2a): the `λ`-route -/

/-- **`λ` on coordinate vectors**: `λ(Σ a_i ζ^i) = Σ a_i β^i` — the
Horner/stored-powers evaluation of (1.3)(i2a). -/
theorem lambdaHom_sum {F : Type _} [CommRing F] {m : ℕ} {z : F}
    (hz : eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0) (a : ℕ → ℤ) (M : ℕ) :
    lambdaHom m hz (∑ i ∈ range M, (a i : CP.CycM m) * CP.zetaM m ^ i)
      = ∑ i ∈ range M, (a i : F) * z ^ i := by
  simp only [map_sum, map_mul, map_intCast, map_pow, lambdaHom_zetaM]

/-- **Equality after `λ` is congruence modulo `𝔪 = ker λ`**: the
(i2a) comparison `λ(j₀)^u·λ(j_v) = β^h` in `ℤ/nℤ` is the (10.3)-test
`j₀^u·j_v ≡ ζ^h (mod 𝔪)`. -/
theorem sub_mem_mKernel_iff {F : Type _} [CommRing F] {m : ℕ} {z : F}
    (hz : eval₂ (Int.castRingHom F) z (cyclotomic m ℤ) = 0) (u v : CP.CycM m) :
    u - v ∈ mKernel m hz ↔ lambdaHom m hz u = lambdaHom m hz v :=
  RingHom.sub_mem_ker_iff (lambdaHom m hz)

end CL

end Azurite

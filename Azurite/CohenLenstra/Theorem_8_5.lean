/-
  **Cohen–Lenstra Theorem (8.5): the Jacobi-sum test implies (7.9).**

  The paper defines, for `p ≥ 3` and integers `a, b` satisfying
  (8.6), the group-ring elements

    `α = Σ_{x ∈ M} [nx/p^k]·σ_x⁻¹`,
    `β = Σ_{x ∈ M} ([((a+b)x)/p^k] − [ax/p^k] − [bx/p^k])·σ_x⁻¹`

  over the index set `M = {x : 1 ≤ x ≤ p^k, p ∤ x}` of (8.4), and
  proves: if `j(χ^a, χ^b)^α ≡ ζ (mod 𝔪)` for some `ζ ∈ U_{p^k}`
  ((8.8), a congruence entirely inside `ℤ[ζ_{p^k}]`), then (7.9)
  holds with the same `ζ` and with `β, 𝔫 = 𝔪B` — so the whole
  Gauss-sum machinery of §7 is driven by a Jacobi-sum test.

  Our rendering keeps the established Galois-free style.  With
  `x* = minv x` the mod-`p^k` inverse and `mAct c x = (c·x) mod p^k`:

  * `j(χ^a,χ^b)^α = ∏_{x ∈ M} j(χ^(a·x*), χ^(b·x*))^(αc x)` — the
    coefficients of `α` are nonnegative (Remark (8.9a)), so this is
    an honest product in the ring;
  * `u_β = τ(χ)^β = ∏_{x ∈ M} τ(χ^(x*))^(βc x)`, which after the
    involution `x ↦ minv x` is the family `(S, ν) = (M, βc ∘ minv)`
    consumed by Theorems (7.8) and (7.19);
  * the paper's chain
    `j^α = τ^((σ_a+σ_b−σ_(a+b))α) = τ^((n−σ_n)β)` becomes the
    unit-free ring identity `j^α · σ(u_β) = u_β^n`, proved from the
    per-`x` instances of (8.2) and the coefficient-wise form of the
    group-ring identity of Lemma (8.12),

      `n·βc(y) + αc(mAct (a+b) y)
         = βc(mAct n y) + αc(mAct a y) + αc(mAct b y)`,

    which is elementary floor arithmetic (`exponent_identity`);
  * Theorem (8.5) then reads: the congruence (8.8),
    `∏ j^(αc) − ζ^(e₀) ∈ I`, implies the hypothesis (7.9) of
    Theorems (7.8)/(7.19) for the family `(M, βc ∘ minv)`, with the
    same `ζ^(e₀)` (Remark (8.9b)) — multiply (8.8) by `σ(u_β)` and
    rewrite by the identity.

  The condition (8.6) on `(a, b)` is not needed for any of this; it
  enters only in the second half of Lemma (8.12) (condition (7.6)
  for `β`, the hypothesis `hβ` of the §7 theorems), whose proof the
  paper gives separately.  The extension `𝔪 ↦ 𝔫 = 𝔪B` with (8.10)
  is model-side bookkeeping, deferred with (7.7) to the §10
  discussion.
-/
import Azurite.CohenLenstra.Equation_8_2
import Azurite.CohenLenstra.Theorem_7_8

namespace Azurite

namespace CL

open Finset

/-! ### The index set `M`, inverses, and the coefficient functions -/

/-- **The paper's (8.4)**: `M = {x : 1 ≤ x < p^k, p ∤ x}` (the
representative `p^k` itself is divisible by `p`, so the paper's
`1 ≤ x ≤ p^k` gives the same set). -/
def Mset (p k : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (p ^ k)).filter (fun x => ¬ p ∣ x)

/-- The mod-`p^k` inverse, as a representative in `[0, p^k)`. -/
def minv (p k x : ℕ) : ℕ := ((x : ZMod (p ^ k))⁻¹).val

/-- Multiplication action on representatives: `(c·x) mod p^k`. -/
def mAct (p k c x : ℕ) : ℕ := ((c * x : ℕ) : ZMod (p ^ k)).val

/-- The coefficients of the paper's `α`: `αc x = [n·x / p^k]`. -/
def αc (n p k x : ℕ) : ℕ := n * x / p ^ k

/-- The coefficients of the paper's `β`:
`βc x = [(a+b)x/p^k] − [ax/p^k] − [bx/p^k]` (a value in `{0, 1}`;
in particular the truncated subtraction is exact). -/
def βc (a b p k x : ℕ) : ℕ :=
  (a + b) * x / p ^ k - a * x / p ^ k - b * x / p ^ k

section Arithmetic

variable {p k : ℕ} (hp : p.Prime) (hk : 0 < k)

theorem mem_Mset {x : ℕ} :
    x ∈ Mset p k ↔ (1 ≤ x ∧ x < p ^ k) ∧ ¬ p ∣ x := by
  simp [Mset, Finset.mem_filter, Finset.mem_Ico]

include hk in
theorem dvd_of_dvd_mod {y : ℕ} (hd : p ∣ y % p ^ k) : p ∣ y := by
  obtain ⟨w, hw⟩ := hd
  obtain ⟨v, hv⟩ := dvd_pow_self p hk.ne'
  refine ⟨v * (y / p ^ k) + w, ?_⟩
  calc y = p ^ k * (y / p ^ k) + y % p ^ k := (Nat.div_add_mod y _).symm
    _ = p * (v * (y / p ^ k) + w) := by rw [hw, hv]; ring

include hp hk in
theorem mAct_mem {c x : ℕ} (hc : ¬ p ∣ c) (hx : x ∈ Mset p k) :
    mAct p k c x ∈ Mset p k := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  obtain ⟨⟨hx1, hxlt⟩, hxp⟩ := mem_Mset.mp hx
  have hval : mAct p k c x = (c * x) % p ^ k := by
    rw [mAct]
    exact ZMod.val_natCast (n := p ^ k) (c * x)
  have hpcx : ¬ p ∣ c * x := fun hd => by
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hc h
    · exact hxp h
  have hmodp : ¬ p ∣ (c * x) % p ^ k := fun hd =>
    hpcx (dvd_of_dvd_mod hk hd)
  refine mem_Mset.mpr ⟨⟨?_, ?_⟩, ?_⟩
  · -- nonzero, else `p ∣ 0 = (c·x) % p^k`
    rw [hval]
    rcases Nat.eq_zero_or_pos ((c * x) % p ^ k) with h0 | h1
    · exact absurd (h0 ▸ dvd_zero p) hmodp
    · exact h1
  · rw [hval]
    exact Nat.mod_lt _ (pow_pos hp.pos k)
  · rw [hval]
    exact hmodp

include hp in
theorem minv_spec {x : ℕ} (hx : ¬ p ∣ x) :
    x * minv p k x ≡ 1 [MOD p ^ k] := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hco : x.Coprime (p ^ k) :=
    Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hx))
  have hunit : IsUnit ((x : ℕ) : ZMod (p ^ k)) :=
    (ZMod.isUnit_iff_coprime x (p ^ k)).mpr hco
  have h1 : ((x : ℕ) : ZMod (p ^ k)) * ((x : ℕ) : ZMod (p ^ k))⁻¹
      = 1 := ZMod.mul_inv_of_unit _ hunit
  have h2 : ((x * minv p k x : ℕ) : ZMod (p ^ k))
      = ((1 : ℕ) : ZMod (p ^ k)) := by
    push_cast
    rw [minv, ZMod.natCast_val, ZMod.cast_id]
    exact_mod_cast h1
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h2

include hp hk in
theorem minv_not_dvd {x : ℕ} (hx : ¬ p ∣ x) : ¬ p ∣ minv p k x := by
  intro hd
  have hspec := minv_spec (k := k) hp hx
  have hplt : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
  have hxm1 : 1 ≤ x * minv p k x := by
    by_contra h0
    have h00 : x * minv p k x = 0 := by omega
    rw [h00] at hspec
    have hdd := (Nat.modEq_iff_dvd' (by omega)).mp hspec
    have := Nat.le_of_dvd (by omega) hdd
    omega
  have hdvd1 : p ^ k ∣ x * minv p k x - 1 :=
    (Nat.modEq_iff_dvd' hxm1).mp hspec.symm
  obtain ⟨w, hw⟩ : p ∣ x * minv p k x := Dvd.dvd.mul_left hd x
  obtain ⟨v, hv⟩ := hdvd1
  obtain ⟨u, hu⟩ := dvd_pow_self p hk.ne'
  have hv' : x * minv p k x - 1 = p * (u * v) := by
    rw [hv, hu]
    ring
  have h1 : 1 + p * (u * v) = p * w := by omega
  have hp1 : p ∣ 1 := ⟨w - u * v, by
    have h2 : p * (w - u * v) = p * w - p * (u * v) :=
      Nat.mul_sub p w (u * v)
    omega⟩
  have := Nat.le_of_dvd one_pos hp1
  have := hp.one_lt
  omega

include hp hk in
theorem minv_mem {x : ℕ} (hx : x ∈ Mset p k) : minv p k x ∈ Mset p k := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  obtain ⟨⟨hx1, hxlt⟩, hxp⟩ := mem_Mset.mp hx
  have hnd := minv_not_dvd hp hk hxp
  refine mem_Mset.mpr ⟨⟨?_, ?_⟩, hnd⟩
  · rcases Nat.eq_zero_or_pos (minv p k x) with h0 | h1
    · exact absurd (h0 ▸ dvd_zero p) hnd
    · exact h1
  · exact ZMod.val_lt _

include hp in
omit hk in
theorem mAct_mAct_one {c1 c2 x : ℕ} (h12 : c1 * c2 ≡ 1 [MOD p ^ k])
    (hxlt : x < p ^ k) :
    mAct p k c1 (mAct p k c2 x) = x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hz : ((c1 * mAct p k c2 x : ℕ) : ZMod (p ^ k))
      = ((x : ℕ) : ZMod (p ^ k)) := by
    push_cast
    rw [mAct, ZMod.natCast_val, ZMod.cast_id]
    push_cast
    rw [← mul_assoc]
    have hone : ((c1 : ℕ) : ZMod (p ^ k)) * ((c2 : ℕ) : ZMod (p ^ k))
        = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h12
      push_cast at this
      exact this
    rw [hone, one_mul]
  rw [mAct, hz, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hxlt

include hp hk in
theorem minv_invol {x : ℕ} (hx : x ∈ Mset p k) :
    minv p k (minv p k x) = x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  obtain ⟨⟨hx1, hxlt⟩, hxp⟩ := mem_Mset.mp hx
  have h1 := minv_spec (k := k) hp hxp
  have h2 := minv_spec (k := k) hp (minv_not_dvd hp hk hxp)
  -- both `x` and `minv (minv x)` invert `minv x`; inverses are
  -- unique mod `p^k`, and both are reduced
  have hcong : minv p k (minv p k x) ≡ x [MOD p ^ k] := by
    calc minv p k (minv p k x)
        ≡ minv p k (minv p k x) * (x * minv p k x) [MOD p ^ k] := by
          conv_lhs => rw [← mul_one (minv p k (minv p k x))]
          exact (h1.symm).mul_left _
      _ = x * (minv p k x * minv p k (minv p k x)) := by ring
      _ ≡ x * 1 [MOD p ^ k] := h2.mul_left x
      _ = x := mul_one x
  have hlt1 : minv p k (minv p k x) < p ^ k := ZMod.val_lt _
  have := hcong
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hxlt] at this
  exact this

include hp in
omit hk in
theorem mAct_minv_cancel {c x : ℕ} (hc : ¬ p ∣ c) (hx : x ∈ Mset p k) :
    mAct p k c (mAct p k (minv p k c) x) = x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  obtain ⟨⟨hx1, hxlt⟩, hxp⟩ := mem_Mset.mp hx
  have hcinv := minv_spec (k := k) hp hc
  -- compute at the `ZMod` level
  have hz : ((c * mAct p k (minv p k c) x : ℕ) : ZMod (p ^ k))
      = ((x : ℕ) : ZMod (p ^ k)) := by
    push_cast
    rw [mAct, ZMod.natCast_val, ZMod.cast_id]
    push_cast
    rw [← mul_assoc]
    have hone : ((c : ℕ) : ZMod (p ^ k)) * ((minv p k c : ℕ) : ZMod (p ^ k))
        = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcinv
      push_cast at this
      exact this
    rw [hone, one_mul]
  rw [mAct, hz, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hxlt

include hp hk in
theorem minv_mAct_congr' {c x : ℕ} (hc : ¬ p ∣ c) (hxp : ¬ p ∣ x) :
    minv p k (mAct p k (minv p k c) x) ≡ c * minv p k x [MOD p ^ k] := by
  set y := mAct p k (minv p k c) x with hy
  have hyp : ¬ p ∣ y := by
    rw [hy, mAct]
    haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
    rw [ZMod.val_natCast]
    intro hd
    have hpd : p ∣ minv p k c * x := dvd_of_dvd_mod hk hd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · exact minv_not_dvd hp hk hc h
    · exact hxp h
  -- `y ≡ c⁻¹·x`, so `c·(minv x)` inverts `y`; conclude by uniqueness
  have hycong : y ≡ minv p k c * x [MOD p ^ k] := by
    rw [hy, mAct]
    haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
    rw [ZMod.val_natCast]
    exact (Nat.mod_modEq _ _)
  have hinv1 : y * (c * minv p k x) ≡ 1 [MOD p ^ k] := by
    calc y * (c * minv p k x)
        ≡ (minv p k c * x) * (c * minv p k x) [MOD p ^ k] :=
          hycong.mul_right _
      _ = (c * minv p k c) * (x * minv p k x) := by ring
      _ ≡ 1 * 1 [MOD p ^ k] :=
          Nat.ModEq.mul (minv_spec (k := k) hp hc)
            (minv_spec (k := k) hp hxp)
      _ = 1 := one_mul 1
  have hinv2 : y * minv p k y ≡ 1 [MOD p ^ k] := minv_spec (k := k) hp hyp
  -- uniqueness of inverses
  calc minv p k y ≡ minv p k y * (y * (c * minv p k x)) [MOD p ^ k] := by
        conv_lhs => rw [← mul_one (minv p k y)]
        exact hinv1.symm.mul_left _
    _ = (y * minv p k y) * (c * minv p k x) := by ring
    _ ≡ 1 * (c * minv p k x) [MOD p ^ k] := hinv2.mul_right _
    _ = c * minv p k x := one_mul _

end Arithmetic

/-! ### The floor-arithmetic identity behind Lemma (8.12) -/

theorem div_shift {N : ℕ} (hN : 0 < N) (m u : ℕ) :
    m * u / N = m * (u % N) / N + m * (u / N) := by
  conv_lhs => rw [← Nat.div_add_mod u N]
  rw [show m * (N * (u / N) + u % N)
      = m * (u % N) + N * (m * (u / N)) from by ring,
    Nat.add_mul_div_left _ _ hN]

theorem div_add_le {N : ℕ} (hN : 0 < N) (u v : ℕ) :
    u / N + v / N ≤ (u + v) / N := by
  rw [Nat.le_div_iff_mul_le hN, Nat.add_mul]
  exact Nat.add_le_add (Nat.div_mul_le_self u N) (Nat.div_mul_le_self v N)

/-- **The coefficient-wise form of the group-ring identity of
Lemma (8.12)**: `(n − σ_n)β = (σ_a + σ_b − σ_(a+b))α`, read off at
the coefficient of `σ_y⁻¹` — pure floor arithmetic. -/
theorem exponent_identity {p k n a b y : ℕ} (hp : p.Prime) :
    n * βc a b p k y + αc n p k (mAct p k (a + b) y)
      = βc a b p k (mAct p k n y)
        + (αc n p k (mAct p k a y) + αc n p k (mAct p k b y)) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hN0 : (0 : ℕ) < p ^ k := pow_pos hp.pos k
  have hact : ∀ c z : ℕ, mAct p k c z = (c * z) % p ^ k := fun c z => by
    rw [mAct]
    exact ZMod.val_natCast (n := p ^ k) _
  simp only [αc, βc, hact]
  -- the six Euclidean decompositions
  have h1 := div_shift hN0 n ((a + b) * y)
  have h2 := div_shift hN0 n (a * y)
  have h3 := div_shift hN0 n (b * y)
  have h4 := div_shift hN0 (a + b) (n * y)
  have h5 := div_shift hN0 a (n * y)
  have h6 := div_shift hN0 b (n * y)
  -- align the mixed products
  have hTs : n * ((a + b) * y) = (a + b) * (n * y) := by ring
  have hTa : n * (a * y) = a * (n * y) := by ring
  have hTb : n * (b * y) = b * (n * y) := by ring
  rw [hTs] at h1
  rw [hTa] at h2
  rw [hTb] at h3
  -- expand the ℕ-subtractions
  have hg1 : a * y / p ^ k + b * y / p ^ k ≤ (a + b) * y / p ^ k := by
    have := div_add_le hN0 (a * y) (b * y)
    rwa [show a * y + b * y = (a + b) * y from by ring] at this
  have hg2 : a * (n * y % p ^ k) / p ^ k + b * (n * y % p ^ k) / p ^ k
      ≤ (a + b) * (n * y % p ^ k) / p ^ k := by
    have := div_add_le hN0 (a * (n * y % p ^ k)) (b * (n * y % p ^ k))
    rwa [show a * (n * y % p ^ k) + b * (n * y % p ^ k)
        = (a + b) * (n * y % p ^ k) from by ring] at this
  have hsub : n * ((a + b) * y / p ^ k - a * y / p ^ k - b * y / p ^ k)
      = n * ((a + b) * y / p ^ k) - n * (a * y / p ^ k)
        - n * (b * y / p ^ k) := by
    rw [Nat.mul_sub, Nat.mul_sub]
  have hQn : (a + b) * (n * y / p ^ k)
      = a * (n * y / p ^ k) + b * (n * y / p ^ k) := by ring
  have hng1 : n * (a * y / p ^ k) + n * (b * y / p ^ k)
      ≤ n * ((a + b) * y / p ^ k) := by
    have h := Nat.mul_le_mul_left (k := n) hg1
    rwa [Nat.mul_add] at h
  omega




/-! ### Product reindexing and the two identities -/

section Products

variable {R : Type _} [CommRing R] [IsDomain R] {q p k n a b : ℕ}
variable [Fact q.Prime]
variable {χ : MulChar (ZMod q) R} {ψ : AddChar (ZMod q) R}

omit [IsDomain R] in
/-- Reindexing a Gauss-sum product over `M` along the multiplication
action by a unit `c`. -/
theorem Pprod_reindex (hp : p.Prime) (hk : 0 < k)
    (hord : orderOf χ = p ^ k) {c : ℕ} (hc : ¬ p ∣ c) (f : ℕ → ℕ) :
    ∏ x ∈ Mset p k, gaussSum (χ ^ (c * minv p k x)) ψ ^ f x
      = ∏ y ∈ Mset p k, gaussSum (χ ^ minv p k y) ψ ^ f (mAct p k c y) := by
  have hchpow : ∀ {A B : ℕ}, A ≡ B [MOD p ^ k] → χ ^ A = χ ^ B :=
    fun hAB => pow_eq_pow_iff_modEq.mpr (hord ▸ hAB)
  refine Finset.prod_nbij' (fun x => mAct p k (minv p k c) x)
    (fun y => mAct p k c y)
    (fun x hx => mAct_mem hp hk (minv_not_dvd hp hk hc) hx)
    (fun y hy => mAct_mem hp hk hc hy)
    (fun x hx => mAct_mAct_one hp
      (minv_spec (k := k) hp hc) (mem_Mset.mp hx).1.2)
    (fun y hy => mAct_mAct_one hp
      (by
        have := minv_spec (k := k) hp hc
        rwa [mul_comm] at this) (mem_Mset.mp hy).1.2)
    (fun x hx => ?_)
  have hcongr := minv_mAct_congr' hp hk hc (mem_Mset.mp hx).2
  have hfx : mAct p k c (mAct p k (minv p k c) x) = x :=
    mAct_mAct_one hp (minv_spec (k := k) hp hc) (mem_Mset.mp hx).1.2
  rw [hfx, hchpow hcongr.symm]

omit [IsDomain R] in
/-- **The `(n−σ_n)β = (σ_a+σ_b−σ_(a+b))α` identity at the
Gauss-sum-product level** — the first half of the paper's
Lemma (8.12), assembled from the coefficient-wise
`exponent_identity`. -/
theorem tau_product_identity (hp : p.Prime) (hk : 0 < k)
    (hord : orderOf χ = p ^ k) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b)
    (hpab : ¬ p ∣ (a + b)) (hpn : ¬ p ∣ n) :
    (∏ x ∈ Mset p k, gaussSum (χ ^ minv p k x) ψ ^ βc a b p k x) ^ n
      * ∏ x ∈ Mset p k,
          gaussSum (χ ^ ((a + b) * minv p k x)) ψ ^ αc n p k x
    = (∏ x ∈ Mset p k, gaussSum (χ ^ (n * minv p k x)) ψ ^ βc a b p k x)
      * ((∏ x ∈ Mset p k, gaussSum (χ ^ (a * minv p k x)) ψ ^ αc n p k x)
        * ∏ x ∈ Mset p k,
            gaussSum (χ ^ (b * minv p k x)) ψ ^ αc n p k x) := by
  rw [Pprod_reindex hp hk hord hpab, Pprod_reindex hp hk hord hpn,
    Pprod_reindex hp hk hord hpa, Pprod_reindex hp hk hord hpb,
    ← Finset.prod_pow]
  simp only [← pow_mul]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  rw [mul_comm (βc a b p k y) n]
  exact exponent_identity hp

/-- **The paper's chain `j(χ^a,χ^b)^α = τ(χ)^((n−σ_n)β)`**, as the
unit-free ring identity `j^α · σ(u_β) = u_β^n`. -/
theorem jacobi_tau_identity (hp : p.Prime) (hk : 0 < k)
    (hord : orderOf χ = p ^ k) (hψ : ψ.IsPrimitive)
    (hq0 : ((q : ℕ) : R) ≠ 0)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpab : ¬ p ∣ (a + b))
    (hpn : ¬ p ∣ n) :
    (∏ x ∈ Mset p k,
        jacobiSum (χ ^ (a * minv p k x)) (χ ^ (b * minv p k x))
          ^ αc n p k x)
      * ∏ x ∈ Mset p k, gaussSum (χ ^ (n * minv p k x)) ψ ^ βc a b p k x
    = (∏ x ∈ Mset p k, gaussSum (χ ^ minv p k x) ψ ^ βc a b p k x) ^ n := by
  have hchne : ∀ {c : ℕ}, ¬ p ∣ c → ∀ x ∈ Mset p k, χ ^ (c * minv p k x) ≠ 1 := by
    intro c hc x hx h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hd
    have hpd : p ∣ c * minv p k x :=
      dvd_trans (dvd_pow_self p hk.ne') hd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · exact hc h
    · exact minv_not_dvd hp hk (mem_Mset.mp hx).2 h
  -- step A: the per-`x` instances of (8.2), multiplied
  have hA : (∏ x ∈ Mset p k,
        jacobiSum (χ ^ (a * minv p k x)) (χ ^ (b * minv p k x))
          ^ αc n p k x)
      * ∏ x ∈ Mset p k,
          gaussSum (χ ^ ((a + b) * minv p k x)) ψ ^ αc n p k x
    = (∏ x ∈ Mset p k, gaussSum (χ ^ (a * minv p k x)) ψ ^ αc n p k x)
      * ∏ x ∈ Mset p k, gaussSum (χ ^ (b * minv p k x)) ψ ^ αc n p k x := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [← mul_pow, ← mul_pow]
    congr 1
    have hdvd : ¬ p ^ k ∣ a * minv p k x + b * minv p k x := by
      rw [show a * minv p k x + b * minv p k x
          = (a + b) * minv p k x from by ring]
      intro hd
      have hpd : p ∣ (a + b) * minv p k x :=
        dvd_trans (dvd_pow_self p hk.ne') hd
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
      · exact hpab h
      · exact minv_not_dvd hp hk (mem_Mset.mp hx).2 h
    have h82 := eq_8_2 hord ψ hdvd
    rw [show a * minv p k x + b * minv p k x
        = (a + b) * minv p k x from by ring] at h82
    rw [mul_comm]
    exact h82
  have hB := tau_product_identity (ψ := ψ) hp hk hord hpa hpb hpab hpn
  -- cancel the common factor `∏ τ(χ^((a+b)·x*))^(αc)`
  have hPs : (∏ x ∈ Mset p k,
      gaussSum (χ ^ ((a + b) * minv p k x)) ψ ^ αc n p k x) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun x hx => ?_
    refine pow_ne_zero _ ?_
    refine gaussSum_ne_zero_of_nontrivial ?_ (hchne hpab x hx) hψ
    rw [ZMod.card]
    exact hq0
  refine mul_right_cancel₀ hPs ?_
  calc (∏ x ∈ Mset p k,
        jacobiSum (χ ^ (a * minv p k x)) (χ ^ (b * minv p k x))
          ^ αc n p k x)
      * (∏ x ∈ Mset p k, gaussSum (χ ^ (n * minv p k x)) ψ ^ βc a b p k x)
      * (∏ x ∈ Mset p k,
          gaussSum (χ ^ ((a + b) * minv p k x)) ψ ^ αc n p k x)
      = ((∏ x ∈ Mset p k,
            jacobiSum (χ ^ (a * minv p k x)) (χ ^ (b * minv p k x))
              ^ αc n p k x)
          * ∏ x ∈ Mset p k,
              gaussSum (χ ^ ((a + b) * minv p k x)) ψ ^ αc n p k x)
        * ∏ x ∈ Mset p k,
            gaussSum (χ ^ (n * minv p k x)) ψ ^ βc a b p k x := by
        ring
    _ = ((∏ x ∈ Mset p k, gaussSum (χ ^ (a * minv p k x)) ψ ^ αc n p k x)
          * ∏ x ∈ Mset p k, gaussSum (χ ^ (b * minv p k x)) ψ ^ αc n p k x)
        * ∏ x ∈ Mset p k,
            gaussSum (χ ^ (n * minv p k x)) ψ ^ βc a b p k x := by
        rw [hA]
    _ = (∏ x ∈ Mset p k, gaussSum (χ ^ minv p k x) ψ ^ βc a b p k x) ^ n
        * ∏ x ∈ Mset p k,
            gaussSum (χ ^ ((a + b) * minv p k x)) ψ ^ αc n p k x := by
        rw [hB]
        ring

end Products

/-! ### Theorem (8.5) and the deferred half of Lemma (8.12) -/

/-- **Cohen–Lenstra Theorem (8.5)** (soundness direction, abstract):
if the Jacobi-sum congruence (8.8) holds —
`∏_{x ∈ M} j(χ^(a·x*), χ^(b·x*))^(αc x) ≡ ζ' (mod I)` — then the
hypothesis (7.9) of Theorems (7.8)/(7.19) holds for the family
`(S, ν) = (Mset p k, βc ∘ minv)`, with the *same* `ζ'`
(Remark (8.9b)).  The second assertion of the paper's theorem (a
prime `n` passes the test) is completeness, assembled with the
algorithm in the later sections. -/
theorem theorem_8_5 {R : Type _} [CommRing R] [IsDomain R]
    {q p k n a b : ℕ} [Fact q.Prime]
    (hp : p.Prime) (hk : 0 < k) (hn0 : n ≠ 0)
    {χ : MulChar (ZMod q) R} {ψ : AddChar (ZMod q) R}
    (hord : orderOf χ = p ^ k) (hψ : ψ.IsPrimitive)
    (hq0 : ((q : ℕ) : R) ≠ 0)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpab : ¬ p ∣ (a + b))
    (hpn : ¬ p ∣ n)
    {σ : R →+* R} (hσχ : ∀ c : ZMod q, σ (χ c) = χ c ^ n)
    (hσψ : ∀ c : ZMod q, σ (ψ c) = ψ c)
    {I : Ideal R} {ζ' : R}
    (h88 : (∏ x ∈ Mset p k,
        jacobiSum (χ ^ (a * minv p k x)) (χ ^ (b * minv p k x))
          ^ αc n p k x) - ζ' ∈ I) :
    (∏ y ∈ Mset p k, gaussSum (χ ^ y) ψ ^ βc a b p k (minv p k y)) ^ n
      - ζ' * σ (∏ y ∈ Mset p k,
          gaussSum (χ ^ y) ψ ^ βc a b p k (minv p k y)) ∈ I := by
  -- the `y`-indexed family is the `minv`-reindexing of the
  -- `x`-indexed one
  have hreidx : (∏ y ∈ Mset p k,
        gaussSum (χ ^ y) ψ ^ βc a b p k (minv p k y))
      = ∏ x ∈ Mset p k, gaussSum (χ ^ minv p k x) ψ ^ βc a b p k x := by
    refine Finset.prod_nbij' (fun y => minv p k y) (fun x => minv p k x)
      (fun y hy => minv_mem hp hk hy) (fun x hx => minv_mem hp hk hx)
      (fun y hy => minv_invol hp hk hy)
      (fun x hx => minv_invol hp hk hx)
      (fun y hy => ?_)
    rw [minv_invol hp hk hy]
  -- σ of the product is the `n`-shifted product
  have hσprod : σ (∏ x ∈ Mset p k,
        gaussSum (χ ^ minv p k x) ψ ^ βc a b p k x)
      = ∏ x ∈ Mset p k,
          gaussSum (χ ^ (n * minv p k x)) ψ ^ βc a b p k x := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [map_pow, sigma_gaussSum hσχ hσψ hn0 ?_]
    · rw [mul_comm]
    · intro h0
      exact minv_not_dvd hp hk (mem_Mset.mp hx).2 (h0 ▸ dvd_zero p)
  rw [hreidx, hσprod]
  have hid := jacobi_tau_identity (ψ := ψ) hp hk hord hψ hq0
    hpa hpb hpab hpn
  have heq : (∏ x ∈ Mset p k,
        gaussSum (χ ^ minv p k x) ψ ^ βc a b p k x) ^ n
      - ζ' * ∏ x ∈ Mset p k,
          gaussSum (χ ^ (n * minv p k x)) ψ ^ βc a b p k x
      = ((∏ x ∈ Mset p k,
            jacobiSum (χ ^ (a * minv p k x)) (χ ^ (b * minv p k x))
              ^ αc n p k x) - ζ')
        * ∏ x ∈ Mset p k,
            gaussSum (χ ^ (n * minv p k x)) ψ ^ βc a b p k x := by
    rw [← hid]
    ring
  rw [heq]
  exact Ideal.mul_mem_right _ I h88

/-! ### Helpers for the proof of Lemma (8.12) -/

/-- Sums preserve congruences. -/
theorem modEq_sum {ι : Type _} {S : Finset ι} {f g : ι → ℕ} {n : ℕ}
    (h : ∀ i ∈ S, f i ≡ g i [MOD n]) :
    ∑ i ∈ S, f i ≡ ∑ i ∈ S, g i [MOD n] := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Nat.ModEq.refl 0
  | insert a S haS ih =>
    rw [Finset.sum_insert haS, Finset.sum_insert haS]
    exact Nat.ModEq.add (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Sums preserve congruences (integer version). -/
theorem int_modEq_sum {ι : Type _} {S : Finset ι} {f g : ι → ℤ} {n : ℤ}
    (h : ∀ i ∈ S, f i ≡ g i [ZMOD n]) :
    ∑ i ∈ S, f i ≡ ∑ i ∈ S, g i [ZMOD n] := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Int.ModEq.refl 0
  | insert a S haS ih =>
    rw [Finset.sum_insert haS, Finset.sum_insert haS]
    exact Int.ModEq.add (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The `p`-th-power lift**: a congruence mod `p^k` raises to a
congruence of `p`-th powers mod `p^(k+1)` — the well-definedness of
the paper's ring homomorphism `ℤ[G] → ℤ/p^(k+1)ℤ`,
`σ_x ↦ x^p`. -/
theorem pow_p_modEq_lift {p k : ℕ} (hk : 0 < k)
    {u v : ℕ} (h : u ≡ v [MOD p ^ k]) :
    u ^ p ≡ v ^ p [MOD p ^ (k + 1)] := by
  have hZ : ((p : ℤ)) ^ k ∣ (u : ℤ) - (v : ℤ) := by
    have hd := h.dvd
    push_cast at hd
    exact dvd_sub_comm.mp hd
  have hgeom := geom_sum₂_mul ((u : ℤ)) ((v : ℤ)) p
  have hpsum : (p : ℤ) ∣ ∑ i ∈ Finset.range p, (u : ℤ) ^ i * (v : ℤ) ^ (p - 1 - i) := by
    have hmod : ∑ i ∈ Finset.range p, (u : ℤ) ^ i * (v : ℤ) ^ (p - 1 - i)
        ≡ ∑ _i ∈ Finset.range p, (v : ℤ) ^ (p - 1) [ZMOD (p : ℤ)] := by
      refine int_modEq_sum fun i hi => ?_
      have huv : (u : ℤ) ≡ (v : ℤ) [ZMOD (p : ℤ)] := by
        have : ((p : ℤ)) ∣ (u : ℤ) - (v : ℤ) :=
          dvd_trans (dvd_pow_self _ hk.ne') hZ
        exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
          have := dvd_neg.mpr this
          rwa [neg_sub] at this))
      calc (u : ℤ) ^ i * (v : ℤ) ^ (p - 1 - i)
          ≡ (v : ℤ) ^ i * (v : ℤ) ^ (p - 1 - i) [ZMOD (p : ℤ)] :=
            Int.ModEq.mul (huv.pow i) (Int.ModEq.refl _)
        _ = (v : ℤ) ^ (p - 1) := by
            rw [← pow_add]
            congr 1
            have hilt := Finset.mem_range.mp hi
            omega
    have hconst : ∑ _i ∈ Finset.range p, (v : ℤ) ^ (p - 1)
        = (p : ℤ) * (v : ℤ) ^ (p - 1) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have := hmod.dvd
    rw [hconst] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨(v : ℤ) ^ (p - 1) - c, by linear_combination -hc⟩
  have hdvd : ((p : ℤ)) ^ (k + 1) ∣ (u : ℤ) ^ p - (v : ℤ) ^ p := by
    rw [← hgeom, pow_succ]
    obtain ⟨c1, hc1⟩ := hpsum
    obtain ⟨c2, hc2⟩ := hZ
    exact ⟨c1 * c2, by rw [hc1, hc2]; ring⟩
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact dvd_sub_comm.mp hdvd

/-- The coefficient-wise form of the paper's (8.14):
`mAct a y + mAct b y = mAct (a+b) y + p^k·βc y` — the division
algorithm, three times. -/
theorem eq_8_14_coeff {p k a b y : ℕ} (hp : p.Prime) :
    mAct p k a y + mAct p k b y
      = mAct p k (a + b) y + p ^ k * βc a b p k y := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hN0 : (0 : ℕ) < p ^ k := pow_pos hp.pos k
  have hact : ∀ c z : ℕ, mAct p k c z = (c * z) % p ^ k := fun c z => by
    rw [mAct]
    exact ZMod.val_natCast (n := p ^ k) _
  simp only [hact, βc]
  have h1 := Nat.div_add_mod ((a + b) * y) (p ^ k)
  have h2 := Nat.div_add_mod (a * y) (p ^ k)
  have h3 := Nat.div_add_mod (b * y) (p ^ k)
  have hg1 : a * y / p ^ k + b * y / p ^ k ≤ (a + b) * y / p ^ k := by
    have := div_add_le hN0 (a * y) (b * y)
    rwa [show a * y + b * y = (a + b) * y from by ring] at this
  have hsub : p ^ k * ((a + b) * y / p ^ k - a * y / p ^ k - b * y / p ^ k)
      = p ^ k * ((a + b) * y / p ^ k) - p ^ k * (a * y / p ^ k)
        - p ^ k * (b * y / p ^ k) := by
    rw [Nat.mul_sub, Nat.mul_sub]
  have haby : (a + b) * y = a * y + b * y := by ring
  have hmul : p ^ k * (a * y / p ^ k) + p ^ k * (b * y / p ^ k)
      ≤ p ^ k * ((a + b) * y / p ^ k) := by
    have h := Nat.mul_le_mul_left (k := p ^ k) hg1
    rwa [Nat.mul_add] at h
  omega

/-- `a^p + b^p ≤ (a+b)^p` (so the `ℕ`-subtraction in `(8.6)` is
exact). -/
theorem add_pow_le_pow_add (a b p : ℕ) (hp : 0 < p) :
    a ^ p + b ^ p ≤ (a + b) ^ p := by
  induction p with
  | zero => omega
  | succ p ih =>
    rcases Nat.eq_zero_or_pos p with rfl | hp'
    · simp
    · have h1 : a ^ (p + 1) + b ^ (p + 1)
          ≤ (a ^ p + b ^ p) * (a + b) := by
        have hexp : (a ^ p + b ^ p) * (a + b)
            = (a ^ (p + 1) + b ^ (p + 1)) + (a ^ p * b + b ^ p * a) := by
          ring
        omega
      calc a ^ (p + 1) + b ^ (p + 1) ≤ (a ^ p + b ^ p) * (a + b) := h1
        _ ≤ (a + b) ^ p * (a + b) := Nat.mul_le_mul_right _ (ih hp')
        _ = (a + b) ^ (p + 1) := by ring

/-- Splitting a sum over `range (a·b)` into blocks. -/
theorem sum_range_mul_split {M' : Type _} [AddCommMonoid M']
    (f : ℕ → M') (a b : ℕ) :
    ∑ i ∈ Finset.range (a * b), f i
      = ∑ t ∈ Finset.range a, ∑ j ∈ Finset.range b, f (t * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ← ih,
      show (a + 1) * b = a * b + b from by ring,
      Finset.sum_range_add]

/-- A sum over `M` is a sum over the unit group of `ZMod (p^k)`. -/
theorem sum_Mset_eq_sum_units {p k : ℕ} [NeZero (p ^ k)]
    (hp : p.Prime) (hk : 0 < k)
    {M' : Type _} [AddCommMonoid M'] (f : ZMod (p ^ k) → M') :
    ∑ x ∈ Mset p k, f ((x : ℕ) : ZMod (p ^ k))
      = ∑ u : (ZMod (p ^ k))ˣ, f ((u : ZMod (p ^ k))) := by
  classical
  haveI : Nontrivial (ZMod (p ^ k)) := by
    haveI : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow hk.ne' hp.one_lt⟩
    infer_instance
  refine Finset.sum_bij
    (fun x hx => ZMod.unitOfCoprime x
      (Nat.Coprime.pow_right _ (Nat.coprime_comm.mp
        (hp.coprime_iff_not_dvd.mpr (mem_Mset.mp hx).2))))
    (fun x hx => Finset.mem_univ _) ?_ ?_ ?_
  · -- injectivity
    intro x hx y hy hxy
    have hval := congrArg
      (fun u : (ZMod (p ^ k))ˣ => ((u : ZMod (p ^ k))).val) hxy
    simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast] at hval
    rwa [Nat.mod_eq_of_lt (mem_Mset.mp hx).1.2,
      Nat.mod_eq_of_lt (mem_Mset.mp hy).1.2] at hval
  · -- surjectivity
    intro u _
    have hvcast : ((((u : ZMod (p ^ k))).val : ℕ) : ZMod (p ^ k))
        = (u : ZMod (p ^ k)) := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    have hvco : (((u : ZMod (p ^ k))).val).Coprime (p ^ k) := by
      refine (ZMod.isUnit_iff_coprime _ _).mp ?_
      rw [hvcast]
      exact u.isUnit
    refine ⟨((u : ZMod (p ^ k))).val, ?_, ?_⟩
    · refine mem_Mset.mpr ⟨⟨?_, ZMod.val_lt _⟩, ?_⟩
      · rcases Nat.eq_zero_or_pos (((u : ZMod (p ^ k))).val) with h0 | h1
        · exfalso
          refine u.ne_zero ?_
          rw [← hvcast, h0, Nat.cast_zero]
        · exact h1
      · intro hd
        have hgcd : p ∣ Nat.gcd (((u : ZMod (p ^ k))).val) (p ^ k) :=
          Nat.dvd_gcd hd (dvd_pow_self p hk.ne')
        rw [hvco] at hgcd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hgcd)
    · refine Units.ext ?_
      rw [ZMod.coe_unitOfCoprime]
      exact hvcast
  · -- values agree
    intro x hx
    rw [ZMod.coe_unitOfCoprime]

/-- A sum over a cyclic group is a sum over powers of a generator. -/
theorem sum_eq_sum_range_pow {G : Type _} [Group G] [Fintype G] {g : G}
    (hg : ∀ u : G, u ∈ Subgroup.zpowers g)
    {M' : Type _} [AddCommMonoid M'] (f : G → M') :
    ∑ u : G, f u = ∑ i ∈ Finset.range (orderOf g), f (g ^ i) := by
  classical
  have hord0 : 0 < orderOf g := orderOf_pos g
  refine (Finset.sum_bij (fun i _ => g ^ i)
    (fun i _ => Finset.mem_univ _) ?_ ?_ ?_).symm
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf
      (Set.mem_Iio.mpr (Finset.mem_range.mp hi))
      (Set.mem_Iio.mpr (Finset.mem_range.mp hj)) hij
  · intro u _
    obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers).mpr (hg u)
    refine ⟨i % orderOf g,
      Finset.mem_range.mpr (Nat.mod_lt _ hord0), ?_⟩
    rw [pow_mod_orderOf]
    exact hi
  · exact fun i _ => rfl

/-- The sum of the `1`-unit powers `h^j` (`h` of order `p^(k−1)`,
congruent to `1` mod `p`) is the cast of `Σ_{i<p^(k−1)} (1 + p·i)`. -/
theorem sum_one_unit_pows {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {h : (ZMod (p ^ k))ˣ} (hordh : orderOf h = p ^ (k - 1))
    (hh1 : ∀ j : ℕ, (((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val % p = 1) :
    ∑ j ∈ Finset.range (p ^ (k - 1)),
        (((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
      = ((∑ i ∈ Finset.range (p ^ (k - 1)), (1 + p * i) : ℕ)
          : ZMod (p ^ k)) := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  set F : ℕ → ℕ := fun j =>
    ((((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val - 1) / p with hF
  have hFval : ∀ j : ℕ,
      1 + p * F j = (((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val := by
    intro j
    have h1 := hh1 j
    have h2 := Nat.div_add_mod
      ((((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val) p
    have h3 : (((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val - 1
        = p * ((((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val / p) := by
      omega
    rw [hF]
    simp only
    rw [h3, Nat.mul_div_cancel_left _ hp.pos]
    omega
  have hFlt : ∀ j : ℕ, F j < p ^ (k - 1) := by
    intro j
    have hlt : (((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val < p ^ k :=
      ZMod.val_lt _
    have hkk : p ^ k = p * p ^ (k - 1) := by
      conv_lhs => rw [show k = 1 + (k - 1) from by omega]
      rw [pow_add, pow_one]
    have hv := hFval j
    have hpf : p * F j < p * p ^ (k - 1) := by omega
    exact Nat.lt_of_mul_lt_mul_left hpf
  have hinj : Set.InjOn F (Finset.range (p ^ (k - 1))) := by
    intro i hi j hj hij
    have hvi := hFval i
    have hvj := hFval j
    rw [hij] at hvi
    have hveq : (((h ^ i : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val
        = (((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))).val := by
      omega
    have helem : ((h ^ i : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
        = ((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by
      have := congrArg (fun v : ℕ => ((v : ℕ) : ZMod (p ^ k))) hveq
      simpa [ZMod.natCast_val, ZMod.cast_id] using this
    have huniteq : (h ^ i : (ZMod (p ^ k))ˣ) = h ^ j := Units.ext helem
    refine pow_injOn_Iio_orderOf ?_ ?_ huniteq
    · rw [Set.mem_Iio, hordh]
      exact Finset.mem_range.mp (Finset.mem_coe.mp hi)
    · rw [Set.mem_Iio, hordh]
      exact Finset.mem_range.mp (Finset.mem_coe.mp hj)
  have himg : (Finset.range (p ^ (k - 1))).image F
      = Finset.range (p ^ (k - 1)) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hFlt j)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ j ∈ Finset.range (p ^ (k - 1)),
        (((h ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
      = ∑ j ∈ Finset.range (p ^ (k - 1)),
          ((1 + p * F j : ℕ) : ZMod (p ^ k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hFval j, ZMod.natCast_val, ZMod.cast_id]
    _ = ∑ i ∈ (Finset.range (p ^ (k - 1))).image F,
          ((1 + p * i : ℕ) : ZMod (p ^ k)) := by
        rw [Finset.sum_image (fun i hi j hj hij =>
          hinj (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hij)]
    _ = ∑ i ∈ Finset.range (p ^ (k - 1)),
          ((1 + p * i : ℕ) : ZMod (p ^ k)) := by rw [himg]
    _ = ((∑ i ∈ Finset.range (p ^ (k - 1)), (1 + p * i) : ℕ)
          : ZMod (p ^ k)) := by push_cast; rfl

/-- The `ℕ`-sum of the `1`-unit representatives:
`Σ_{i<p^(k−1)} (1 + p·i) = p^(k−1) + p^k·s` for odd `p`. -/
theorem sum_one_add_mul {p k : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    (hk : 0 < k) :
    ∃ s : ℕ, ∑ i ∈ Finset.range (p ^ (k - 1)), (1 + p * i)
      = p ^ (k - 1) + p ^ k * s := by
  have hodd : Odd (p ^ (k - 1)) := Odd.pow (hp.odd_of_ne_two (by omega))
  obtain ⟨s, hs⟩ : ∃ s, p ^ (k - 1) - 1 = 2 * s := by
    obtain ⟨c, hc⟩ := hodd
    exact ⟨c, by omega⟩
  refine ⟨s, ?_⟩
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one, ← Finset.mul_sum]
  have hgauss := Finset.sum_range_id_mul_two (p ^ (k - 1))
  have hsum : ∑ i ∈ Finset.range (p ^ (k - 1)), i = p ^ (k - 1) * s := by
    have h2 : p ^ (k - 1) * (p ^ (k - 1) - 1) = 2 * (p ^ (k - 1) * s) := by
      rw [hs]
      ring
    omega
  have hkk : (k - 1) + 1 = k := by omega
  rw [hsum, ← mul_assoc, ← pow_succ', hkk]

/-- **(8.16), in congruence form**: the power sum over `M` satisfies
`Σ_{x ∈ M} x^(p−1) ≡ (p−1)·p^(k−1) (mod p^k)`.  The `(p−1)`-power map
on the cyclic unit group has image the `1`-units, each value taken
`p − 1` times. -/
theorem sum_pow_M_modEq {p k : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    (hk : 0 < k) :
    ∑ x ∈ Mset p k, x ^ (p - 1) ≡ (p - 1) * p ^ (k - 1) [MOD p ^ k] := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp (by omega) k
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (p ^ k))ˣ)
  have hgord : orderOf g = (p - 1) * p ^ (k - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp hk, mul_comm]
  have hordh : orderOf (g ^ (p - 1)) = p ^ (k - 1) := by
    rw [orderOf_pow, hgord]
    have hgcd : Nat.gcd ((p - 1) * p ^ (k - 1)) (p - 1) = p - 1 := by
      have h1 := Nat.gcd_mul_left (p - 1) (p ^ (k - 1)) 1
      simp only [Nat.gcd_one_right, mul_one] at h1
      exact h1
    rw [hgcd, Nat.mul_div_cancel_left _ (by omega : 0 < p - 1)]
  have hh1 : ∀ j : ℕ,
      (((g ^ (p - 1)) ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)).val % p
        = 1 := by
    intro j
    have hgu : (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p))
        ((g : ZMod (p ^ k))) ≠ 0 :=
      (g.isUnit.map _).ne_zero
    have hone : (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p))
        ((((g ^ (p - 1)) ^ j : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) = 1 := by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        map_pow, map_pow, ZMod.pow_card_sub_one_eq_one hgu, one_pow]
    rw [ZMod.castHom_apply, ← ZMod.natCast_val] at hone
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp
      (by rw [hone, Nat.cast_one] :
        (((((g ^ (p - 1)) ^ j : (ZMod (p ^ k))ˣ)
          : ZMod (p ^ k)).val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p))
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt hp.one_lt] at hmod
  obtain ⟨s, hs⟩ := sum_one_add_mul hp hp3 hk
  have hpow1 : ((g ^ (p - 1)) ^ (p ^ (k - 1)) : (ZMod (p ^ k))ˣ) = 1 := by
    rw [← hordh]
    exact pow_orderOf_eq_one _
  have hchain : ((∑ x ∈ Mset p k, x ^ (p - 1) : ℕ) : ZMod (p ^ k))
      = (((p - 1) * (p ^ (k - 1) + p ^ k * s) : ℕ) : ZMod (p ^ k)) := by
    calc ((∑ x ∈ Mset p k, x ^ (p - 1) : ℕ) : ZMod (p ^ k))
        = ∑ x ∈ Mset p k, ((x : ℕ) : ZMod (p ^ k)) ^ (p - 1) := by
          push_cast
          rfl
      _ = ∑ u : (ZMod (p ^ k))ˣ, ((u : ZMod (p ^ k))) ^ (p - 1) :=
          sum_Mset_eq_sum_units hp hk (fun z => z ^ (p - 1))
      _ = ∑ i ∈ Finset.range ((p - 1) * p ^ (k - 1)),
            ((g ^ i : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) ^ (p - 1) := by
          rw [sum_eq_sum_range_pow hg
            (fun u => ((u : ZMod (p ^ k))) ^ (p - 1)), hgord]
      _ = ∑ i ∈ Finset.range ((p - 1) * p ^ (k - 1)),
            ((((g ^ (p - 1)) ^ i : (ZMod (p ^ k))ˣ)) : ZMod (p ^ k)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm i (p - 1),
            pow_mul]
      _ = ∑ t ∈ Finset.range (p - 1), ∑ j ∈ Finset.range (p ^ (k - 1)),
            ((((g ^ (p - 1)) ^ (t * p ^ (k - 1) + j)
              : (ZMod (p ^ k))ˣ)) : ZMod (p ^ k)) :=
          sum_range_mul_split _ (p - 1) (p ^ (k - 1))
      _ = ∑ t ∈ Finset.range (p - 1), ∑ j ∈ Finset.range (p ^ (k - 1)),
            ((((g ^ (p - 1)) ^ j : (ZMod (p ^ k))ˣ)) : ZMod (p ^ k)) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          rw [pow_add, pow_mul', hpow1, one_pow, one_mul]
      _ = (p - 1) • ∑ j ∈ Finset.range (p ^ (k - 1)),
            ((((g ^ (p - 1)) ^ j : (ZMod (p ^ k))ˣ)) : ZMod (p ^ k)) := by
          rw [Finset.sum_const, Finset.card_range]
      _ = (p - 1) • ((∑ i ∈ Finset.range (p ^ (k - 1)), (1 + p * i) : ℕ)
            : ZMod (p ^ k)) := by
          rw [sum_one_unit_pows hp hk hordh hh1]
      _ = (((p - 1) * (p ^ (k - 1) + p ^ k * s) : ℕ) : ZMod (p ^ k)) := by
          rw [hs, nsmul_eq_mul]
          push_cast
          ring
  have hcong : ∑ x ∈ Mset p k, x ^ (p - 1)
      ≡ (p - 1) * (p ^ (k - 1) + p ^ k * s) [MOD p ^ k] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hchain
  refine hcong.trans ?_
  have hdvd : (p : ℕ) ^ k ∣ (p - 1) * (p ^ (k - 1) + p ^ k * s)
      - (p - 1) * p ^ (k - 1) := ⟨(p - 1) * s, by
    rw [Nat.mul_add, Nat.add_sub_cancel_left]
    ring⟩
  have hle : (p - 1) * p ^ (k - 1)
      ≤ (p - 1) * (p ^ (k - 1) + p ^ k * s) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm

/-- The image of `Σ_{x} (mAct c x)·(minv x)^p` under the paper's ring
homomorphism argument: it is `≡ c^p·T (mod p^(k+1))`. -/
theorem sum_mAct_pow_modEq {p k c : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hc : ¬ p ∣ c) :
    ∑ x ∈ Mset p k, mAct p k c x * minv p k x ^ p
      ≡ c ^ p * ∑ x ∈ Mset p k, x * minv p k x ^ p [MOD p ^ (k + 1)] := by
  classical
  have hre : ∑ x ∈ Mset p k, mAct p k c x * minv p k x ^ p
      = ∑ z ∈ Mset p k, z * minv p k (mAct p k (minv p k c) z) ^ p := by
    refine Finset.sum_nbij' (fun x => mAct p k c x)
      (fun z => mAct p k (minv p k c) z)
      (fun x hx => mAct_mem hp hk hc hx)
      (fun z hz => mAct_mem hp hk (minv_not_dvd hp hk hc) hz)
      (fun x hx => mAct_mAct_one hp
        (by
          have := minv_spec (k := k) hp hc
          rwa [mul_comm] at this) (mem_Mset.mp hx).1.2)
      (fun z hz => mAct_mAct_one hp (minv_spec (k := k) hp hc)
        (mem_Mset.mp hz).1.2)
      (fun x hx => ?_)
    have hback : mAct p k (minv p k c) (mAct p k c x) = x :=
      mAct_mAct_one hp
        (by
          have := minv_spec (k := k) hp hc
          rwa [mul_comm] at this) (mem_Mset.mp hx).1.2
    rw [hback]
  rw [hre, Finset.mul_sum]
  refine modEq_sum fun z hz => ?_
  have hcong := minv_mAct_congr' hp hk hc (mem_Mset.mp hz).2
  have hlift := pow_p_modEq_lift hk hcong
  calc z * minv p k (mAct p k (minv p k c) z) ^ p
      ≡ z * (c * minv p k z) ^ p [MOD p ^ (k + 1)] := hlift.mul_left z
    _ = c ^ p * (z * minv p k z ^ p) := by ring

/-- Fermat's little theorem, `ℕ`-congruence form: `m^p ≡ m (mod p)`. -/
theorem fermat_nat {p : ℕ} (hp : p.Prime) (m : ℕ) :
    m ^ p ≡ m [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  push_cast
  exact ZMod.pow_card _

/-- **The second half of Lemma (8.12)**: condition (7.6) for `β` —
the weighted sum of the `β`-coefficients is not divisible by `p`.
This is where the hypothesis (8.6) on `(a, b)` enters: applying the
ring homomorphism `σ_x ↦ x^p mod p^(k+1)` to the identity (8.14)
gives `((a+b)^p − a^p − b^p)·T ≡ p^k·U (mod p^(k+1))` with
`T = Σ x·(x*)^p`; by (8.6) the left side has `p`-valuation exactly
`k` (using (8.16): `v_p(T) = k − 1`), whence `p ∤ U`, and `U` is the
target sum mod `p` by Fermat. -/
theorem lemma_8_12 {p k a b : ℕ} (hp : p.Prime) (hp3 : 2 < p)
    (hk : 0 < k) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (hpab : ¬ p ∣ (a + b))
    (h86 : ¬ (a + b) ^ p ≡ a ^ p + b ^ p [MOD p ^ 2]) :
    ¬ p ∣ ∑ y ∈ Mset p k, βc a b p k (minv p k y) * y := by
  classical
  -- reindex by the involution
  have hSre : ∑ y ∈ Mset p k, βc a b p k (minv p k y) * y
      = ∑ x ∈ Mset p k, βc a b p k x * minv p k x := by
    refine Finset.sum_nbij' (fun y => minv p k y) (fun x => minv p k x)
      (fun y hy => minv_mem hp hk hy) (fun x hx => minv_mem hp hk hx)
      (fun y hy => minv_invol hp hk hy)
      (fun x hx => minv_invol hp hk hx)
      (fun y hy => ?_)
    rw [minv_invol hp hk hy]
  rw [hSre]
  set S := ∑ x ∈ Mset p k, βc a b p k x * minv p k x with hSdef
  set U := ∑ x ∈ Mset p k, βc a b p k x * minv p k x ^ p with hUdef
  set T := ∑ x ∈ Mset p k, x * minv p k x ^ p with hTdef
  -- `S ≡ U (mod p)` by Fermat
  have hSU : S ≡ U [MOD p] := by
    rw [hSdef, hUdef]
    refine modEq_sum fun x hx => ?_
    exact ((fermat_nat hp (minv p k x)).symm).mul_left _
  -- the summed (8.14)
  have h814 : ∑ x ∈ Mset p k, mAct p k a x * minv p k x ^ p
      + ∑ x ∈ Mset p k, mAct p k b x * minv p k x ^ p
      = ∑ x ∈ Mset p k, mAct p k (a + b) x * minv p k x ^ p
        + p ^ k * U := by
    rw [hUdef, ← Finset.sum_add_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have h := eq_8_14_coeff (a := a) (b := b) (y := x) (k := k) hp
    calc mAct p k a x * minv p k x ^ p + mAct p k b x * minv p k x ^ p
        = (mAct p k a x + mAct p k b x) * minv p k x ^ p := by ring
      _ = (mAct p k (a + b) x + p ^ k * βc a b p k x)
            * minv p k x ^ p := by rw [h]
      _ = mAct p k (a + b) x * minv p k x ^ p
            + p ^ k * (βc a b p k x * minv p k x ^ p) := by ring
  -- the three reindexed congruences
  have hca := sum_mAct_pow_modEq (c := a) hp hk hpa
  have hcb := sum_mAct_pow_modEq (c := b) hp hk hpb
  have hcab := sum_mAct_pow_modEq (c := a + b) hp hk hpab
  rw [← hTdef] at hca hcb hcab
  -- `T ≡ (p−1)·p^(k−1) (mod p^k)`
  have hpow_split : ∀ m : ℕ, m ^ p = m * m ^ (p - 1) := by
    intro m
    conv_lhs => rw [show p = (p - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  have hT : T ≡ (p - 1) * p ^ (k - 1) [MOD p ^ k] := by
    have h1 : T ≡ ∑ x ∈ Mset p k, minv p k x ^ (p - 1) [MOD p ^ k] := by
      rw [hTdef]
      refine modEq_sum fun x hx => ?_
      have hsp := minv_spec (k := k) hp (mem_Mset.mp hx).2
      calc x * minv p k x ^ p
          = (x * minv p k x) * minv p k x ^ (p - 1) := by
            rw [hpow_split]
            ring
        _ ≡ 1 * minv p k x ^ (p - 1) [MOD p ^ k] := hsp.mul_right _
        _ = minv p k x ^ (p - 1) := one_mul _
    have h2 : ∑ x ∈ Mset p k, minv p k x ^ (p - 1)
        = ∑ y ∈ Mset p k, y ^ (p - 1) := by
      refine Finset.sum_nbij' (fun x => minv p k x) (fun y => minv p k y)
        (fun x hx => minv_mem hp hk hx) (fun y hy => minv_mem hp hk hy)
        (fun x hx => minv_invol hp hk hx)
        (fun y hy => minv_invol hp hk hy)
        (fun x hx => rfl)
    rw [h2] at h1
    exact h1.trans (sum_pow_M_modEq hp hp3 hk)
  -- `E := (a+b)^p − (a^p + b^p)` has `v_p(E) = 1` exactly
  have hEle : a ^ p + b ^ p ≤ (a + b) ^ p := add_pow_le_pow_add a b p hp.pos
  have hE1 : p ∣ (a + b) ^ p - (a ^ p + b ^ p) := by
    have hf1 := fermat_nat hp (a + b)
    have hf2 := fermat_nat hp a
    have hf3 := fermat_nat hp b
    have hmm : (a + b) ^ p ≡ a ^ p + b ^ p [MOD p] :=
      hf1.trans ((hf2.add hf3).symm)
    exact (Nat.modEq_iff_dvd' hEle).mp hmm.symm
  have hE2 : ¬ p ^ 2 ∣ (a + b) ^ p - (a ^ p + b ^ p) := by
    intro hd
    exact h86 ((Nat.modEq_iff_dvd' hEle).mpr hd).symm
  obtain ⟨e, hE⟩ := hE1
  have hpe : ¬ p ∣ e := by
    intro hd
    obtain ⟨e', rfl⟩ := hd
    exact hE2 ⟨e', by rw [hE]; ring⟩
  -- assemble mod `p^(k+1)`, all in `ℕ`
  have hcomb : a ^ p * T + b ^ p * T
      ≡ (a + b) ^ p * T + p ^ k * U [MOD p ^ (k + 1)] := by
    calc a ^ p * T + b ^ p * T
        ≡ (∑ x ∈ Mset p k, mAct p k a x * minv p k x ^ p)
          + ∑ x ∈ Mset p k, mAct p k b x * minv p k x ^ p
          [MOD p ^ (k + 1)] := (hca.symm).add (hcb.symm)
      _ = (∑ x ∈ Mset p k, mAct p k (a + b) x * minv p k x ^ p)
          + p ^ k * U := h814
      _ ≡ (a + b) ^ p * T + p ^ k * U [MOD p ^ (k + 1)] :=
          hcab.add_right _
  have hABle : a ^ p * T + b ^ p * T ≤ (a + b) ^ p * T + p ^ k * U := by
    have h1 : a ^ p * T + b ^ p * T ≤ (a + b) ^ p * T := by
      have := Nat.mul_le_mul_right T hEle
      rwa [Nat.add_mul] at this
    omega
  have hNdvd : p ^ (k + 1)
      ∣ ((a + b) ^ p * T + p ^ k * U) - (a ^ p * T + b ^ p * T) :=
    (Nat.modEq_iff_dvd' hABle).mp hcomb
  have hBA : ((a + b) ^ p * T + p ^ k * U) - (a ^ p * T + b ^ p * T)
      = p * e * T + p ^ k * U := by
    have hsubmul : ((a + b) ^ p - (a ^ p + b ^ p)) * T
        = (a + b) ^ p * T - (a ^ p + b ^ p) * T := Nat.sub_mul _ _ _
    have hdist : (a ^ p + b ^ p) * T = a ^ p * T + b ^ p * T :=
      Nat.add_mul _ _ _
    have hTle : (a ^ p + b ^ p) * T ≤ (a + b) ^ p * T :=
      Nat.mul_le_mul_right T hEle
    have hpeT : p * e * T = ((a + b) ^ p - (a ^ p + b ^ p)) * T := by
      rw [← hE]
    omega
  rw [hBA] at hNdvd
  -- pass to `ℤ`, substitute the valuation of `T`, cancel `p^k`
  have hcombZ : ((p : ℤ)) ^ (k + 1)
      ∣ (p : ℤ) * (e : ℤ) * (T : ℤ) + (p : ℤ) ^ k * (U : ℤ) := by
    have := Int.natCast_dvd_natCast.mpr hNdvd
    push_cast at this
    exact_mod_cast this
  obtain ⟨t, ht⟩ : ∃ t : ℤ,
      (T : ℤ) = ((p : ℤ) - 1) * (p : ℤ) ^ (k - 1) + (p : ℤ) ^ k * t := by
    have hd := hT.dvd
    push_cast [hp.one_le] at hd
    obtain ⟨t, htt⟩ := hd
    exact ⟨-t, by linarith⟩
  have hppow : (p : ℤ) * (p : ℤ) ^ (k - 1) = (p : ℤ) ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  have hkey : (p : ℤ) ∣ (e : ℤ) * ((p : ℤ) - 1) + (U : ℤ) := by
    have hpk0 : ((p : ℤ)) ^ k ≠ 0 := by positivity
    have hexp : (p : ℤ) ^ k * ((e : ℤ) * ((p : ℤ) - 1) + (U : ℤ))
          + (p : ℤ) ^ (k + 1) * ((e : ℤ) * t)
        = (p : ℤ) * (e : ℤ) * (T : ℤ) + (p : ℤ) ^ k * (U : ℤ) := by
      rw [ht]
      have hps : ((p : ℤ)) ^ (k + 1) = (p : ℤ) * (p : ℤ) ^ k := by
        rw [pow_succ]
        ring
      rw [hps]
      linear_combination (-(e : ℤ) * ((p : ℤ) - 1)) * hppow
    have hstep : ((p : ℤ)) ^ (k + 1)
        ∣ (p : ℤ) ^ k * ((e : ℤ) * ((p : ℤ) - 1) + (U : ℤ))
          + (p : ℤ) ^ (k + 1) * ((e : ℤ) * t) := by
      rw [hexp]
      exact hcombZ
    have hred : ((p : ℤ)) ^ (k + 1)
        ∣ (p : ℤ) ^ k * ((e : ℤ) * ((p : ℤ) - 1) + (U : ℤ)) := by
      obtain ⟨w, hw⟩ := hstep
      exact ⟨w - (e : ℤ) * t, by linarith⟩
    obtain ⟨w, hw⟩ := hred
    refine ⟨w, ?_⟩
    have hexp2 : ((p : ℤ)) ^ (k + 1) * w = (p : ℤ) ^ k * ((p : ℤ) * w) := by
      rw [pow_succ]
      ring
    rw [hexp2] at hw
    exact mul_left_cancel₀ hpk0 hw
  -- conclude
  intro hdvdS
  have hS0 : S ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hdvdS
  have hU0 : U ≡ 0 [MOD p] := (hSU.symm.trans hS0)
  have hdvdU : p ∣ U := (Nat.modEq_zero_iff_dvd).mp hU0
  have hdvdUZ : (p : ℤ) ∣ (U : ℤ) := Int.natCast_dvd_natCast.mpr hdvdU
  have hfinal : (p : ℤ) ∣ (e : ℤ) * ((p : ℤ) - 1) := by
    obtain ⟨w1, hw1⟩ := hkey
    obtain ⟨w2, hw2⟩ := hdvdUZ
    exact ⟨w1 - w2, by linarith⟩
  have hpZ : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_mul.mp hfinal with h | h
  · exact hpe (by exact_mod_cast h)
  · have h1 : (p : ℤ) ∣ 1 := by
      obtain ⟨w, hw⟩ := h
      exact ⟨1 - w, by linarith⟩
    have h2 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have h3 : p ≤ 1 := by exact_mod_cast h2
    have := hp.one_lt
    omega

end CL

end Azurite

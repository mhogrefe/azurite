/-
  **Soundness of the `n − 1` test** (Algorithm 4.1.7): every verdict is
  a proof.

  * `nMinusOneTest_eq_some_true`: a `some true` verdict proves
    `Nat.Prime n.toNat` — the Pocklington conditions established by the
    passing witness feed Corollary 4.1.4, Theorem 4.1.5, or
    Theorem 4.1.6' according to the magnitude of `F`.
  * `nMinusOneTest_eq_some_false`: a `some false` verdict proves
    compositeness — a Fermat failure (for a witness in `[2, n − 2]`,
    hence nonzero mod `n`), a nontrivial gcd, a square BLS
    discriminant, a square shifted discriminant, or a factor found by
    the bounded scan.

  The bridges are the usual two-rail pattern: `AzZMod.toZMod` transports
  the limb-level Fermat/gcd computations into `ZMod n.toNat`, `toNat_*`
  lemmas transport the arithmetic, and `certProduct` ties the factor
  list to `F`.
-/
import Azurite.AzNat.NMinusOneTest
import Azurite.AzNat.Equiv.Pratt
import Azurite.AzNat.Equiv.IsSquare
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Gcd
import Azurite.CrandallPomerance.Chapter4.Corollary_4_1_4
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_5
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_6

namespace Azurite.AzNat

open Azurite.CP

/-! ### Small bridges -/

private lemma compare_ne_gt_iff {a b : AzNat} :
    compare a b ≠ .gt ↔ a.toNat ≤ b.toNat := by
  rw [compare_eq_compare_toNat]
  constructor
  · intro h
    exact Nat.le_of_not_lt (fun hlt => h (Nat.compare_eq_gt.mpr hlt))
  · intro h hgt
    exact absurd (Nat.compare_eq_gt.mp hgt) (by omega)

private lemma compare_eq_gt_iff {a b : AzNat} :
    compare a b = .gt ↔ b.toNat < a.toNat := by
  rw [compare_eq_compare_toNat]
  exact Nat.compare_eq_gt

private lemma compare_eq_lt_iff {a b : AzNat} :
    compare a b = .lt ↔ a.toNat < b.toNat := by
  rw [compare_eq_compare_toNat]
  exact Nat.compare_eq_lt

private lemma beq_iff_toNat_eq {a b : AzNat} :
    (a == b) = true ↔ a.toNat = b.toNat := by
  rw [beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, fun h => toNat_injective h⟩

/-- `IsSquare` transfers between `ℕ` and its cast into `ℤ`. -/
private lemma isSquare_natCast_iff {k : ℕ} :
    IsSquare ((k : ℕ) : ℤ) ↔ IsSquare k := by
  constructor
  · rintro ⟨r, hr⟩
    have h := congrArg Int.natAbs hr
    rw [Int.natAbs_natCast, Int.natAbs_mul] at h
    exact ⟨r.natAbs, h⟩
  · rintro ⟨r, rfl⟩
    exact ⟨(r : ℤ), by push_cast; ring⟩

/-- The three-way discriminant bridge: our `Bool` test of
`IsSquare ((a : ℤ) − b)` by comparing the `ℕ` values. -/
private lemma isSquare_int_sub_iff {a b : ℕ} (hab : b ≤ a) :
    IsSquare ((a : ℤ) - b) ↔ IsSquare (a - b : ℕ) := by
  rw [show ((a : ℤ) - b) = ((a - b : ℕ) : ℤ) by push_cast [hab]; ring]
  exact isSquare_natCast_iff

/-! ### The witness is nonzero mod `n` -/

private lemma hybridWitness_range {n : AzNat} (hn : 214 ≤ n.toNat)
    (seed : UInt64) (i : ℕ) :
    2 ≤ (hybridWitness n seed i).toNat ∧
      (hybridWitness n seed i).toNat ≤ n.toNat - 2 := by
  unfold hybridWitness
  have hm : (n - ofNat 3).toNat = n.toNat - 3 := by
    rw [toNat_sub, toNat_ofNat]
  have hm0 : 0 < (n - ofNat 3).toNat := by omega
  set z : AzNat :=
    if i < 2 ^ 64 then
      ofLimbs (randomLimbs n.limbs.size
        (Random.mkSplitMix64 (seed + UInt64.ofNat i)) #[])
    else ofNat (i - 2 ^ 64) with hz
  have hlt : (z % (n - ofNat 3)).toNat < n.toNat - 3 := by
    rw [toNat_mod, ← hm]
    exact Nat.mod_lt _ hm0
  rw [toNat_add, toNat_ofNat]
  omega

/-! ### Stage 1: the Pocklington step -/

section Pocklington

variable {n M : AzNat} [NeZero n.toNat]

/-- The value of a residue under `toZMod` is the cast of its `val`. -/
private lemma toZMod_eq_cast_val (P : AzZMod n) :
    AzZMod.toZMod P = ((P.val.toNat : ℕ) : ZMod n.toNat) := by
  conv_lhs => rw [← AzZMod.ofAzNat_val P]
  rw [AzZMod.toZMod_ofAzNat]

/-- A `.comp` verdict from the per-factor classification yields a
nontrivial divisor of `n`. -/
private lemma gcdVerdict_comp {n x : AzNat} (hn2 : 2 ≤ n.toNat)
    (h : gcdVerdict n x = .comp) :
    ∃ g : ℕ, g ∣ n.toNat ∧ 1 < g ∧ g < n.toNat := by
  rw [gcdVerdict] at h
  by_cases h0 : (x == 0) = true
  · rw [if_pos h0] at h
    exact absurd h (by simp)
  rw [if_neg h0] at h
  by_cases h1 : (gcd (x - 1) n == n) = true
  · rw [if_pos h1] at h
    exact absurd h (by simp)
  rw [if_neg h1] at h
  by_cases h2 : (gcd (x - 1) n == 1) = true
  · rw [if_pos h2] at h
    exact absurd h (by simp)
  refine ⟨(gcd (x - 1) n).toNat, ?_, ?_, ?_⟩
  · rw [toNat_gcd]
    exact Nat.gcd_dvd_right _ _
  · have hne1 : (gcd (x - 1) n).toNat ≠ 1 := by
      intro hone
      exact h2 (beq_iff_toNat_eq.mpr (by rw [hone, toNat_one]))
    have hpos : 0 < (gcd (x - 1) n).toNat := by
      rw [toNat_gcd]
      exact Nat.gcd_pos_of_pos_right _ (by omega)
    omega
  · have hnen : (gcd (x - 1) n).toNat ≠ n.toNat := by
      intro heq
      exact h1 (beq_iff_toNat_eq.mpr heq)
    have hdvd : (gcd (x - 1) n).toNat ∣ n.toNat := by
      rw [toNat_gcd]
      exact Nat.gcd_dvd_right _ _
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- A `.pass` verdict from the per-factor classification makes
`x − 1` a unit mod `n`. -/
private lemma gcdVerdict_pass {n x : AzNat} [NeZero n.toNat]
    (h : gcdVerdict n x = .pass) :
    IsUnit (((x.toNat : ℕ) : ZMod n.toNat) - 1) := by
  rw [gcdVerdict] at h
  by_cases h0 : (x == 0) = true
  · -- `x = 0`: the difference is `−1`
    rw [beq_iff_toNat_eq.mp h0, toNat_zero]
    simp only [Nat.cast_zero, zero_sub]
    exact isUnit_one.neg
  rw [if_neg h0] at h
  by_cases h1 : (gcd (x - 1) n == n) = true
  · rw [if_pos h1] at h
    exact absurd h (by simp)
  rw [if_neg h1] at h
  by_cases h2 : (gcd (x - 1) n == 1) = true
  · -- `gcd(x − 1, n) = 1`: coprime, hence a unit
    have hg : (gcd (x - 1) n).toNat = 1 :=
      beq_iff_toNat_eq.mp h2 |>.trans toNat_one
    rw [toNat_gcd, toNat_sub, toNat_one] at hg
    have hx1 : 1 ≤ x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h' | h'
      · exact absurd (beq_iff_toNat_eq.mpr (by rw [h', toNat_zero])) h0
      · exact h'
    have hunit : IsUnit (((x.toNat - 1 : ℕ)) : ZMod n.toNat) :=
      (ZMod.isUnit_iff_coprime _ _).mpr hg
    rw [show ((x.toNat : ℕ) : ZMod n.toNat) - 1
      = ((x.toNat - 1 : ℕ) : ZMod n.toNat) by push_cast [hx1]; ring]
    exact hunit
  · rw [if_neg h2] at h
    exact absurd h (by simp)

/-- A `.comp` verdict from the gcd loop yields a nontrivial divisor. -/
private lemma pocklingtonGcds_comp {a : AzZMod n} (hn2 : 2 ≤ n.toNat) :
    ∀ {qs : List AzNat}, pocklingtonGcds n M a qs = .comp →
      ∃ g : ℕ, g ∣ n.toNat ∧ 1 < g ∧ g < n.toNat := by
  intro qs
  induction qs with
  | nil => intro h; simp [pocklingtonGcds] at h
  | cons q rest ih =>
    intro h
    rw [pocklingtonGcds] at h
    cases hv : gcdVerdict n (a.powAzNat (M / q)).val with
    | pass => rw [hv] at h; exact ih h
    | retry => rw [hv] at h; exact absurd h (by simp)
    | comp => exact gcdVerdict_comp hn2 hv

/-- A `.pass` verdict from the gcd loop establishes the unit conditions
for every listed factor. -/
private lemma pocklingtonGcds_pass {a : AzZMod n} :
    ∀ {qs : List AzNat}, pocklingtonGcds n M a qs = .pass →
      ∀ q ∈ qs, IsUnit ((AzZMod.toZMod a) ^ ((M / q).toNat)
        - (1 : ZMod n.toNat)) := by
  intro qs
  induction qs with
  | nil => intro _ q hq; exact absurd hq List.not_mem_nil
  | cons q rest ih =>
    intro h q' hq'
    rw [pocklingtonGcds] at h
    cases hv : gcdVerdict n (a.powAzNat (M / q)).val with
    | pass =>
      rw [hv] at h
      rcases List.mem_cons.mp hq' with rfl | hq''
      · have := gcdVerdict_pass hv
        rwa [← toZMod_eq_cast_val, AzZMod.toZMod_powAzNat] at this
      · exact ih h q' hq''
    | retry => rw [hv] at h; exact absurd h (by simp)
    | comp => rw [hv] at h; exact absurd h (by simp)

/-- A `.comp` verdict from a witness in `(0, n)` proves compositeness. -/
private lemma pocklingtonStep_comp {factors : List AzNat} {a : AzNat}
    (hM : M.toNat = n.toNat - 1) (hn2 : 2 ≤ n.toNat)
    (ha : 0 < a.toNat) (ha' : a.toNat < n.toNat)
    (h : pocklingtonStep n M factors a = .comp) : ¬Nat.Prime n.toNat := by
  intro hprime
  rw [pocklingtonStep] at h
  by_cases hferm : (AzZMod.ofAzNat n a).powAzNat M == 1
  · rw [if_pos hferm] at h
    obtain ⟨g, hg, hg1, hgn⟩ := pocklingtonGcds_comp hn2 h
    rcases (hprime.eq_one_or_self_of_dvd g hg) with h' | h' <;> omega
  · rw [if_neg hferm] at h
    apply hferm
    rw [beq_iff_eq]
    apply AzZMod.toZMod_injective
    haveI : Fact (Nat.Prime n.toNat) := ⟨hprime⟩
    rw [AzZMod.toZMod_powAzNat, AzZMod.toZMod_ofAzNat, AzZMod.toZMod_one, hM]
    have hb0 : ((a.toNat : ℕ) : ZMod n.toNat) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd ha hdvd
      omega
    exact ZMod.pow_card_sub_one_eq_one hb0

/-- A `.pass` verdict establishes the Pocklington data for the witness. -/
private lemma pocklingtonStep_pass {factors : List AzNat} {a : AzNat}
    (h : pocklingtonStep n M factors a = .pass) :
    (AzZMod.toZMod (AzZMod.ofAzNat n a)) ^ (M.toNat) = 1 ∧
      ∀ q ∈ factors, IsUnit ((AzZMod.toZMod (AzZMod.ofAzNat n a))
        ^ ((M / q).toNat) - (1 : ZMod n.toNat)) := by
  rw [pocklingtonStep] at h
  by_cases hferm : (AzZMod.ofAzNat n a).powAzNat M == 1
  · rw [if_pos hferm] at h
    refine ⟨?_, pocklingtonGcds_pass h⟩
    have := beq_iff_eq.mp hferm
    have := congrArg AzZMod.toZMod this
    rwa [AzZMod.toZMod_powAzNat, AzZMod.toZMod_one] at this
  · rw [if_neg hferm] at h
    exact absurd h (by simp)

end Pocklington

/-! ### The KP divisor scan -/

private lemma kpDivisorScan_spec {n F F3 : AzNat}
    (hF3 : F3.toNat = F.toNat ^ 3) :
    ∀ (fuel : ℕ) (x : AzNat),
      kpDivisorScan n F F3 x fuel = true ↔
        ∃ k < fuel, 3 * (x.toNat + k) * F.toNat ^ 3 < n.toNat ∧
          ((x.toNat + k) * F.toNat + 1) ∣ n.toNat := by
  intro fuel
  induction fuel with
  | zero => intro x; simp [kpDivisorScan]
  | succ fuel ih =>
    intro x
    rw [kpDivisorScan]
    have hguard : (compare (ofNat 3 * (x * F3)) n = .lt) ↔
        3 * x.toNat * F.toNat ^ 3 < n.toNat := by
      rw [compare_eq_lt_iff, toNat_mul, toNat_mul, toNat_ofNat, hF3,
        Nat.mul_assoc]
    split_ifs with hg hd
    · -- found a divisor at `x`
      simp only [true_iff]
      refine ⟨0, by omega, ?_, ?_⟩
      · rw [Nat.add_zero]
        exact hguard.mp hg
      · rw [Nat.add_zero]
        have := beq_iff_toNat_eq.mp hd
        rw [toNat_mod, toNat_zero, toNat_add, toNat_mul, toNat_one] at this
        exact Nat.dvd_of_mod_eq_zero this
    · -- keep scanning
      rw [ih]
      have hx1 : (x + 1).toNat = x.toNat + 1 := by
        rw [toNat_add, toNat_one]
      constructor
      · rintro ⟨k, hk, hlt, hdvd⟩
        refine ⟨k + 1, by omega, ?_, ?_⟩
        · have he : x.toNat + (k + 1) = (x + 1).toNat + k := by omega
          rw [he]
          exact hlt
        · have he : x.toNat + (k + 1) = (x + 1).toNat + k := by omega
          rw [he]
          exact hdvd
      · rintro ⟨k, hk, hlt, hdvd⟩
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · exfalso
          apply hd
          rw [beq_iff_toNat_eq, toNat_mod, toNat_zero, toNat_add, toNat_mul,
            toNat_one]
          rw [Nat.add_zero] at hdvd
          exact Nat.mod_eq_zero_of_dvd hdvd
        · refine ⟨k - 1, by omega, ?_, ?_⟩
          · have he : (x + 1).toNat + (k - 1) = x.toNat + k := by omega
            rw [he]
            exact hlt
          · have he : (x + 1).toNat + (k - 1) = x.toNat + k := by omega
            rw [he]
            exact hdvd
    · -- guard failed: `3xF³ ≥ n`, and the quantity grows with `x`
      simp only [false_iff]
      rintro ⟨k, hk, hlt, hdvd⟩
      apply hg
      rw [hguard]
      have hmono : 3 * x.toNat * F.toNat ^ 3
          ≤ 3 * (x.toNat + k) * F.toNat ^ 3 := by
        have : 3 * x.toNat ≤ 3 * (x.toNat + k) := by omega
        exact Nat.mul_le_mul_right _ this
      omega

/-! ### Stages 2–4: the magnitude dispatch -/

/-- The `Bool` discriminant test decides `IsSquare` of the `ℤ` value
`s − c`, comparing in `ℕ`. -/
private lemma discTest_iff {s c : ℕ} {sa ca : AzNat}
    (hs : sa.toNat = s) (hc : ca.toNat = c) :
    ((if compare sa ca = .gt then isSquare (sa - ca)
      else sa == ca) = true) ↔ IsSquare ((s : ℤ) - c) := by
  split_ifs with hgt
  · have hlt : c < s := by
      have := compare_eq_gt_iff.mp hgt
      omega
    rw [isSquare_eq_true_iff, toNat_sub, hs, hc, isSquare_int_sub_iff hlt.le]
  · have hle : s ≤ c := by
      by_contra hgt'
      exact hgt (compare_eq_gt_iff.mpr (by omega))
    constructor
    · intro h
      have := beq_iff_toNat_eq.mp h
      rw [hs, hc] at this
      exact ⟨0, by push_cast [this]; ring⟩
    · rintro ⟨r, hr⟩
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · rw [beq_iff_toNat_eq, hs, hc, heq]
      · exact absurd ⟨r, hr⟩
          (_root_.not_isSquare_of_neg (by omega))

/-- Under the validated context, the magnitude dispatch decides
primality. -/
private lemma nm1Magnitude_iff {n F : AzNat} {R : ℕ}
    (hn : 214 ≤ n.toNat) (hsplit : n.toNat - 1 = F.toNat * R)
    (b : ZMod n.toNat) (hb : b ^ (n.toNat - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F.toNat →
      IsUnit (b ^ ((n.toNat - 1) / q) - 1))
    (hlo : n.toNat ^ 3 ≤ F.toNat ^ 10) :
    nm1Magnitude n F = true ↔ Nat.Prime n.toNat := by
  have hn1 : 1 < n.toNat := by omega
  have hF2 : 2 ≤ F.toNat := by
    by_contra h
    have h1 : F.toNat ^ 10 ≤ 1 := by
      have hF1 : F.toNat ≤ 1 := by omega
      calc F.toNat ^ 10 ≤ 1 ^ 10 := Nat.pow_le_pow_left hF1 10
      _ = 1 := one_pow 10
    have h2 : 214 ^ 3 ≤ n.toNat ^ 3 := Nat.pow_le_pow_left hn 3
    norm_num at h2
    omega
  rw [nm1Magnitude]
  have hF2sq : (square F).toNat = F.toNat ^ 2 := toNat_square F
  by_cases hs2 : compare n (square F) ≠ .gt
  · -- stage 2: `n ≤ F²`, Pocklington's corollary
    rw [if_pos hs2]
    simp only [true_iff]
    have hFn : n.toNat ≤ F.toNat ^ 2 := by
      have := compare_ne_gt_iff.mp hs2
      omega
    exact corollary_4_1_4 hn1 hsplit b hb hunit hFn
  · rw [if_neg hs2]
    have hhi : F.toNat ^ 2 < n.toNat := by
      by_contra hno
      exact hs2 (fun hg => absurd (compare_eq_gt_iff.mp hg) (by omega))
    have hF0 : 0 < F.toNat := by omega
    have hFdvd : F.toNat ∣ n.toNat - 1 := ⟨R, hsplit⟩
    have hmval : ((n - 1) / F).toNat = (n.toNat - 1) / F.toNat := by
      rw [toNat_div, toNat_sub, toNat_one]
    set m := (n - 1) / F with hm
    set c₁ := m % F with hc₁
    set chi := m / F with hchi
    have hc1val : c₁.toNat = (n.toNat - 1) / F.toNat % F.toNat := by
      rw [hc₁, toNat_mod, hmval]
    have hchival : chi.toNat = (n.toNat - 1) / F.toNat / F.toNat := by
      rw [hchi, toNat_div, hmval]
    have hc1lt : c₁.toNat < F.toNat := by
      rw [hc1val]
      exact Nat.mod_lt _ hF0
    have hrep : n.toNat
        = chi.toNat * F.toNat ^ 2 + c₁.toNat * F.toNat + 1 := by
      have hd1 : F.toNat * ((n.toNat - 1) / F.toNat) = n.toNat - 1 :=
        Nat.mul_div_cancel' hFdvd
      have hd2 := Nat.div_add_mod ((n.toNat - 1) / F.toNat) F.toNat
      have hd3 : F.toNat * ((n.toNat - 1) / F.toNat)
          = F.toNat * (F.toNat * ((n.toNat - 1) / F.toNat / F.toNat)
            + (n.toNat - 1) / F.toNat % F.toNat) := by
        rw [hd2]
      rw [hc1val, hchival]
      have hexp : F.toNat * (F.toNat * ((n.toNat - 1) / F.toNat / F.toNat)
          + (n.toNat - 1) / F.toNat % F.toNat)
          = (n.toNat - 1) / F.toNat / F.toNat * F.toNat ^ 2
            + (n.toNat - 1) / F.toNat % F.toNat * F.toNat := by ring
      omega
    have h4chi : (ofNat 4 * chi).toNat = 4 * chi.toNat := by
      rw [toNat_mul, toNat_ofNat]
    by_cases hs3 : compare n (square F * F) ≠ .gt
    · -- stage 3: `F² < n ≤ F³`, BLS
      rw [if_pos hs3]
      have hF3n : n.toNat ≤ F.toNat ^ 3 := by
        have := compare_ne_gt_iff.mp hs3
        rw [toNat_mul, hF2sq] at this
        calc n.toNat ≤ F.toNat ^ 2 * F.toNat := this
        _ = F.toNat ^ 3 := by ring
      rw [theorem_4_1_5 hn1 hsplit b hb hunit hF3n hhi hc1lt hrep]
      -- our Bool is the pointwise negation of the disc test
      have hd := discTest_iff (toNat_square c₁) h4chi
      have hcast : ((c₁.toNat ^ 2 : ℕ) : ℤ) - ((4 * chi.toNat : ℕ) : ℤ)
          = ((c₁.toNat : ℤ)) ^ 2 - 4 * (chi.toNat : ℤ) := by
        push_cast
        ring
      rw [hcast] at hd
      have hpush : (if compare (square c₁) (ofNat 4 * chi) = .gt then
          !isSquare (square c₁ - ofNat 4 * chi)
        else !(square c₁ == ofNat 4 * chi))
          = !(if compare (square c₁) (ofNat 4 * chi) = .gt then
            isSquare (square c₁ - ofNat 4 * chi)
          else square c₁ == ofNat 4 * chi) := by
        split_ifs <;> rfl
      rw [hpush, Bool.not_eq_true']
      constructor
      · intro hf hsq
        rw [← hd] at hsq
        rw [hsq] at hf
        exact Bool.noConfusion hf
      · intro hns
        rcases Bool.eq_false_or_eq_true (if compare (square c₁)
            (ofNat 4 * chi) = .gt then isSquare (square c₁ - ofNat 4 * chi)
          else square c₁ == ofNat 4 * chi) with ht | hf
        · exact absurd (hd.mp ht) hns
        · exact hf
    · -- stage 4: `F³ < n`, Konyagin–Pomerance
      rw [if_neg hs3]
      have hF3n : F.toNat ^ 3 < n.toNat := by
        by_contra hno
        apply hs3
        intro hg
        have := compare_eq_gt_iff.mp hg
        rw [toNat_mul, hF2sq] at this
        have h3 : F.toNat ^ 3 < n.toNat := by
          calc F.toNat ^ 3 = F.toNat ^ 2 * F.toNat := by ring
          _ < n.toNat := this
        omega
      rw [theorem_4_1_6' hn hsplit b hb hunit hF3n hlo hc1lt hrep]
      -- per-`t` value bridge
      have htval : ∀ t : ℕ,
          ((square (c₁ + ofNat t * F) + ofNat (4 * t))).toNat
            = (c₁.toNat + t * F.toNat) ^ 2 + 4 * t := by
        intro t
        rw [toNat_add, toNat_square, toNat_add, toNat_mul, toNat_ofNat,
          toNat_ofNat]
      have htcast : ∀ t : ℕ,
          (((c₁.toNat + t * F.toNat) ^ 2 + 4 * t : ℕ) : ℤ)
            - ((4 * chi.toNat : ℕ) : ℤ)
          = ((c₁.toNat : ℤ) + t * F.toNat) ^ 2 + 4 * t
            - 4 * chi.toNat := by
        intro t
        push_cast
        ring
      have hdisc : ∀ t : ℕ,
          ((if compare (square (c₁ + ofNat t * F) + ofNat (4 * t))
              (ofNat 4 * chi) = .gt then
            isSquare (square (c₁ + ofNat t * F) + ofNat (4 * t)
              - ofNat 4 * chi)
          else square (c₁ + ofNat t * F) + ofNat (4 * t)
            == ofNat 4 * chi) = true) ↔
          IsSquare (((c₁.toNat : ℤ) + t * F.toNat) ^ 2 + 4 * t
            - 4 * chi.toNat) := by
        intro t
        rw [discTest_iff (htval t) h4chi, htcast t]
      -- condition (1) as a Bool
      have hbad1 : ((List.range 6).any (fun t =>
          if compare (square (c₁ + ofNat t * F) + ofNat (4 * t))
              (ofNat 4 * chi) = .gt then
            isSquare (square (c₁ + ofNat t * F) + ofNat (4 * t)
              - ofNat 4 * chi)
          else square (c₁ + ofNat t * F) + ofNat (4 * t)
            == ofNat 4 * chi) = true) ↔
          ∃ t : ℕ, t ≤ 5 ∧ IsSquare (((c₁.toNat : ℤ) + t * F.toNat) ^ 2
            + 4 * t - 4 * chi.toNat) := by
        rw [List.any_eq_true]
        constructor
        · rintro ⟨t, htmem, htsq⟩
          exact ⟨t, by have := List.mem_range.mp htmem; omega,
            (hdisc t).mp htsq⟩
        · rintro ⟨t, ht5, htsq⟩
          exact ⟨t, List.mem_range.mpr (by omega), (hdisc t).mpr htsq⟩
      -- the divisor scan spec
      have hF3val : (square F * F).toNat = F.toNat ^ 3 := by
        rw [toNat_mul, hF2sq]
        ring
      have hscan_iff : kpDivisorScan n F (square F * F) 1
          ((n / (ofNat 3 * (square F * F))).toNat + 1) = true ↔
          ∃ x : ℕ, 0 < x ∧ 3 * x * F.toNat ^ 3 < n.toNat ∧
            (x * F.toNat + 1) ∣ n.toNat := by
        rw [kpDivisorScan_spec hF3val]
        constructor
        · rintro ⟨k, hk, hlt, hdvd⟩
          refine ⟨1 + k, by omega, ?_, ?_⟩
          · rw [toNat_one] at hlt
            exact hlt
          · rw [toNat_one] at hdvd
            exact hdvd
        · rintro ⟨x, hx0, hxlt, hxdvd⟩
          refine ⟨x - 1, ?_, ?_, ?_⟩
          · have h3F0 : 0 < 3 * F.toNat ^ 3 := by positivity
            have hxle : x * (3 * F.toNat ^ 3) ≤ n.toNat := by
              calc x * (3 * F.toNat ^ 3) = 3 * x * F.toNat ^ 3 := by ring
              _ ≤ n.toNat := hxlt.le
            have := (Nat.le_div_iff_mul_le h3F0).mpr hxle
            have hdivval : (n / (ofNat 3 * (square F * F))).toNat
                = n.toNat / (3 * F.toNat ^ 3) := by
              rw [toNat_div, toNat_mul, toNat_ofNat, hF3val]
            omega
          · rw [toNat_one]
            have he : 1 + (x - 1) = x := by omega
            rw [he]
            exact hxlt
          · rw [toNat_one]
            have he : 1 + (x - 1) = x := by omega
            rw [he]
            exact hxdvd
      -- assemble
      rcases Bool.eq_false_or_eq_true ((List.range 6).any (fun t =>
          if compare (square (c₁ + ofNat t * F) + ofNat (4 * t))
              (ofNat 4 * chi) = .gt then
            isSquare (square (c₁ + ofNat t * F) + ofNat (4 * t)
              - ofNat 4 * chi)
          else square (c₁ + ofNat t * F) + ofNat (4 * t)
            == ofNat 4 * chi)) with h1 | h1
      · -- condition (1) FAILS: some discriminant is a square
        rw [h1]
        simp only [if_true]
        constructor
        · intro h
          exact absurd h (by simp)
        · rintro ⟨hcond1, -⟩
          obtain ⟨t, ht5, htsq⟩ := hbad1.mp h1
          exact absurd htsq (hcond1 t ht5)
      · rw [h1]
        simp only [Bool.false_eq_true, if_false, Bool.not_eq_true']
        have hcond1 : ∀ t : ℕ, t ≤ 5 →
            ¬IsSquare (((c₁.toNat : ℤ) + t * F.toNat) ^ 2 + 4 * t
              - 4 * chi.toNat) := by
          intro t ht5 hsq
          have : ((List.range 6).any _) = true := hbad1.mpr ⟨t, ht5, hsq⟩
          rw [h1] at this
          exact Bool.noConfusion this
        constructor
        · intro hscan_false
          refine ⟨hcond1, ?_⟩
          rintro ⟨x, hx0, hxlt, hxdvd⟩
          have := hscan_iff.mpr ⟨x, hx0, hxlt, hxdvd⟩
          rw [hscan_false] at this
          exact Bool.noConfusion this
        · rintro ⟨-, hnoexists⟩
          rcases Bool.eq_false_or_eq_true (kpDivisorScan n F (square F * F) 1
              ((n / (ofNat 3 * (square F * F))).toNat + 1)) with ht | hf
          · exact absurd (hscan_iff.mp ht) hnoexists
          · exact hf

/-! ### The witness loop and the main theorems -/

/-- Soundness of the witness loop: under the validated context, any
`some` verdict is correct. -/
private lemma nm1Loop_sound {n M F : AzNat} [NeZero n.toNat]
    {qlist : List AzNat} {seed : UInt64} {R : ℕ}
    (hn : 214 ≤ n.toNat) (hM : M.toNat = n.toNat - 1)
    (hsplit : n.toNat - 1 = F.toNat * R)
    (hcover : ∀ p : ℕ, p.Prime → p ∣ F.toNat →
      ∃ q ∈ qlist, q.toNat = p)
    (hlo : n.toNat ^ 3 ≤ F.toNat ^ 10) :
    ∀ (i fuel : ℕ) (v : Bool),
      nm1Loop n M F qlist seed i fuel = some v →
      (v = true ↔ Nat.Prime n.toNat) := by
  intro i fuel
  induction fuel generalizing i with
  | zero => intro v hv; rw [nm1Loop] at hv; exact absurd hv (by simp)
  | succ fuel ih =>
    intro v hv
    rw [nm1Loop] at hv
    have hrange := hybridWitness_range hn seed i
    cases hstep : pocklingtonStep n M qlist (hybridWitness n seed i) with
    | comp =>
      rw [hstep] at hv
      have hcomp := pocklingtonStep_comp hM (by omega) (by omega) (by omega)
        hstep
      simp only [Option.some_inj] at hv
      constructor
      · intro htrue
        rw [htrue] at hv
        exact Bool.noConfusion hv
      · intro hprime
        exact absurd hprime hcomp
    | retry =>
      rw [hstep] at hv
      exact ih (i + 1) v hv
    | pass =>
      rw [hstep] at hv
      simp only [Option.some_inj] at hv
      obtain ⟨hferm, hunits⟩ := pocklingtonStep_pass hstep
      -- upgrade the per-list conditions to all prime divisors of `F`
      set b := AzZMod.toZMod (AzZMod.ofAzNat n (hybridWitness n seed i))
        with hbdef
      have hb : b ^ (n.toNat - 1) = 1 := by
        rw [← hM]
        exact hferm
      have hunit : ∀ p : ℕ, p.Prime → p ∣ F.toNat →
          IsUnit (b ^ ((n.toNat - 1) / p) - 1) := by
        intro p hp hpF
        obtain ⟨q, hqmem, hqval⟩ := hcover p hp hpF
        have := hunits q hqmem
        rwa [toNat_div, hM, hqval] at this
      have := nm1Magnitude_iff hn hsplit b hb hunit hlo
      rw [← hv]
      exact this

/-- Unpack the validation and feed the loop-soundness lemma. -/
private lemma nMinusOneTest_sound {n : AzNat} {factors : List (AzNat × ℕ)}
    {attempts : ℕ} {seed : UInt64} {v : Bool}
    (h : nMinusOneTest n factors attempts seed = some v) :
    v = true ↔ Nat.Prime n.toNat := by
  rw [nMinusOneTest] at h
  by_cases h214 : 214 ≤ n.toNat
  · rw [dif_pos h214] at h
    haveI : NeZero n.toNat := ⟨by omega⟩
    by_cases hcheck : (factors.all (fun qe => isPrime qe.1)
        && (n - 1) % certProduct factors == 0
        && (decide (compare (pow n 3)
            (pow (certProduct factors) 10) ≠ .gt))) = true
    · rw [if_pos hcheck] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hcheck
      obtain ⟨⟨hprimes, hmod⟩, hcmp⟩ := hcheck
      -- the validated context
      have hM : (n - 1).toNat = n.toNat - 1 := by
        rw [toNat_sub, toNat_one]
      have hFval : (certProduct factors).toNat
          = (factors.map (fun qe => qe.1.toNat ^ qe.2)).prod :=
        toNat_certProduct factors
      have hdvd : (certProduct factors).toNat ∣ n.toNat - 1 := by
        have := beq_iff_toNat_eq.mp hmod
        rw [toNat_mod, toNat_zero, hM] at this
        exact Nat.dvd_of_mod_eq_zero this
      have hsplit : n.toNat - 1
          = (certProduct factors).toNat
            * ((n.toNat - 1) / (certProduct factors).toNat) :=
        (Nat.mul_div_cancel' hdvd).symm
      have hlo : n.toNat ^ 3 ≤ (certProduct factors).toNat ^ 10 := by
        have := compare_ne_gt_iff.mp hcmp
        rwa [toNat_pow, toNat_pow] at this
      -- every prime divisor of `F` is a listed base
      have hcover : ∀ p : ℕ, p.Prime → p ∣ (certProduct factors).toNat →
          ∃ q ∈ factors.map (·.1), q.toNat = p := by
        intro p hp hpF
        rw [hFval] at hpF
        obtain ⟨x, hxmem, hpx⟩ := (Prime.dvd_prod_iff hp.prime).mp hpF
        obtain ⟨qe, hqe, rfl⟩ := List.mem_map.mp hxmem
        have hqprime : Nat.Prime qe.1.toNat :=
          (isPrime_eq_true_iff _).mp (hprimes qe hqe)
        have hpq : p = qe.1.toNat :=
          (Nat.prime_dvd_prime_iff_eq hp hqprime).mp (hp.dvd_of_dvd_pow hpx)
        exact ⟨qe.1, List.mem_map.mpr ⟨qe, hqe, rfl⟩, hpq.symm⟩
      exact nm1Loop_sound h214 hM hsplit hcover hlo 0 attempts v h
    · rw [if_neg hcheck] at h
      exact absurd h (by simp)
  · rw [dif_neg h214] at h
    exact absurd h (by simp)

/-- **A `some true` verdict of the `n − 1` test is a primality proof.** -/
theorem nMinusOneTest_eq_some_true {n : AzNat}
    {factors : List (AzNat × ℕ)} {attempts : ℕ} {seed : UInt64}
    (h : nMinusOneTest n factors attempts seed = some true) :
    Nat.Prime n.toNat :=
  (nMinusOneTest_sound h).mp rfl

/-- **A `some false` verdict of the `n − 1` test is a compositeness
proof.** -/
theorem nMinusOneTest_eq_some_false {n : AzNat}
    {factors : List (AzNat × ℕ)} {attempts : ℕ} {seed : UInt64}
    (h : nMinusOneTest n factors attempts seed = some false) :
    ¬Nat.Prime n.toNat := by
  intro hp
  exact absurd ((nMinusOneTest_sound h).mpr hp) (by simp)

end Azurite.AzNat

/-
  Crandall–Pomerance, Theorem 4.2.6: **the Lucas–Lehmer test**.  With
  `v_0 = 4`, `v_{k+1} = v_k² − 2`, and `p` an odd prime, the Mersenne
  number `M_p = 2^p − 1` is prime IF AND ONLY IF `v_{p−2} ≡ 0 (mod M_p)`.

  We state the result with Mathlib's `LucasLehmer.s` (which is exactly
  `(v_k)`) and `mersenne`.  Mathlib itself proves only the sufficiency
  direction (`lucas_lehmer_sufficiency`); both directions here are
  derived from our Theorem 4.2.5, following the book — in particular
  the NECESSITY direction is new relative to Mathlib.

  Take `f(x) = x² − 4x + 1`, so `Δ = 12`, and note
  `V_{2^k}(4, 1) = v_k` by the `V`-doubling formula (`b = 1`!).  Since
  `M_p ≡ 3 (mod 4)` and `M_p ≡ 1 (mod 3)`, Jacobi reciprocity gives
  `(12/M_p) = −1`.

  Sufficiency: apply Theorem 4.2.5 with `F = 2^(p−1) = (M_p + 1)/2`;
  conditions (4.15) reduce to `V_{2^(p−2)} = v_{p−2} ≡ 0` — `F` has no
  odd prime factors.

  Necessity: with `M = M_p` prime, work in `K = 𝔽_M[x]/(f) = GF(M²)`,
  `α` the image of `x`, `β = 4 − α = α^M` (Frobenius).  From
  `(α−1)² = 2α`, Euler's criterion for `2` (using `M ≡ 7 (mod 8)`), and
  `(α−1)^(M+1) = (α−1)(α^M−1) = (α−1)(3−α) = −2`, one gets
  `α^((M+1)/2) = −1`; likewise `β^((M+1)/2) = −1`.  Hence
  `M ∣ U_{2^(p−1)}`, while `M ∤ U_{2^(p−2)}` (else
  `−1 = α^(2^(p−1)) = (αβ)^(2^(p−2)) = 1`).  Since
  `U_{2^(p−1)} = U_{2^(p−2)} · V_{2^(p−2)}`, primality of `M` forces
  `M ∣ V_{2^(p−2)} = v_{p−2}`.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_5
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_4
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace Azurite

namespace CP

open Polynomial

/-- The Lucas–Lehmer sequence is `V` at powers of two:
`V_{2^k}(4, 1) = v_k`. -/
theorem lucasV_two_pow_eq_s (k : ℕ) :
    lucasV 4 1 (2 ^ k) = LucasLehmer.s k := by
  induction k with
  | zero =>
    rw [pow_zero, lucasV_one, LucasLehmer.s]
  | succ k ih =>
    rw [pow_succ, mul_comm, lucasV_two_mul, ih, one_pow, LucasLehmer.s]
    ring

/-- `(12/M) = −1` whenever `M ≡ 3 (mod 4)` and `M ≡ 1 (mod 3)`. -/
theorem jacobiSym_twelve {M : ℕ} (h4 : M % 4 = 3) (h3 : M % 3 = 1) :
    jacobiSym 12 M = -1 := by
  have hModd : M % 2 = 1 := by omega
  have h2gcd : Int.gcd 2 M = 1 := by
    have : Nat.gcd 2 M = 1 := Nat.coprime_two_left.mpr
      (Nat.odd_iff.mpr hModd)
    simpa [Int.gcd] using this
  rw [show (12 : ℤ) = 3 * 2 ^ 2 by norm_num, jacobiSym.mul_left,
    jacobiSym.sq_one' h2gcd, mul_one,
    show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num,
    jacobiSym.quadratic_reciprocity_three_mod_four (by norm_num) h4,
    jacobiSym.mod_left ((M : ℕ) : ℤ) 3,
    show ((M : ℕ) : ℤ) % ((3 : ℕ) : ℤ) = 1 by omega, jacobiSym.one_left]

section OddPrime

variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)

include hp hp2

/-- Arithmetic of `M_p` for odd prime `p`: sizes and residues. -/
private theorem mersenne_facts :
    7 ≤ mersenne p ∧ mersenne p % 2 = 1 ∧ mersenne p % 4 = 3 ∧
      mersenne p % 8 = 7 ∧ mersenne p % 3 = 1 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp2
    · exact h
  have h8 : (8 : ℕ) ∣ 2 ^ p := ⟨2 ^ (p - 3), by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega⟩
  have h2p8 : 8 ≤ 2 ^ p := Nat.le_of_dvd (by positivity) h8
  -- `2^p ≡ 2 (mod 3)` for odd `p`
  have h3' : 2 ^ p % 3 = 2 := by
    obtain ⟨t, ht⟩ : ∃ t, p = 2 * t + 1 :=
      ⟨p / 2, by
        have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
        omega⟩
    have h4t : 4 ^ t % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [ht, pow_succ, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num,
      Nat.mul_mod, h4t]
  rw [mersenne]
  obtain ⟨s, hs⟩ := h8
  omega

/-- **Sufficiency**: if `M_p ∣ v_{p−2}`, then `M_p` is prime — by
Morrison's `V`-test with `F = 2^(p−1)`. -/
theorem mersenne_prime_of_s (hdvd : (mersenne p : ℤ) ∣ LucasLehmer.s (p - 2)) :
    (mersenne p).Prime := by
  obtain ⟨hM7, hM2, hM4, hM8, hM3⟩ := mersenne_facts hp hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp2
    · exact h
  have hMsucc : mersenne p + 1 = 2 ^ p := succ_mersenne p
  refine morrison_test_V (a := 4) (b := 1) (F := 2 ^ (p - 1))
    (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- coprime to `2·1 = 2`
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.gcd (mersenne p) 2 = 1 :=
      Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hM2)
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · rw [show ((4 : ℤ) ^ 2 - 4 * 1) = 12 by norm_num]
    exact jacobiSym_twelve hM4 hM3
  · rw [hMsucc]
    exact pow_dvd_pow 2 (by omega)
  · exact dvd_pow_self 2 (by omega)
  · have hidx : 2 ^ (p - 1) / 2 = 2 ^ (p - 2) := by
      rw [show p - 1 = (p - 2) + 1 by omega, pow_succ]
      exact Nat.mul_div_cancel _ (by norm_num)
    rw [hidx, lucasV_two_pow_eq_s]
    exact hdvd
  · intro q hq hq2 hqF
    exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      (hq.dvd_of_dvd_pow hqF)) hq2
  · -- `M_p < (2^(p−1) − 1)²`
    set X := 2 ^ (p - 1) with hX
    have hX4 : 4 ≤ X := by
      rw [hX, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hM : mersenne p = 2 * X - 1 := by
      rw [mersenne, hX, ← pow_succ']
      congr 2
      omega
    have hXX : 4 * X ≤ X * X := Nat.mul_le_mul_right X hX4
    have hexp : (X - 1) ^ 2 = X * X - 2 * X + 1 := by
      have h1 : 1 ≤ X := by omega
      zify [h1, (by omega : 2 * X ≤ X * X)]
      ring
    omega

/-- **Necessity**: if `M_p` is prime, then `M_p ∣ v_{p−2}` — the
converse direction of the Lucas–Lehmer test (absent from Mathlib). -/
theorem s_of_mersenne_prime (hM : (mersenne p).Prime) :
    (mersenne p : ℤ) ∣ LucasLehmer.s (p - 2) := by
  obtain ⟨hM7, hM2, hM4, hM8, hM3⟩ := mersenne_facts hp hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd rfl hp2
    · exact h
  have hMsucc : mersenne p + 1 = 2 ^ p := succ_mersenne p
  set M := mersenne p with hMdef
  haveI : Fact M.Prime := ⟨hM⟩
  -- `(12/M) = −1`, hence `12` is a nonsquare mod `M`
  have hleg : legendreSym M 12 = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    exact jacobiSym_twelve hM4 hM3
  have hΔ0 : ((12 : ℤ) : ZMod M) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff M 12).mpr h0] at hleg
    omega
  have hns : ¬IsSquare ((12 : ℤ) : ZMod M) := by
    intro hsq
    rw [(legendreSym.eq_one_iff (p := M) hΔ0).mpr hsq] at hleg
    omega
  -- the quadratic `x² − 4x + 1` is irreducible over `ZMod M`
  set A : ZMod M := ((4 : ℤ) : ZMod M) with hA
  set B : ZMod M := ((1 : ℤ) : ZMod M) with hB
  set g : (ZMod M)[X] := X ^ 2 - C A * X + C B with hg
  have h12AB : ((12 : ℤ) : ZMod M) = A ^ 2 - 4 * B := by
    rw [hA, hB]
    push_cast
    ring
  have hnoroot : ∀ γ : ZMod M, ¬IsRoot g γ := by
    intro γ hγ
    rw [hg, IsRoot] at hγ
    simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X] at hγ
    apply hns
    rw [h12AB]
    exact ⟨2 * γ - A, by linear_combination -4 * hγ⟩
  have hgdeg : g.natDegree = 2 := by
    rw [hg, show (X ^ 2 - C A * X + C B : (ZMod M)[X])
        = C 1 * X ^ 2 + C (-A) * X + C B by rw [map_one, map_neg]; ring]
    exact natDegree_quadratic one_ne_zero
  have hgirr : Irreducible g :=
    irreducible_of_degree_le_three_of_not_isRoot
      (by rw [hgdeg]; decide) hnoroot
  haveI : Fact (Irreducible g) := ⟨hgirr⟩
  -- the field `K = GF(M²)`
  set K := AdjoinRoot g with hK
  haveI : Module.Finite (ZMod M) K :=
    (AdjoinRoot.powerBasis hgirr.ne_zero).finite
  haveI : Finite K := Module.finite_of_finite (ZMod M)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : DecidableEq K := Classical.decEq K
  haveI : CharP K M :=
    charP_of_injective_algebraMap (algebraMap (ZMod M) K).injective M
  set α : K := AdjoinRoot.root g with hαdef
  -- the root identity in numeral form
  have hroot : α ^ 2 - algebraMap (ZMod M) K A * α
      + algebraMap (ZMod M) K B = 0 := by
    have h0 : AdjoinRoot.mk g (X ^ 2 - C A * X + C B) = 0 := by
      rw [← hg]
      exact AdjoinRoot.mk_self
    simp only [map_add, map_sub, map_pow, map_mul, AdjoinRoot.mk_X,
      AdjoinRoot.mk_C] at h0
    rw [show ((A : K)) = algebraMap (ZMod M) K A from rfl,
      show ((B : K)) = algebraMap (ZMod M) K B from rfl] at h0
    exact h0
  have hAcast : algebraMap (ZMod M) K A = ((4 : ℤ) : K) := by
    rw [hA, map_intCast]
  have hBcast : algebraMap (ZMod M) K B = ((1 : ℤ) : K) := by
    rw [hB, map_intCast]
  have hroot4 : α ^ 2 - 4 * α + 1 = 0 := by
    have h := hroot
    rw [hAcast, hBcast] at h
    push_cast at h
    exact h
  set β : K := 4 - α with hβdef
  have hsum : α + β = ((4 : ℤ) : K) := by
    rw [hβdef]
    push_cast
    ring
  have hprod : α * β = ((1 : ℤ) : K) := by
    rw [hβdef]
    push_cast
    linear_combination -hroot4
  have hsum4 : α + β = 4 := by
    rw [hβdef]
    ring
  have hprod1 : α * β = 1 := by
    rw [hβdef]
    linear_combination -hroot4
  -- Frobenius sends `α` to the conjugate root `β`
  have hquad : ∀ γ : K, γ ^ 2 - 4 * γ + 1 = (γ - α) * (γ - β) := by
    intro γ
    linear_combination γ * hsum4 - hprod1
  have hfroot : (α ^ M) ^ 2 - 4 * α ^ M + 1 = 0 := by
    have h := congrArg (frobenius K M) hroot4
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_one,
      map_ofNat] at h
    simp only [frobenius_def] at h
    exact h
  have hnotfix : α ^ M ≠ α := by
    intro hfix
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_pow_card (K := K) hfix
    apply hnoroot c
    rw [hg, IsRoot]
    simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X]
    apply (algebraMap (ZMod M) K).injective
    rw [map_zero, map_add, map_sub, map_pow, map_mul, hc, hAcast, hBcast]
    have h := hroot
    rw [hAcast, hBcast] at h
    exact h
  have hfrob : α ^ M = β := by
    have h0 := hquad (α ^ M)
    rw [hfroot] at h0
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd (sub_eq_zero.mp h) hnotfix
    · exact sub_eq_zero.mp h
  have hαβ : α - β ≠ 0 := sub_ne_zero.mpr (hfrob ▸ hnotfix ∘ Eq.symm)
  -- Euler's criterion for `2`, transported into `K`
  have h20 : (2 : ZMod M) ≠ 0 := by
    intro h0
    rw [show (2 : ZMod M) = ((2 : ℕ) : ZMod M) by push_cast; ring,
      ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by norm_num) h0
    omega
  have hsq2 : IsSquare (2 : ZMod M) :=
    (ZMod.exists_sq_eq_two_iff (by omega)).mpr (Or.inr hM8)
  have hEuler : (2 : ZMod M) ^ ((M - 1) / 2) = 1 := by
    have h := (ZMod.euler_criterion M h20).mp hsq2
    rwa [show M / 2 = (M - 1) / 2 by omega] at h
  have h2K : (2 : K) = algebraMap (ZMod M) K (2 : ZMod M) := by
    rw [map_ofNat]
  have h2K0 : (2 : K) ≠ 0 := by
    rw [h2K]
    intro h0
    exact h20 ((algebraMap (ZMod M) K).injective (by rw [h0, map_zero]))
  have hEulerK : (2 : K) ^ ((M - 1) / 2) = 1 := by
    rw [h2K, ← map_pow, hEuler, map_one]
  -- the two evaluations of `(α − 1)^(M+1)`
  have hsq2α : (α - 1) ^ 2 = 2 * α := by
    linear_combination hroot4
  have hway1 : (α - 1) ^ (M + 1) = 2 * α ^ ((M + 1) / 2) := by
    calc (α - 1) ^ (M + 1) = ((α - 1) ^ 2) ^ ((M + 1) / 2) := by
          rw [← pow_mul]
          congr 1
          omega
    _ = 2 ^ ((M + 1) / 2) * α ^ ((M + 1) / 2) := by
        rw [hsq2α, mul_pow]
    _ = (2 ^ ((M - 1) / 2) * 2) * α ^ ((M + 1) / 2) := by
        rw [← pow_succ]
        congr 2
        omega
    _ = 2 * α ^ ((M + 1) / 2) := by
        rw [hEulerK]
        ring
  have hway2 : (α - 1) ^ (M + 1) = -2 := by
    calc (α - 1) ^ (M + 1) = (α - 1) ^ M * (α - 1) := by rw [← pow_succ]
    _ = (α ^ M - 1 ^ M) * (α - 1) := by rw [sub_pow_char]
    _ = (β - 1) * (α - 1) := by rw [one_pow, hfrob]
    _ = -2 := by
        rw [hβdef]
        linear_combination -hroot4
  have hαkey : α ^ ((M + 1) / 2) = -1 := by
    have h := hway1.symm.trans hway2
    have h2 : (2 : K) * α ^ ((M + 1) / 2) = 2 * (-1) := by
      rw [h]
      ring
    exact mul_left_cancel₀ h2K0 h2
  have hβkey : β ^ ((M + 1) / 2) = -1 := by
    rw [← hfrob, ← pow_right_comm, hαkey]
    exact (Nat.odd_iff.mpr hM2).neg_one_pow
  -- index bookkeeping
  have hidx1 : (M + 1) / 2 = 2 ^ (p - 1) := by
    rw [hMdef, hMsucc, show p = (p - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ (by norm_num)
  have hidx2 : 2 ^ (p - 1) = 2 * 2 ^ (p - 2) := by
    rw [show p - 1 = (p - 2) + 1 by omega, pow_succ]
    ring
  -- `M ∣ U_{2^(p−1)}` but `M ∤ U_{2^(p−2)}`
  have hUdesc : ∀ k : ℕ, α ^ k = β ^ k → (M : ℤ) ∣ lucasU 4 1 k := by
    intro k hk
    have hspec := lucasU_spec hsum hprod k
    rw [show α ^ k - β ^ k = 0 by rw [hk]; ring] at hspec
    have hU0 : ((lucasU 4 1 k : ℤ) : K) = 0 := by
      rcases mul_eq_zero.mp hspec with h | h
      · exact h
      · exact absurd h hαβ
    have : ((lucasU 4 1 k : ℤ) : ZMod M) = 0 := by
      rw [show ((lucasU 4 1 k : ℤ) : K)
          = algebraMap (ZMod M) K ((lucasU 4 1 k : ℤ) : ZMod M) from
          (map_intCast _ _).symm] at hU0
      exact (algebraMap (ZMod M) K).injective (by rw [hU0, map_zero])
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have hU1 : (M : ℤ) ∣ lucasU 4 1 (2 ^ (p - 1)) := by
    apply hUdesc
    rw [← hidx1, hαkey, hβkey]
  have hU2 : ¬(M : ℤ) ∣ lucasU 4 1 (2 ^ (p - 2)) := by
    intro hd
    have hspec := lucasU_spec hsum hprod (2 ^ (p - 2))
    have hU0 : ((lucasU 4 1 (2 ^ (p - 2)) : ℤ) : K) = 0 := by
      rw [show ((lucasU 4 1 (2 ^ (p - 2)) : ℤ) : K)
          = algebraMap (ZMod M) K ((lucasU 4 1 (2 ^ (p - 2)) : ℤ) : ZMod M)
          from (map_intCast _ _).symm,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd, map_zero]
    rw [hU0, zero_mul] at hspec
    have hk : α ^ 2 ^ (p - 2) = β ^ 2 ^ (p - 2) :=
      sub_eq_zero.mp hspec.symm
    have hone : α ^ 2 ^ (p - 1) = 1 := by
      rw [hidx2, mul_comm, pow_mul, pow_two]
      nth_rewrite 1 [hk]
      rw [show β ^ 2 ^ (p - 2) * α ^ 2 ^ (p - 2)
          = (α * β) ^ 2 ^ (p - 2) by rw [mul_pow]; ring,
        hprod1, one_pow]
    rw [← hidx1, hαkey] at hone
    have : (2 : K) = 0 := by
      linear_combination -hone
    exact h2K0 this
  -- doubling finishes it
  have hdouble : lucasU 4 1 (2 ^ (p - 1))
      = lucasU 4 1 (2 ^ (p - 2)) * lucasV 4 1 (2 ^ (p - 2)) := by
    rw [hidx2]
    exact lucasU_two_mul 4 1 (2 ^ (p - 2))
  rw [hdouble] at hU1
  rcases (Nat.prime_iff_prime_int.mp hM).dvd_mul.mp hU1 with h | h
  · exact absurd h hU2
  · rwa [lucasV_two_pow_eq_s] at h

/-- **Crandall–Pomerance Theorem 4.2.6 (the Lucas–Lehmer test)**: for
an odd prime `p`, the Mersenne number `M_p = 2^p − 1` is prime if and
only if `v_{p−2} ≡ 0 (mod M_p)`, where `v_0 = 4` and
`v_{k+1} = v_k² − 2` (Mathlib's `LucasLehmer.s`). -/
theorem theorem_4_2_6 :
    (mersenne p).Prime ↔ (mersenne p : ℤ) ∣ LucasLehmer.s (p - 2) :=
  ⟨s_of_mersenne_prime hp hp2, mersenne_prime_of_s hp hp2⟩

end OddPrime

/-- `M_7 = 127` is prime: five squarings mod `127` suffice. -/
example : (mersenne 7).Prime :=
  mersenne_prime_of_s (by decide) (by decide) (by decide)

/-- `M_11 = 2047 = 23 · 89` fails the test, so it is composite — this
uses the necessity direction. -/
example : ¬(mersenne 11).Prime := fun h =>
  absurd (s_of_mersenne_prime (by decide) (by decide) h) (by decide)

end CP

end Azurite

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Landau
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.Algorithm.Equiv.PrimeSieve
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Find

/-!
## Correctness of `AzNat.landauFunctionPrefix`

Mathlib has no Landau function, so the reference is defined here: `Nat.ell M = Σ p^{v_p(M)}`
over the prime factors of `M` (the additive function `ℓ` of Landau), and
`Nat.landau n`, the greatest `M ≥ 1` with `ℓ(M) ≤ n` (`isGreatest_landau`; the bound
`M ≤ 2^{ℓ(M)}` makes it a `Nat.findGreatest`).  The table invariant `LandauInv ps g` says that
`g[m]` is the greatest `M ≥ 1` with `ℓ(M) ≤ m` whose prime factors lie in the list `ps`
(`Smooth ps M`); it holds for the initial table and the empty list, is preserved by
`landauStep` for a new prime (`landauInv_step`, the induction relation of the paper), and for
the list of all primes up to `n` the smoothness condition is vacuous below `n`
(`landauFunctionPrefix_spec`, `toNat_landauFunctionPrefix`).
-/

namespace Nat

/-- Landau's additive function `ℓ(M) = Σ p^{v_p(M)}` over the prime factors of `M`. -/
def ell (M : ℕ) : ℕ := ∑ p ∈ M.primeFactors, p ^ M.factorization p

@[simp] theorem ell_one : ell 1 = 0 := by simp [ell]

/-- `ℓ(p^k M) = p^k + ℓ(M)` when the prime `p` does not divide `M`. -/
theorem ell_prime_pow_mul {p M k : ℕ} (hp : p.Prime) (hM : M ≠ 0) (hpM : ¬ p ∣ M)
    (hk : k ≠ 0) : ell (p ^ k * M) = p ^ k + ell M := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  have hnot : p ∉ M.primeFactors := fun h => hpM (mem_primeFactors.mp h).2.1
  have hfac : (p ^ k * M).factorization = Finsupp.single p k + M.factorization := by
    rw [factorization_mul hpk hM, hp.factorization_pow]
  unfold ell
  rw [primeFactors_mul hpk hM, primeFactors_prime_pow hk hp, Finset.singleton_union,
    Finset.sum_insert hnot, hfac]
  congr 1
  · rw [Finsupp.add_apply, Finsupp.single_eq_same, factorization_eq_zero_of_not_dvd hpM,
      add_zero]
  · apply Finset.sum_congr rfl
    intro q hq
    have hqp : q ≠ p := fun h => hnot (h ▸ hq)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hqp, zero_add]

/-- Every prime factor of `M` is at most `ℓ(M)`. -/
theorem le_ell_of_mem_primeFactors {M p : ℕ} (hp : p ∈ M.primeFactors) : p ≤ ell M := by
  have hpp := (mem_primeFactors.mp hp).1
  have hM := (mem_primeFactors.mp hp).2.2
  have hpos : M.factorization p ≠ 0 :=
    (hpp.factorization_pos_of_dvd hM (mem_primeFactors.mp hp).2.1).ne'
  calc p ≤ p ^ M.factorization p := le_self_pow hpos p
    _ ≤ ell M :=
        Finset.single_le_sum (f := fun q => q ^ M.factorization q) (fun _ _ => Nat.zero_le _) hp

/-- `M ≤ 2^{ℓ(M)}`. -/
theorem le_two_pow_ell {M : ℕ} (hM : M ≠ 0) : M ≤ 2 ^ ell M := by
  have hself : ∏ p ∈ M.primeFactors, p ^ M.factorization p = M := by
    have := prod_factorization_pow_eq_self hM
    rwa [Finsupp.prod, support_factorization] at this
  calc M = ∏ p ∈ M.primeFactors, p ^ M.factorization p := hself.symm
    _ ≤ ∏ p ∈ M.primeFactors, 2 ^ (p ^ M.factorization p) :=
        Finset.prod_le_prod (fun _ _ => Nat.lt_two_pow_self.le)
    _ = 2 ^ ell M := Finset.prod_pow_eq_pow_sum _ _ _

/-- **Landau's function** `g(n)`: the greatest `M ≥ 1` with `ℓ(M) ≤ n`. -/
def landau (n : ℕ) : ℕ := Nat.findGreatest (fun M => 0 < M ∧ ell M ≤ n) (2 ^ n)

theorem isGreatest_landau (n : ℕ) : IsGreatest {M | 0 < M ∧ ell M ≤ n} (landau n) := by
  have h1 : 0 < 1 ∧ ell 1 ≤ n := ⟨Nat.one_pos, by simp⟩
  refine ⟨Nat.findGreatest_spec (P := fun M => 0 < M ∧ ell M ≤ n) Nat.one_le_two_pow h1, ?_⟩
  intro M ⟨hM0, hM⟩
  exact Nat.le_findGreatest ((le_two_pow_ell hM0.ne').trans (Nat.pow_le_pow_right two_pos hM))
    ⟨hM0, hM⟩

end Nat

namespace Azurite.AzNat

open Nat (ell)

/-! ### Folding `max` over a list -/

theorem le_foldl_max {α : Type*} [LinearOrder α] (l : List α) (a : α) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih _)

theorem le_foldl_max_of_mem {α : Type*} [LinearOrder α] (l : List α) (a : α) {x : α}
    (hx : x ∈ l) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right a x).trans (le_foldl_max _ _)
    · exact ih _ hx

theorem foldl_max_eq_or_mem {α : Type*} [LinearOrder α] (l : List α) (a : α) :
    l.foldl max a = a ∨ l.foldl max a ∈ l := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons y ys ih =>
    rw [List.foldl_cons]
    rcases ih (max a y) with h | h
    · rw [h]
      rcases max_choice a y with h' | h'
      · exact Or.inl h'
      · right
        rw [h']
        exact List.mem_cons_self ..
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-! ### The table invariant -/

/-- All prime factors of `M` lie in the list `ps`. -/
def Smooth (ps : List ℕ) (M : ℕ) : Prop := ∀ q ∈ M.primeFactors, q ∈ ps

/-- `g[m]` is the greatest `M ≥ 1` with `ℓ(M) ≤ m` whose prime factors lie in `ps`. -/
def LandauInv (ps : List ℕ) (g : Array AzNat) : Prop :=
  ∀ m (hm : m < g.size), IsGreatest {M | 0 < M ∧ Smooth ps M ∧ ell M ≤ m} (g[m]).toNat

theorem landauInv_init (n : ℕ) : LandauInv [] (Array.replicate n 1) := by
  intro m hm
  rw [Array.getElem_replicate, toNat_one]
  refine ⟨⟨Nat.one_pos, fun q hq => by simp at hq, by simp⟩, ?_⟩
  intro M ⟨hM0, hsm, _⟩
  have : M.primeFactors = ∅ := Finset.eq_empty_of_forall_notMem fun q hq => by
    have := hsm q hq; simp at this
  rcases Nat.primeFactors_eq_empty.mp this with h | h
  · omega
  · omega

theorem size_landauStep (g : Array AzNat) (p : ℕ) : (landauStep g p).size = g.size := by
  simp [landauStep]

/-- The candidate for `p^k`, `1 ≤ k`, `p^k ≤ m`, is in the candidate list. -/
theorem mem_landauCandidates (g : Array AzNat) {p : ℕ} (hp : 1 < p) {m k : ℕ} (hk : k ≠ 0)
    (hpk : p ^ k ≤ m) (hm : m < g.size) :
    ofNat (p ^ k) * g[m - p ^ k]'(by omega) ∈ landauCandidates g p m := by
  unfold landauCandidates
  rw [List.mem_map]
  refine ⟨k - 1, List.mem_range.mpr ?_, ?_⟩
  · have hm0 : m ≠ 0 := by
      intro h; rw [h] at hpk; exact absurd hpk (not_le.mpr (pow_pos (by omega) k))
    have := Nat.le_log_of_pow_le hp hpk
    omega
  · rw [show k - 1 + 1 = k by omega]
    congr 1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]

/-- Every candidate is `p^k · g[m − p^k]` for some `1 ≤ k` with `p^k ≤ m`. -/
theorem of_mem_landauCandidates (g : Array AzNat) (p : ℕ) {m : ℕ}
    (hm : m < g.size) {c : AzNat} (hc : c ∈ landauCandidates g p m) :
    ∃ k, k ≠ 0 ∧ p ^ k ≤ m ∧ ∃ (h : m - p ^ k < g.size),
      c.toNat = p ^ k * (g[m - p ^ k]'h).toNat := by
  unfold landauCandidates at hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hm0 : m ≠ 0 := by
    intro h; rw [h, Nat.log_zero_right] at hi; simp at hi
  have hpk : p ^ (i + 1) ≤ m := Nat.pow_le_of_le_log hm0 (List.mem_range.mp hi)
  refine ⟨i + 1, Nat.succ_ne_zero i, hpk, by omega, ?_⟩
  rw [toNat_mul, toNat_ofNat, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
    Option.getD_some]

theorem not_dvd_of_smooth {ps : List ℕ} {p M : ℕ} (hp : p.Prime) (hM : M ≠ 0)
    (hps : p ∉ ps) (hsm : Smooth ps M) : ¬ p ∣ M := fun h =>
  hps (hsm p (Nat.mem_primeFactors.mpr ⟨hp, h, hM⟩))

/-- **The induction relation**: one `landauStep` with a new prime extends the invariant. -/
theorem landauInv_step {ps ps' : List ℕ} {g : Array AzNat} {p : ℕ} (hp : p.Prime)
    (hps : p ∉ ps) (hps' : ∀ q, q ∈ ps' ↔ q ∈ ps ∨ q = p) (hinv : LandauInv ps g) :
    LandauInv ps' (landauStep g p) := by
  intro m hm
  rw [size_landauStep] at hm
  have hget : (landauStep g p)[m]'(by rw [size_landauStep]; exact hm)
      = (landauCandidates g p m).foldl max g[m] := by
    simp [landauStep]
  rw [hget]
  set c := (landauCandidates g p m).foldl max g[m] with hc
  have hp1 : 1 < p := hp.one_lt
  have hsm_mono : ∀ M, Smooth ps M → Smooth ps' M := fun M h q hq => (hps' q).mpr (Or.inl (h q hq))
  constructor
  · -- `c` is attained
    rcases foldl_max_eq_or_mem (landauCandidates g p m) g[m] with h | h
    · rw [← hc] at h
      rw [h]
      obtain ⟨⟨h0, hsm, hell⟩, _⟩ := hinv m hm
      exact ⟨h0, hsm_mono _ hsm, hell⟩
    · rw [← hc] at h
      obtain ⟨k, hk, hpk, hlt, hval⟩ := of_mem_landauCandidates g p hm h
      obtain ⟨⟨h0, hsm, hell⟩, _⟩ := hinv (m - p ^ k) hlt
      set M' := (g[m - p ^ k]'hlt).toNat
      have hpM' : ¬ p ∣ M' := not_dvd_of_smooth hp h0.ne' hps hsm
      refine ⟨hval ▸ Nat.mul_pos (pow_pos hp.pos k) h0, ?_, ?_⟩
      · intro q hq
        rw [hval, Nat.primeFactors_mul (pow_ne_zero k hp.ne_zero) h0.ne',
          Nat.primeFactors_prime_pow hk hp, Finset.mem_union, Finset.mem_singleton] at hq
        rcases hq with rfl | hq
        · exact (hps' q).mpr (Or.inr rfl)
        · exact hsm_mono _ hsm q hq
      · rw [hval, Nat.ell_prime_pow_mul hp h0.ne' hpM' hk]
        omega
  · -- `c` dominates
    intro M ⟨hM0, hsm, hell⟩
    have hM : M ≠ 0 := hM0.ne'
    set k := M.factorization p with hk
    set M' := M / p ^ k with hM'
    have hsplit : p ^ k * M' = M := Nat.ordProj_mul_ordCompl_eq_self M p
    have hM'0 : M' ≠ 0 := (Nat.ordCompl_pos p hM).ne'
    have hpM' : ¬ p ∣ M' := Nat.not_dvd_ordCompl hp hM
    have hsm' : Smooth ps M' := by
      intro q hq
      have hqM : q ∈ M.primeFactors := Nat.primeFactors_mono (Nat.ordCompl_dvd M p) hM hq
      rcases (hps' q).mp (hsm q hqM) with h | rfl
      · exact h
      · exact absurd (Nat.mem_primeFactors.mp hq).2.1 hpM'
    by_cases hk0 : k = 0
    · -- `p` does not divide `M`
      have hMM' : M = M' := by rw [← hsplit, hk0, pow_zero, one_mul]
      obtain ⟨_, hub⟩ := hinv m hm
      have := hub ⟨hM0, hMM' ▸ hsm', hell⟩
      exact this.trans ((le_iff_toNat_le _ _).mp (le_foldl_max _ _))
    · -- `M = p^k M'` with `k ≥ 1`
      have hellM : ell M = p ^ k + ell M' := by
        rw [← hsplit, Nat.ell_prime_pow_mul hp hM'0 hpM' hk0]
      have hpk : p ^ k ≤ m := by omega
      obtain ⟨_, hub⟩ := hinv (m - p ^ k) (by omega)
      have hle : M' ≤ (g[m - p ^ k]'(by omega)).toNat :=
        hub ⟨Nat.pos_of_ne_zero hM'0, hsm', by omega⟩
      have hcand := le_foldl_max_of_mem (landauCandidates g p m) g[m]
        (mem_landauCandidates g hp1 hk0 hpk hm)
      rw [le_iff_toNat_le, toNat_mul, toNat_ofNat] at hcand
      calc M = p ^ k * M' := hsplit.symm
        _ ≤ p ^ k * (g[m - p ^ k]'(by omega)).toNat := Nat.mul_le_mul_left _ hle
        _ ≤ c.toNat := hcand

theorem size_foldl_landauStep (ps : List ℕ) (g : Array AzNat) :
    (ps.foldl landauStep g).size = g.size := by
  induction ps generalizing g with
  | nil => rfl
  | cons p ps ih => rw [List.foldl_cons, ih, size_landauStep]

theorem landauInv_foldl : ∀ (ps done : List ℕ) (g : Array AzNat), (done ++ ps).Nodup →
    (∀ p ∈ ps, p.Prime) → LandauInv done g → LandauInv (done ++ ps) (ps.foldl landauStep g)
  | [], done, g, _, _, hinv => by simpa using hinv
  | p :: ps, done, g, hnd, hpr, hinv => by
    rw [List.foldl_cons]
    have hnd' : (done ++ [p] ++ ps).Nodup := by simpa [List.append_assoc] using hnd
    have hnot : p ∉ done := by
      intro h
      have := List.nodup_append.mp hnd
      exact this.2.2 p h p (List.mem_cons_self ..) rfl
    have hstep := landauInv_step (hpr p (List.mem_cons_self ..)) hnot
      (ps' := done ++ [p]) (fun q => by simp) hinv
    have := landauInv_foldl ps (done ++ [p]) _ hnd' (fun q hq => hpr q (List.mem_cons_of_mem p hq))
      hstep
    simpa [List.append_assoc] using this

theorem length_landauFunctionPrefix (n : ℕ) : (landauFunctionPrefix n).length = n := by
  unfold landauFunctionPrefix
  rw [Array.length_toList, size_foldl_landauStep, Array.size_replicate]

/-- **Correctness of `landauFunctionPrefix`**: entry `i` is the greatest `M ≥ 1` with
`ℓ(M) ≤ i`. -/
theorem landauFunctionPrefix_spec (n : ℕ) (i : ℕ) (hi : i < (landauFunctionPrefix n).length) :
    IsGreatest {M | 0 < M ∧ ell M ≤ i} ((landauFunctionPrefix n)[i]).toNat := by
  have hlen := length_landauFunctionPrefix n
  set ps := (primesUpTo n).toList with hps
  have hnd : ([] ++ ps).Nodup := by
    rw [List.nil_append]; exact (primesUpTo_sorted n).imp ne_of_lt
  have hpr : ∀ p ∈ ps, p.Prime := fun p hp =>
    (mem_primesUpTo.mp (Array.mem_toList_iff.mp hp)).1
  have hinv := landauInv_foldl ps [] (Array.replicate n 1) hnd hpr (landauInv_init n)
  rw [List.nil_append] at hinv
  have hi' : i < (ps.foldl landauStep (Array.replicate n 1)).size := by
    rw [size_foldl_landauStep, Array.size_replicate]; omega
  have hget : (landauFunctionPrefix n)[i] = (ps.foldl landauStep (Array.replicate n 1))[i] := by
    unfold landauFunctionPrefix
    rw [Array.getElem_toList]
  have key : IsGreatest {M | 0 < M ∧ ell M ≤ i}
      ((ps.foldl landauStep (Array.replicate n 1))[i]'hi').toNat := by
    obtain ⟨⟨h0, _, hell⟩, hub⟩ := hinv i hi'
    refine ⟨⟨h0, hell⟩, ?_⟩
    intro M ⟨hM0, hM⟩
    apply hub
    refine ⟨hM0, ?_, hM⟩
    intro q hq
    have hq' := Nat.le_ell_of_mem_primeFactors hq
    exact Array.mem_toList_iff.mpr
      (mem_primesUpTo.mpr ⟨(Nat.mem_primeFactors.mp hq).1, by omega⟩)
  exact (congrArg (fun x : AzNat => IsGreatest {M | 0 < M ∧ ell M ≤ i} x.toNat) hget).mpr key

/-- **`landauFunctionPrefix` computes Landau's function.** -/
theorem toNat_landauFunctionPrefix (n : ℕ) (i : ℕ) (hi : i < (landauFunctionPrefix n).length) :
    ((landauFunctionPrefix n)[i]).toNat = Nat.landau i :=
  (landauFunctionPrefix_spec n i hi).unique (Nat.isGreatest_landau i)

end Azurite.AzNat

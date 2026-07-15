/-
  Correctness of the trial-division divisor enumeration: soundness (every
  listed value divides `n`) and COMPLETENESS (every positive divisor of
  `n` is listed) — the latter via the classical square-root pairing: a
  divisor `k` of `n` has `min(k, n/k)² ≤ n`, so the loop reaches it
  either directly or as the complement `n / d`.
-/
import Azurite.AzNat.Divisors
import Azurite.AzNat.Equiv.SqrtRem
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare

namespace Azurite

namespace AzNat

/-- Soundness: everything `divisorsAux` emits divides `n` (for `n ≠ 0`). -/
theorem mem_divisorsAux_dvd {n : AzNat} :
    ∀ (fuel : ℕ) (d x : AzNat), x ∈ divisorsAux n fuel d → x.toNat ∣ n.toNat := by
  intro fuel
  induction fuel with
  | zero => intro d x hx; exact absurd hx (by simp [divisorsAux])
  | succ fuel ih =>
    intro d x hx
    rw [divisorsAux] at hx
    by_cases hstop : compare (d * d) n == .gt
    · rw [if_pos hstop] at hx
      exact absurd hx (List.not_mem_nil)
    rw [if_neg hstop] at hx
    by_cases hdvd : n % d = 0
    · rw [if_pos hdvd] at hx
      have hd : d.toNat ∣ n.toNat := by
        have h0 : (n % d).toNat = 0 := by rw [hdvd]; rfl
        rw [toNat_mod] at h0
        exact Nat.dvd_of_mod_eq_zero h0
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hd
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [toNat_div]
        exact Nat.div_dvd_of_dvd hd
      · exact ih (d + 1) x hx
    · rw [if_neg hdvd] at hx
      exact ih (d + 1) x hx

/-- The completeness invariant: a divisor `k` with `d ≤ k` and `k² ≤ n`
is reached (as is its complement) provided the fuel spans from `d` past
`√n`. -/
theorem divisorsAux_complete {n : AzNat} :
    ∀ (fuel : ℕ) (d : AzNat) (k : ℕ), k ∣ n.toNat → d.toNat ≤ k →
      k * k ≤ n.toNat → Nat.sqrt n.toNat + 1 ≤ d.toNat + fuel →
      (∃ x ∈ divisorsAux n fuel d, x.toNat = k) ∧
      (∃ x ∈ divisorsAux n fuel d, x.toNat = n.toNat / k) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d k hk hdk hkk hfuel
    exfalso
    have hks : k ≤ Nat.sqrt n.toNat := Nat.le_sqrt.mpr hkk
    omega
  | succ fuel ih =>
    intro d k hk hdk hkk hfuel
    rw [divisorsAux]
    have hstop : ¬(compare (d * d) n == .gt) := by
      rw [compare_eq_compare_toNat, toNat_mul]
      have hdd : d.toNat * d.toNat ≤ n.toNat :=
        Nat.le_trans (Nat.mul_le_mul hdk hdk) hkk
      intro h
      have := Nat.compare_eq_gt.mp (by simpa using h)
      omega
    rw [if_neg hstop]
    rcases Nat.lt_or_ge d.toNat k with hlt | hge
    · -- not yet at `k`: recurse (whichever branch is taken)
      have hrec := ih (d + 1) k hk (by rw [toNat_add, toNat_one]; omega) hkk
        (by rw [toNat_add, toNat_one]; omega)
      by_cases hdvd : n % d = 0
      · rw [if_pos hdvd]
        exact ⟨⟨hrec.1.choose, List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hrec.1.choose_spec.1), hrec.1.choose_spec.2⟩,
          ⟨hrec.2.choose, List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hrec.2.choose_spec.1), hrec.2.choose_spec.2⟩⟩
      · rw [if_neg hdvd]
        exact hrec
    · -- `d.toNat = k`: this step emits both
      have hdk' : d.toNat = k := by omega
      have h0 : (n % d).toNat = 0 := by
        rw [toNat_mod, hdk']
        exact Nat.mod_eq_zero_of_dvd hk
      have hdvd : n % d = 0 := by
        apply toNat_injective
        rw [h0]
        rfl
      rw [if_pos hdvd]
      refine ⟨⟨d, List.mem_cons_self, hdk'⟩,
        ⟨n / d, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩⟩
      rw [toNat_div, hdk']

/-- **Completeness**: every positive divisor of `n ≠ 0` is listed. -/
theorem divisors_complete {n : AzNat} (hn : n.toNat ≠ 0) {k : ℕ}
    (hk : k ∣ n.toNat) : ∃ x ∈ AzNat.divisors n, x.toNat = k := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hn (Nat.eq_zero_of_zero_dvd hk)
  -- the smaller of `k` and `n / k` is below the square root
  rcases Nat.lt_or_ge n.toNat (k * k) with hbig | hsmall
  case inr =>
    -- `k` itself is reached directly
    have h := divisorsAux_complete (n.sqrt.toNat + 1) 1 k hk
      (by rw [toNat_one]; omega) hsmall
      (by rw [toNat_one, toNat_sqrt]; omega)
    exact h.1
  case inl =>
    -- `k` is the complement of `m := n / k`
    have hm : n.toNat / k ∣ n.toNat := Nat.div_dvd_of_dvd hk
    have hm0 : n.toNat / k ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hk)
        (Nat.pos_of_ne_zero hk0)
      omega
    have hmm : (n.toNat / k) * (n.toNat / k) ≤ n.toNat := by
      have hlt : n.toNat / k < k :=
        (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hk0)).mpr hbig
      calc (n.toNat / k) * (n.toNat / k) ≤ (n.toNat / k) * k :=
            Nat.mul_le_mul_left _ (by omega)
        _ ≤ n.toNat := Nat.div_mul_le_self n.toNat k
    have h := divisorsAux_complete (n.sqrt.toNat + 1) 1 (n.toNat / k) hm
      (by
        rw [toNat_one]
        have := Nat.pos_of_ne_zero hm0
        omega) hmm
      (by rw [toNat_one, toNat_sqrt]; omega)
    obtain ⟨x, hx, hxval⟩ := h.2
    refine ⟨x, hx, ?_⟩
    rw [hxval]
    exact Nat.div_div_self hk hn

/-- Soundness at the top level. -/
theorem mem_divisors_dvd {n : AzNat} {x : AzNat}
    (hx : x ∈ AzNat.divisors n) : x.toNat ∣ n.toNat :=
  mem_divisorsAux_dvd _ _ _ hx

end AzNat

end Azurite

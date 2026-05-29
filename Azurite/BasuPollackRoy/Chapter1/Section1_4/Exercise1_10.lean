import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleQF
import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleSets
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_2
import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization
import Azurite.BasuPollackRoy.Chapter1.Section1_4.Theorem1_23

/-! # BPR Section 1.4 — Exercise 1.10

> **Exercise 1.10.** Prove that the sets $\mathbb{N}$ and $\mathbb{Z}$ are
> not constructible subsets of $C$. Prove that the sets $\mathbb{N}$ and
> $\mathbb{Z}$ cannot be defined inside $C$ by a formula of the language of
> fields with coefficients in $C$.

Both halves follow from Exercise 1.2 / Corollary 1.25: a constructible
(resp.\ formula-definable) subset of $C$ must be finite or cofinite. We
show that $\mathbb{N}$ and $\mathbb{Z}$ — viewed as subsets of an
algebraically closed field $C$ of characteristic $0$ — are neither, so
both negative claims follow.
-/

namespace Azurite.BPR

variable {C : Type*} [Field C] [IsAlgClosed C] [CharZero C]

/-- The image of `ℕ` in `C` (lifted to `Fin 1 → C`). -/
def liftNat : Set (Fin 1 → C) := {y | ∃ n : ℕ, (n : C) = y 0}

/-- The image of `ℤ` in `C` (lifted to `Fin 1 → C`). -/
def liftInt : Set (Fin 1 → C) := {y | ∃ k : ℤ, (k : C) = y 0}

/-! ### Cardinality computations -/

omit [IsAlgClosed C] in
private theorem liftNat_infinite : (liftNat (C := C)).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => (fun _ : Fin 1 => (n : C))) := by
    intro n m h
    have := congrFun h 0
    exact Nat.cast_injective this
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact ⟨n, rfl⟩

omit [IsAlgClosed C] in
private theorem liftNat_compl_infinite : (liftNat (C := C))ᶜ.Infinite := by
  let f : ℕ → (Fin 1 → C) := fun n _ => -((n + 1 : ℕ) : C)
  have hinj : Function.Injective f := by
    intro n m hnm
    have h := congrFun hnm 0
    simp only [f, neg_inj] at h
    have : (n + 1 : ℕ) = (m + 1 : ℕ) := Nat.cast_injective h
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro y ⟨n, rfl⟩ ⟨m, hm⟩
  -- hm : (m : C) = f n 0 = -((n + 1 : ℕ) : C)
  simp only [f] at hm
  have h_cast_zero : ((m + (n + 1) : ℕ) : C) = 0 := by
    push_cast at hm ⊢
    linear_combination hm
  rw [Nat.cast_eq_zero] at h_cast_zero
  omega

omit [IsAlgClosed C] in
private theorem liftInt_infinite : (liftInt (C := C)).Infinite := by
  apply liftNat_infinite.mono
  rintro y ⟨n, hn⟩
  exact ⟨(n : ℤ), by rw [Int.cast_natCast]; exact hn⟩

omit [IsAlgClosed C] in
private theorem liftInt_compl_infinite : (liftInt (C := C))ᶜ.Infinite := by
  -- Use 1 / (n + 2) for n : ℕ — pairwise distinct, none is an integer.
  let g : ℕ → (Fin 1 → C) := fun n _ => ((n + 2 : ℕ) : C)⁻¹
  have h_ne_zero : ∀ n : ℕ, ((n + 2 : ℕ) : C) ≠ 0 := by
    intro n h
    rw [Nat.cast_eq_zero] at h
    omega
  have hinj : Function.Injective g := by
    intro n m hnm
    have h := congrFun hnm 0
    simp only [g] at h
    have h_eq : ((n + 2 : ℕ) : C) = ((m + 2 : ℕ) : C) :=
      inv_injective h
    have : (n + 2 : ℕ) = (m + 2 : ℕ) := Nat.cast_injective h_eq
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro y ⟨n, rfl⟩ ⟨k, hk⟩
  -- hk : (k : C) = ((n + 2 : ℕ) : C)⁻¹
  have h_prod : (k : C) * ((n + 2 : ℕ) : C) = 1 := by
    rw [hk]; exact inv_mul_cancel₀ (h_ne_zero n)
  have h_in_C : ((k * (n + 2 : ℤ) : ℤ) : C) = ((1 : ℤ) : C) := by
    push_cast at h_prod ⊢
    linear_combination h_prod
  have h_int : k * (n + 2 : ℤ) = 1 := Int.cast_injective h_in_C
  -- (n+2 : ℤ) divides 1 in ℤ, contradicting (n+2) ≥ 2.
  have h_dvd : (n + 2 : ℤ) ∣ 1 := ⟨k, by linarith⟩
  have h_le : (n + 2 : ℤ) ≤ 1 :=
    Int.le_of_dvd one_pos h_dvd
  omega

/-! ### Exercise 1.10 -/

omit [IsAlgClosed C] in
/-- **BPR Exercise 1.10 (a) — `ℕ` part.** The image of `ℕ` in `C` is not
a constructible subset of `C`. -/
theorem exercise_1_10_nat_not_constructible :
    ¬ IsConstructibleSet (liftNat (C := C)) := by
  intro hcon
  rcases exercise_1_2 _ hcon with hfin | hcofin
  · exact liftNat_infinite hfin
  · exact liftNat_compl_infinite hcofin

omit [IsAlgClosed C] in
/-- **BPR Exercise 1.10 (a) — `ℤ` part.** The image of `ℤ` in `C` is not
a constructible subset of `C`. -/
theorem exercise_1_10_int_not_constructible :
    ¬ IsConstructibleSet (liftInt (C := C)) := by
  intro hcon
  rcases exercise_1_2 _ hcon with hfin | hcofin
  · exact liftInt_infinite hfin
  · exact liftInt_compl_infinite hcofin

/-- **BPR Exercise 1.10 (b) — `ℕ` part.** The image of `ℕ` in `C` cannot
be defined by a formula in the language of fields with coefficients in
`C`. -/
theorem exercise_1_10_nat_not_formula_definable :
    ¬ ∃ Φ : Formula (Fin 1) (FieldAtom (Fin 1) C),
        Φ.realization (C := C) = liftNat := by
  rintro ⟨Φ, hΦ⟩
  rcases corollary_1_25 Φ with hfin | hcofin
  · rw [hΦ] at hfin; exact liftNat_infinite hfin
  · rw [hΦ] at hcofin; exact liftNat_compl_infinite hcofin

/-- **BPR Exercise 1.10 (b) — `ℤ` part.** The image of `ℤ` in `C` cannot
be defined by a formula in the language of fields with coefficients in
`C`. -/
theorem exercise_1_10_int_not_formula_definable :
    ¬ ∃ Φ : Formula (Fin 1) (FieldAtom (Fin 1) C),
        Φ.realization (C := C) = liftInt := by
  rintro ⟨Φ, hΦ⟩
  rcases corollary_1_25 Φ with hfin | hcofin
  · rw [hΦ] at hfin; exact liftInt_infinite hfin
  · rw [hΦ] at hcofin; exact liftInt_compl_infinite hcofin

end Azurite.BPR

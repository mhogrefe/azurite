import Azurite.BasuPollackRoy.Chapter2.Section2_5.Corollary_2_79
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83

/-! # BPR Exercise 2.15: `{(x, y) | ∃ n ∈ ℕ, y = n x}` is not semialgebraic

The set `S = {(x, y) ∈ R² | ∃ n ∈ ℕ, y = n·x}` is not semialgebraic. Slicing with the line
`x = 1` (intersect with `{x = 1}`, then project to the `y`-axis) gives the image
`{n·1 | n ∈ ℕ} = range(ℕ → R)`, which by the one-dimensional structure theorem (Corollary
2.79) would have to be a finite union of points and intervals. But `range(ℕ → R)` is an
infinite discrete set: any order-connected piece is a single point (its midpoint with a
neighbour would be a half-integer, not an integer), so a finite union of such pieces is
finite — contradicting that `ℕ → R` has infinite range.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The natural numbers, embedded in `R`, are not a finite union of points and intervals:
every order-connected subset of `range (ℕ → R)` is a single point (a midpoint argument),
and a finite union of points is finite. -/
theorem not_FUOC_range_natCast :
    ¬ IsFinUnionOfOrdConnected (Set.range (Nat.cast : ℕ → R)) := by
  rintro ⟨𝒞, h𝒞fin, hoc, hunion⟩
  have hCsub : ∀ C ∈ 𝒞, C ⊆ Set.range (Nat.cast : ℕ → R) := by
    intro C hC; rw [hunion]; exact Set.subset_sUnion_of_mem hC
  have hsub : ∀ C ∈ 𝒞, C.Subsingleton := by
    intro C hC
    have hmid : ∀ r s : ℕ, r < s → (↑r : R) ∈ C → (↑s : R) ∈ C → False := by
      intro r s hrs hrC hsC
      have h0 : (0 : R) ≤ 2⁻¹ := by positivity
      have h2 : (2 : R)⁻¹ ≤ 1 := (inv_le_one₀ (by norm_num)).mpr (by norm_num)
      have h1 : (↑r : R) + 1 ≤ ↑s := by
        have : r + 1 ≤ s := hrs
        exact_mod_cast this
      have hmem : (↑r + 2⁻¹ : R) ∈ Set.Icc (↑r : R) ↑s :=
        ⟨by linarith, by linarith⟩
      have hmC : (↑r + 2⁻¹ : R) ∈ C := (hoc C hC).out hrC hsC hmem
      obtain ⟨t, ht⟩ := hCsub C hC hmC
      have e2 : (2 : R) * ↑t = 2 * ↑r + 1 := by
        rw [ht, mul_add, mul_inv_cancel₀ (two_ne_zero)]
      have e3 : ((2 * t : ℕ) : R) = ((2 * r + 1 : ℕ) : R) := by push_cast; linarith [e2]
      have := Nat.cast_injective e3
      omega
    intro a ha b hb
    obtain ⟨p, rfl⟩ := hCsub C hC ha
    obtain ⟨q, rfl⟩ := hCsub C hC hb
    rcases lt_trichotomy p q with h | h | h
    · exact (hmid p q h ha hb).elim
    · rw [h]
    · exact (hmid q p h hb ha).elim
  have hfin : (Set.range (Nat.cast : ℕ → R)).Finite := by
    rw [hunion]
    exact Set.Finite.sUnion h𝒞fin (fun C hC => (hsub C hC).finite)
  exact Set.infinite_range_of_injective Nat.cast_injective hfin

variable [IsRealClosed R]

/-- **BPR Exercise 2.15.** The set `{(x, y) ∈ R² | ∃ n ∈ ℕ, y = n·x}` is not semialgebraic. -/
theorem exercise_2_15 :
    ¬ IsSemialgebraicSet {p : Fin 2 → R | ∃ n : ℕ, p 1 = ↑n * p 0} := by
  intro hS
  -- the line `x = 1` is semialgebraic
  have hL : IsSemialgebraicSet {p : Fin 2 → R | p 0 = 1} := by
    convert IsSemialgebraicSet.eqZero (MvPolynomial.X 0 - 1 : MvPolynomial (Fin 2) R) using 1
    ext p
    simp only [Set.mem_setOf_eq, map_sub, MvPolynomial.eval_X, map_one, sub_eq_zero]
  -- project `S ∩ {x = 1}` to the `y`-axis
  have e0 : ∀ (x y : Fin 1 → R), Fin.append x y 0 = x 0 := fun x y => by
    rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from Fin.ext rfl, Fin.append_left]
  have e1 : ∀ (x y : Fin 1 → R), Fin.append x y 1 = y 0 := fun x y => by
    rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from Fin.ext rfl, Fin.append_right]
  have hV := IsSemialgebraicSet.exists_append_left (k := 1) (ℓ := 1) (hS.inter hL)
  have hVeq : {y : Fin 1 → R | ∃ x : Fin 1 → R, Fin.append x y ∈
        ({p : Fin 2 → R | ∃ n : ℕ, p 1 = ↑n * p 0} ∩ {p | p 0 = 1})}
      = {y : Fin 1 → R | y 0 ∈ Set.range (Nat.cast : ℕ → R)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_range]
    constructor
    · rintro ⟨x, ⟨n, hn⟩, hx1⟩
      rw [e0, e1] at hn
      rw [e0] at hx1
      exact ⟨n, by rw [hn, hx1, mul_one]⟩
    · rintro ⟨n, hn⟩
      refine ⟨fun _ => 1, ⟨n, ?_⟩, ?_⟩
      · rw [e0, e1, hn, mul_one]
      · rw [e0]
  rw [hVeq] at hV
  have hFUOC := semialgebraic_sect_FUOC hV
  have hpre : constPt ⁻¹' {y : Fin 1 → R | y 0 ∈ Set.range (Nat.cast : ℕ → R)}
      = Set.range (Nat.cast : ℕ → R) := by
    ext t; simp [constPt]
  rw [hpre] at hFUOC
  exact not_FUOC_range_natCast hFUOC

end Azurite.BPR

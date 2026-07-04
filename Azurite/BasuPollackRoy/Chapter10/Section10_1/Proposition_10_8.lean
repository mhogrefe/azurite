import Azurite.BasuPollackRoy.Chapter10.Section10_1.NormLengthMeasure
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_11_a_b
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.Nat.Choose.Sum

/-!
# BPR Proposition 10.8: the length is bounded by the measure

`proposition_10_8`: `Len(P) ≤ 2^p · Mea(P)`. BPR's proof: by Vieta
(BPR Lemma 2.12; here Mathlib's `coeff_eq_esymm_roots_of_card`, applicable
since `C = R[i]` is algebraically closed by Theorem 2.11),

  `a_{p−k} = (−1)^k · eₖ(z₁, …, zₚ) · aₚ`,

and the elementary symmetric function `eₖ` is a sum of `C(p,k)` products of
`k` roots, each bounded in modulus by `∏ᵢ max(1, |zᵢ|)`; hence
`|a_{p−k}| ≤ C(p,k) · Mea(P)` and summing over `k` gives
`Len(P) ≤ ∑ₖ C(p,k) · Mea(P) = 2^p · Mea(P)`.

The multiset lemmas (`Ri.abs` of sums and products, the domination of subset
products by the full `max`-product) are proved here on the way.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The modulus of a multiset product is the product of the moduli. -/
theorem Ri.abs_multiset_prod (s : Multiset (Ri R)) :
    Ri.abs s.prod = (s.map Ri.abs).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using Ri.abs_one
  | cons z s ih => rw [Multiset.prod_cons, Ri.abs_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

/-- The modulus of a multiset sum is at most the sum of the moduli. -/
theorem Ri.abs_multiset_sum (s : Multiset (Ri R)) :
    Ri.abs s.sum ≤ (s.map Ri.abs).sum := by
  induction s using Multiset.induction_on with
  | empty => simpa using le_of_eq Ri.abs_zero
  | cons z s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    calc Ri.abs (z + s.sum) ≤ Ri.abs z + Ri.abs s.sum := Ri.abs_add _ _
      _ ≤ Ri.abs z + (s.map Ri.abs).sum := by linarith [ih]

theorem Ri.abs_neg_one_pow_mul (k : ℕ) (x : Ri R) :
    Ri.abs ((-1) ^ k * x) = Ri.abs x := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, one_mul]
  · rw [h.neg_one_pow, neg_one_mul, Ri.abs_neg]

/-- The product of the `max(1, |z|)` terms is at least `1`. -/
theorem one_le_prod_max (s : Multiset (Ri R)) :
    1 ≤ (s.map (fun z => max 1 (Ri.abs z))).prod := by
  apply Multiset.one_le_prod
  intro a ha
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp ha
  exact le_max_left _ _

/-- The `max`-product only grows along multiset inclusion. -/
theorem prod_max_mono {t s : Multiset (Ri R)} (h : t ≤ s) :
    (t.map (fun z => max 1 (Ri.abs z))).prod
      ≤ (s.map (fun z => max 1 (Ri.abs z))).prod := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [Multiset.map_add, Multiset.prod_add]
  calc (t.map (fun z => max 1 (Ri.abs z))).prod
      = (t.map (fun z => max 1 (Ri.abs z))).prod * 1 := (mul_one _).symm
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (one_le_prod_max u)
        exact le_trans zero_le_one (one_le_prod_max t)

/-- The modulus of a product of roots is at most the full `max`-product. -/
theorem abs_prod_le_prod_max (t : Multiset (Ri R)) :
    Ri.abs t.prod ≤ (t.map (fun z => max 1 (Ri.abs z))).prod := by
  rw [Ri.abs_multiset_prod]
  induction t using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    apply mul_le_mul (le_max_right _ _) ih
      (Multiset.prod_nonneg (fun a ha => by
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp ha
        exact Ri.abs_nonneg' w))
      (le_trans zero_le_one (le_max_left _ _))

/-- `|eₖ(s)| ≤ C(card s, k) · ∏_{z ∈ s} max(1, |z|)`: the elementary symmetric
function is a sum of `C(card s, k)` products of `k` elements, each dominated
by the full `max`-product. -/
theorem abs_esymm_le (s : Multiset (Ri R)) (k : ℕ) :
    Ri.abs (s.esymm k) ≤ (s.card.choose k : R)
      * (s.map (fun z => max 1 (Ri.abs z))).prod := by
  rw [Multiset.esymm]
  calc Ri.abs ((s.powersetCard k).map Multiset.prod).sum
      ≤ (((s.powersetCard k).map Multiset.prod).map Ri.abs).sum :=
        Ri.abs_multiset_sum _
    _ ≤ (((s.powersetCard k).map Multiset.prod).map
          (fun _ => (s.map (fun z => max 1 (Ri.abs z))).prod)).sum := by
        apply Multiset.sum_map_le_sum_map
        intro a ha
        obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp ha
        calc Ri.abs t.prod ≤ (t.map (fun z => max 1 (Ri.abs z))).prod :=
              abs_prod_le_prod_max t
          _ ≤ _ := prod_max_mono (Multiset.mem_powersetCard.mp ht).1
    _ = (s.card.choose k : R) * (s.map (fun z => max 1 (Ri.abs z))).prod := by
        rw [Multiset.map_map,
          show ((fun _ => (s.map (fun z => max 1 (Ri.abs z))).prod) ∘ Multiset.prod)
            = (fun _ : Multiset (Ri R) => (s.map (fun z => max 1 (Ri.abs z))).prod) from rfl,
          Multiset.map_const', Multiset.sum_replicate, Multiset.card_powersetCard,
          nsmul_eq_mul]

/-- **BPR Proposition 10.8.** `Len(P) ≤ 2^p · Mea(P)`. -/
theorem proposition_10_8 (P : Polynomial (Ri R)) :
    polyLength P ≤ 2 ^ P.natDegree * polyMeasure P := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [polyLength, polyMeasure]
    simp [Ri.abs_zero]
  haveI : IsAlgClosed (Ri R) := Theorem2_11.isAlgClosed_Ri
  have hcard : P.roots.card = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  set p := P.natDegree with hp
  set M := (P.roots.map (fun z => max 1 (Ri.abs z))).prod with hM
  -- the coefficient bound |a_{p−k}| ≤ C(p,k) · Mea(P), from Vieta
  have hcoeff : ∀ k, k ≤ p → Ri.abs (P.coeff (p - k))
      ≤ (p.choose k : R) * (Ri.abs P.leadingCoeff * M) := by
    intro k hk
    have hVieta := Polynomial.coeff_eq_esymm_roots_of_card hcard
      (show p - k ≤ P.natDegree by omega)
    rw [show P.natDegree - (p - k) = k from by omega] at hVieta
    rw [hVieta, show P.leadingCoeff * (-1) ^ k * P.roots.esymm k
      = (-1) ^ k * (P.leadingCoeff * P.roots.esymm k) from by ring,
      Ri.abs_neg_one_pow_mul, Ri.abs_mul]
    calc Ri.abs P.leadingCoeff * Ri.abs (P.roots.esymm k)
        ≤ Ri.abs P.leadingCoeff * ((p.choose k : R) * M) := by
          apply mul_le_mul_of_nonneg_left _ (Ri.abs_nonneg' _)
          have h := abs_esymm_le P.roots k
          rwa [hcard, ← hM] at h
      _ = (p.choose k : R) * (Ri.abs P.leadingCoeff * M) := by ring
  -- sum the bounds over the reflected coefficient index
  rw [polyLength, polyMeasure, ← hM, ← hp]
  have hreflect := Finset.sum_range_reflect (fun i => Ri.abs (P.coeff i)) (p + 1)
  rw [← hreflect]
  calc ∑ k ∈ Finset.range (p + 1), Ri.abs (P.coeff (p + 1 - 1 - k))
      ≤ ∑ k ∈ Finset.range (p + 1), (p.choose k : R) * (Ri.abs P.leadingCoeff * M) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k ≤ p := by
          have := Finset.mem_range.mp hk
          omega
        have h := hcoeff k hk'
        rwa [show p + 1 - 1 - k = p - k from by omega]
    _ = ((∑ k ∈ Finset.range (p + 1), p.choose k : ℕ) : R)
          * (Ri.abs P.leadingCoeff * M) := by
        rw [← Finset.sum_mul, Nat.cast_sum]
    _ = 2 ^ p * (Ri.abs P.leadingCoeff * M) := by
        rw [Nat.sum_range_choose]
        push_cast
        ring

end Azurite.BPR

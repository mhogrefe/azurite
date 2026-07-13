/-
  Gathen–Gerhard, Lemma 14.6: the k-th powers in `F_q^×`.

  For a prime power `q` and a divisor `k` of `q − 1`, the set
  `S = {b^k : b ∈ F_q^×}` of `k`-th powers

  (i)  is a subgroup of `F_q^×` of order `(q − 1)/k`, and
  (ii) equals `{a ∈ F_q^× : a^((q−1)/k) = 1}`.

  Following the book: `S` is the image of the `k`-th power homomorphism
  `σ_k`, hence a subgroup (here by construction: `kthPowers` IS
  `(powMonoidHom k).range`).  Its kernel is the group of `k`-th roots of
  unity (`rootsOfUnity k F` in Mathlib), of size at most `k` since
  `x^k − 1` has at most `k` roots over a field (the book's Lemma 25.4 =
  Mathlib's `card_rootsOfUnity`).  By Fermat (14.1),
  `(b^k)^((q−1)/k) = b^(q−1) = 1`, so `S ⊆ ker σ_((q−1)/k)`, giving
  `#S ≤ (q−1)/k` by the same root count.  The homomorphism theorem
  (`Subgroup.index_ker` + `Subgroup.index_mul_card`) gives
  `q − 1 = #ker σ_k · #S ≤ k · (q−1)/k = q − 1`, forcing equality
  throughout: `#ker σ_k = k`, `#S = (q−1)/k`, and `S = ker σ_((q−1)/k)`.

  This is the counting fact behind equal-degree splitting
  (Cantor–Zassenhaus): it pins down exactly how many elements pass the
  `a^((q−1)/k) = 1` test.  A field-level corollary
  (`exists_pow_eq_iff_pow_card_sub_one_div_eq_one`) restates (ii) for
  nonzero field elements without mentioning the unit group.
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.Basic

namespace Azurite

namespace GG

variable {F : Type*} [Field F]

/-- `S`, the subgroup of `k`-th powers of `F^×` (GG Lemma 14.6): the range
of the `k`-th power homomorphism `σ_k`.  Being a subgroup — the first
assertion of the lemma — is the type. -/
def kthPowers (F : Type*) [Field F] (k : ℕ) : Subgroup Fˣ :=
  (powMonoidHom k : Fˣ →* Fˣ).range

theorem mem_kthPowers {k : ℕ} {a : Fˣ} :
    a ∈ kthPowers F k ↔ ∃ b : Fˣ, b ^ k = a :=
  Iff.rfl

/-- The kernel of the `k`-th power homomorphism is the group of `k`-th
roots of unity. -/
theorem ker_powMonoidHom_eq_rootsOfUnity (k : ℕ) :
    (powMonoidHom k : Fˣ →* Fˣ).ker = rootsOfUnity k F := by
  ext a
  rw [MonoidHom.mem_ker, powMonoidHom_apply, mem_rootsOfUnity]

/-- Subgroups squeezed between a subgroup and its cardinality are equal
(the finite-order equality extraction used twice below). -/
private theorem subgroup_eq_of_le_of_card_le {G : Type*} [Group G]
    {H K : Subgroup G} [Finite K] (hle : H ≤ K)
    (hcard : Nat.card K ≤ Nat.card H) : H = K :=
  SetLike.coe_injective <|
    Set.eq_of_subset_of_ncard_le hle
      (by rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq])
      (K : Set G).toFinite

/-- The sandwich arithmetic of the book's counting: if `a ≤ k`, `b ≤ m`,
and `b·a = m·k`, then both bounds are attained. -/
private theorem nat_sandwich {a b k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (ha : a ≤ k) (hb : b ≤ m) (hprod : b * a = m * k) : a = k ∧ b = m := by
  have hbm : b * a ≤ b * k := Nat.mul_le_mul_left b ha
  have hmk : b * k ≤ m * k := Nat.mul_le_mul_right k hb
  have h1 : b * k = m * k := le_antisymm hmk (hprod ▸ hbm)
  have hbeq : b = m := Nat.eq_of_mul_eq_mul_right hk h1
  refine ⟨?_, hbeq⟩
  rw [hbeq] at hprod
  exact Nat.eq_of_mul_eq_mul_left hm hprod

/-- **GG Lemma 14.6.**  For `k ∣ q − 1`, the `k`-th powers `S ≤ F_q^×`
satisfy: `#S = (q−1)/k` (part i, with `#ker σ_k = k` as the byproduct of
the book's counting), and `S` is exactly the group of `(q−1)/k`-th roots
of unity, i.e. `{a : a^((q−1)/k) = 1}` (part ii). -/
theorem lemma_14_6 [Fintype F] {k : ℕ} (hk0 : k ≠ 0)
    (hk : k ∣ Fintype.card F - 1) :
    Nat.card (kthPowers F k) = (Fintype.card F - 1) / k ∧
    kthPowers F k = rootsOfUnity ((Fintype.card F - 1) / k) F ∧
    Nat.card ((powMonoidHom k : Fˣ →* Fˣ).ker) = k := by
  haveI : NeZero k := ⟨hk0⟩
  -- the order of the unit group is `q − 1`, positive; and `(q−1)/k ≠ 0`
  have hnu : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  have hn0 : Fintype.card F - 1 ≠ 0 := by
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hnk0 : (Fintype.card F - 1) / k ≠ 0 := by
    have hkn := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hk
    have := Nat.div_pos hkn (Nat.pos_of_ne_zero hk0)
    omega
  haveI : NeZero ((Fintype.card F - 1) / k) := ⟨hnk0⟩
  -- the kernel is at most `k` (at most `k` roots of `x^k − 1`)
  have hker_le : Nat.card ((powMonoidHom k : Fˣ →* Fˣ).ker) ≤ k := by
    rw [ker_powMonoidHom_eq_rootsOfUnity]
    exact card_rootsOfUnity (R := F) (k := k)
  -- Fermat: `S ⊆ ker σ_((q−1)/k)`
  have hSle : kthPowers F k ≤ rootsOfUnity ((Fintype.card F - 1) / k) F := by
    rintro a ⟨b, rfl⟩
    rw [mem_rootsOfUnity]
    show (b ^ k) ^ ((Fintype.card F - 1) / k) = 1
    rw [← pow_mul, Nat.mul_div_cancel' hk, ← hnu]
    exact pow_card_eq_one'
  have hS_le : Nat.card (kthPowers F k) ≤ (Fintype.card F - 1) / k :=
    le_trans (Subgroup.card_le_of_le hSle)
      (card_rootsOfUnity (R := F) (k := (Fintype.card F - 1) / k))
  -- the homomorphism theorem: `q − 1 = #S · #ker σ_k`
  have hprod : Nat.card (kthPowers F k)
      * Nat.card ((powMonoidHom k : Fˣ →* Fˣ).ker) = Fintype.card F - 1 := by
    rw [← hnu, kthPowers, ← Subgroup.index_ker, Subgroup.index_mul_card]
  -- the sandwich forces equality throughout
  have hnkk : (Fintype.card F - 1) / k * k = Fintype.card F - 1 :=
    Nat.div_mul_cancel hk
  obtain ⟨hker_eq, hS_eq⟩ := nat_sandwich (Nat.pos_of_ne_zero hk0)
    (Nat.pos_of_ne_zero hnk0) hker_le hS_le (hprod.trans hnkk.symm)
  refine ⟨hS_eq, ?_, hker_eq⟩
  -- `S ≤ ker σ_((q−1)/k)` with `#ker σ_((q−1)/k) ≤ (q−1)/k = #S`
  exact subgroup_eq_of_le_of_card_le hSle
    (le_trans (card_rootsOfUnity (R := F) (k := (Fintype.card F - 1) / k))
      hS_eq.ge)

/-- Part (i): the `k`-th powers form a subgroup of order `(q − 1)/k`. -/
theorem card_kthPowers [Fintype F] {k : ℕ} (hk0 : k ≠ 0)
    (hk : k ∣ Fintype.card F - 1) :
    Nat.card (kthPowers F k) = (Fintype.card F - 1) / k :=
  (lemma_14_6 hk0 hk).1

/-- The byproduct of the counting: the `k`-th roots of unity number
exactly `k` (the root bound is attained). -/
theorem card_rootsOfUnity_eq [Fintype F] {k : ℕ} (hk0 : k ≠ 0)
    (hk : k ∣ Fintype.card F - 1) :
    Nat.card (rootsOfUnity k F) = k := by
  rw [← ker_powMonoidHom_eq_rootsOfUnity]
  exact (lemma_14_6 hk0 hk).2.2

/-- Part (ii): an element of `F_q^×` is a `k`-th power exactly when its
`(q−1)/k`-th power is `1`. -/
theorem mem_kthPowers_iff_pow_eq_one [Fintype F] {k : ℕ} (hk0 : k ≠ 0)
    (hk : k ∣ Fintype.card F - 1) {a : Fˣ} :
    a ∈ kthPowers F k ↔ a ^ ((Fintype.card F - 1) / k) = 1 := by
  rw [(lemma_14_6 hk0 hk).2.1, mem_rootsOfUnity]

/-- Part (ii) at the field level: a nonzero `a : F_q` is a `k`-th power
exactly when `a^((q−1)/k) = 1` (the power-residue test of equal-degree
splitting). -/
theorem exists_pow_eq_iff_pow_card_sub_one_div_eq_one [Fintype F] {k : ℕ}
    (hk0 : k ≠ 0) (hk : k ∣ Fintype.card F - 1) {a : F} (ha : a ≠ 0) :
    (∃ b : F, b ≠ 0 ∧ b ^ k = a)
      ↔ a ^ ((Fintype.card F - 1) / k) = 1 := by
  have hmem := mem_kthPowers_iff_pow_eq_one (F := F) hk0 hk
    (a := Units.mk0 a ha)
  rw [mem_kthPowers] at hmem
  constructor
  · rintro ⟨b, hb0, rfl⟩
    have h1 : (Units.mk0 b hb0) ^ k = Units.mk0 (b ^ k) (pow_ne_zero k hb0) :=
      Units.ext (by simp)
    have := hmem.mp ⟨Units.mk0 b hb0, h1⟩
    calc (b ^ k) ^ ((Fintype.card F - 1) / k)
        = ((Units.mk0 (b ^ k) (pow_ne_zero k hb0))
            ^ ((Fintype.card F - 1) / k) : Fˣ) := by simp
      _ = 1 := by rw [this, Units.val_one]
  · intro hpow
    have h1 : (Units.mk0 a ha) ^ ((Fintype.card F - 1) / k) = 1 :=
      Units.ext (by simpa using hpow)
    obtain ⟨b, hb⟩ := hmem.mpr h1
    exact ⟨(b : F), b.ne_zero, by
      calc (b : F) ^ k = ((b ^ k : Fˣ) : F) := by simp
        _ = a := by rw [hb, Units.val_mk0]⟩

end GG

end Azurite

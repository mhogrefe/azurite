/-
  Gathen–Gerhard, Algorithm 14.3 (distinct-degree factorization) and
  Theorem 14.4 (its correctness).

  The algorithm: starting from `h₀ = x` and `f₀ = f` (squarefree monic),
  repeatedly compute `hᵢ = hᵢ₋₁^q rem fᵢ₋₁`, `gᵢ = gcd(hᵢ − x, fᵢ₋₁)`, and
  `fᵢ = fᵢ₋₁ / gᵢ`, until `fᵢ = 1`; return `(g₁, …, g_s)`.  Per the book's
  remark, `hᵢ` is powered mod `fᵢ₋₁` rather than mod `f`: it is only ever
  consumed by `gcd(hᵢ − x, fᵢ₋₁)`, so its class mod `fᵢ₋₁` is all that
  matters, and the powering gets cheaper as factors are peeled off.  The
  correctness invariant is accordingly a congruence, `fᵢ ∣ h − x^(qⁱ)`,
  rather than a canonical form.

  Theorem 14.4, following the book: by induction, `hᵢ ≡ x^(qⁱ) mod fᵢ`, so
  `gᵢ = gcd(x^(qⁱ) − x, fᵢ₋₁)`, which by Theorem 14.2 is the product of the
  monic irreducible factors of `fᵢ₋₁` of degree dividing `i` — all of degree
  exactly `i`, since the factors of degree `< i` were already removed — i.e.
  `gᵢ = Gᵢ`, the `i`-th part of the distinct-degree decomposition, and
  `fᵢ = Gᵢ₊₁ ⋯ G_s`.  The formal invariant carries `fᵢ` as `ddTail f i`, the
  product of the prime factors of `f` of degree `> i`.

  Two rails, as usual:

  * the ABSTRACT algorithm `distinctDegreeFactorization` on Mathlib
    polynomials (fuel-recursive loop `dddLoop`, fuel `deg f` suffices since
    the largest factor degree is at most `deg f`), with `theorem_14_4`:
    for squarefree monic `f` it computes `distinctDegreeDecomposition f`;

  * the COMPUTABLE algorithm `AzPolynomial.distinctDegreeFactorization`
    (in `Azurite/AzPolynomial/DistinctDegreeFactorization.lean`, alongside
    the other computable polynomial algorithms), whose bridge
    `map_toPoly_distinctDegreeFactorization` (here) transports
    Theorem 14.4, so the computable output IS the distinct-degree
    decomposition of the represented polynomial.

  Both rails implement the book's EARLY ABORT (the remark after
  Theorem 14.4): as soon as `deg fᵢ < 2(i + 1)` the loop stops — all
  irreducible factors of `fᵢ` have degree at least `i + 1`, so `fᵢ` is
  itself irreducible, and the rest of the output is `(1, …, 1, fᵢ)` with
  `fᵢ` in position `deg fᵢ` (`ddTail_early_abort`).  This caps the
  iteration count at `max(m₁/2, m₂) ≤ (deg f)/2`, where `m₁ ≥ m₂` are the
  two largest factor degrees.
-/
import Azurite.GathenGerhard.Chapter14.DistinctDegree
import Azurite.AzPolynomial.DistinctDegreeFactorization
import Azurite.AzPolyMod.Equiv.AdjoinRoot
import Azurite.AzPolynomial.Equiv.Gcd
import Azurite.AzZMod.Fintype
import Mathlib.Algebra.Ring.GeomSum

namespace Azurite

namespace GG

open Polynomial UniqueFactorizationMonoid

/- Chapter 1 (imported through the subresultant-gcd correctness theory)
installs the `EuclideanDomain`-derived `GCDMonoid K[X]` instance
`Azurite.BPR.gcdMonoidPolynomial`, which would win over Mathlib's
`NormalizedGCDMonoid`-derived gcd.  This file's `gcd` is Mathlib's (the
monic-normalized one, matching `toPoly_gcdMonic`), so we locally prefer it. -/
attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The tail products `fᵢ`

`ddTail f i` is the loop variable `fᵢ` of Algorithm 14.3 in closed form: the
product of the prime factors of `f` of degree `> i` (each once — for
squarefree `f` that is all of their contribution). -/

/-- A monic squarefree polynomial is the product of its prime-factor set
(the `prod_distinctDegreeDecomposition` assembly step, standalone). -/
theorem prod_primeFactors_eq {f : F[X]} (hm : f.Monic) (hsq : Squarefree f) :
    (primeFactors f).prod id = f := by
  have hrad := radical_associated hsq.isRadical hm.ne_zero
  exact Polynomial.eq_of_monic_of_associated
    (Polynomial.monic_prod_of_monic _ _
      (fun g hg => monic_of_mem_primeFactors hg)) hm hrad

/-- Membership in the prime-factor set, unfolded (`mem_primeFactors` +
`mem_normalizedFactors_iff'`). -/
theorem mem_primeFactors_iff'' {g p : F[X]} (hg0 : g ≠ 0) :
    p ∈ primeFactors g ↔ Irreducible p ∧ normalize p = p ∧ p ∣ g := by
  rw [mem_primeFactors, mem_normalizedFactors_iff' hg0]

/-- The loop variable `fᵢ` of Algorithm 14.3: the product of the prime
factors of `f` of degree `> i`. -/
noncomputable def ddTail (f : F[X]) (i : ℕ) : F[X] :=
  ((primeFactors f).filter (fun g => i < g.natDegree)).prod id

theorem ddTail_monic (f : F[X]) (i : ℕ) : (ddTail f i).Monic :=
  Polynomial.monic_prod_of_monic _ _
    (fun _ hg => monic_of_mem_primeFactors (Finset.mem_filter.mp hg).1)

theorem ddTail_dvd (f : F[X]) (i : ℕ) : ddTail f i ∣ f :=
  (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
    radical_dvd_self

theorem squarefree_ddTail {f : F[X]} (hsq : Squarefree f) (i : ℕ) :
    Squarefree (ddTail f i) :=
  hsq.squarefree_of_dvd (ddTail_dvd f i)

/-- `f₀ = f`: for squarefree monic `f`, the degree-`> 0` tail is all of `f`
(irreducible factors have positive degree). -/
theorem ddTail_zero {f : F[X]} (hm : f.Monic) (hsq : Squarefree f) :
    ddTail f 0 = f := by
  rw [ddTail, Finset.filter_true_of_mem
    (fun g hg => (irreducible_of_mem_primeFactors hg).natDegree_pos)]
  exact prod_primeFactors_eq hm hsq

/-- The prime factors of the tail are exactly the prime factors of `f` of
degree `> i`. -/
theorem mem_primeFactors_ddTail {f : F[X]} (hf0 : f ≠ 0) {i : ℕ} {p : F[X]} :
    p ∈ primeFactors (ddTail f i) ↔ p ∈ primeFactors f ∧ i < p.natDegree := by
  rw [mem_primeFactors_iff'' (ddTail_monic f i).ne_zero]
  constructor
  · rintro ⟨hirr, hnorm, hdvd⟩
    obtain ⟨g, hgmem, hpg⟩ :=
      ((UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr).dvd_finsetProd_iff
        id).mp hdvd
    rw [Finset.mem_filter] at hgmem
    obtain ⟨hgf, hgi⟩ := hgmem
    have hgf' := (mem_primeFactors_iff'' hf0).mp hgf
    have hpg' : p = g := by
      have hassoc := hirr.associated_of_dvd hgf'.1 hpg
      calc p = normalize p := hnorm.symm
        _ = normalize g := normalize_eq_normalize hpg hassoc.symm.dvd
        _ = g := hgf'.2.1
    rw [hpg']
    exact ⟨hgf, hgi⟩
  · rintro ⟨hpf, hideg⟩
    have hpf' := (mem_primeFactors_iff'' hf0).mp hpf
    refine ⟨hpf'.1, hpf'.2.1, Finset.dvd_prod_of_mem id ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hpf, hideg⟩

/-- The loop's termination condition: `fᵢ = 1` exactly when all factor
degrees are `≤ i`, i.e. `i ≥ s`. -/
theorem ddTail_eq_one_iff {f : F[X]} {i : ℕ} :
    ddTail f i = 1 ↔ ddLength f ≤ i := by
  constructor
  · intro h1
    by_contra hlt
    rw [not_le, ddLength] at hlt
    have hne : (primeFactors f).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sup_empty] at hlt
      exact absurd hlt (by simp)
    obtain ⟨m, hmmem, hmax⟩ := Finset.exists_mem_eq_sup _ hne natDegree
    have hdvd : m ∣ ddTail f i := by
      refine Finset.dvd_prod_of_mem id ?_
      rw [Finset.mem_filter]
      exact ⟨hmmem, by omega⟩
    rw [h1] at hdvd
    exact (irreducible_of_mem_primeFactors hmmem).not_isUnit
      (isUnit_of_dvd_one hdvd)
  · intro hle
    rw [ddLength] at hle
    rw [ddTail, Finset.filter_false_of_mem, Finset.prod_empty]
    intro g hg
    have := Finset.le_sup (f := natDegree) hg
    omega

/-- Peeling the loop: `fᵢ = gᵢ₊₁ · fᵢ₊₁` (split the degree-`> i` factor set
at degree `i + 1`). -/
theorem ddTail_succ (f : F[X]) (i : ℕ) :
    ddTail f i = ddFactor f (i + 1) * ddTail f (i + 1) := by
  rw [ddTail, ddTail, ddFactor]
  conv_lhs => rw [← Finset.prod_filter_mul_prod_filter_not
    ((primeFactors f).filter fun g => i < g.natDegree)
    (fun g => g.natDegree = i + 1) id]
  congr 1
  · congr 1
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun g _ => by omega
  · congr 1
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun g _ => by omega

/-- The fuel bound: factor degrees are at most `deg f`. -/
theorem ddLength_le_natDegree {f : F[X]} (hf0 : f ≠ 0) :
    ddLength f ≤ f.natDegree :=
  Finset.sup_le fun _ hg =>
    Polynomial.natDegree_le_of_dvd ((mem_primeFactors_iff'' hf0).mp hg).2.2 hf0

/-- **The early-abort criterion** (the book's remark after Theorem 14.4):
if `fᵢ ≠ 1` has degree `< 2(i + 1)`, then — all its factors having degree
`≥ i + 1` — the factor set of `fᵢ` is a single prime `p = fᵢ`, so `fᵢ` is
irreducible, `s = deg fᵢ`, and the rest of the decomposition is
`(1, …, 1, fᵢ)` with `fᵢ` in position `deg fᵢ`. -/
theorem ddTail_early_abort {f : F[X]} {i : ℕ} (h1 : ddTail f i ≠ 1)
    (hdeg : (ddTail f i).natDegree < 2 * (i + 1)) :
    ddLength f = (ddTail f i).natDegree ∧
    i + 1 ≤ (ddTail f i).natDegree ∧
    ddFactor f ((ddTail f i).natDegree) = ddTail f i ∧
    (∀ j, i < j → j < (ddTail f i).natDegree → ddFactor f j = 1) := by
  -- the degree-`> i` factor set is a singleton `{p}`
  have hSne : ((primeFactors f).filter (fun g => i < g.natDegree)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    apply h1
    rw [ddTail, hemp, Finset.prod_empty]
  obtain ⟨p, hpS⟩ := hSne
  obtain ⟨hpf, hpdeg⟩ := Finset.mem_filter.mp hpS
  have hproddeg : (ddTail f i).natDegree
      = ∑ g ∈ (primeFactors f).filter (fun g => i < g.natDegree),
          g.natDegree := by
    rw [ddTail]
    exact Polynomial.natDegree_prod _ _ (fun g hg =>
      (irreducible_of_mem_primeFactors (Finset.mem_filter.mp hg).1).ne_zero)
  have hSp : (primeFactors f).filter (fun g => i < g.natDegree) = {p} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨hpS, fun r hrS => ?_⟩
    by_contra hne
    have hrdeg := (Finset.mem_filter.mp hrS).2
    have hsum : r.natDegree + p.natDegree
        ≤ ∑ g ∈ (primeFactors f).filter (fun g => i < g.natDegree),
            g.natDegree := by
      rw [← Finset.sum_pair hne]
      refine Finset.sum_le_sum_of_subset ?_
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rwa [h]
      · rw [Finset.mem_singleton.mp h]
        exact hpS
    omega
  have hddp : ddTail f i = p := by
    rw [ddTail, hSp, Finset.prod_singleton]
    rfl
  rw [hddp]
  refine ⟨?_, by omega, ?_, ?_⟩
  · -- `s = deg p`
    refine le_antisymm (Finset.sup_le fun g hg => ?_)
      (Finset.le_sup (f := natDegree) hpf)
    by_cases hgi : i < g.natDegree
    · have hgS : g ∈ (primeFactors f).filter (fun g => i < g.natDegree) :=
        Finset.mem_filter.mpr ⟨hg, hgi⟩
      rw [hSp, Finset.mem_singleton] at hgS
      rw [hgS]
    · omega
  · -- the part in position `deg p` is `p` itself
    have hslice : (primeFactors f).filter
        (fun g => g.natDegree = p.natDegree) = {p} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨Finset.mem_filter.mpr ⟨hpf, rfl⟩, fun r hr => ?_⟩
      obtain ⟨hrf, hrd⟩ := Finset.mem_filter.mp hr
      have hrS : r ∈ (primeFactors f).filter (fun g => i < g.natDegree) :=
        Finset.mem_filter.mpr ⟨hrf, by omega⟩
      rw [hSp, Finset.mem_singleton] at hrS
      exact hrS
    rw [ddFactor, hslice, Finset.prod_singleton]
    rfl
  · -- the parts strictly between are `1`
    intro j hij hjd
    rw [ddFactor, Finset.filter_false_of_mem, Finset.prod_empty]
    intro g hg hgj
    have hgS : g ∈ (primeFactors f).filter (fun g' => i < g'.natDegree) :=
      Finset.mem_filter.mpr ⟨hg, by omega⟩
    rw [hSp, Finset.mem_singleton] at hgS
    rw [hgS] at hgj
    omega

omit [DecidableEq F] in
/-- Assembling the early-abort output: a `range'`-map whose values are `1`
except at the endpoint is a `replicate` followed by the endpoint. -/
theorem map_range'_eq_replicate_append (g : ℕ → F[X]) :
    ∀ (n a : ℕ), (∀ j, a ≤ j → j < a + n → g j = 1) →
      (List.range' a (n + 1)).map g = List.replicate n 1 ++ [g (a + n)] := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a hmid
    have hcons : (List.range' a (n + 1 + 1)).map g
        = g a :: (List.range' (a + 1) (n + 1)).map g := rfl
    rw [hcons, hmid a le_rfl (by omega),
      ih (a + 1) (fun j hj1 hj2 => hmid j (by omega) (by omega)),
      List.replicate_succ]
    have hidx : a + 1 + n = a + (n + 1) := by omega
    rw [hidx]
    rfl

/-! ### The two gcd computations of the loop body -/

/-- Adding a multiple of `c` to the first argument does not change the gcd. -/
theorem gcd_congr_left_of_dvd_sub {a b c : F[X]} (h : c ∣ a - b) :
    gcd a c = gcd b c := by
  have h1 : gcd a c ∣ gcd b c := by
    refine dvd_gcd ?_ (gcd_dvd_right a c)
    have hab : gcd a c ∣ a - b := (gcd_dvd_right a c).trans h
    simpa using dvd_sub (gcd_dvd_left a c) hab
  have h2 : gcd b c ∣ gcd a c := by
    refine dvd_gcd ?_ (gcd_dvd_right b c)
    have hab : gcd b c ∣ a - b := (gcd_dvd_right b c).trans h
    simpa using dvd_add (gcd_dvd_left b c) hab
  rw [← normalize_gcd a c, ← normalize_gcd b c]
  exact normalize_eq_normalize h1 h2

/-- **The heart of Theorem 14.4** (the book's application of Theorem 14.2):
`gcd(x^(q^(i+1)) − x, fᵢ) = gᵢ₊₁`, the product of the monic irreducible
factors of `f` of degree exactly `i + 1`.  Both sides are monic squarefree,
so it suffices that they have the same prime-factor set: a prime divides
the gcd iff it divides `x^(q^(i+1)) − x` (degree dividing `i + 1`, by the
criterion) and divides `fᵢ` (a factor of `f` of degree `> i`) — together,
degree exactly `i + 1`. -/
theorem gcd_X_pow_card_pow_sub_X_ddTail [Fintype F] {f : F[X]} (hm : f.Monic)
    (hsq : Squarefree f) (i : ℕ) :
    gcd (X ^ Fintype.card F ^ (i + 1) - X) (ddTail f i) = ddFactor f (i + 1) := by
  have ht0 : ddTail f i ≠ 0 := (ddTail_monic f i).ne_zero
  have hg0 : gcd (X ^ Fintype.card F ^ (i + 1) - X) (ddTail f i) ≠ 0 := by
    rw [Ne, gcd_eq_zero_iff]
    rintro ⟨-, h⟩
    exact ht0 h
  have hgm : (gcd (X ^ Fintype.card F ^ (i + 1) - X) (ddTail f i)).Monic :=
    (Polynomial.normalize_eq_self_iff_monic hg0).mp (normalize_gcd _ _)
  have hgsq : Squarefree (gcd (X ^ Fintype.card F ^ (i + 1) - X) (ddTail f i)) :=
    (squarefree_ddTail hsq i).squarefree_of_dvd (gcd_dvd_right _ _)
  have hset : primeFactors (gcd (X ^ Fintype.card F ^ (i + 1) - X) (ddTail f i))
      = (primeFactors f).filter (fun g => g.natDegree = i + 1) := by
    ext p
    rw [mem_primeFactors_iff'' hg0, Finset.mem_filter]
    constructor
    · rintro ⟨hirr, hnorm, hdvd⟩
      rw [dvd_gcd_iff] at hdvd
      obtain ⟨hdA, hdT⟩ := hdvd
      have hdd : p.natDegree ∣ i + 1 :=
        (irreducible_dvd_X_pow_card_pow_sub_X_iff hirr).mp hdA
      have hmemT : p ∈ primeFactors f ∧ i < p.natDegree :=
        (mem_primeFactors_ddTail hm.ne_zero).mp
          ((mem_primeFactors_iff'' ht0).mpr ⟨hirr, hnorm, hdT⟩)
      have hdegle : p.natDegree ≤ i + 1 := Nat.le_of_dvd (Nat.succ_pos i) hdd
      exact ⟨hmemT.1, by omega⟩
    · rintro ⟨hpf, hdeg⟩
      have hpf' := (mem_primeFactors_iff'' hm.ne_zero).mp hpf
      refine ⟨hpf'.1, hpf'.2.1, dvd_gcd ?_ ?_⟩
      · exact (irreducible_dvd_X_pow_card_pow_sub_X_iff hpf'.1).mpr
          (hdeg ▸ dvd_refl _)
      · have hmem : p ∈ primeFactors (ddTail f i) :=
          (mem_primeFactors_ddTail hm.ne_zero).mpr ⟨hpf, by omega⟩
        exact ((mem_primeFactors_iff'' ht0).mp hmem).2.2
  calc gcd (X ^ Fintype.card F ^ (i + 1) - X) (ddTail f i)
      = (primeFactors (gcd (X ^ Fintype.card F ^ (i + 1) - X) (ddTail f i))).prod id :=
        (prod_primeFactors_eq hgm hgsq).symm
    _ = ((primeFactors f).filter (fun g => g.natDegree = i + 1)).prod id := by
        rw [hset]
    _ = ddFactor f (i + 1) := rfl

/-! ### The `h` chain: `hᵢ ≡ x^(qⁱ) mod f` -/

omit [DecidableEq F] in
/-- The remainder is congruent to the polynomial itself. -/
theorem dvd_modByMonic_sub (f p : F[X]) : f ∣ p %ₘ f - p := by
  rw [Polynomial.modByMonic_eq_sub_mul_div p f]
  exact ⟨-(p /ₘ f), by ring⟩

omit [DecidableEq F] in
/-- Congruent polynomials have equal remainders. -/
theorem modByMonic_congr {f a b : F[X]} (hm : f.Monic) (h : f ∣ a - b) :
    a %ₘ f = b %ₘ f := by
  rw [← sub_eq_zero, ← Polynomial.sub_modByMonic,
    Polynomial.modByMonic_eq_zero_iff_dvd hm]
  exact h

omit [DecidableEq F] in
/-- The loop's `h`-update, in congruence form: if `h ≡ x^(qⁱ) mod T`, then
`(h rem T)^q rem T ≡ x^(q^(i+1)) mod T`.  (The loop powers `h` modulo the
current tail `T = fᵢ`, not modulo `f`; no monic hypothesis needed, the
remainder being unconditionally congruent.) -/
theorem dvd_powModByMonic_sub_pow {T h : F[X]} {q i : ℕ}
    (hcong : T ∣ h - X ^ q ^ i) :
    T ∣ (h %ₘ T) ^ q %ₘ T - X ^ q ^ (i + 1) := by
  have c1 : T ∣ h %ₘ T - X ^ q ^ i := by
    have h1 := dvd_add (dvd_modByMonic_sub T h) hcong
    rwa [sub_add_sub_cancel] at h1
  have c2 : T ∣ (h %ₘ T) ^ q - (X ^ q ^ i) ^ q :=
    c1.trans ((Commute.all _ _).sub_dvd_pow_sub_pow q)
  have c3 := dvd_add (dvd_modByMonic_sub T ((h %ₘ T) ^ q)) c2
  rw [sub_add_sub_cancel] at c3
  rwa [← pow_mul, ← pow_succ] at c3

/-! ### Algorithm 14.3, abstract rail -/

open Classical in
/-- The loop of Algorithm 14.3 (fuel-recursive): given `h = hᵢ` (congruent
to `x^(qⁱ)` mod `fᵢ`) and `fi = fᵢ`, run steps `i+1, i+2, …` until `fᵢ = 1`
or the early abort fires (or the fuel runs out), returning
`(gᵢ₊₁, gᵢ₊₂, …)`.  The `q`-th power runs mod the CURRENT `fᵢ` (the book's
remark: `hᵢ` is only needed modulo `fᵢ₋₁`), so the loop does not reference
the original `f` at all. -/
noncomputable def dddLoop (q : ℕ) : ℕ → ℕ → F[X] → F[X] → List F[X]
  | 0, _, _, _ => []
  | fuel + 1, i, h, fi =>
    if fi = 1 then []
    else if fi.natDegree < 2 * (i + 1) then
      List.replicate (fi.natDegree - i - 1) 1 ++ [fi]
    else
      gcd ((h %ₘ fi) ^ q %ₘ fi - X) fi ::
        dddLoop q fuel (i + 1) ((h %ₘ fi) ^ q %ₘ fi)
          (fi /ₘ gcd ((h %ₘ fi) ^ q %ₘ fi - X) fi)

/-- **Algorithm 14.3 (distinct-degree factorization), abstract rail.**
`h₀ = x`, `f₀ = f`; fuel `deg f` (enough, since factor degrees are at most
`deg f`). -/
noncomputable def distinctDegreeFactorization (q : ℕ) (f : F[X]) : List F[X] :=
  dddLoop q f.natDegree 0 X f

/-- The loop invariant of Theorem 14.4, discharged by induction on the fuel:
entering step `i + 1` with `hᵢ = x^(qⁱ) rem f` and `fᵢ = ddTail f i`, the
loop emits exactly `(gᵢ₊₁, …, g_s)`. -/
theorem dddLoop_ddTail [Fintype F] {f : F[X]} (hm : f.Monic)
    (hsq : Squarefree f) {q : ℕ} (hq : q = Fintype.card F) :
    ∀ (fuel i : ℕ) (h : F[X]), ddLength f ≤ i + fuel →
      ddTail f i ∣ h - X ^ q ^ i →
      dddLoop q fuel i h (ddTail f i)
        = (List.range' (i + 1) (ddLength f - i)).map (ddFactor f) := by
  subst hq
  intro fuel
  induction fuel with
  | zero =>
    intro i h hfuel _
    have h0 : ddLength f - i = 0 := by omega
    rw [h0]
    rfl
  | succ fuel ih =>
    intro i h hfuel hcong
    by_cases h1 : ddTail f i = 1
    · rw [dddLoop, ite_eq_left h1]
      have h0 : ddLength f - i = 0 := by
        have := ddTail_eq_one_iff.mp h1
        omega
      rw [h0]
      rfl
    · have hlt : i < ddLength f := by
        rcases Nat.lt_or_ge i (ddLength f) with h' | h'
        · exact h'
        · exact absurd (ddTail_eq_one_iff.mpr h') h1
      by_cases h2 : (ddTail f i).natDegree < 2 * (i + 1)
      · -- EARLY ABORT: the tail is a single irreducible in position `deg fᵢ`
        rw [dddLoop, ite_eq_right h1, ite_eq_left h2]
        obtain ⟨hlen, hge, hlast, hmid⟩ := ddTail_early_abort h1 h2
        rw [hlen,
          show (ddTail f i).natDegree - i
            = ((ddTail f i).natDegree - i - 1) + 1 from by omega,
          map_range'_eq_replicate_append (ddFactor f) _ _
            (fun j hj1 hj2 => hmid j (by omega) (by omega)),
          show i + 1 + ((ddTail f i).natDegree - i - 1)
            = (ddTail f i).natDegree from by omega,
          hlast, Nat.add_sub_cancel]
      · rw [dddLoop, ite_eq_right h1, ite_eq_right h2]
        -- the powered `h` is congruent to `x^(q^(i+1))` mod the tail
        have hstep : ddTail f i
            ∣ (h %ₘ ddTail f i) ^ Fintype.card F %ₘ ddTail f i
              - X ^ Fintype.card F ^ (i + 1) :=
          dvd_powModByMonic_sub_pow hcong
        have hdvdsub : ddTail f i
            ∣ ((h %ₘ ddTail f i) ^ Fintype.card F %ₘ ddTail f i - X)
              - (X ^ Fintype.card F ^ (i + 1) - X) := by
          rw [sub_sub_sub_cancel_right]
          exact hstep
        have hgcd : gcd ((h %ₘ ddTail f i) ^ Fintype.card F %ₘ ddTail f i - X)
              (ddTail f i)
            = ddFactor f (i + 1) := by
          rw [gcd_congr_left_of_dvd_sub hdvdsub]
          exact gcd_X_pow_card_pow_sub_X_ddTail hm hsq i
        have hdiv : ddTail f i /ₘ ddFactor f (i + 1) = ddTail f (i + 1) := by
          rw [ddTail_succ f i,
            Polynomial.mul_divByMonic_cancel_left _ (ddFactor_monic f (i + 1))]
        rw [hgcd, hdiv, ih (i + 1) _ (by omega) ?_]
        · have hs : ddLength f - i = (ddLength f - (i + 1)) + 1 := by omega
          rw [hs]
          rfl
        · -- the congruence descends to the next tail, which divides this one
          have hnext : ddTail f (i + 1) ∣ ddTail f i :=
            ⟨ddFactor f (i + 1), by rw [ddTail_succ f i]; ring⟩
          exact hnext.trans hstep

/-- **GG Theorem 14.4.** The distinct-degree factorization algorithm works
correctly as specified: for a squarefree monic `f`, Algorithm 14.3 computes
the distinct-degree decomposition of `f`. -/
theorem theorem_14_4 [Fintype F] {f : F[X]} (hm : f.Monic)
    (hsq : Squarefree f) :
    distinctDegreeFactorization (Fintype.card F) f
      = distinctDegreeDecomposition f := by
  have h := dddLoop_ddTail hm hsq (q := Fintype.card F) rfl f.natDegree 0 X
    (by simpa using ddLength_le_natDegree hm.ne_zero)
    (by rw [pow_zero, pow_one, sub_self]; exact dvd_zero _)
  rw [ddTail_zero hm hsq, Nat.sub_zero] at h
  rw [distinctDegreeFactorization, h, distinctDegreeDecomposition,
    List.range'_eq_map_range, List.map_map]
  congr 1
  funext j
  simp [Nat.add_comm]

/-! ### The bridge to the computable rail

The computable `AzPolynomial.distinctDegreeFactorization` (in
`Azurite/AzPolynomial/DistinctDegreeFactorization.lean`) mirrors `dddLoop`
step for step: the `q`-th powers by `powModByMonic` (limb-level
`AzNat`-exponent powering in `AzPolyMod fᵢ`, mod the current shrinking
tail), the gcd by the signed-subresultant `gcdMonic`, the exact division by
`divByMonic`, and the same early abort. -/

section Computable

variable {K : Type _} [Field K] [DecidableEq K]

/-- The power bridge inside a fixed `AzPolyMod` modulus, at the level of
reduced representatives: the limb-level power `a ^ (q : AzNat)` represents
`(toPoly a)^q rem f`.  (Both are the canonical reduced representative of
the same `AdjoinRoot` class.) -/
theorem toPoly_val_pow {fAz : AzPolynomial K}
    (hf : (AzPolynomial.toPoly fAz).Monic) (a : AzPolyMod fAz) (q : AzNat) :
    AzPolynomial.toPoly ((a ^ q).val)
      = AzPolynomial.toPoly a.val ^ q.toNat %ₘ AzPolynomial.toPoly fAz := by
  have : Fact (AzPolynomial.toPoly fAz).Monic := ⟨hf⟩
  have hmk := AzPolyMod.toAdjoin_powAzNat (f := fAz) a q
  rw [AzPolyMod.toAdjoin_def, AzPolyMod.toAdjoin_def, ← map_pow,
    AdjoinRoot.mk_eq_mk] at hmk
  calc AzPolynomial.toPoly ((a ^ q).val)
      = AzPolynomial.toPoly ((a ^ q).val) %ₘ AzPolynomial.toPoly fAz :=
        ((Polynomial.modByMonic_eq_self_iff hf).mpr
          (AzPolyMod.degree_toPoly_val_lt hf hf.ne_zero (a ^ q))).symm
    _ = AzPolynomial.toPoly a.val ^ q.toNat %ₘ AzPolynomial.toPoly fAz :=
        modByMonic_congr hf hmk

/-- The `h`-update bridge: `powModByMonic` represents
`(· rem f)^q rem f`. -/
theorem toPoly_powModByMonic {fAz : AzPolynomial K}
    (hf : (AzPolynomial.toPoly fAz).Monic) (a : AzPolynomial K) (q : AzNat) :
    AzPolynomial.toPoly (AzPolynomial.powModByMonic a q fAz)
      = (AzPolynomial.toPoly a %ₘ AzPolynomial.toPoly fAz) ^ q.toNat
          %ₘ AzPolynomial.toPoly fAz := by
  have hbase : AzPolynomial.toPoly (AzPolyMod.ofPoly (f := fAz) a).val
      = AzPolynomial.toPoly a %ₘ AzPolynomial.toPoly fAz := by
    show AzPolynomial.toPoly (AzPolynomial.modByMonic a fAz) = _
    exact AzPolynomial.toPoly_modByMonic hf hf.ne_zero a
  rw [AzPolynomial.powModByMonic, toPoly_val_pow hf _ q, hbase]

/-- The loop bridge: the computable loop represents the abstract loop,
step for step (including the early abort).  The divisor invariant carried
through the induction is monicity of the current tail, needed both for the
power bridge and for the division bridge; it propagates because the monic
gcd divides the monic tail exactly. -/
theorem map_toPoly_distinctDegreeFactorizationLoop (q : AzNat) :
    ∀ (fuel i : ℕ) (h : AzPolynomial K) (fi : AzPolynomial K),
      (AzPolynomial.toPoly fi).Monic →
      (AzPolynomial.distinctDegreeFactorizationLoop q fuel i h fi).map
          AzPolynomial.toPoly
        = dddLoop q.toNat fuel i
            (AzPolynomial.toPoly h) (AzPolynomial.toPoly fi) := by
  intro fuel
  induction fuel with
  | zero => intro i h fi _; rfl
  | succ fuel ih =>
    intro i h fi hfim
    have hfi0' : AzPolynomial.toPoly fi ≠ 0 := hfim.ne_zero
    rw [AzPolynomial.distinctDegreeFactorizationLoop, dddLoop]
    by_cases h1 : fi = 1
    · rw [ite_eq_left h1, ite_eq_left (by rw [h1, toPoly_one])]
      rfl
    · have h1' : AzPolynomial.toPoly fi ≠ 1 := by
        rw [Ne, ← toPoly_one (R := K), toPoly_inj]
        exact h1
      rw [ite_eq_right h1, ite_eq_right h1']
      by_cases h2 : fi.natDegree < 2 * (i + 1)
      · -- the early aborts fire together (the degrees agree)
        rw [ite_eq_left h2,
          ite_eq_left (by rw [AzPolynomial.natDegree_toPoly]; exact h2),
          List.map_append, List.map_replicate, toPoly_one,
          List.map_singleton, AzPolynomial.natDegree_toPoly]
      · rw [ite_eq_right h2,
          ite_eq_right (by rw [AzPolynomial.natDegree_toPoly]; exact h2)]
        have hpow := toPoly_powModByMonic hfim h q
        -- the gcd bridge
        have hg : AzPolynomial.toPoly
              (AzPolynomial.gcdMonic
                (AzPolynomial.powModByMonic h q fi - AzPolynomial.X) fi)
            = gcd ((AzPolynomial.toPoly h %ₘ AzPolynomial.toPoly fi) ^ q.toNat
                %ₘ AzPolynomial.toPoly fi - X) (AzPolynomial.toPoly fi) := by
          rw [AzPolynomial.toPoly_gcdMonic, AzPolynomial.toPoly_sub,
            AzPolynomial.toPoly_X, hpow]
        have hgcd0 : AzPolynomial.toPoly
            (AzPolynomial.gcdMonic
              (AzPolynomial.powModByMonic h q fi - AzPolynomial.X) fi) ≠ 0 := by
          rw [hg, Ne, gcd_eq_zero_iff]
          rintro ⟨-, hz⟩
          exact hfi0' hz
        have hgm : (AzPolynomial.toPoly
            (AzPolynomial.gcdMonic
              (AzPolynomial.powModByMonic h q fi - AzPolynomial.X) fi)).Monic := by
          refine (Polynomial.normalize_eq_self_iff_monic hgcd0).mp ?_
          rw [hg]
          exact normalize_gcd _ _
        -- the gcd divides the tail exactly, so the next tail is monic
        have hdvd : AzPolynomial.toPoly
              (AzPolynomial.gcdMonic
                (AzPolynomial.powModByMonic h q fi - AzPolynomial.X) fi)
            ∣ AzPolynomial.toPoly fi := by
          rw [hg]
          exact gcd_dvd_right _ _
        have hrec := Polynomial.modByMonic_add_div (AzPolynomial.toPoly fi)
          (AzPolynomial.toPoly
            (AzPolynomial.gcdMonic
              (AzPolynomial.powModByMonic h q fi - AzPolynomial.X) fi))
        rw [(Polynomial.modByMonic_eq_zero_iff_dvd hgm).mpr hdvd, zero_add]
          at hrec
        have hfim' : (AzPolynomial.toPoly (AzPolynomial.divByMonic fi
            (AzPolynomial.gcdMonic
              (AzPolynomial.powModByMonic h q fi - AzPolynomial.X) fi))).Monic := by
          rw [AzPolynomial.toPoly_divByMonic hgm hgcd0]
          exact hgm.of_mul_monic_left (by rwa [hrec])
        rw [List.map_cons, hg, ih (i + 1) _ _ hfim',
          AzPolynomial.toPoly_divByMonic hgm hgcd0, hg, hpow]

/-- **Correctness of the computable Algorithm 14.3** (Theorem 14.4,
transported): over a finite coefficient field with `q` elements, for
squarefree monic `f` the computable distinct-degree factorization
represents the distinct-degree decomposition of the represented
polynomial. -/
theorem map_toPoly_distinctDegreeFactorization [Fintype K] {q : AzNat}
    (hq : q.toNat = Fintype.card K) {f : AzPolynomial K}
    (hm : (AzPolynomial.toPoly f).Monic)
    (hsq : Squarefree (AzPolynomial.toPoly f)) :
    (AzPolynomial.distinctDegreeFactorization q f).map AzPolynomial.toPoly
      = distinctDegreeDecomposition (AzPolynomial.toPoly f) := by
  rw [AzPolynomial.distinctDegreeFactorization,
    map_toPoly_distinctDegreeFactorizationLoop q _ _ _ _ hm,
    AzPolynomial.toPoly_X, hq,
    show f.natDegree = (AzPolynomial.toPoly f).natDegree from
      (AzPolynomial.natDegree_toPoly f).symm]
  exact theorem_14_4 hm hsq

/-- Correctness of the computable Algorithm 14.3 at a CONCRETE prime
modulus: over `AzZMod p` (`p` prime, so a field with `p.toNat` elements —
`AzZMod.card_eq`), running the algorithm with `q := p` itself computes the
distinct-degree decomposition.  The modulus, the exponent, and every
residue stay limb-level `AzNat`s throughout. -/
theorem map_toPoly_distinctDegreeFactorization_azZMod {p : AzNat}
    [Fact (Nat.Prime p.toNat)] {f : AzPolynomial (AzZMod p)}
    (hm : (AzPolynomial.toPoly f).Monic)
    (hsq : Squarefree (AzPolynomial.toPoly f)) :
    (AzPolynomial.distinctDegreeFactorization p f).map AzPolynomial.toPoly
      = distinctDegreeDecomposition (AzPolynomial.toPoly f) :=
  map_toPoly_distinctDegreeFactorization (AzZMod.card_eq p).symm hm hsq

end Computable

end GG

end Azurite

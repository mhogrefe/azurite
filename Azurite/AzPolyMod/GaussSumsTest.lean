/-
  **The Gauss sums primality test, assembled from the rail**: the
  verdict theorem `prime_of_rail_checks` — if every check of
  Algorithm 4.4.5 PASSES at the level of the computable tower
  (`GaussTowerPQ` equalities, `step5Check`, the generator and table
  checks, and a clean step-6 scan), then `n` is prime.

  This is the `some true`-soundness core of the checker: the proof
  is by contradiction through `theorem_4_4_6_composite_tower` — a
  composite `n` surviving the checks would be factored by the
  step-6 scan, which the hypotheses say came up clean.  Each rail
  check crosses into the tower hypotheses through the bridge stack:

  * step 3/4: the `powAzNat` equality against `zetaPPowT` becomes
    the congruence `G^(p^w u) ≡ ζ_p^l (mod n)` via
    `reduceT_gaussSum`, `constT_pow`, and the kernel theorem
    `natCast_dvd_iff_reduceT`;
  * step 5: `step5Check = true` becomes the divisor-quantified
    non-divisibility via `not_dvd_of_towerContentGcd_eq_one`, with
    the `∀ j`-extension by `ζ_p`-periodicity;
  * the tables and the generator enter directly.

  The computable `Option Bool` wrapper (performing these checks and
  the arithmetic side conditions) is the next layer.
-/
import Azurite.AzPolyMod.Equiv.TowerContent
import Azurite.CrandallPomerance.Chapter4.Algorithm_4_4_5

namespace Azurite

namespace AzPolyMod

open AzPolynomial

/-- **The `some true`-soundness core of the Gauss sums test**: if all
rail-level checks pass and the step-6 scan finds no nontrivial
factor, `n` is prime. -/
theorem prime_of_rail_checks
    {n : AzNat} {I F : ℕ} [Fact (1 < n.toNat)]
    (hI : Squarefree I) (hF : Squarefree F)
    (hqI : ∀ q ∈ F.primeFactors, (q - 1) ∣ I)
    (hgcd : Nat.Coprime (I * F) n.toNat) (hnF : n.toNat < F ^ 2)
    {w u : ℕ → ℕ}
    (hw : ∀ p ∈ I.primeFactors, 0 < w p)
    (hu : ∀ p ∈ I.primeFactors, ¬p ∣ u p)
    {lTab : ℕ → ℕ → ℕ} {lq : ℕ → ℕ} {l : ℕ} {q₀ : ℕ → ℕ}
    (hq₀ : ∀ p ∈ I.primeFactors, q₀ p ∈ F.primeFactors ∧ p ∣ q₀ p - 1)
    {g : ℕ → ℕ} {gu : (q : ℕ) → (ZMod q)ˣ}
    (hgu : ∀ q ∈ F.primeFactors, ((g q : ℕ) : ZMod q) = (gu q : ZMod q))
    (hgen : ∀ q, q ∈ F.primeFactors → ∀ x, x ∈ Subgroup.zpowers (gu q))
    {e e' : ℕ → AzNat}
    (he : ∀ p ∈ I.primeFactors, (e p).toNat = p ^ w p * u p)
    (he' : ∀ p ∈ I.primeFactors, (e' p).toNat = p ^ (w p - 1) * u p)
    (hstep : ∀ q (_ : q ∈ F.primeFactors) [Fact q.Prime],
      ∀ p (_ : p ∈ (q - 1).primeFactors) [Fact p.Prime],
      (gaussSumT n p q (g q)).powAzNat (e p) = zetaPPowT n p q (lTab p q))
    (h5 : ∀ p (_ : p ∈ I.primeFactors) [Fact p.Prime]
      [Fact (q₀ p).Prime],
      step5Check n p (q₀ p)
        ((gaussSumT n p (q₀ p) (g (q₀ p))).powAzNat (e' p)) = true)
    (hlq : ∀ q ∈ F.primeFactors, ∀ p ∈ (q - 1).primeFactors,
      lq q ≡ lTab p q [MOD p])
    (hl : ∀ q ∈ F.primeFactors,
      ((l : ℕ) : ZMod q) = ((gu q ^ lq q : (ZMod q)ˣ) : ZMod q))
    (hscan : ∀ j, 0 < j → j < I → l ^ j % F ∣ n.toNat →
      l ^ j % F = 1 ∨ l ^ j % F = n.toNat) :
    n.toNat.Prime := by
  have hn1 : 1 < n.toNat := Fact.out
  by_contra hncomp
  -- the reduction of a step-3/4-shaped element: an equality in the
  -- tower is the congruence in `ℤ[ζ_p, ζ_q]`
  have hreduce : ∀ (q : ℕ) (hq : q ∈ F.primeFactors),
      ∀ (p : ℕ) (hp : p ∈ (q - 1).primeFactors),
      ∀ (_ : Fact q.Prime) (_ : Fact p.Prime) (E L : ℕ),
      reduceT n p q (gaussSum
          (MulChar.ofRootOfUnity (CP.zetaPQUnit_mem hp) (hgen q hq))
          (AddChar.zmodChar q (CP.isPrimitiveRoot_zetaQPQ hp).pow_eq_one)
          ^ E
        - ((CP.zetaPQUnit p q : (CP.CycPQ p q)ˣ) : CP.CycPQ p q) ^ L)
      = (gaussSumT n p q (g q)) ^ E - zetaPPowT n p q L := by
    intro q hq p hp _ _ E L
    rw [map_sub, map_pow, map_pow,
      reduceT_gaussSum n hp (hgen q hq) (hgu q hq),
      CP.val_zetaPQUnit hp, reduceT_zetaP, constT_pow, zetaPPowT]
  have hfound : ∃ j, 0 < j ∧ j < I ∧ l ^ j % F ∣ n.toNat
      ∧ 1 < l ^ j % F ∧ l ^ j % F < n.toNat := by
    refine CP.theorem_4_4_6_composite_tower hn1 hncomp hI hF hqI hgcd hnF
      hw hu (lTab := lTab) (lq := lq) (l := l) (q₀ := q₀) hq₀
      (g := gu) hgen ?_ ?_ hlq hl
    · -- step 3/4: rail equality → tower congruence
      intro q hq _ p hp
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      have hpI : p ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans (hqI q hq), hI.ne_zero⟩
      have hrail := hstep q hq p hp
      rw [powAzNat_eq_pow, he p hpI] at hrail
      rw [natCast_dvd_iff_reduceT, hreduce q hq p hp ‹_› ‹_›, hrail,
        sub_self]
    · -- step 5: `step5Check = true` → divisor-quantified
      -- non-divisibility, extended to all `j` by periodicity
      intro q hq _ p hp hq₀p d hd hd1 j
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      have hpI : p ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans (hqI q hq), hI.ne_zero⟩
      subst hq₀p
      have hrail := h5 p hpI
      rw [step5Check, List.all_eq_true] at hrail
      -- reduce `j` mod `p` (the tower `ζ_p` has order `p`)
      have hζp : ((CP.zetaPQUnit p (q₀ p) : (CP.CycPQ p (q₀ p))ˣ)
          : CP.CycPQ p (q₀ p)) ^ p = 1 := by
        rw [← Units.val_pow_eq_pow_val,
          (CP.isPrimitiveRoot_zetaPQUnit hp).pow_eq_one, Units.val_one]
      have hper : ((CP.zetaPQUnit p (q₀ p) : (CP.CycPQ p (q₀ p))ˣ)
          : CP.CycPQ p (q₀ p)) ^ j
          = ((CP.zetaPQUnit p (q₀ p) : (CP.CycPQ p (q₀ p))ˣ)
            : CP.CycPQ p (q₀ p)) ^ (j % p) := by
        conv_lhs => rw [← Nat.div_add_mod j p, pow_add, pow_mul, hζp,
          one_pow, one_mul]
      rw [hper]
      -- the rail check at `j % p`
      have hjp : j % p ∈ List.range p :=
        List.mem_range.mpr (Nat.mod_lt j
          (Nat.prime_of_mem_primeFactors hp).pos)
      have hcheck := hrail (j % p) hjp
      rw [decide_eq_true_eq] at hcheck
      have hgcd1 : (towerContentGcd n p (q₀ p)
          ((gaussSumT n p (q₀ p) (g (q₀ p))).powAzNat (e' p)
            - zetaPPowT n p (q₀ p) (j % p))).toNat = 1 := by
        rw [hcheck]
        exact AzNat.toNat_ofNat 1
      have hred := hreduce (q₀ p) hq p hp ‹_› ‹_›
        (p ^ (w p - 1) * u p) (j % p)
      rw [powAzNat_eq_pow, he' p hpI] at hgcd1
      rw [← hred] at hgcd1
      exact not_dvd_of_towerContentGcd_eq_one n p (q₀ p) _ hgcd1 d hd hd1

  obtain ⟨j, hj0, hjI, hjdvd, hj1, hjn⟩ := hfound
  rcases hscan j hj0 hjI hjdvd with h | h <;> omega

/-! ### The computable wrapper -/

section Lists

/-- A prime dividing a list product divides some element. -/
private theorem prime_dvd_list_prod {r : ℕ} (hr : r.Prime) :
    ∀ {l : List ℕ}, r ∣ l.prod → ∃ q ∈ l, r ∣ q := by
  intro l
  induction l with
  | nil =>
    intro h
    rw [List.prod_nil, Nat.dvd_one] at h
    exact absurd h hr.one_lt.ne'
  | cons a l ih =>
    intro h
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨q, hq, hdvd⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hdvd⟩

/-- The product of distinct primes is squarefree. -/
theorem squarefree_prod_of_nodup_primes :
    ∀ {l : List ℕ}, l.Nodup → (∀ p ∈ l, p.Prime) → Squarefree l.prod := by
  intro l
  induction l with
  | nil =>
    intro _ _
    rw [List.prod_nil]
    exact squarefree_one
  | cons a l ih =>
    intro hnd hpr
    rw [List.prod_cons]
    have ha : a.Prime := hpr a List.mem_cons_self
    have hco : Nat.Coprime a l.prod := by
      rw [Nat.Prime.coprime_iff_not_dvd ha]
      intro hdvd
      obtain ⟨q, hq, hdvd'⟩ := prime_dvd_list_prod ha hdvd
      rw [(Nat.prime_dvd_prime_iff_eq ha
        (hpr q (List.mem_cons_of_mem _ hq))).mp hdvd'] at hnd
      exact (List.nodup_cons.mp hnd).1 hq
    exact (Nat.squarefree_mul hco).mpr
      ⟨ha.squarefree, ih (List.nodup_cons.mp hnd).2
        (fun p hp => hpr p (List.mem_cons_of_mem _ hp))⟩

/-- The prime factors of a product of distinct primes are exactly the
list. -/
theorem mem_primeFactors_prod_iff {l : List ℕ} (_ : l.Nodup)
    (hpr : ∀ p ∈ l, p.Prime) {r : ℕ} :
    r ∈ l.prod.primeFactors ↔ r ∈ l := by
  constructor
  · intro hm
    obtain ⟨q, hq, hdvd⟩ := prime_dvd_list_prod
      (Nat.prime_of_mem_primeFactors hm)
      (Nat.dvd_of_mem_primeFactors hm)
    rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hm)
      (hpr q hq)).mp hdvd]
  · intro hm
    refine Nat.mem_primeFactors.mpr ⟨hpr r hm, List.dvd_prod hm, ?_⟩
    exact Nat.pos_iff_ne_zero.mp
      (List.prod_pos fun p hp => (hpr p hp).pos)

end Lists

/-- **The certificate of the Gauss sums primality test**: the
factorizations of `I` and `F`, the step-3/4 tables `w`, `u`,
`l(p,q)`, the step-5 choices `q₀`, the primitive roots `g`, and the
step-6 data `l(q)`, `l`.  (The large values `u p` and `l` are plain
naturals in this first wrapper; their limb-level port follows the
usual two-rail pattern.) -/
structure GaussSumsCert where
  Ips : List ℕ
  Fps : List ℕ
  w : ℕ → ℕ
  u : ℕ → ℕ
  lTab : ℕ → ℕ → ℕ
  lq : ℕ → ℕ
  l : ℕ
  q₀ : ℕ → ℕ
  g : ℕ → ℕ

section Checker

variable (n : AzNat) (c : GaussSumsCert)

/-- The step-3/4 exponent `p^(w p) · u p` at the limb level. -/
def certE (p : ℕ) : AzNat := AzNat.ofNat (p ^ c.w p * c.u p)

/-- The step-5 exponent `p^(w p − 1) · u p` at the limb level. -/
def certE' (p : ℕ) : AzNat := AzNat.ofNat (p ^ (c.w p - 1) * c.u p)

/-- The step-3/4 check at a pair, instance-gated on the primality
facts the types need. -/
def pairCheck [Fact (1 < n.toNat)] (q p : ℕ) : Bool :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    decide ((gaussSumT n p q (c.g q)).powAzNat (certE c p)
      = zetaPPowT n p q (c.lTab p q))
  else false

/-- The step-5 check at `p` (against `q₀ p`), instance-gated. -/
def pCheck [Fact (1 < n.toNat)] (p : ℕ) : Bool :=
  if hp : p.Prime then
    if hq : (c.q₀ p).Prime then
      letI : Fact p.Prime := ⟨hp⟩
      letI : Fact (c.q₀ p).Prime := ⟨hq⟩
      decide (0 < c.w p) && decide (¬p ∣ c.u p)
        && decide (c.q₀ p ∈ c.Fps) && decide (p ∣ c.q₀ p - 1)
        && step5Check n p (c.q₀ p)
          ((gaussSumT n p (c.q₀ p) (c.g (c.q₀ p))).powAzNat (certE' c p))
    else false
  else false

/-- The per-`q` checks: primality, `q − 1 ∣ I`, the verified
primitive root, the step-3/4 pair checks over the prime factors of
`q − 1`, and the step-6 tables. -/
def qCheck [Fact (1 < n.toNat)] (q : ℕ) : Bool :=
  if hq : q.Prime then
    letI : Fact q.Prime := ⟨hq⟩
    decide ((q - 1) ∣ c.Ips.prod)
      && decide (Nat.Coprime (c.g q) q)
      && (c.Ips.filter (fun r => decide (r ∣ q - 1))).all
        (fun r => decide (((c.g q : ℕ) : ZMod q) ^ ((q - 1) / r) ≠ 1))
      && (c.Ips.filter (fun r => decide (r ∣ q - 1))).all
        (fun p => pairCheck n c q p
          && decide (c.lq q ≡ c.lTab p q [MOD p]))
      && decide (((c.l : ℕ) : ZMod q)
        = ((c.g q : ℕ) : ZMod q) ^ c.lq q)
  else false

/-- The step-6 divisor scan comes up clean: no `l^j mod F` is a
nontrivial factor of `n`. -/
def scanCheck : Bool :=
  (List.range c.Ips.prod).all fun j =>
    (j == 0)
      || (let d := c.l ^ j % c.Fps.prod
          (d == 1) || !(n % AzNat.ofNat d == AzNat.ofNat 0)
            || (AzNat.ofNat d == n))

/-- **The Gauss sums primality test** (Algorithm 4.4.5 as a
checker): verify the certificate's arithmetic side conditions, the
generator checks, the step-3/4 congruences and step-5 coprimality
checks in the computable tower, the step-6 tables, and the divisor
scan.  `true` PROVES `n` prime (`gaussSumsTest_eq_true`). -/
def gaussSumsTest : Bool :=
  if h1 : AzNat.ofNat 1 < n then
    letI : Fact (1 < n.toNat) := ⟨by
      have h := (AzNat.lt_iff_toNat_lt _ _).mp h1
      rwa [AzNat.toNat_ofNat] at h⟩
    decide c.Ips.Nodup && c.Ips.all (fun p => decide p.Prime)
      && decide c.Fps.Nodup && c.Fps.all (fun q => decide q.Prime)
      && (AzNat.gcd (AzNat.ofNat (c.Ips.prod * c.Fps.prod)) n
        == AzNat.ofNat 1)
      && decide (n < AzNat.ofNat (c.Fps.prod ^ 2))
      && c.Ips.all (pCheck n c)
      && c.Fps.all (qCheck n c)
      && scanCheck n c
  else false

/-- **Soundness of the Gauss sums primality test**: a `true` verdict
proves `n` prime.  Every certificate check is unfolded and fed into
`prime_of_rail_checks` through the bridge stack. -/
theorem gaussSumsTest_eq_true (h : gaussSumsTest n c = true) :
    n.toNat.Prime := by
  rw [gaussSumsTest] at h
  by_cases h1 : AzNat.ofNat 1 < n
  case neg => rw [dif_neg h1] at h; exact absurd h (by simp)
  rw [dif_pos h1] at h
  haveI : Fact (1 < n.toNat) := ⟨by
    have h' := (AzNat.lt_iff_toNat_lt _ _).mp h1
    rwa [AzNat.toNat_ofNat] at h'⟩
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hIndup, hIpr⟩, hFndup⟩, hFpr⟩, hgcd'⟩, hlt⟩, hP⟩, hQ⟩,
    hscan'⟩ := h
  set I := c.Ips.prod with hIdef
  set F := c.Fps.prod with hFdef
  have memI : ∀ {r : ℕ}, r ∈ I.primeFactors ↔ r ∈ c.Ips :=
    mem_primeFactors_prod_iff hIndup hIpr
  have memF : ∀ {r : ℕ}, r ∈ F.primeFactors ↔ r ∈ c.Fps :=
    mem_primeFactors_prod_iff hFndup hFpr
  -- unfold the per-`q` checks
  have hQ' : ∀ q ∈ c.Fps, (q - 1) ∣ I ∧ Nat.Coprime (c.g q) q
      ∧ (∀ r ∈ c.Ips, r ∣ q - 1 →
          ((c.g q : ℕ) : ZMod q) ^ ((q - 1) / r) ≠ 1)
      ∧ (∀ p ∈ c.Ips, p ∣ q - 1 →
          pairCheck n c q p = true ∧ c.lq q ≡ c.lTab p q [MOD p])
      ∧ ((c.l : ℕ) : ZMod q) = ((c.g q : ℕ) : ZMod q) ^ c.lq q := by
    intro q hq
    have hcheck := hQ q hq
    rw [qCheck, dif_pos (hFpr q hq)] at hcheck
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter,
      decide_eq_true_eq, and_imp] at hcheck
    obtain ⟨⟨⟨⟨hdvd, hco⟩, hgen'⟩, hpair⟩, hl'⟩ := hcheck
    exact ⟨hdvd, hco, fun r hr hrd => hgen' r hr hrd,
      fun p hp hpd => hpair p hp hpd, hl'⟩
  -- unfold the per-`p` checks
  have hP' : ∀ p ∈ c.Ips, (c.q₀ p).Prime ∧ 0 < c.w p ∧ ¬p ∣ c.u p
      ∧ c.q₀ p ∈ c.Fps ∧ p ∣ c.q₀ p - 1
      ∧ ∀ (_ : Fact p.Prime) (_ : Fact (c.q₀ p).Prime),
        step5Check n p (c.q₀ p)
          ((gaussSumT n p (c.q₀ p) (c.g (c.q₀ p))).powAzNat (certE' c p))
          = true := by
    intro p hp
    have hcheck := hP p hp
    rw [pCheck, dif_pos (hIpr p hp)] at hcheck
    by_cases hq : (c.q₀ p).Prime
    · rw [dif_pos hq] at hcheck
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
      obtain ⟨⟨⟨⟨hw, hu⟩, hq₀F⟩, hq₀d⟩, h5⟩ := hcheck
      exact ⟨hq, hw, hu, hq₀F, hq₀d, fun _ _ => h5⟩
    · rw [dif_neg hq] at hcheck
      exact absurd hcheck (by simp)
  -- the generator family
  let gu : (q : ℕ) → (ZMod q)ˣ := fun q =>
    if h : Nat.Coprime (c.g q) q then ZMod.unitOfCoprime _ h else 1
  refine prime_of_rail_checks (n := n) (I := I) (F := F)
    (squarefree_prod_of_nodup_primes hIndup hIpr)
    (squarefree_prod_of_nodup_primes hFndup hFpr)
    (fun q hq => (hQ' q (memF.mp hq)).1)
    ?_ ?_
    (w := c.w) (u := c.u)
    (fun p hp => (hP' p (memI.mp hp)).2.1)
    (fun p hp => (hP' p (memI.mp hp)).2.2.1)
    (lTab := c.lTab) (lq := c.lq) (l := c.l) (q₀ := c.q₀)
    (fun p hp => ⟨memF.mpr (hP' p (memI.mp hp)).2.2.2.1,
      (hP' p (memI.mp hp)).2.2.2.2.1⟩)
    (g := c.g) (gu := gu) ?_ ?_
    (e := certE c) (e' := certE' c)
    (fun p _ => by rw [certE, AzNat.toNat_ofNat])
    (fun p _ => by rw [certE', AzNat.toNat_ofNat])
    ?_ ?_ ?_ ?_ ?_
  · -- gcd
    have h := congrArg AzNat.toNat hgcd'
    rwa [AzNat.toNat_gcd, AzNat.toNat_ofNat, AzNat.toNat_ofNat] at h
  · -- n < F²
    have h := (AzNat.lt_iff_toNat_lt _ _).mp hlt
    rwa [AzNat.toNat_ofNat] at h
  · -- hgu
    intro q hq
    have hco := (hQ' q (memF.mp hq)).2.1
    show _ = ((gu q : (ZMod q)ˣ) : ZMod q)
    rw [show gu q = ZMod.unitOfCoprime _ hco from dif_pos hco,
      ZMod.coe_unitOfCoprime]
  · -- hgen
    intro q hq
    haveI : Fact q.Prime := ⟨hFpr q (memF.mp hq)⟩
    have hco := (hQ' q (memF.mp hq)).2.1
    refine CP.forall_mem_zpowers_of_pow_div_prime (g := gu q) ?_
    intro r hr
    have hrI : r ∈ c.Ips := by
      have hrIF : r ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hr,
          (Nat.dvd_of_mem_primeFactors hr).trans
            (hQ' q (memF.mp hq)).1,
          (squarefree_prod_of_nodup_primes hIndup hIpr).ne_zero⟩
      exact memI.mp hrIF
    have hval := (hQ' q (memF.mp hq)).2.2.1 r hrI
      (Nat.dvd_of_mem_primeFactors hr)
    intro heq
    refine hval ?_
    have h := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) heq
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    rwa [show ((gu q : (ZMod q)ˣ) : ZMod q) = ((c.g q : ℕ) : ZMod q) from by
      rw [show gu q = ZMod.unitOfCoprime _ hco from dif_pos hco,
        ZMod.coe_unitOfCoprime]] at h
  · -- hstep
    intro q hq _ p hp _
    have hpI : p ∈ c.Ips := by
      have : p ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans
            (hQ' q (memF.mp hq)).1,
          (squarefree_prod_of_nodup_primes hIndup hIpr).ne_zero⟩
      exact memI.mp this
    have hpair := ((hQ' q (memF.mp hq)).2.2.2.1 p hpI
      (Nat.dvd_of_mem_primeFactors hp)).1
    rw [pairCheck, dif_pos (Nat.prime_of_mem_primeFactors hp),
      decide_eq_true_eq] at hpair
    exact hpair
  · -- h5
    intro p hp _ _
    exact (hP' p (memI.mp hp)).2.2.2.2.2 ‹_› ‹_›
  · -- hlq
    intro q hq p hp
    have hpI : p ∈ c.Ips := by
      have : p ∈ I.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans
            (hQ' q (memF.mp hq)).1,
          (squarefree_prod_of_nodup_primes hIndup hIpr).ne_zero⟩
      exact memI.mp this
    exact ((hQ' q (memF.mp hq)).2.2.2.1 p hpI
      (Nat.dvd_of_mem_primeFactors hp)).2
  · -- hl
    intro q hq
    have hco := (hQ' q (memF.mp hq)).2.1
    rw [(hQ' q (memF.mp hq)).2.2.2.2, Units.val_pow_eq_pow_val,
      show ((gu q : (ZMod q)ˣ) : ZMod q) = ((c.g q : ℕ) : ZMod q) from by
        rw [show gu q = ZMod.unitOfCoprime _ hco from dif_pos hco,
          ZMod.coe_unitOfCoprime]]
  · -- hscan
    intro j hj0 hjI hjdvd
    have hcheck := hscan' -- scanCheck = true
    rw [scanCheck, List.all_eq_true] at hcheck
    have hj := hcheck j (List.mem_range.mpr hjI)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at hj
    rcases hj with hj | hj
    · omega
    rcases hj with hj | hj
    case inr =>
      exact Or.inr (by
        have h := congrArg AzNat.toNat hj
        rwa [AzNat.toNat_ofNat] at h)
    rcases hj with hj | hj
    · exact Or.inl hj
    · -- the divisibility branch is contradicted
      exfalso
      rw [beq_eq_false_iff_ne] at hj
      refine hj ?_
      apply AzNat.toNat_injective
      rw [AzNat.toNat_mod, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
      obtain ⟨k, hk⟩ := hjdvd
      rw [hk]
      exact Nat.mul_mod_right _ _

/-! ### The gcd fold divides everything it folds -/

section Fold

variable (n : AzNat) (p q : ℕ) [Fact (1 < n.toNat)] [Fact p.Prime]
  [Fact q.Prime]

private theorem foldl_gcd_dvd {α : Type _} (f : α → AzNat) :
    ∀ (l : List α) (acc : AzNat),
    ((l.foldl (fun a x => AzNat.gcd a (f x)) acc).toNat ∣ acc.toNat)
      ∧ ∀ x ∈ l,
        (l.foldl (fun a x => AzNat.gcd a (f x)) acc).toNat ∣ (f x).toNat := by
  intro l
  induction l with
  | nil =>
    intro acc
    exact ⟨dvd_rfl, by simp⟩
  | cons v l ih =>
    intro acc
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (AzNat.gcd acc (f v))
    refine ⟨h1.trans ?_, ?_⟩
    · rw [AzNat.toNat_gcd]
      exact Nat.gcd_dvd_left _ _
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1.trans (by
          rw [AzNat.toNat_gcd]
          exact Nat.gcd_dvd_right _ _)
      · exact h2 x hx

omit [Fact q.Prime] in
/-- The content gcd divides its seed `n` and every grid entry. -/
theorem towerContentGcd_dvd (T : GaussTowerPQ n p q) :
    (towerContentGcd n p q T).toNat ∣ n.toNat
      ∧ ∀ c2 ∈ T.val.coeffs, ∀ c1 ∈ c2.val.coeffs,
        (towerContentGcd n p q T).toNat ∣ c1.val.toNat := by
  rw [towerContentGcd]
  have houter : ∀ (l : List (GaussTowerP n p)) (acc : AzNat),
      ((l.foldl (fun acc' c2 =>
          c2.val.coeffs.foldl (fun acc'' c1 => AzNat.gcd acc'' c1.val)
            acc') acc).toNat ∣ acc.toNat)
        ∧ ∀ c2 ∈ l, ∀ c1 ∈ c2.val.coeffs,
          (l.foldl (fun acc' c2 =>
            c2.val.coeffs.foldl (fun acc'' c1 => AzNat.gcd acc'' c1.val)
              acc') acc).toNat ∣ c1.val.toNat := by
    intro l
    induction l with
    | nil =>
      intro acc
      exact ⟨dvd_rfl, by simp⟩
    | cons c2 l ih =>
      intro acc
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih
        (c2.val.coeffs.foldl (fun acc'' c1 => AzNat.gcd acc'' c1.val) acc)
      have hinner := foldl_gcd_dvd (fun c1 : AzZMod n => c1.val)
        c2.val.coeffs.toList acc
      rw [← Array.foldl_toList] at h1 h2 ⊢
      refine ⟨h1.trans ?_, ?_⟩
      · rw [Array.foldl_toList]
        rw [← Array.foldl_toList]
        exact hinner.1
      · intro c2' hc2' c1 hc1
        rcases List.mem_cons.mp hc2' with rfl | hc2'
        · refine h1.trans ?_
          rw [Array.foldl_toList, ← Array.foldl_toList]
          exact hinner.2 c1 (by simpa using hc1)
        · exact h2 c2' hc2' c1 hc1
  have h := houter T.val.coeffs.toList n
  rw [← Array.foldl_toList]
  exact ⟨h.1, fun c2 hc2 => h.2 c2 (by simpa using hc2)⟩

end Fold

/-! ### The prime-side step-5 shortcut: a nonzero tower element has
content gcd `1` when `n` is prime -/

section PrimeShortcut

variable (n : AzNat) (p q : ℕ) [Fact (1 < n.toNat)] [Fact p.Prime]
  [Fact q.Prime]

private theorem azPolynomial_eq_zero {R : Type _} [Semiring R]
    (P : AzPolynomial R) (h : ∀ x ∈ P.coeffs, x = 0) : P = 0 := by
  by_cases hs : P.coeffs.size = 0
  · apply AzPolynomial.ext
    rw [Array.eq_empty_of_size_eq_zero hs]
    rfl
  · exfalso
    have hlast : P.coeffs.back? = some (P.coeffs[P.coeffs.size - 1]) := by
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem
        (by omega)]
    refine P.last_ne_zero ?_
    rw [hlast, h _ (P.coeffs.getElem_mem (by omega))]

private theorem azZMod_eq_zero {m : AzNat} [NeZero m.toNat]
    (x : AzZMod m) (h : x.val.toNat = 0) : x = 0 := by
  have hv : x.val = 0 :=
    AzNat.toNat_injective (by rw [h, AzNat.toNat_zero])
  cases x with
  | mk v hlt => cases hv; rfl

omit [Fact q.Prime] in
/-- A tower element whose whole coefficient grid vanishes is zero. -/
theorem gaussTower_eq_zero_of_grid (T : GaussTowerPQ n p q)
    (h : ∀ c2 ∈ T.val.coeffs, ∀ c1 ∈ c2.val.coeffs, c1.val.toNat = 0) :
    T = 0 := by
  haveI : NeZero n.toNat :=
    ⟨by have := Fact.out (p := 1 < n.toNat); omega⟩
  have hc2 : ∀ c2 ∈ T.val.coeffs, c2 = 0 := by
    intro c2 hc2
    have hval : c2.val = 0 :=
      azPolynomial_eq_zero _ fun c1 hc1 =>
        azZMod_eq_zero c1 (h c2 hc2 c1 hc1)
    exact AzPolyMod.ext (by rw [hval]; rfl)
  have hval : T.val = 0 := azPolynomial_eq_zero _ hc2
  exact AzPolyMod.ext (by rw [hval]; rfl)

omit [Fact q.Prime] in
/-- **The prime-`n` shortcut**: the content gcd of a NONZERO tower
element is `1` when `n` is prime — it divides the prime `n`, and the
value `n` would force the whole (canonical, sub-`n`) coefficient
grid to vanish. -/
theorem towerContentGcd_eq_one_of_ne_zero (hprime : n.toNat.Prime)
    (T : GaussTowerPQ n p q) (hT : T ≠ 0) :
    (towerContentGcd n p q T).toNat = 1 := by
  obtain ⟨hseed, hentries⟩ := towerContentGcd_dvd n p q T
  rcases hprime.eq_one_or_self_of_dvd _ hseed with h1 | hN
  · exact h1
  · exfalso
    refine hT (gaussTower_eq_zero_of_grid n p q T ?_)
    intro c2 hc2 c1 hc1
    have hd := hentries c2 hc2 c1 hc1
    rw [hN] at hd
    exact Nat.eq_zero_of_dvd_of_lt hd c1.isLt

end PrimeShortcut

/-! ### The reduction of a check-shaped element (shared by soundness
and completeness) -/

/-- The reduction of `G^E − ζ_p^L` into the computable tower. -/
theorem reduceT_sub_pow {n : AzNat} [Fact (1 < n.toNat)]
    {q p : ℕ} [Fact q.Prime] [Fact p.Prime]
    (hp : p ∈ (q - 1).primeFactors) {gu : (ZMod q)ˣ}
    (hgen : ∀ x, x ∈ Subgroup.zpowers gu) {g : ℕ}
    (hg : ((g : ℕ) : ZMod q) = (gu : ZMod q)) (E L : ℕ) :
    reduceT n p q (gaussSum
        (MulChar.ofRootOfUnity (CP.zetaPQUnit_mem hp) hgen)
        (AddChar.zmodChar q (CP.isPrimitiveRoot_zetaQPQ hp).pow_eq_one)
        ^ E
      - ((CP.zetaPQUnit p q : (CP.CycPQ p q)ˣ) : CP.CycPQ p q) ^ L)
      = (gaussSumT n p q g) ^ E - zetaPPowT n p q L := by
  rw [map_sub, map_pow, map_pow, reduceT_gaussSum n hp hgen hg,
    CP.val_zetaPQUnit hp, reduceT_zetaP, constT_pow, zetaPPowT]

/-! ### The `Option Bool` verdicts -/

/-- **Completeness of the Gauss sums primality test**: for PRIME `n`,
a certificate whose data is genuinely valid — distinct-prime lists,
the arithmetic side conditions, a true generator family, the
step-3/4 congruences, the step-5 minimality of `w`, and the step-6
tables — makes every check pass.  The step-5 content gcds come out
`1` by the prime-`n` shortcut (`towerContentGcd_eq_one_of_ne_zero`),
and the step-6 scan cannot find a proper factor of a prime. -/
theorem gaussSumsTest_complete
    {n : AzNat} {c : GaussSumsCert} [Fact (1 < n.toNat)]
    (hprime : n.toNat.Prime)
    (hIndup : c.Ips.Nodup) (hIpr : ∀ p ∈ c.Ips, p.Prime)
    (hFndup : c.Fps.Nodup) (hFpr : ∀ q ∈ c.Fps, q.Prime)
    (hgcd : Nat.Coprime (c.Ips.prod * c.Fps.prod) n.toNat)
    (hnF : n.toNat < c.Fps.prod ^ 2)
    (hqI : ∀ q ∈ c.Fps, (q - 1) ∣ c.Ips.prod)
    (hw : ∀ p ∈ c.Ips, 0 < c.w p)
    (hu : ∀ p ∈ c.Ips, ¬p ∣ c.u p)
    (hq₀F : ∀ p ∈ c.Ips, c.q₀ p ∈ c.Fps)
    (hq₀d : ∀ p ∈ c.Ips, p ∣ c.q₀ p - 1)
    {gu : (q : ℕ) → (ZMod q)ˣ}
    (hgu : ∀ q ∈ c.Fps, ((c.g q : ℕ) : ZMod q) = (gu q : ZMod q))
    (hgen : ∀ q, q ∈ c.Fps → ∀ x, x ∈ Subgroup.zpowers (gu q))
    (hpair : ∀ q (hq : q ∈ c.Fps) [Fact q.Prime],
      ∀ p (hp : p ∈ (q - 1).primeFactors) [Fact p.Prime],
      ((n.toNat : ℕ) : CP.CycPQ p q) ∣
        gaussSum
            (MulChar.ofRootOfUnity (CP.zetaPQUnit_mem hp) (hgen q hq))
            (AddChar.zmodChar q
              (CP.isPrimitiveRoot_zetaQPQ hp).pow_eq_one)
            ^ (p ^ c.w p * c.u p)
          - ((CP.zetaPQUnit p q : (CP.CycPQ p q)ˣ) : CP.CycPQ p q)
            ^ c.lTab p q)
    (hmin : ∀ p (hpI : p ∈ c.Ips) [Fact p.Prime]
      [Fact (c.q₀ p).Prime] (hp : p ∈ (c.q₀ p - 1).primeFactors),
      ∀ j < p,
      ¬((n.toNat : ℕ) : CP.CycPQ p (c.q₀ p)) ∣
        (gaussSum
            (MulChar.ofRootOfUnity (CP.zetaPQUnit_mem hp)
              (hgen (c.q₀ p) (hq₀F p hpI)))
            (AddChar.zmodChar (c.q₀ p)
              (CP.isPrimitiveRoot_zetaQPQ hp).pow_eq_one)
            ^ (p ^ (c.w p - 1) * c.u p)
          - ((CP.zetaPQUnit p (c.q₀ p) : (CP.CycPQ p (c.q₀ p))ˣ)
              : CP.CycPQ p (c.q₀ p)) ^ j))
    (hlqh : ∀ q ∈ c.Fps, ∀ p ∈ c.Ips, p ∣ q - 1 →
      c.lq q ≡ c.lTab p q [MOD p])
    (hlh : ∀ q ∈ c.Fps,
      ((c.l : ℕ) : ZMod q) = ((c.g q : ℕ) : ZMod q) ^ c.lq q) :
    gaussSumsTest n c = true := by
  have hn1 : 1 < n.toNat := Fact.out
  have h1 : AzNat.ofNat 1 < n := by
    rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_ofNat]
    exact hn1
  rw [gaussSumsTest, dif_pos h1]
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hIndup, hIpr⟩, hFndup⟩, hFpr⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- the step-2 gcd
    exact AzNat.toNat_injective (by
      rw [AzNat.toNat_gcd, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
      exact hgcd)
  · -- `n < F^2`
    rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_ofNat]
    exact hnF
  · -- the per-`p` checks, including step 5
    intro p hp
    haveI : Fact p.Prime := ⟨hIpr p hp⟩
    haveI : Fact (c.q₀ p).Prime := ⟨hFpr _ (hq₀F p hp)⟩
    rw [pCheck, dif_pos (hIpr p hp), dif_pos (hFpr _ (hq₀F p hp))]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨hw p hp, hu p hp⟩, hq₀F p hp⟩, hq₀d p hp⟩, ?_⟩
    have hpmem : p ∈ (c.q₀ p - 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hIpr p hp, hq₀d p hp, by
        have := (hFpr _ (hq₀F p hp)).two_le
        omega⟩
    rw [step5Check, List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [decide_eq_true_eq]
    refine AzNat.toNat_injective ?_
    rw [AzNat.toNat_ofNat]
    refine towerContentGcd_eq_one_of_ne_zero n p (c.q₀ p) hprime _ ?_
    intro h0
    rw [powAzNat_eq_pow] at h0
    simp only [certE', AzNat.toNat_ofNat] at h0
    refine hmin p hp hpmem j hj
      ((natCast_dvd_iff_reduceT n p (c.q₀ p) _).mpr ?_)
    rw [reduceT_sub_pow hpmem (hgen _ (hq₀F p hp)) (hgu _ (hq₀F p hp))]
    exact h0
  · -- the per-`q` checks: generator, step 3/4, step-6 tables
    intro q hq
    haveI : Fact q.Prime := ⟨hFpr q hq⟩
    have hq1 : q - 1 ≠ 0 := by
      have := (hFpr q hq).two_le
      omega
    rw [qCheck, dif_pos (hFpr q hq)]
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨hqI q hq, ?_⟩, ?_⟩, ?_⟩, hlh q hq⟩
    · -- the verified primitive root is coprime to `q`
      haveI : NeZero q := ⟨(hFpr q hq).pos.ne'⟩
      rw [← ZMod.isUnit_iff_coprime, hgu q hq]
      exact (gu q).isUnit
    · -- the generator power checks
      intro r hr
      rw [List.mem_filter] at hr
      obtain ⟨hrI, hrdvd⟩ := hr
      rw [decide_eq_true_eq] at hrdvd
      have hrp : r.Prime := hIpr r hrI
      haveI : NeZero q := ⟨(hFpr q hq).pos.ne'⟩
      have hord : orderOf (gu q) = q - 1 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers (hgen q hq),
          Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
          Nat.totient_prime (hFpr q hq)]
      rw [hgu q hq]
      intro heq
      rw [← Units.val_pow_eq_pow_val, Units.val_eq_one] at heq
      have hdvd := orderOf_dvd_of_pow_eq_one heq
      rw [hord] at hdvd
      have hq2 : 0 < q - 1 := by omega
      have hrle : r ≤ q - 1 := Nat.le_of_dvd hq2 hrdvd
      have hpos : 0 < (q - 1) / r := Nat.div_pos hrle hrp.pos
      have hle := Nat.le_of_dvd hpos hdvd
      have hlt : (q - 1) / r < q - 1 :=
        Nat.div_lt_self hq2 hrp.one_lt
      omega
    · -- the step-3/4 pair checks and step-6 table congruences
      intro p hp
      rw [List.mem_filter] at hp
      obtain ⟨hpI, hpdvd⟩ := hp
      rw [decide_eq_true_eq] at hpdvd
      haveI : Fact p.Prime := ⟨hIpr p hpI⟩
      have hpmem : p ∈ (q - 1).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hIpr p hpI, hpdvd, hq1⟩
      refine ⟨?_, hlqh q hq p hpI hpdvd⟩
      rw [pairCheck, dif_pos (hIpr p hpI), decide_eq_true_eq]
      have hd := hpair q hq p hpmem
      rw [natCast_dvd_iff_reduceT,
        reduceT_sub_pow hpmem (hgen q hq) (hgu q hq)] at hd
      rw [powAzNat_eq_pow]
      simp only [certE, AzNat.toNat_ofNat]
      exact sub_eq_zero.mp hd
  · -- the step-6 scan comes up clean on a prime
    rw [scanCheck, List.all_eq_true]
    intro j _
    by_cases hj0 : j = 0
    · rw [Bool.or_eq_true]
      left
      rw [hj0]
      rfl
    · rw [Bool.or_eq_true]
      right
      show ((c.l ^ j % c.Fps.prod == 1)
        || !(n % AzNat.ofNat (c.l ^ j % c.Fps.prod) == AzNat.ofNat 0)
        || (AzNat.ofNat (c.l ^ j % c.Fps.prod) == n)) = true
      set d := c.l ^ j % c.Fps.prod with hd
      by_cases hdvd : d ∣ n.toNat
      · rcases hprime.eq_one_or_self_of_dvd d hdvd with hd1 | hdn
        · rw [Bool.or_eq_true, Bool.or_eq_true]
          left; left
          rw [beq_iff_eq]
          exact hd1
        · rw [Bool.or_eq_true]
          right
          rw [beq_iff_eq, hdn]
          exact AzNat.toNat_injective (by rw [AzNat.toNat_ofNat])
      · rw [Bool.or_eq_true, Bool.or_eq_true]
        left; right
        rw [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne]
        intro heq
        refine hdvd (Nat.dvd_of_mod_eq_zero ?_)
        have h' := congrArg AzNat.toNat heq
        rwa [AzNat.toNat_mod, AzNat.toNat_ofNat, AzNat.toNat_ofNat] at h'

section OptionChecker

variable (n : AzNat) (c : GaussSumsCert)

/-- Membership of `n` in a small-prime list, at the limb level. -/
def memListAz (l : List ℕ) : Bool := l.any fun p => AzNat.ofNat p == n

/-- The step-5 factor detector at `p`: some content gcd is a
NONTRIVIAL divisor of `n` (a proper factor — composite verdict). -/
def step5FactorFound [Fact (1 < n.toNat)] (p : ℕ) : Bool :=
  if hp : p.Prime then
    if hq : (c.q₀ p).Prime then
      letI : Fact p.Prime := ⟨hp⟩
      letI : Fact (c.q₀ p).Prime := ⟨hq⟩
      (List.range p).any fun j =>
        let ggcd := towerContentGcd n p (c.q₀ p)
          ((gaussSumT n p (c.q₀ p) (c.g (c.q₀ p))).powAzNat (certE' c p)
            - zetaPPowT n p (c.q₀ p) j)
        decide (AzNat.ofNat 1 < ggcd) && decide (ggcd < n)
    else false
  else false

/-- The step-6 factor detector: some `l^j mod F` is a nontrivial
factor of `n`. -/
def scanFactorFound : Bool :=
  (List.range c.Ips.prod).any fun j =>
    !(j == 0) &&
      (let d := c.l ^ j % c.Fps.prod
       (n % AzNat.ofNat d == AzNat.ofNat 0) && decide (1 < d)
         && decide (AzNat.ofNat d < n))

/-- The certificate's factor lists are distinct primes. -/
def listChecks : Bool :=
  decide c.Ips.Nodup && c.Ips.all (fun p => decide p.Prime)
    && decide c.Fps.Nodup && c.Fps.all (fun q => decide q.Prime)

/-- **The Gauss sums primality test with verdicts**: `some true`
proves `n` prime, `some false` proves `n` composite, `none` makes no
claim.  The composite verdicts are the book's: the step-2 gcd (`n`
not among the certificate primes), a step-5 content gcd revealing a
proper factor, or the step-6 scan finding one. -/
def gaussSumsTestO : Option Bool :=
  if h1 : AzNat.ofNat 1 < n then
    letI : Fact (1 < n.toNat) := ⟨by
      have h := (AzNat.lt_iff_toNat_lt _ _).mp h1
      rwa [AzNat.toNat_ofNat] at h⟩
    if listChecks c then
      if memListAz n c.Ips || memListAz n c.Fps then some true
      else if !(AzNat.gcd (AzNat.ofNat (c.Ips.prod * c.Fps.prod)) n
          == AzNat.ofNat 1) then some false
      else if c.Ips.any (step5FactorFound n c) || scanFactorFound n c then
        some false
      else if gaussSumsTest n c then some true
      else none
    else none
  else none

/-- A nontrivial divisor witnesses compositeness. -/
private theorem not_prime_of_factor {N d : ℕ} (hd : d ∣ N) (h1 : 1 < d)
    (hN : d < N) : ¬N.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd d hd with h | h <;> omega

/-- **Soundness of the `some true` verdict.** -/
theorem gaussSumsTestO_eq_some_true
    (h : gaussSumsTestO n c = some true) : n.toNat.Prime := by
  rw [gaussSumsTestO] at h
  by_cases h1 : AzNat.ofNat 1 < n
  case neg => rw [dif_neg h1] at h; exact absurd h (by simp)
  rw [dif_pos h1] at h
  haveI : Fact (1 < n.toNat) := ⟨by
    have h' := (AzNat.lt_iff_toNat_lt _ _).mp h1
    rwa [AzNat.toNat_ofNat] at h'⟩
  by_cases hlists : listChecks c = true
  case neg => rw [if_neg hlists] at h; exact absurd h (by simp)
  rw [if_pos hlists] at h
  rw [listChecks] at hlists
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    at hlists
  obtain ⟨⟨⟨-, hIpr⟩, -⟩, hFpr⟩ := hlists
  by_cases hmem : (memListAz n c.Ips || memListAz n c.Fps) = true
  · -- `n` is one of the (verified-prime) certificate primes
    simp only [memListAz, Bool.or_eq_true, List.any_eq_true,
      beq_iff_eq] at hmem
    rcases hmem with ⟨p, hp, hpn⟩ | ⟨p, hp, hpn⟩
    · have := congrArg AzNat.toNat hpn
      rw [AzNat.toNat_ofNat] at this
      rw [← this]
      exact hIpr p hp
    · have := congrArg AzNat.toNat hpn
      rw [AzNat.toNat_ofNat] at this
      rw [← this]
      exact hFpr p hp
  · rw [if_neg hmem] at h
    by_cases hgcd : (!(AzNat.gcd
        (AzNat.ofNat (c.Ips.prod * c.Fps.prod)) n
        == AzNat.ofNat 1)) = true
    case pos => rw [if_pos hgcd] at h; exact absurd h (by simp)
    rw [if_neg hgcd] at h
    by_cases hfac : (c.Ips.any (step5FactorFound n c)
        || scanFactorFound n c) = true
    case pos => rw [if_pos hfac] at h; exact absurd h (by simp)
    rw [if_neg hfac] at h
    by_cases htest : gaussSumsTest n c = true
    case neg => rw [if_neg htest] at h; exact absurd h (by simp)
    exact gaussSumsTest_eq_true n c htest

/-- A firing factor detector (step 5 or the step-6 scan) exhibits a
proper factor of `n`, so `n` is composite. -/
private theorem not_prime_of_factor_found [Fact (1 < n.toNat)]
    (hIpr : ∀ p ∈ c.Ips, p.Prime)
    (hfac : (c.Ips.any (step5FactorFound n c)
      || scanFactorFound n c) = true) : ¬n.toNat.Prime := by
  rw [Bool.or_eq_true, List.any_eq_true] at hfac
  rcases hfac with ⟨p, hp, hfound⟩ | hfound
  · -- a step-5 content gcd is a proper factor
    rw [step5FactorFound, dif_pos (hIpr p hp)] at hfound
    by_cases hq : (c.q₀ p).Prime
    case neg => rw [dif_neg hq] at hfound; exact absurd hfound (by simp)
    rw [dif_pos hq] at hfound
    rw [List.any_eq_true] at hfound
    obtain ⟨j, -, hj⟩ := hfound
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    obtain ⟨hj1, hjn⟩ := hj
    haveI : Fact p.Prime := ⟨hIpr p hp⟩
    haveI : Fact (c.q₀ p).Prime := ⟨hq⟩
    set T := (gaussSumT n p (c.q₀ p) (c.g (c.q₀ p))).powAzNat (certE' c p)
      - zetaPPowT n p (c.q₀ p) j with hT
    have hdvd := (towerContentGcd_dvd n p (c.q₀ p) T).1
    refine not_prime_of_factor hdvd ?_ ?_
    · have h' := (AzNat.lt_iff_toNat_lt _ _).mp hj1
      rwa [AzNat.toNat_ofNat] at h'
    · exact (AzNat.lt_iff_toNat_lt _ _).mp hjn
  · -- a scanned residue is a proper factor
    rw [scanFactorFound, List.any_eq_true] at hfound
    obtain ⟨j, -, hj⟩ := hfound
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      beq_iff_eq, decide_eq_true_eq] at hj
    obtain ⟨-, hj2⟩ := hj
    obtain ⟨⟨hmod, hd1⟩, hdn⟩ := hj2
    set d := c.l ^ j % c.Fps.prod with hd
    have hdvd : d ∣ n.toNat := by
      refine Nat.dvd_of_mod_eq_zero ?_
      have h' := congrArg AzNat.toNat hmod
      rwa [AzNat.toNat_mod, AzNat.toNat_ofNat, AzNat.toNat_ofNat] at h'
    have hlt : d < n.toNat := by
      have h' := (AzNat.lt_iff_toNat_lt _ _).mp hdn
      rwa [AzNat.toNat_ofNat] at h'
    exact not_prime_of_factor hdvd hd1 hlt

/-- **Soundness of the `some false` verdict**: `n` is composite —
by the step-2 gcd, or by an exhibited proper factor from a step-5
content gcd or the step-6 scan. -/
theorem gaussSumsTestO_eq_some_false
    (h : gaussSumsTestO n c = some false) : ¬n.toNat.Prime := by
  rw [gaussSumsTestO] at h
  by_cases h1 : AzNat.ofNat 1 < n
  case neg => rw [dif_neg h1] at h; exact absurd h (by simp)
  rw [dif_pos h1] at h
  haveI hfact : Fact (1 < n.toNat) := ⟨by
    have h' := (AzNat.lt_iff_toNat_lt _ _).mp h1
    rwa [AzNat.toNat_ofNat] at h'⟩
  by_cases hlists : listChecks c = true
  case neg => rw [if_neg hlists] at h; exact absurd h (by simp)
  rw [if_pos hlists] at h
  rw [listChecks] at hlists
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    at hlists
  obtain ⟨⟨⟨hIndup, hIpr⟩, hFndup⟩, hFpr⟩ := hlists
  have hIpos : 0 < c.Ips.prod :=
    List.prod_pos fun p hp => (hIpr p hp).pos
  have hFpos : 0 < c.Fps.prod :=
    List.prod_pos fun q hq => (hFpr q hq).pos
  by_cases hmem : (memListAz n c.Ips || memListAz n c.Fps) = true
  case pos => rw [if_pos hmem] at h; exact absurd h (by simp)
  rw [if_neg hmem] at h
  by_cases hgcd : (!(AzNat.gcd
      (AzNat.ofNat (c.Ips.prod * c.Fps.prod)) n
      == AzNat.ofNat 1)) = true
  · -- the step-2 verdict
    rw [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne]
      at hgcd
    have hne : Nat.gcd (c.Ips.prod * c.Fps.prod) n.toNat ≠ 1 := by
      intro heq
      refine hgcd (AzNat.toNat_injective ?_)
      rw [AzNat.toNat_gcd, AzNat.toNat_ofNat, AzNat.toNat_ofNat, heq]
    have hg1 : 1 < Nat.gcd n.toNat (c.Ips.prod * c.Fps.prod) := by
      rw [Nat.gcd_comm]
      rcases Nat.eq_zero_or_pos
        (Nat.gcd (c.Ips.prod * c.Fps.prod) n.toNat) with h0 | hpos
      · have := (Nat.gcd_eq_zero_iff.mp h0).2
        have := hfact.out
        omega
      · omega
    refine CP.step2_composite_of_gcd (by positivity) hg1 ?_
    intro hmem'
    have hIF : c.Ips.prod ≠ 0 := hIpos.ne'
    have hFF : c.Fps.prod ≠ 0 := hFpos.ne'
    rw [Nat.primeFactors_mul hIF hFF, Finset.mem_union] at hmem'
    have hself : AzNat.ofNat n.toNat = n :=
      AzNat.toNat_injective (by rw [AzNat.toNat_ofNat])
    rcases hmem' with hmem' | hmem'
    · refine absurd ?_ hmem
      have hm : memListAz n c.Ips = true := by
        rw [memListAz, List.any_eq_true]
        exact ⟨n.toNat,
          (mem_primeFactors_prod_iff hIndup hIpr).mp hmem',
          by rw [beq_iff_eq]; exact hself⟩
      simp [hm]
    · refine absurd ?_ hmem
      have hm : memListAz n c.Fps = true := by
        rw [memListAz, List.any_eq_true]
        exact ⟨n.toNat,
          (mem_primeFactors_prod_iff hFndup hFpr).mp hmem',
          by rw [beq_iff_eq]; exact hself⟩
      simp [hm]
  rw [if_neg hgcd] at h
  by_cases hfac : (c.Ips.any (step5FactorFound n c)
      || scanFactorFound n c) = true
  case neg =>
    rw [if_neg hfac] at h
    by_cases htest : gaussSumsTest n c = true
    · rw [if_pos htest] at h; exact absurd h (by simp)
    · rw [if_neg htest] at h; exact absurd h (by simp)
  rw [if_pos hfac] at h
  exact not_prime_of_factor_found n c hIpr hfac

/-- **Completeness of the verdicts**: for PRIME `n` and a genuinely
valid certificate the `Option Bool` checker answers `some true` —
the step-2 gcd is `1`, no factor detector can fire on a prime, and
the underlying test passes by `gaussSumsTest_complete`. -/
theorem gaussSumsTestO_complete [Fact (1 < n.toNat)]
    (hprime : n.toNat.Prime)
    (hIndup : c.Ips.Nodup) (hIpr : ∀ p ∈ c.Ips, p.Prime)
    (hFndup : c.Fps.Nodup) (hFpr : ∀ q ∈ c.Fps, q.Prime)
    (hgcd : Nat.Coprime (c.Ips.prod * c.Fps.prod) n.toNat)
    (hnF : n.toNat < c.Fps.prod ^ 2)
    (hqI : ∀ q ∈ c.Fps, (q - 1) ∣ c.Ips.prod)
    (hw : ∀ p ∈ c.Ips, 0 < c.w p)
    (hu : ∀ p ∈ c.Ips, ¬p ∣ c.u p)
    (hq₀F : ∀ p ∈ c.Ips, c.q₀ p ∈ c.Fps)
    (hq₀d : ∀ p ∈ c.Ips, p ∣ c.q₀ p - 1)
    {gu : (q : ℕ) → (ZMod q)ˣ}
    (hgu : ∀ q ∈ c.Fps, ((c.g q : ℕ) : ZMod q) = (gu q : ZMod q))
    (hgen : ∀ q, q ∈ c.Fps → ∀ x, x ∈ Subgroup.zpowers (gu q))
    (hpair : ∀ q (hq : q ∈ c.Fps) [Fact q.Prime],
      ∀ p (hp : p ∈ (q - 1).primeFactors) [Fact p.Prime],
      ((n.toNat : ℕ) : CP.CycPQ p q) ∣
        gaussSum
            (MulChar.ofRootOfUnity (CP.zetaPQUnit_mem hp) (hgen q hq))
            (AddChar.zmodChar q
              (CP.isPrimitiveRoot_zetaQPQ hp).pow_eq_one)
            ^ (p ^ c.w p * c.u p)
          - ((CP.zetaPQUnit p q : (CP.CycPQ p q)ˣ) : CP.CycPQ p q)
            ^ c.lTab p q)
    (hmin : ∀ p (hpI : p ∈ c.Ips) [Fact p.Prime]
      [Fact (c.q₀ p).Prime] (hp : p ∈ (c.q₀ p - 1).primeFactors),
      ∀ j < p,
      ¬((n.toNat : ℕ) : CP.CycPQ p (c.q₀ p)) ∣
        (gaussSum
            (MulChar.ofRootOfUnity (CP.zetaPQUnit_mem hp)
              (hgen (c.q₀ p) (hq₀F p hpI)))
            (AddChar.zmodChar (c.q₀ p)
              (CP.isPrimitiveRoot_zetaQPQ hp).pow_eq_one)
            ^ (p ^ (c.w p - 1) * c.u p)
          - ((CP.zetaPQUnit p (c.q₀ p) : (CP.CycPQ p (c.q₀ p))ˣ)
              : CP.CycPQ p (c.q₀ p)) ^ j))
    (hlqh : ∀ q ∈ c.Fps, ∀ p ∈ c.Ips, p ∣ q - 1 →
      c.lq q ≡ c.lTab p q [MOD p])
    (hlh : ∀ q ∈ c.Fps,
      ((c.l : ℕ) : ZMod q) = ((c.g q : ℕ) : ZMod q) ^ c.lq q) :
    gaussSumsTestO n c = some true := by
  have htest : gaussSumsTest n c = true :=
    gaussSumsTest_complete hprime hIndup hIpr hFndup hFpr hgcd hnF
      hqI hw hu hq₀F hq₀d hgu hgen hpair hmin hlqh hlh
  have hn1 : 1 < n.toNat := Fact.out
  have h1 : AzNat.ofNat 1 < n := by
    rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_ofNat]
    exact hn1
  rw [gaussSumsTestO, dif_pos h1]
  have hlc : listChecks c = true := by
    rw [listChecks]
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hIndup, hIpr⟩, hFndup⟩, hFpr⟩
  rw [if_pos hlc]
  by_cases hmem : (memListAz n c.Ips || memListAz n c.Fps) = true
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    have hbeq : (AzNat.gcd (AzNat.ofNat (c.Ips.prod * c.Fps.prod)) n
        == AzNat.ofNat 1) = true := by
      rw [beq_iff_eq]
      exact AzNat.toNat_injective (by
        rw [AzNat.toNat_gcd, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
        exact hgcd)
    rw [if_neg (by rw [hbeq]; simp)]
    rw [if_neg fun hfac =>
      not_prime_of_factor_found n c hIpr hfac hprime]
    rw [if_pos htest]

end OptionChecker

end Checker

end AzPolyMod

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolyMod

/-! `n = 7` certified prime through the full Gauss sums checker:
`I = 2`, `F = 2·3 = 6` (both `q − 1 ∣ 2`), `F² = 36 > 7`,
`7^1 − 1 = 2^1·3` so `w(2) = 1`, `u(2) = 3`; the pair `(2,3)` has
`G(2,3)^(2·3) = (−3)³ = 1 = ζ₂⁰` so `l(2,3) = 0`; step 5 at
`q₀(2) = 3` with `H = G³`; step 6: `l(q) = 0`, `l = 1` (`≡ g_q⁰`
mod each `q`), and the scan `1^1 mod 6 = 1` is clean. -/

private def cert7 : GaussSumsCert :=
  { Ips := [2], Fps := [2, 3]
    w := fun _ => 1, u := fun _ => 3
    lTab := fun _ _ => 0, lq := fun _ => 0, l := 1
    q₀ := fun _ => 3, g := fun q => if q = 3 then 2 else 1 }

#guard gaussSumsTest (AzNat.ofNat 7) cert7 = true
-- the same certificate rejects composites outright (`gcd(12, 9) = 3`)
#guard gaussSumsTest (AzNat.ofNat 9) cert7 = false

-- the verdict form: `7` certified prime, `9` PROVEN composite
-- (step-2 gcd `gcd(6, 9) = 3`), and on `25` (coprime to `6` but not
-- congruence-certified) the checker makes no claim
#guard gaussSumsTestO (AzNat.ofNat 7) cert7 = some true
#guard gaussSumsTestO (AzNat.ofNat 9) cert7 = some false
#guard gaussSumsTestO (AzNat.ofNat 25) cert7 = none

end Tests

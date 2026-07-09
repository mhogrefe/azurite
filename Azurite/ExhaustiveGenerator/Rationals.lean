/-
  Exhaustive generators over `AzRat` (Malachite's `exhaustive_positive_rationals`,
  `exhaustive_non_negative_rationals`, `exhaustive_negative_rationals`,
  `exhaustive_nonzero_rationals`, `exhaustive_rationals`).

  Every one of these rests on the Calkin–Wilf enumeration of the positive
  rationals, whose numerators and denominators are consecutive terms of the
  Stern–Brocot sequence. That sequence obeys the single self-contained
  recurrence (attributed to David S. Newman, OEIS A002487)
    a_{n+1} = (2·⌊a_{n-1} / a_n⌋ + 1)·a_n − a_{n-1},
  needing no pairing/interleaving machinery. The `n`-th positive rational is
  `a_n / a_{n+1}`, with consecutive terms automatically coprime (so the fraction
  is already reduced).

  The file has two layers: the *computable* enumerations as plain `def`s with
  `#guard`s pinning their order to Malachite's doctests, and then the full
  bijectivity proofs (`occurs_exactly_once`, via Stern's diatomic sequence
  `fusc` and the Calkin–Wilf theorem) giving `ExhaustiveGenerator` instances
  over the order subtypes (`{q // 0 < q}`, etc.) and all of `AzRat`.
-/
import Azurite.ExhaustiveGenerator.Basic
import Azurite.AzRat.Construct
import Azurite.AzRat.ToString
import Azurite.AzRat.Unary
import Azurite.AzRat.Equiv.Basic
import Azurite.AzRat.Equiv.Construct
import Azurite.AzRat.Equiv.Order
import Azurite.AzNat.Add
import Azurite.AzNat.Mul
import Azurite.AzNat.Sub
import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Gcd

namespace Azurite

/-! ### The Calkin–Wilf positive-rational enumeration -/

/-- One step of the Stern–Brocot / Calkin–Wilf recurrence on a pair of
consecutive terms `(pp, p) = (a_{n-1}, a_n)`, producing `(a_n, a_{n+1})`. With
`k = ⌊pp / p⌋` (floor `AzNat` division), the next term is
`a_{n+1} = (2k+1)·p − pp`, written `(k + k + 1)·p − pp` to avoid an `AzNat`
literal `2`. Since `pp = k·p + r` with `r < p`, the subtraction never truncates
(`(2k+1)·p − pp = (k+1)·p − r > 0`). -/
def sternBrocotStep (s : AzNat × AzNat) : AzNat × AzNat :=
  let pp := s.1
  let p := s.2
  let k := pp / p
  (p, (k + k + 1) * p - pp)

/-- The numerator/denominator pair `(a_n, a_{n+1})` of the `n`-th positive
rational: the state after iterating `sternBrocotStep` `n + 1` times from the
initial `(0, 1)`. The two components are consecutive Stern–Brocot terms, hence
coprime — this is what Phase 2 will use to prove the Calkin–Wilf bijection. -/
def positiveRationalPair (n : ℕ) : AzNat × AzNat :=
  sternBrocotStep^[n + 1] (0, 1)

/-! ### The five enumerations -/

/-- All positive rationals in Calkin–Wilf order:
`1, 1/2, 2, 1/3, 3/2, 2/3, 3, 1/4, …`. The `n`-th value is `a_n / a_{n+1}`
built from `positiveRationalPair n` via `AzRat.ofAzNats`. -/
def positiveRationals (n : ℕ) : AzRat :=
  AzRat.ofAzNats (positiveRationalPair n).1 (positiveRationalPair n).2

/-- All nonnegative rationals: `0` first, then the positive rationals:
`0, 1, 1/2, 2, 1/3, …`. -/
def nonnegativeRationals (n : ℕ) : AzRat :=
  if n = 0 then 0 else positiveRationals (n - 1)

/-- All negative rationals: the positive rationals negated:
`-1, -1/2, -2, -1/3, …`. -/
def negativeRationals (n : ℕ) : AzRat :=
  -(positiveRationals n)

/-- All nonzero rationals: the positive rationals interleaved with their
negatives: `1, -1, 1/2, -1/2, 2, -2, …`. -/
def nonzeroRationals (n : ℕ) : AzRat :=
  if n % 2 = 0 then positiveRationals (n / 2) else -(positiveRationals (n / 2))

/-- All rationals: `0` first, then the nonzero rationals:
`0, 1, -1, 1/2, -1/2, 2, -2, …`. -/
def rationals (n : ℕ) : AzRat :=
  if n = 0 then 0 else nonzeroRationals (n - 1)

/-! ### Guards pinning the order to Malachite's doctests -/

-- `exhaustive_positive_rationals` (first 19 of the doctest prefix).
#guard ((List.range 19).map (fun i => AzRat.toString (positiveRationals i))) ==
  ["1", "1/2", "2", "1/3", "3/2", "2/3", "3", "1/4", "4/3", "3/5", "5/2", "2/5",
   "5/3", "3/4", "4", "1/5", "5/4", "4/7", "7/3"]

-- `exhaustive_non_negative_rationals` (first 10).
#guard ((List.range 10).map (fun i => AzRat.toString (nonnegativeRationals i))) ==
  ["0", "1", "1/2", "2", "1/3", "3/2", "2/3", "3", "1/4", "4/3"]

-- `exhaustive_negative_rationals` (first 10).
#guard ((List.range 10).map (fun i => AzRat.toString (negativeRationals i))) ==
  ["-1", "-1/2", "-2", "-1/3", "-3/2", "-2/3", "-3", "-1/4", "-4/3", "-3/5"]

-- `exhaustive_nonzero_rationals` (first 10).
#guard ((List.range 10).map (fun i => AzRat.toString (nonzeroRationals i))) ==
  ["1", "-1", "1/2", "-1/2", "2", "-2", "1/3", "-1/3", "3/2", "-3/2"]

-- `exhaustive_rationals` (first 10).
#guard ((List.range 10).map (fun i => AzRat.toString (rationals i))) ==
  ["0", "1", "-1", "1/2", "-1/2", "2", "-2", "1/3", "-1/3", "3/2"]

/-! ### Stern's diatomic sequence (`fusc`)

The bijectivity of the Calkin–Wilf enumeration is proved through Stern's
diatomic sequence `fusc` (OEIS A002487):
`fusc 0 = 0`, `fusc 1 = 1`, `fusc (2n) = fusc n`, `fusc (2n+1) = fusc n + fusc (n+1)`.
The `n`-th positive-rational pair is `(fusc (n+1), fusc (n+2))`, and the map
`m ↦ (fusc m, fusc (m+1))` is a bijection from `{m ≥ 1}` onto reduced positive
pairs (the Calkin–Wilf theorem, proved here by tree descent). -/

/-- Stern's diatomic sequence. -/
def fusc : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    if h : (n + 2) % 2 = 0 then fusc ((n + 2) / 2)
    else fusc ((n + 2) / 2) + fusc ((n + 2) / 2 + 1)
  decreasing_by
    · omega
    · omega
    · omega

@[simp] theorem fusc_zero : fusc 0 = 0 := by simp only [fusc]
@[simp] theorem fusc_one : fusc 1 = 1 := by simp only [fusc]

/-- The even recurrence `fusc (2n) = fusc n`. -/
theorem fusc_two_mul (n : ℕ) : fusc (2 * n) = fusc n := by
  match n with
  | 0 => rfl
  | k + 1 =>
    have he : 2 * (k + 1) = (2 * k) + 2 := by ring
    rw [he, fusc]
    rw [dif_pos (by omega)]
    congr 1
    omega

/-- The odd recurrence `fusc (2n+1) = fusc n + fusc (n+1)`. -/
theorem fusc_two_mul_add_one (n : ℕ) : fusc (2 * n + 1) = fusc n + fusc (n + 1) := by
  match n with
  | 0 => simp
  | k + 1 =>
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [he, fusc]
    rw [dif_neg (by omega)]
    have h1 : (2 * k + 1 + 2) / 2 = k + 1 := by omega
    rw [h1]

@[simp] theorem fusc_two : fusc 2 = 1 := by
  rw [show (2 : ℕ) = 2 * 1 by rfl, fusc_two_mul, fusc_one]

@[simp] theorem fusc_three : fusc 3 = 2 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 by rfl, fusc_two_mul_add_one, fusc_one,
      show (1 : ℕ) + 1 = 2 by rfl, fusc_two]

/-- `fusc n ≥ 1` for `n ≥ 1`: every positive index has a positive value. -/
theorem fusc_pos : ∀ n, 1 ≤ n → 0 < fusc n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n, hn with
    | 1, _ => simp
    | (m + 2), _ =>
      rcases Nat.even_or_odd (m + 2) with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- even: m + 2 = 2k, k ≥ 1
        have hk2 : m + 2 = 2 * k := by omega
        rw [hk2, fusc_two_mul]
        exact ih k (by omega) (by omega)
      · -- odd: m + 2 = 2k + 1, k ≥ 1
        have hk2 : m + 2 = 2 * k + 1 := by omega
        rw [hk2, fusc_two_mul_add_one]
        have : 0 < fusc (k + 1) := ih (k + 1) (by omega) (by omega)
        omega

/-- Consecutive `fusc` terms are coprime (the fractions are reduced). -/
theorem fusc_coprime : ∀ n, Nat.Coprime (fusc n) (fusc (n + 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [Nat.Coprime]
    | 1 => simp [Nat.Coprime]
    | (m + 2) =>
      rcases Nat.even_or_odd (m + 2) with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- m + 2 = 2k
        have hk2 : m + 2 = 2 * k := by omega
        rw [hk2, fusc_two_mul, fusc_two_mul_add_one]
        rw [Nat.coprime_self_add_right]
        exact ih k (by omega)
      · -- m + 2 = 2k + 1
        have hk2 : m + 2 = 2 * k + 1 := by omega
        rw [hk2, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, fusc_two_mul_add_one, fusc_two_mul]
        rw [Nat.coprime_add_self_left]
        exact ih k (by omega)

/-- Newman's recurrence: `fusc (m+2) = (2⌊fusc m / fusc (m+1)⌋ + 1)·fusc (m+1) − fusc m`
for `m ≥ 1`. This single self-contained recurrence is what `sternBrocotStep`
computes, so it bridges the concrete enumeration to `fusc`. -/
theorem fusc_newman : ∀ m, 1 ≤ m →
    fusc (m + 2) = (2 * (fusc m / fusc (m + 1)) + 1) * fusc (m + 1) - fusc m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- m = 2j, j ≥ 1: floor is 0
      have hj1 : 1 ≤ j := by omega
      have hm2 : m = 2 * j := by omega
      rw [hm2]
      simp only [show 2 * j + 2 = 2 * (j + 1) by ring, fusc_two_mul, fusc_two_mul_add_one]
      -- goal: fusc (j+1) = (2*(fusc j / (fusc j + fusc (j+1))) + 1)*(fusc j + fusc (j+1)) - fusc j
      have hpos : 0 < fusc (j + 1) := fusc_pos (j + 1) (by omega)
      have hfloor : fusc j / (fusc j + fusc (j + 1)) = 0 :=
        Nat.div_eq_of_lt (by omega)
      rw [hfloor]
      omega
    · -- m = 2j + 1
      have hm2 : m = 2 * j + 1 := by omega
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · -- j = 0: m = 1, base case, floor = 1
        subst hj0
        have hm1 : m = 1 := by omega
        subst hm1
        -- fusc 3 = (2*(fusc 1 / fusc 2)+1)*fusc 2 - fusc 1
        show fusc 3 = (2 * (fusc 1 / fusc 2) + 1) * fusc 2 - fusc 1
        rw [fusc_one, fusc_two, fusc_three]
      · -- j ≥ 1: use IH at j
        rw [hm2]
        simp only [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring,
          show 2 * j + 1 + 1 = 2 * (j + 1) by ring, fusc_two_mul_add_one, fusc_two_mul]
        rw [show j + 1 + 1 = j + 2 by rfl]
        -- goal: fusc (j+1) + fusc (j+2) =
        --   (2*((fusc j + fusc (j+1)) / fusc (j+1)) + 1)*fusc (j+1) - (fusc j + fusc (j+1))
        have hpos : 0 < fusc (j + 1) := fusc_pos (j + 1) (by omega)
        have hdiv : (fusc j + fusc (j + 1)) / fusc (j + 1) = fusc j / fusc (j + 1) + 1 := by
          rw [Nat.add_div_right _ hpos]
        rw [hdiv]
        have hIH : fusc (j + 2) = (2 * (fusc j / fusc (j + 1)) + 1) * fusc (j + 1) - fusc j :=
          ih j (by omega) hjpos
        have hle : fusc j ≤ (2 * (fusc j / fusc (j + 1)) + 1) * fusc (j + 1) := by
          have h1 := Nat.div_add_mod (fusc j) (fusc (j + 1))
          have h2 := Nat.mod_lt (fusc j) hpos
          have hexp : (2 * (fusc j / fusc (j + 1)) + 1) * fusc (j + 1)
              = fusc (j + 1) * (fusc j / fusc (j + 1))
                + (fusc (j + 1) * (fusc j / fusc (j + 1)) + fusc (j + 1)) := by ring
          omega
        -- Now pure Nat arithmetic; expand and cancel.
        set k := fusc j / fusc (j + 1) with hk
        set a := fusc j with ha
        set b := fusc (j + 1) with hb
        set c := fusc (j + 2) with hc
        -- goal: b + c = (2*(k+1)+1)*b - (a + b), with c = (2k+1)*b - a and a ≤ (2k+1)*b
        have hexp : (2 * (k + 1) + 1) * b = (2 * k + 1) * b + 2 * b := by ring
        omega

/-! ### The concrete pair equals the `fusc` pair -/

/-- `toNat` of one Stern–Brocot step, first component: it is just the second
input component. -/
theorem sternBrocotStep_fst_toNat (s : AzNat × AzNat) :
    (sternBrocotStep s).1.toNat = s.2.toNat := rfl

/-- `toNat` of one Stern–Brocot step, second component, in `ℕ` arithmetic. -/
theorem sternBrocotStep_snd_toNat (s : AzNat × AzNat) :
    (sternBrocotStep s).2.toNat =
      (2 * (s.1.toNat / s.2.toNat) + 1) * s.2.toNat - s.1.toNat := by
  show ((s.1 / s.2 + s.1 / s.2 + 1) * s.2 - s.1).toNat = _
  rw [AzNat.toNat_sub, AzNat.toNat_mul, AzNat.toNat_add, AzNat.toNat_add,
      AzNat.toNat_div, AzNat.toNat_one]
  ring_nf

/-- The heart of the bridge: the `n`-th positive-rational pair has `toNat`
components `(fusc (n+1), fusc (n+2))`. -/
theorem positiveRationalPair_toNat (n : ℕ) :
    (positiveRationalPair n).1.toNat = fusc (n + 1) ∧
    (positiveRationalPair n).2.toNat = fusc (n + 2) := by
  induction n with
  | zero =>
    have h0 : positiveRationalPair 0 = sternBrocotStep (0, 1) := by
      show sternBrocotStep^[0 + 1] (0, 1) = sternBrocotStep (0, 1)
      rw [Function.iterate_one]
    rw [h0]
    constructor
    · rw [sternBrocotStep_fst_toNat, fusc_one]; rfl
    · rw [sternBrocotStep_snd_toNat, fusc_two]
      simp [AzNat.toNat_zero, AzNat.toNat_one]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : positiveRationalPair (n + 1)
        = sternBrocotStep (positiveRationalPair n) := by
      show sternBrocotStep^[n + 1 + 1] (0, 1) = sternBrocotStep (sternBrocotStep^[n + 1] (0, 1))
      rw [Function.iterate_succ_apply']
    rw [hstep]
    constructor
    · rw [sternBrocotStep_fst_toNat, ih2]
    · rw [sternBrocotStep_snd_toNat, ih1, ih2]
      have hN := fusc_newman (n + 1) (by omega)
      rw [show n + 1 + 1 = n + 2 from rfl] at hN
      exact hN.symm

/-! ### The Calkin–Wilf bijection for `fusc` -/

/-- Even index: `fusc (2k) < fusc (2k+1)` for `k ≥ 1` (a left child has a smaller
numerator than denominator). -/
theorem fusc_lt_of_even {k : ℕ} (hk : 1 ≤ k) : fusc (2 * k) < fusc (2 * k + 1) := by
  rw [fusc_two_mul, fusc_two_mul_add_one]
  have : 0 < fusc (k + 1) := fusc_pos (k + 1) (by omega)
  omega

/-- Odd index (strict): `fusc (2k+2) < fusc (2k+1)` for `k ≥ 1` (a right child has
a larger numerator than denominator). -/
theorem fusc_gt_of_odd {k : ℕ} (hk : 1 ≤ k) : fusc (2 * k + 1 + 1) < fusc (2 * k + 1) := by
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, fusc_two_mul, fusc_two_mul_add_one]
  have : 0 < fusc k := fusc_pos k hk
  omega

/-- Odd index (non-strict, all `k`): `fusc (2k+2) ≤ fusc (2k+1)`. -/
theorem fusc_odd_le (k : ℕ) : fusc (2 * k + 1 + 1) ≤ fusc (2 * k + 1) := by
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, fusc_two_mul, fusc_two_mul_add_one]
  omega

/-- Injectivity of the Calkin–Wilf map on positive indices. -/
theorem fusc_inj : ∀ m n, 1 ≤ m → 1 ≤ n →
    fusc m = fusc n → fusc (m + 1) = fusc (n + 1) → m = n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hm hn hnum hden
    rcases Nat.even_or_odd m with ⟨mk, hmk⟩ | ⟨mk, hmk⟩ <;>
      rcases Nat.even_or_odd n with ⟨nk, hnk⟩ | ⟨nk, hnk⟩
    · -- both even: descend
      have hmk2 : m = 2 * mk := by omega
      have hnk2 : n = 2 * nk := by omega
      rw [hmk2, hnk2] at hnum hden
      simp only [fusc_two_mul] at hnum
      simp only [fusc_two_mul_add_one] at hden
      have e2 : fusc (mk + 1) = fusc (nk + 1) := by omega
      have : mk = nk := ih mk (by omega) nk (by omega) (by omega) hnum e2
      omega
    · -- m even, n odd: contradiction
      exfalso
      have hmk2 : m = 2 * mk := by omega
      have hn2 : n = 2 * nk + 1 := by omega
      have hlt := fusc_lt_of_even (k := mk) (by omega)
      rw [← hmk2] at hlt
      have hle := fusc_odd_le nk
      rw [← hn2] at hle
      omega
    · -- m odd, n even: symmetric contradiction
      exfalso
      have hnk2 : n = 2 * nk := by omega
      have hm2 : m = 2 * mk + 1 := by omega
      have hlt := fusc_lt_of_even (k := nk) (by omega)
      rw [← hnk2] at hlt
      have hle := fusc_odd_le mk
      rw [← hm2] at hle
      omega
    · -- both odd
      have hm2 : m = 2 * mk + 1 := by omega
      have hn2 : n = 2 * nk + 1 := by omega
      rcases Nat.eq_zero_or_pos mk with hmk0 | hmkp <;>
        rcases Nat.eq_zero_or_pos nk with hnk0 | hnkp
      · omega  -- both = 1
      · -- m = 1, n odd ≥ 3: contradiction
        exfalso
        have hgt := fusc_gt_of_odd hnkp
        rw [← hn2] at hgt
        have hm1 : m = 1 := by omega
        subst hm1
        rw [fusc_one] at hnum
        rw [show (1 : ℕ) + 1 = 2 by rfl, fusc_two] at hden
        omega
      · -- n = 1, m odd ≥ 3: contradiction
        exfalso
        have hgt := fusc_gt_of_odd hmkp
        rw [← hm2] at hgt
        have hn1 : n = 1 := by omega
        subst hn1
        rw [fusc_one] at hnum
        rw [show (1 : ℕ) + 1 = 2 by rfl, fusc_two] at hden
        omega
      · -- both odd ≥ 3: descend
        rw [hm2, hn2] at hnum hden
        simp only [fusc_two_mul_add_one] at hnum
        simp only [show 2 * mk + 1 + 1 = 2 * (mk + 1) by ring,
          show 2 * nk + 1 + 1 = 2 * (nk + 1) by ring, fusc_two_mul] at hden
        have e2 : fusc mk = fusc nk := by omega
        have : mk = nk := ih mk (by omega) nk (by omega) (by omega) e2 hden
        omega

/-- Surjectivity of the Calkin–Wilf map (helper form, strong induction on the
sum `a + b`). -/
theorem fusc_surj_aux : ∀ s a b, a + b = s → 0 < a → 0 < b → Nat.Coprime a b →
    ∃ m, 1 ≤ m ∧ fusc m = a ∧ fusc (m + 1) = b := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro a b hs ha hb hcop
    rcases lt_trichotomy a b with hab | hab | hab
    · -- a < b: parent (a, b - a), then m = 2k (left child)
      have hba : 0 < b - a := by omega
      have hcop' : Nat.Coprime a (b - a) := by
        have : Nat.Coprime a (a + (b - a)) := by rw [show a + (b - a) = b from by omega]; exact hcop
        rwa [Nat.coprime_self_add_right] at this
      obtain ⟨k, hk1, hka, hkb⟩ := ih b (by omega) a (b - a) (by omega) ha hba hcop'
      refine ⟨2 * k, by omega, ?_, ?_⟩
      · rw [fusc_two_mul]; exact hka
      · rw [fusc_two_mul_add_one, hka, hkb]; omega
    · -- a = b: coprime forces a = b = 1
      subst hab
      have ha1 : a = 1 := by
        have h := hcop; unfold Nat.Coprime at h; rw [Nat.gcd_self] at h; exact h
      subst ha1
      exact ⟨1, by omega, by simp, by simp⟩
    · -- a > b: parent (a - b, b), then m = 2k + 1 (right child)
      have hab' : 0 < a - b := by omega
      have hcop' : Nat.Coprime (a - b) b := by
        have : Nat.Coprime ((a - b) + b) b := by rw [show (a - b) + b = a from by omega]; exact hcop
        rwa [Nat.coprime_add_self_left] at this
      obtain ⟨k, hk1, hka, hkb⟩ := ih a (by omega) (a - b) b (by omega) hab' hb hcop'
      refine ⟨2 * k + 1, by omega, ?_, ?_⟩
      · rw [fusc_two_mul_add_one, hka, hkb]; omega
      · rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by ring, fusc_two_mul]; exact hkb

/-- Surjectivity of the Calkin–Wilf map: every reduced positive pair `(a, b)` is
`(fusc m, fusc (m+1))` for some `m ≥ 1`. -/
theorem fusc_surj (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) :
    ∃ m, 1 ≤ m ∧ fusc m = a ∧ fusc (m + 1) = b :=
  fusc_surj_aux (a + b) a b rfl ha hb hcop

/-! ### The positive-rationals generator -/

/-- `toRat` of the `n`-th positive rational: the reduced fraction
`fusc (n+1) / fusc (n+2)`. -/
theorem toRat_positiveRationals (n : ℕ) :
    AzRat.toRat (positiveRationals n) = (fusc (n + 1) : ℚ) / (fusc (n + 2) : ℚ) := by
  obtain ⟨h1, h2⟩ := positiveRationalPair_toNat n
  rw [positiveRationals, AzRat.toRat_ofAzNats, h1, h2]

/-- Each `positiveRationals n` is strictly positive. -/
theorem positiveRationals_pos (n : ℕ) : 0 < positiveRationals n := by
  rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero, toRat_positiveRationals]
  have h1 : 0 < fusc (n + 1) := fusc_pos (n + 1) (by omega)
  have h2 : 0 < fusc (n + 2) := fusc_pos (n + 2) (by omega)
  positivity

/-- `positiveRationals` packaged as a map into the subtype `{q // 0 < q}`. -/
def positiveRationalsFun : ℕ → {q : AzRat // 0 < q} :=
  fun n => ⟨positiveRationals n, positiveRationals_pos n⟩

/-- Recovering the numerator/denominator of `ofAzNats` on a reduced positive
pair: no reduction happens, so the fields are returned verbatim. -/
theorem ofAzNats_num_den {a b : AzNat} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : AzNat.coprime a b = true) :
    (AzRat.ofAzNats a b).num = a ∧ (AzRat.ofAzNats a b).den = b := by
  have hg1 : AzNat.gcd a b = 1 := by
    apply AzNat.toNat_injective
    rw [AzNat.toNat_gcd, AzNat.toNat_one]
    exact (AzNat.coprime_iff a b).mp hcop
  have hdiv : ∀ x : AzNat, x / AzNat.gcd a b = x := by
    intro x
    apply AzNat.toNat_injective
    rw [AzNat.toNat_div, hg1, AzNat.toNat_one, Nat.div_one]
  constructor
  · show (AzRat.ofSignAzNats true a b).num = a
    rw [AzRat.ofSignAzNats, dif_neg hb, dif_neg ha]
    exact hdiv a
  · show (AzRat.ofSignAzNats true a b).den = b
    rw [AzRat.ofSignAzNats, dif_neg hb, dif_neg ha]
    exact hdiv b

/-- `positiveRationalsFun` is a bijection onto the positive `AzRat`s — the
Calkin–Wilf theorem, transported to `AzRat`. -/
theorem positiveRationalsFun_bijective : Function.Bijective positiveRationalsFun := by
  constructor
  · -- injective
    intro m n h
    have hv : positiveRationals m = positiveRationals n := congrArg Subtype.val h
    -- reduce to equality of the numerator/denominator AzNats
    obtain ⟨hm1, hm2⟩ := positiveRationalPair_toNat m
    obtain ⟨hn1, hn2⟩ := positiveRationalPair_toNat n
    -- the pairs are reduced positive, so `ofAzNats` returns them verbatim
    have hmna : (positiveRationalPair m).1 ≠ 0 := by
      intro h0; rw [h0, AzNat.toNat_zero] at hm1
      exact absurd hm1.symm (Nat.ne_of_gt (fusc_pos (m + 1) (by omega)))
    have hmnb : (positiveRationalPair m).2 ≠ 0 := by
      intro h0; rw [h0, AzNat.toNat_zero] at hm2
      exact absurd hm2.symm (Nat.ne_of_gt (fusc_pos (m + 2) (by omega)))
    have hnna : (positiveRationalPair n).1 ≠ 0 := by
      intro h0; rw [h0, AzNat.toNat_zero] at hn1
      exact absurd hn1.symm (Nat.ne_of_gt (fusc_pos (n + 1) (by omega)))
    have hnnb : (positiveRationalPair n).2 ≠ 0 := by
      intro h0; rw [h0, AzNat.toNat_zero] at hn2
      exact absurd hn2.symm (Nat.ne_of_gt (fusc_pos (n + 2) (by omega)))
    have hmcop : AzNat.coprime (positiveRationalPair m).1 (positiveRationalPair m).2 = true := by
      rw [AzNat.coprime_iff, hm1, hm2]; exact fusc_coprime (m + 1)
    have hncop : AzNat.coprime (positiveRationalPair n).1 (positiveRationalPair n).2 = true := by
      rw [AzNat.coprime_iff, hn1, hn2]; exact fusc_coprime (n + 1)
    obtain ⟨hmnum, hmden⟩ := ofAzNats_num_den hmna hmnb hmcop
    obtain ⟨hnnum, hnden⟩ := ofAzNats_num_den hnna hnnb hncop
    -- from `hv` extract equality of num and den fields
    have hnum : (positiveRationalPair m).1 = (positiveRationalPair n).1 := by
      rw [← hmnum, ← hnnum]; exact congrArg AzRat.num hv
    have hden : (positiveRationalPair m).2 = (positiveRationalPair n).2 := by
      rw [← hmden, ← hnden]; exact congrArg AzRat.den hv
    -- convert to `fusc` equalities and apply injectivity
    have enum : fusc (m + 1) = fusc (n + 1) := by
      rw [← hm1, ← hn1, hnum]
    have eden : fusc (m + 2) = fusc (n + 2) := by
      rw [← hm2, ← hn2, hden]
    have : m + 1 = n + 1 :=
      fusc_inj (m + 1) (n + 1) (by omega) (by omega) enum
        (by rw [show m + 1 + 1 = m + 2 from rfl, show n + 1 + 1 = n + 2 from rfl]; exact eden)
    omega
  · -- surjective
    rintro ⟨q, hq⟩
    -- q is positive: sign true, num > 0, and reduced
    have hpos : 0 < AzRat.toRat q := by
      rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero] at hq; exact hq
    have hnum_pos : 0 < (AzRat.toRat q).num := Rat.num_pos.mpr hpos
    have hqsign : q.sign = true := by
      rw [← AzRat.ofRat_toRat q]
      show decide (0 ≤ (AzRat.toRat q).num) = true
      rw [decide_eq_true_eq]; omega
    have hqnum : q.num ≠ 0 := by
      intro h0
      have hnum_eq : (AzRat.toRat q).num
          = if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ) := rfl
      rw [h0, AzNat.toNat_zero, Nat.cast_zero] at hnum_eq
      have hz : (AzRat.toRat q).num = 0 := by rw [hnum_eq]; split <;> simp
      omega
    have hqden : q.den ≠ 0 := q.den_nz
    have hnumpos : 0 < q.num.toNat := by
      rcases Nat.eq_zero_or_pos q.num.toNat with h | h
      · exact absurd (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)) hqnum
      · exact h
    have hdenpos : 0 < q.den.toNat := by
      rcases Nat.eq_zero_or_pos q.den.toNat with h | h
      · exact absurd (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)) hqden
      · exact h
    have hqcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
    obtain ⟨msucc, hmge, hma, hmb⟩ := fusc_surj q.num.toNat q.den.toNat hnumpos hdenpos hqcop
    -- msucc ≥ 1, set n = msucc - 1
    refine ⟨msucc - 1, ?_⟩
    apply Subtype.ext
    show positiveRationals (msucc - 1) = q
    have hmn : msucc - 1 + 1 = msucc := by omega
    obtain ⟨hp1, hp2⟩ := positiveRationalPair_toNat (msucc - 1)
    rw [hmn] at hp1
    have hp2' : (positiveRationalPair (msucc - 1)).2.toNat = q.den.toNat := by
      rw [hp2, show msucc - 1 + 2 = msucc + 1 from by omega, hmb]
    have hp1' : (positiveRationalPair (msucc - 1)).1.toNat = q.num.toNat := by
      rw [hp1, hma]
    -- the pair equals (q.num, q.den) as AzNats
    have ea : (positiveRationalPair (msucc - 1)).1 = q.num := AzNat.toNat_injective hp1'
    have eb : (positiveRationalPair (msucc - 1)).2 = q.den := AzNat.toNat_injective hp2'
    rw [positiveRationals, ea, eb]
    -- ofAzNats q.num q.den = q since q is positive reduced
    have := AzRat.ofSignAzNats_self q
    rw [hqsign] at this
    exact this

/-- Exhaustive generator for the positive `AzRat`s, in Calkin–Wilf order. -/
instance positiveRationalsGen : ExhaustiveGenerator {q : AzRat // 0 < q} :=
  ExhaustiveGenerator.ofBijective positiveRationalsFun positiveRationalsFun_bijective

instance : Contiguous {q : AzRat // 0 < q} :=
  ExhaustiveGenerator.contiguous_of_gen_some positiveRationalsGen rfl

/-! ### The negative-rationals generator (negate the positives) -/

/-- `negativeRationals n` is strictly negative. -/
theorem negativeRationals_neg (n : ℕ) : negativeRationals n < 0 := by
  rw [negativeRationals, AzRat.lt_iff_toRat_lt, AzRat.toRat_zero, AzRat.toRat_neg]
  have := positiveRationals_pos n
  rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero] at this
  linarith

/-- `negativeRationals` packaged into `{q // q < 0}`. -/
def negativeRationalsFun : ℕ → {q : AzRat // q < 0} :=
  fun n => ⟨negativeRationals n, negativeRationals_neg n⟩

theorem negativeRationalsFun_bijective : Function.Bijective negativeRationalsFun := by
  constructor
  · intro m n h
    have hv : negativeRationals m = negativeRationals n := congrArg Subtype.val h
    have : positiveRationals m = positiveRationals n := by
      have := congrArg AzRat.toRat hv
      rw [negativeRationals, negativeRationals, AzRat.toRat_neg, AzRat.toRat_neg] at this
      exact AzRat.toRat_injective (by linarith)
    exact positiveRationalsFun_bijective.injective (Subtype.ext this)
  · rintro ⟨q, hq⟩
    obtain ⟨n, hn⟩ := positiveRationalsFun_bijective.surjective ⟨-q, by
      rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero, AzRat.toRat_neg]
      rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero] at hq; linarith⟩
    refine ⟨n, Subtype.ext ?_⟩
    show negativeRationals n = q
    have : positiveRationals n = -q := congrArg Subtype.val hn
    rw [negativeRationals, this]
    exact AzRat.toRat_injective (by simp)

instance negativeRationalsGen : ExhaustiveGenerator {q : AzRat // q < 0} :=
  ExhaustiveGenerator.ofBijective negativeRationalsFun negativeRationalsFun_bijective

instance : Contiguous {q : AzRat // q < 0} :=
  ExhaustiveGenerator.contiguous_of_gen_some negativeRationalsGen rfl

/-! ### The nonnegative-rationals generator (prepend `0`) -/

/-- `nonnegativeRationals n` is nonnegative. -/
theorem nonnegativeRationals_nonneg (n : ℕ) : 0 ≤ nonnegativeRationals n := by
  rw [nonnegativeRationals]
  split
  · exact le_refl 0
  · exact le_of_lt (positiveRationals_pos _)

def nonnegativeRationalsFun : ℕ → {q : AzRat // 0 ≤ q} :=
  fun n => ⟨nonnegativeRationals n, nonnegativeRationals_nonneg n⟩

theorem nonnegativeRationalsFun_bijective : Function.Bijective nonnegativeRationalsFun := by
  constructor
  · intro m n h
    have hv : nonnegativeRationals m = nonnegativeRationals n := congrArg Subtype.val h
    rw [nonnegativeRationals, nonnegativeRationals] at hv
    -- case on the two `if`s
    by_cases hm0 : m = 0 <;> by_cases hn0 : n = 0
    · omega
    · exfalso; rw [if_pos hm0, if_neg hn0] at hv
      exact absurd (positiveRationals_pos (n - 1)) (by rw [← hv]; exact lt_irrefl 0)
    · exfalso; rw [if_neg hm0, if_pos hn0] at hv
      exact absurd (positiveRationals_pos (m - 1)) (by rw [hv]; exact lt_irrefl 0)
    · rw [if_neg hm0, if_neg hn0] at hv
      have : m - 1 = n - 1 :=
        positiveRationalsFun_bijective.injective (Subtype.ext hv)
      omega
  · rintro ⟨q, hq⟩
    rcases eq_or_lt_of_le hq with h0 | h0
    · exact ⟨0, Subtype.ext (by show nonnegativeRationals 0 = q; rw [nonnegativeRationals, if_pos rfl]; exact h0)⟩
    · obtain ⟨n, hn⟩ := positiveRationalsFun_bijective.surjective ⟨q, h0⟩
      refine ⟨n + 1, Subtype.ext ?_⟩
      show nonnegativeRationals (n + 1) = q
      rw [nonnegativeRationals, if_neg (by omega), Nat.add_sub_cancel]
      exact congrArg Subtype.val hn

instance nonnegativeRationalsGen : ExhaustiveGenerator {q : AzRat // 0 ≤ q} :=
  ExhaustiveGenerator.ofBijective nonnegativeRationalsFun nonnegativeRationalsFun_bijective

instance : Contiguous {q : AzRat // 0 ≤ q} :=
  ExhaustiveGenerator.contiguous_of_gen_some nonnegativeRationalsGen rfl

/-! ### The nonzero-rationals generator (interleave positive and negative) -/

/-- `nonzeroRationals n` is never zero. -/
theorem nonzeroRationals_ne_zero (n : ℕ) : nonzeroRationals n ≠ 0 := by
  rw [nonzeroRationals]
  split
  · exact ne_of_gt (positiveRationals_pos _)
  · intro h
    have hp := positiveRationals_pos (n / 2)
    rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero] at hp
    have h2 := congrArg AzRat.toRat h
    rw [AzRat.toRat_neg, AzRat.toRat_zero] at h2
    linarith

def nonzeroRationalsFun : ℕ → {q : AzRat // q ≠ 0} :=
  fun n => ⟨nonzeroRationals n, nonzeroRationals_ne_zero n⟩

theorem nonzeroRationalsFun_bijective : Function.Bijective nonzeroRationalsFun := by
  constructor
  · intro m n h
    have hv : nonzeroRationals m = nonzeroRationals n := congrArg Subtype.val h
    rw [nonzeroRationals, nonzeroRationals] at hv
    by_cases hm : m % 2 = 0 <;> by_cases hn : n % 2 = 0
    · rw [if_pos hm, if_pos hn] at hv
      have : m / 2 = n / 2 := positiveRationalsFun_bijective.injective (Subtype.ext hv)
      omega
    · exfalso; rw [if_pos hm, if_neg hn] at hv
      -- positive = negative, impossible
      have hp := positiveRationals_pos (m / 2)
      have hp2 := positiveRationals_pos (n / 2)
      rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero] at hp hp2
      have := congrArg AzRat.toRat hv
      rw [AzRat.toRat_neg] at this
      linarith
    · exfalso; rw [if_neg hm, if_pos hn] at hv
      have hp := positiveRationals_pos (m / 2)
      have hp2 := positiveRationals_pos (n / 2)
      rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero] at hp hp2
      have := congrArg AzRat.toRat hv
      rw [AzRat.toRat_neg] at this
      linarith
    · rw [if_neg hm, if_neg hn] at hv
      have hneg : positiveRationals (m / 2) = positiveRationals (n / 2) := by
        have := congrArg AzRat.toRat hv
        rw [AzRat.toRat_neg, AzRat.toRat_neg] at this
        exact AzRat.toRat_injective (by linarith)
      have : m / 2 = n / 2 := positiveRationalsFun_bijective.injective (Subtype.ext hneg)
      omega
  · rintro ⟨q, hq⟩
    rcases lt_trichotomy q 0 with hlt | heq | hgt
    · -- negative: q = -(positive), use odd index
      obtain ⟨n, hn⟩ := positiveRationalsFun_bijective.surjective ⟨-q, by
        rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero, AzRat.toRat_neg]
        rw [AzRat.lt_iff_toRat_lt, AzRat.toRat_zero] at hlt; linarith⟩
      refine ⟨2 * n + 1, Subtype.ext ?_⟩
      show nonzeroRationals (2 * n + 1) = q
      rw [nonzeroRationals, if_neg (by omega),
          show (2 * n + 1) / 2 = n from by omega]
      have : positiveRationals n = -q := congrArg Subtype.val hn
      rw [this]
      exact AzRat.toRat_injective (by simp)
    · exact absurd heq hq
    · -- positive: even index
      obtain ⟨n, hn⟩ := positiveRationalsFun_bijective.surjective ⟨q, hgt⟩
      refine ⟨2 * n, Subtype.ext ?_⟩
      show nonzeroRationals (2 * n) = q
      rw [nonzeroRationals, if_pos (by omega), show (2 * n) / 2 = n from by omega]
      exact congrArg Subtype.val hn

instance nonzeroRationalsGen : ExhaustiveGenerator {q : AzRat // q ≠ 0} :=
  ExhaustiveGenerator.ofBijective nonzeroRationalsFun nonzeroRationalsFun_bijective

instance : Contiguous {q : AzRat // q ≠ 0} :=
  ExhaustiveGenerator.contiguous_of_gen_some nonzeroRationalsGen rfl

/-! ### The all-rationals generator (prepend `0` to the nonzero) -/

theorem rationals_bijective : Function.Bijective rationals := by
  constructor
  · intro m n h
    rw [rationals, rationals] at h
    by_cases hm0 : m = 0 <;> by_cases hn0 : n = 0
    · omega
    · exfalso; rw [if_pos hm0, if_neg hn0] at h
      exact nonzeroRationals_ne_zero (n - 1) h.symm
    · exfalso; rw [if_neg hm0, if_pos hn0] at h
      exact nonzeroRationals_ne_zero (m - 1) h
    · rw [if_neg hm0, if_neg hn0] at h
      have : m - 1 = n - 1 := nonzeroRationalsFun_bijective.injective (Subtype.ext h)
      omega
  · intro q
    by_cases hq0 : q = 0
    · exact ⟨0, by rw [rationals, if_pos rfl]; exact hq0.symm⟩
    · obtain ⟨n, hn⟩ := nonzeroRationalsFun_bijective.surjective ⟨q, hq0⟩
      refine ⟨n + 1, ?_⟩
      rw [rationals, if_neg (by omega), Nat.add_sub_cancel]
      exact congrArg Subtype.val hn

instance rationalsGen : ExhaustiveGenerator AzRat :=
  ExhaustiveGenerator.ofBijective rationals rationals_bijective

instance : Contiguous AzRat := ExhaustiveGenerator.contiguous_of_gen_some rationalsGen rfl

/-! ### Infiniteness of every rational generator

Each result is REGISTERED as an instance (the types/subtypes are Azurite's own,
so there is no Mathlib instance to clash with); the named theorem form is kept
for the blueprint/discoverability. -/

theorem positiveRationalsGen_infinite : Infinite {q : AzRat // 0 < q} :=
  Infinite.of_injective positiveRationalsFun positiveRationalsFun_bijective.injective

instance : Infinite {q : AzRat // 0 < q} := positiveRationalsGen_infinite

theorem negativeRationalsGen_infinite : Infinite {q : AzRat // q < 0} :=
  Infinite.of_injective negativeRationalsFun negativeRationalsFun_bijective.injective

instance : Infinite {q : AzRat // q < 0} := negativeRationalsGen_infinite

theorem nonnegativeRationalsGen_infinite : Infinite {q : AzRat // 0 ≤ q} :=
  Infinite.of_injective nonnegativeRationalsFun nonnegativeRationalsFun_bijective.injective

instance : Infinite {q : AzRat // 0 ≤ q} := nonnegativeRationalsGen_infinite

theorem nonzeroRationalsGen_infinite : Infinite {q : AzRat // q ≠ 0} :=
  Infinite.of_injective nonzeroRationalsFun nonzeroRationalsFun_bijective.injective

instance : Infinite {q : AzRat // q ≠ 0} := nonzeroRationalsGen_infinite

theorem rationalsGen_infinite : Infinite AzRat :=
  Infinite.of_injective rationals rationals_bijective.injective

instance : Infinite AzRat := rationalsGen_infinite

/-! ### Generator previews (Malachite doctests) -/

#guard ((ExhaustiveGenerator.firstN {q : AzRat // 0 < q} 7).map (·.val.toString)) ==
  ["1", "1/2", "2", "1/3", "3/2", "2/3", "3"]
#guard ((ExhaustiveGenerator.firstN {q : AzRat // q < 0} 7).map (·.val.toString)) ==
  ["-1", "-1/2", "-2", "-1/3", "-3/2", "-2/3", "-3"]
#guard ((ExhaustiveGenerator.firstN {q : AzRat // 0 ≤ q} 7).map (·.val.toString)) ==
  ["0", "1", "1/2", "2", "1/3", "3/2", "2/3"]
#guard ((ExhaustiveGenerator.firstN {q : AzRat // q ≠ 0} 7).map (·.val.toString)) ==
  ["1", "-1", "1/2", "-1/2", "2", "-2", "1/3"]
#guard ((ExhaustiveGenerator.firstN AzRat 7).map (·.toString)) ==
  ["0", "1", "-1", "1/2", "-1/2", "2", "-2"]

end Azurite

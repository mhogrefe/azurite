/-
  Crandall–Pomerance, Algorithm 2.1.7 (CRT reconstruction with
  preconditioning (Garner)): given `r ≥ 2` fixed, pairwise coprime
  moduli `m_0, …, m_(r−1)` with product `M` and residues
  `{n_i (mod m_i)}`, return the unique `n ∈ [0, M−1]` with those
  residues.  Step 1 precomputes `μ_i = m_0 ⋯ m_(i−1)` and
  `c_i = μ_i^(−1) mod m_i` (`1 ≤ i < r`); step 2 — the reentry point,
  reusable across inputs `{n_i}` — accumulates

    `n := n_0`;  `u := ((n_i − n) c_i) mod m_i`;  `n := n + u μ_i`,

  maintaining `n ≡ n_j (mod m_j)` for `j ≤ i` and `n < μ_(i+1)`.

  The two steps are formalized separately, mirroring the book's
  precompute/reenter split: `garnerPrecomp` (step 1, driven by the
  running product) and `garnerLoop` (step 2) over `garnerStep`, with
  the signed subtraction `(n_i − n) mod m_i` realized in `ℕ` as
  `(n_i mod m_i) + (m_i − n mod m_i)` — congruent to `n_i − n` and
  safe of underflow.  (The inner reductions make the algorithm total
  and correct for arbitrary `n_i`, agreeing verbatim with the book's
  when the `n_i` are genuine residues, i.e. `n_i < m_i`.)  The
  modular inverse is `invMod`, the extended Euclidean algorithm
  (`Nat.gcdA`) reduced to the least nonnegative representative.

  Correctness (`garner_lt`, `garner_modEq`) needs no length
  hypothesis — the specification is over `ms.zip ns` — and the book's
  UNIQUENESS claim is `eq_garner_of_modEq`: any `x < M` with the
  residues of `garner ms ns` IS `garner ms ns` (via the
  pairwise-coprime product congruence of Theorem 2.1.6).
  Kernel-checked: the classical `x ≡ 2 (3), 3 (5), 2 (7) ↦ 23`, and a
  reentry at the same moduli.
-/
import Azurite.CrandallPomerance.Chapter2.Theorem_2_1_6

namespace Azurite

namespace CP

/-- The least nonnegative inverse of `a` mod `n` (meaningful for
`a`, `n` coprime), via the extended Euclidean algorithm. -/
def invMod (a n : ℕ) : ℕ := (Nat.gcdA a n % (n : ℤ)).toNat

theorem invMod_lt (a : ℕ) {n : ℕ} (hn : 0 < n) : invMod a n < n := by
  have h := Int.emod_lt_of_pos (Nat.gcdA a n) (b := (n : ℤ))
    (by exact_mod_cast hn)
  rw [invMod]
  omega

/-- The defining property: for coprime `a`, `n`,
`a · invMod a n ≡ 1 (mod n)`. -/
theorem mul_invMod {a n : ℕ} (h : Nat.Coprime a n) (hn : 0 < n) :
    a * invMod a n ≡ 1 [MOD n] := by
  have h0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hcast : ((invMod a n : ℕ) : ℤ) = Nat.gcdA a n % (n : ℤ) := by
    rw [invMod]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ h0.ne')
  have hbez : (1 : ℤ) = a * Nat.gcdA a n + n * Nat.gcdB a n := by
    have := Nat.gcd_eq_gcd_ab a n
    rwa [h] at this
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
  push_cast
  rw [hcast]
  refine ⟨-(a * (Nat.gcdA a n / n)) - Nat.gcdB a n, ?_⟩
  rw [Int.emod_def, hbez]
  ring

/-- The modular inverse is unique: any residue `x < n` with
`a x ≡ 1 (mod n)` IS `invMod a n` — so any correctly-computed inverse
(e.g. from a different Bézout pair) agrees with `invMod`.
Coprimality is forced by the hypothesis. -/
theorem invMod_unique {a n x : ℕ} (hn : 0 < n) (hx : x < n)
    (hax : a * x ≡ 1 [MOD n]) : x = invMod a n := by
  have h1 : (n : ℤ) ∣ 1 - (a : ℤ) * x := by
    have := (Nat.modEq_iff_dvd (n := n) (a := a * x) (b := 1)).mp hax
    push_cast at this ⊢
    exact this
  have hg1 : Nat.Coprime a n := by
    have hga : ((Nat.gcd a n : ℕ) : ℤ) ∣ (a : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a n)
    have hgn : ((Nat.gcd a n : ℕ) : ℤ) ∣ (n : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a n)
    have hone : ((Nat.gcd a n : ℕ) : ℤ) ∣ 1 := by
      have h2 : ((Nat.gcd a n : ℕ) : ℤ) ∣ (a : ℤ) * x := hga.mul_right x
      simpa using dvd_add h2 (hgn.trans h1)
    exact Nat.dvd_one.mp (by exact_mod_cast hone)
  have hinv := mul_invMod hg1 hn
  have hlt := invMod_lt a hn
  have hxy : x ≡ invMod a n [MOD n] :=
    calc x ≡ x * (a * invMod a n) [MOD n] := by
          simpa using (hinv.mul_left x).symm
      _ = invMod a n * (a * x) := by ring
      _ ≡ invMod a n * 1 [MOD n] := hax.mul_left _
      _ = invMod a n := Nat.mul_one _
  rw [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hlt] at hxy
  exact hxy

/-- The inner-loop update of step 2: from `x` solving the earlier
congruences (with `μ` the product of the earlier moduli and
`c = invMod μ mᵢ`) to a solution of `· ≡ nᵢ (mod mᵢ)` too.  The
book's `u := ((nᵢ − n) cᵢ) mod mᵢ` is computed underflow-free. -/
def garnerStep (mᵢ μ c nᵢ x : ℕ) : ℕ :=
  x + ((nᵢ % mᵢ + (mᵢ - x % mᵢ)) * c) % mᵢ * μ

/-- **Step 1 (precomputation)**: the triples `(m_i, μ_i, c_i)` for
`1 ≤ i < r`, driven by the running product `μ` (initially `m_0`). -/
def garnerPrecomp (μ : ℕ) : List ℕ → List (ℕ × ℕ × ℕ)
  | [] => []
  | mᵢ :: ms => (mᵢ, μ, invMod μ mᵢ) :: garnerPrecomp (μ * mᵢ) ms

/-- **Step 2 (the reentry point)**: fold the Garner updates over the
precomputed triples and the residues. -/
def garnerLoop : ℕ → List (ℕ × ℕ × ℕ) → List ℕ → ℕ
  | x, _, [] => x
  | x, [], _ => x
  | x, (mᵢ, μ, c) :: pre, nᵢ :: ns => garnerLoop (garnerStep mᵢ μ c nᵢ x) pre ns

/-- **Algorithm 2.1.7 (Garner)**: CRT reconstruction with
preconditioning — the unique `n ∈ [0, M−1]` with `n ≡ nᵢ (mod mᵢ)`. -/
def garner (ms ns : List ℕ) : ℕ :=
  match ms, ns with
  | m₀ :: ms', n₀ :: ns' =>
    garnerLoop (n₀ % m₀) (garnerPrecomp m₀ ms') ns' % (m₀ :: ms').prod
  | _, _ => 0

-- the book's classical example shape: x ≡ 2 (3), 3 (5), 2 (7) ↦ 23
#guard garner [3, 5, 7] [2, 3, 2] = 23
-- reentry at the same moduli with fresh residues
#guard garner [3, 5, 7] [1, 2, 3] = 52
-- r = 2, and unreduced inputs agree with their reductions
#guard garner [4, 9] [3, 4] = 31
#guard garner [4, 9] [7, 13] = 31

/-- The loop invariant of step 2: starting from `x < μ` with the
moduli in `ms` coprime to `μ` and pairwise coprime, the loop result
is below `μ · ∏ ms`, is `≡ x (mod μ)` — preserving all earlier
congruences — and solves every congruence in `ms.zip ns`. -/
theorem garnerLoop_spec (μ : ℕ) (ms : List ℕ) :
    ∀ (x : ℕ) (ns : List ℕ), x < μ →
    (∀ mᵢ ∈ ms, 0 < mᵢ) → (∀ mᵢ ∈ ms, Nat.Coprime μ mᵢ) →
    ms.Pairwise Nat.Coprime →
    garnerLoop x (garnerPrecomp μ ms) ns < μ * ms.prod ∧
      garnerLoop x (garnerPrecomp μ ms) ns ≡ x [MOD μ] ∧
      ∀ p ∈ ms.zip ns, garnerLoop x (garnerPrecomp μ ms) ns ≡ p.2 [MOD p.1] := by
  induction ms generalizing μ with
  | nil =>
    intro x ns hx _ _ _
    have hres : garnerLoop x (garnerPrecomp μ []) ns = x := by
      cases ns <;> rfl
    rw [hres]
    exact ⟨by simpa using hx, Nat.ModEq.refl x, by simp⟩
  | cons mᵢ ms ih =>
    intro x ns hx hpos hcoμ hco
    have hmᵢ : 0 < mᵢ := hpos mᵢ (by simp)
    match ns with
    | [] =>
      have hres : garnerLoop x (garnerPrecomp μ (mᵢ :: ms)) [] = x := rfl
      rw [hres]
      refine ⟨lt_of_lt_of_le hx ?_, Nat.ModEq.refl x, by simp⟩
      exact Nat.le_mul_of_pos_right μ (List.prod_pos hpos)
    | nᵢ :: ns =>
      have hc : Nat.Coprime μ mᵢ := hcoμ mᵢ (by simp)
      set u : ℕ := ((nᵢ % mᵢ + (mᵢ - x % mᵢ)) * invMod μ mᵢ) % mᵢ with hu
      have hgs : garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x = x + u * μ := rfl
      have hult : u < mᵢ := Nat.mod_lt _ hmᵢ
      have hx' : garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x < μ * mᵢ := by
        rw [hgs, Nat.mul_comm μ mᵢ]
        calc x + u * μ < (u + 1) * μ := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ mᵢ * μ := Nat.mul_le_mul_right μ (by omega)
      have hstep_mod_μ : garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x ≡ x [MOD μ] := by
        rw [hgs]
        show (x + u * μ) % μ = x % μ
        exact Nat.add_mul_mod_self_right x u μ
      have hstep_mod_mᵢ : garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x
          ≡ nᵢ [MOD mᵢ] := by
        rw [hgs]
        have hcμ : μ * invMod μ mᵢ ≡ 1 [MOD mᵢ] := mul_invMod hc hmᵢ
        have h1 : u * μ ≡ (nᵢ % mᵢ + (mᵢ - x % mᵢ)) * (μ * invMod μ mᵢ)
            [MOD mᵢ] :=
          calc u * μ
              ≡ (nᵢ % mᵢ + (mᵢ - x % mᵢ)) * invMod μ mᵢ * μ [MOD mᵢ] :=
              (Nat.mod_modEq _ _).mul_right μ
            _ = (nᵢ % mᵢ + (mᵢ - x % mᵢ)) * (μ * invMod μ mᵢ) := by ring
        have h2 : u * μ ≡ nᵢ % mᵢ + (mᵢ - x % mᵢ) [MOD mᵢ] :=
          h1.trans (by simpa using hcμ.mul_left (nᵢ % mᵢ + (mᵢ - x % mᵢ)))
        have h3 : x + (nᵢ % mᵢ + (mᵢ - x % mᵢ))
            = nᵢ % mᵢ + mᵢ * (x / mᵢ + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          have hdm := Nat.div_add_mod x mᵢ
          have hlt := Nat.mod_lt x hmᵢ
          generalize mᵢ * (x / mᵢ) = P at hdm ⊢
          generalize x % mᵢ = R at hdm hlt ⊢
          omega
        calc x + u * μ
            ≡ x + (nᵢ % mᵢ + (mᵢ - x % mᵢ)) [MOD mᵢ] := h2.add_left x
          _ = nᵢ % mᵢ + mᵢ * (x / mᵢ + 1) := h3
          _ ≡ nᵢ % mᵢ [MOD mᵢ] := by
              show (nᵢ % mᵢ + mᵢ * (x / mᵢ + 1)) % mᵢ = nᵢ % mᵢ % mᵢ
              exact Nat.add_mul_mod_self_left _ _ _
          _ ≡ nᵢ [MOD mᵢ] := Nat.mod_modEq nᵢ mᵢ
      obtain ⟨ih_lt, ih_μ, ih_zip⟩ := ih (μ * mᵢ)
        (garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x) ns hx'
        (fun m hm => hpos m (List.mem_cons_of_mem _ hm))
        (fun m hm => (Nat.Coprime.mul_right
          (hcoμ m (List.mem_cons_of_mem _ hm)).symm
          ((List.pairwise_cons.mp hco).1 m hm).symm).symm)
        (List.pairwise_cons.mp hco).2
      have hres : garnerLoop x (garnerPrecomp μ (mᵢ :: ms)) (nᵢ :: ns)
          = garnerLoop (garnerStep mᵢ μ (invMod μ mᵢ) nᵢ x)
            (garnerPrecomp (μ * mᵢ) ms) ns := rfl
      rw [hres]
      refine ⟨by rw [List.prod_cons, ← Nat.mul_assoc]; exact ih_lt, ?_, ?_⟩
      · exact (ih_μ.of_dvd (dvd_mul_right μ mᵢ)).trans hstep_mod_μ
      · intro p hp
        rw [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact (ih_μ.of_dvd (dvd_mul_left mᵢ μ)).trans hstep_mod_mᵢ
        · exact ih_zip p hp

/-- **Algorithm 2.1.7 is correct, part 1**: the result lies in
`[0, M−1]`. -/
theorem garner_lt (ms ns : List ℕ) (hpos : ∀ mᵢ ∈ ms, 0 < mᵢ) :
    garner ms ns < ms.prod := by
  have hM : 0 < ms.prod := List.prod_pos hpos
  match ms, ns with
  | [], _ => simp [garner]
  | m₀ :: ms', [] => simpa [garner] using hM
  | m₀ :: ms', n₀ :: ns' => exact Nat.mod_lt _ hM

/-- **Algorithm 2.1.7 is correct, part 2**: the result has the given
residues. -/
theorem garner_modEq (ms ns : List ℕ) (hpos : ∀ mᵢ ∈ ms, 0 < mᵢ)
    (hco : ms.Pairwise Nat.Coprime) :
    ∀ p ∈ ms.zip ns, garner ms ns ≡ p.2 [MOD p.1] := by
  match ms, ns with
  | [], _ => simp
  | m₀ :: ms', [] => simp
  | m₀ :: ms', n₀ :: ns' =>
    have hm₀ : 0 < m₀ := hpos m₀ (by simp)
    obtain ⟨hlt, hμ, hzip⟩ := garnerLoop_spec m₀ ms' (n₀ % m₀) ns'
      (Nat.mod_lt _ hm₀)
      (fun m hm => hpos m (List.mem_cons_of_mem _ hm))
      (fun m hm => (List.pairwise_cons.mp hco).1 m hm)
      (List.pairwise_cons.mp hco).2
    have hself : garner (m₀ :: ms') (n₀ :: ns')
        = garnerLoop (n₀ % m₀) (garnerPrecomp m₀ ms') ns' := by
      rw [garner, Nat.mod_eq_of_lt (by rw [List.prod_cons]; exact hlt)]
    intro p hp
    rw [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hself ▸ (hμ.trans (Nat.mod_modEq n₀ m₀))
    · exact hself ▸ hzip p hp

/-- **The uniqueness claim of Algorithm 2.1.7** (via Theorem 2.1.6's
product congruence): any `x ∈ [0, M−1]` with the given residues IS
the algorithm's output.  (`ns` must cover `ms`, else a congruence is
unconstrained.) -/
theorem eq_garner_of_modEq (ms ns : List ℕ) (hpos : ∀ mᵢ ∈ ms, 0 < mᵢ)
    (hco : ms.Pairwise Nat.Coprime) (hlen : ms.length ≤ ns.length) {x : ℕ}
    (hlt : x < ms.prod) (hx : ∀ p ∈ ms.zip ns, x ≡ p.2 [MOD p.1]) :
    x = garner ms ns := by
  have hmod : x ≡ garner ms ns [MOD ms.prod] := by
    rw [Nat.modEq_list_prod_iff hco]
    intro i
    have hi : (i : ℕ) < (ms.zip ns).length := by
      rw [List.length_zip]
      omega
    have hmem : (ms.zip ns)[(i : ℕ)] ∈ ms.zip ns := List.getElem_mem hi
    have hpair : (ms.zip ns)[(i : ℕ)]
        = (ms[(i : ℕ)], ns[(i : ℕ)]'(by have := i.isLt; omega)) :=
      List.getElem_zip ..
    rw [hpair] at hmem
    have hgi : ms.get i = ms[(i : ℕ)] := rfl
    rw [hgi]
    exact (hx _ hmem).trans (garner_modEq ms ns hpos hco _ hmem).symm
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt (garner_lt ms ns hpos)] at hmod
  exact hmod

end CP

end Azurite

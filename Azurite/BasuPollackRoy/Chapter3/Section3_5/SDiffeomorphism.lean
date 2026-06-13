import Azurite.BasuPollackRoy.Chapter3.Section3_5.SClass

/-! # BPR §3.5 — `𝒮^∞`-diffeomorphisms

**An `𝒮^∞`-diffeomorphism `ϕ` from a semialgebraic open `U` of `R^k` to a semialgebraic
open `Ω` of `R^k` is a bijection from `U` to `Ω` that is `𝒮^∞` and such that `ϕ⁻¹` is
`𝒮^∞`.**

Mirroring `IsSemialgebraicHomeomorphism` (§3.1), the inverse is carried as explicit data
`ϕinv`; `𝒮^∞` membership is `SClassInfty`. Domain and codomain live in the same `R^k`
(differentiability requires equal dimension), and their semialgebraic openness — part of
BPR's phrasing — is recorded in the structure so the predicate is self-contained. -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- **BPR definition (`𝒮^∞`-diffeomorphism).** A bijection `ϕ : U → Ω` between semialgebraic
open subsets of `R^k`, of class `𝒮^∞`, whose inverse `ϕinv : Ω → U` is also of class
`𝒮^∞`. -/
structure IsSInftyDiffeomorphism (U Ω : Set (Fin k → R))
    (ϕ ϕinv : (Fin k → R) → (Fin k → R)) : Prop where
  /-- the source `U` is open. -/
  isOpen_source : IsOpen U
  /-- the source `U` is semialgebraic. -/
  isSemialgebraic_source : IsSemialgebraicSet U
  /-- the target `Ω` is open. -/
  isOpen_target : IsOpen Ω
  /-- the target `Ω` is semialgebraic. -/
  isSemialgebraic_target : IsSemialgebraicSet Ω
  /-- `ϕ` is a bijection from `U` onto `Ω`. -/
  bijOn : Set.BijOn ϕ U Ω
  /-- `ϕ` is of class `𝒮^∞` from `U` to `Ω`. -/
  mem_sClassInfty : ϕ ∈ SClassInfty U Ω
  /-- `ϕinv` is the two-sided inverse of `ϕ` on `U` and `Ω`. -/
  invOn : Set.InvOn ϕinv ϕ U Ω
  /-- the inverse `ϕinv` is of class `𝒮^∞` from `Ω` to `U`. -/
  inv_mem_sClassInfty : ϕinv ∈ SClassInfty Ω U

/-! ### `𝒮^∞` submanifolds -/

/-- The coordinate subspace `R^ℓ × {0} = {(a₁, …, a_ℓ, 0, …, 0)}` of `R^k`: the points
whose coordinates from index `ℓ` on vanish. -/
def coordSubspace (k ℓ : ℕ) : Set (Fin k → R) :=
  {z : Fin k → R | ∀ i : Fin k, ℓ ≤ (i : ℕ) → z i = 0}

/-- **BPR definition (`𝒮^∞` submanifold).** A semialgebraic subset `M ⊆ R^k` is an `𝒮^∞`
submanifold of `R^k` of dimension `ℓ` if for every `x ∈ M` there is a semialgebraic open
`U ⊆ R^k` and an `𝒮^∞`-diffeomorphism `ϕ` from `U` to a semialgebraic open neighborhood
`Ω` of `x` with `ϕ(0) = x` and `ϕ(U ∩ (R^ℓ × {0})) = M ∩ Ω`. -/
def IsSInftySubmanifold (ℓ : ℕ) (M : Set (Fin k → R)) : Prop :=
  IsSemialgebraicSet M ∧
  ∀ x ∈ M, ∃ (U Ω : Set (Fin k → R)) (ϕ ϕinv : (Fin k → R) → (Fin k → R)),
    IsSInftyDiffeomorphism U Ω ϕ ϕinv ∧ (0 : Fin k → R) ∈ U ∧ x ∈ Ω ∧ ϕ 0 = x ∧
      ϕ '' (U ∩ coordSubspace k ℓ) = M ∩ Ω

/-! ### `𝒮^∞` maps between submanifolds -/

/-- **BPR definition (`𝒮^∞` map).** A semialgebraic map `f` from `M ⊆ R^m` to `N ⊆ R^n`
(`M`, `N` understood to be `𝒮^∞` submanifolds) is an *`𝒮^∞` map* if it is locally the
restriction of an `𝒮^∞` map from `R^m` to `R^n`: for every `x ∈ M` there is a semialgebraic
open `W ∋ x` in `R^m` and an `𝒮^∞` map `F : W → R^n` (i.e. `F ∈ 𝒮^∞(W, R^n)`) agreeing with
`f` on `M ∩ W`. -/
def IsSInftyMap {m n : ℕ} (M : Set (Fin m → R)) (N : Set (Fin n → R))
    (f : (Fin m → R) → (Fin n → R)) : Prop :=
  IsSemialgebraicFunction M f ∧ Set.MapsTo f M N ∧
  ∀ x ∈ M, ∃ (W : Set (Fin m → R)) (F : (Fin m → R) → (Fin n → R)),
    IsOpen W ∧ IsSemialgebraicSet W ∧ x ∈ W ∧
      F ∈ SClassInfty W (Set.univ : Set (Fin n → R)) ∧ Set.EqOn F f (M ∩ W)

/-! ### Smooth points -/

/-- **BPR definition (smooth point).** A point `x` of a semialgebraic set `S ⊆ R^k` is a
*smooth point of dimension `ℓ`* if there is a semialgebraic, relatively open subset `U` of
`S` containing `x` which is an `𝒮^∞` submanifold of `R^k` of dimension `ℓ`. Here
*relatively open* means `U = S ∩ V` for some open `V ⊆ R^k` (the subspace topology — an
`ℓ`-submanifold with `ℓ < k` is never open in `R^k`). -/
def IsSmoothPoint (ℓ : ℕ) (S : Set (Fin k → R)) (x : Fin k → R) : Prop :=
  ∃ U : Set (Fin k → R), (∃ V : Set (Fin k → R), IsOpen V ∧ U = S ∩ V) ∧
    IsSemialgebraicSet U ∧ x ∈ U ∧ IsSInftySubmanifold ℓ U

end Azurite.BPR

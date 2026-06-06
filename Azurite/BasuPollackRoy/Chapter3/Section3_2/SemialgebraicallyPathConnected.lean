import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_4

/-! # BPR §3.2 — semialgebraically path connected sets

Over a real closed field `R`, a semialgebraic set `S ⊆ R^k` is **semialgebraically path connected**
if any two of its points are joined by a *semialgebraic path*: a continuous semialgebraic function
`ϕ : [0,1] → S` with `ϕ(0) = x` and `ϕ(1) = y`.

The line is modeled as `R^1 = Fin 1 → R`, the unit interval as `Set.Icc (constPt 0) (constPt 1)`,
and a path is a total map `(Fin 1 → R) → (Fin k → R)` constrained on the interval (semialgebraic
graph, continuous there, and mapping the interval into `S`). -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The **unit interval** `[0,1]` as a subset of the line `R^1 = Fin 1 → R`. -/
def unitIntervalPt : Set (Fin 1 → R) := Set.Icc (constPt (0 : R)) (constPt (1 : R))

/-- A **semialgebraic path** in `S` from `x` to `y`: a continuous semialgebraic map `[0,1] → S` with
endpoints `ϕ(0) = x` and `ϕ(1) = y`. -/
structure IsSemialgebraicPath (S : Set (Fin k → R)) (x y : Fin k → R)
    (ϕ : (Fin 1 → R) → (Fin k → R)) : Prop where
  /-- `ϕ` is a semialgebraic function on `[0,1]`. -/
  isSemialgebraicFunction : IsSemialgebraicFunction unitIntervalPt ϕ
  /-- `ϕ` is continuous on `[0,1]`. -/
  continuousOn : ContinuousOn ϕ unitIntervalPt
  /-- `ϕ` maps `[0,1]` into `S`. -/
  mapsTo : Set.MapsTo ϕ unitIntervalPt S
  /-- the path starts at `x`. -/
  source : ϕ (constPt 0) = x
  /-- the path ends at `y`. -/
  target : ϕ (constPt 1) = y

/-- **BPR definition (semialgebraically path connected set).** A semialgebraic set `S ⊆ R^k` is
*semialgebraically path connected* if every pair of its points is joined by a semialgebraic path
in `S`. -/
def IsSemialgebraicallyPathConnected (S : Set (Fin k → R)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ ϕ : (Fin 1 → R) → (Fin k → R), IsSemialgebraicPath S x y ϕ

end Azurite.BPR

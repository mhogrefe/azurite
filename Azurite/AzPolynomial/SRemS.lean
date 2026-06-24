import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Neg
import Azurite.AzPolynomial.QuoRem

/-!
# Two-argument signed remainder sequence on `AzPolynomial`

The two-argument signed remainder sequence `sRemS P Q` mirrors
`Azurite.BPR.SRemS` (BPR Definition 1.7) on `Polynomial K`:

* `sRemS P Q 0 = P`
* `sRemS P Q 1 = Q`
* `sRemS P Q (n+2) = -((sRemS P Q n).rem (sRemS P Q (n+1)))` when the
  `(n+1)`-th term is nonzero, otherwise `0`.

`sturmSequence P n = sRemS P (derivative P) n` for the Sturm sequence
specialisation.
-/

namespace Azurite.AzPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- Two-argument signed remainder sequence: matches the recursion of
    `Azurite.BPR.SRemS` after `toPoly`. -/
def sRemS (P Q : AzPolynomial K) : ℕ → AzPolynomial K
  | 0 => P
  | 1 => Q
  | n + 2 =>
      let prev := sRemS P Q (n + 1)
      if prev = 0 then 0
      else -((sRemS P Q n).rem prev)

@[simp] theorem sRemS_zero (P Q : AzPolynomial K) : sRemS P Q 0 = P := rfl

@[simp] theorem sRemS_one (P Q : AzPolynomial K) : sRemS P Q 1 = Q := rfl

theorem sRemS_succ_succ (P Q : AzPolynomial K) (n : ℕ) :
    sRemS P Q (n + 2) =
      (if sRemS P Q (n + 1) = 0 then 0
       else -((sRemS P Q n).rem (sRemS P Q (n + 1)))) := rfl

/-! ### Efficient single-pass list

The recursion `sRemS` recomputes from scratch (`sRemS P Q (n+2)` evaluates both
`sRemS P Q n` and `sRemS P Q (n+1)`, so it is exponential). For computing the list
of terms we walk the sequence once, carrying the previous two remainders and using
a single `.rem` per step. `sRemSList_eq` proves the fast list equals the spec
`(List.range n).map (sRemS P Q)`. -/

/-- One step of the signed remainder sequence: from terms `i-1` and `i`, produce
    term `i+1`. -/
def sRemSStep (s₀ s₁ : AzPolynomial K) : AzPolynomial K :=
  if s₁ = 0 then 0 else -(s₀.rem s₁)

/-- `sRemSBuild n a b = [a, b, step a b, …]` of length `n`: the consecutive
    remainders obtained by iterating `sRemSStep`, each computed once. -/
def sRemSBuild : ℕ → AzPolynomial K → AzPolynomial K → List (AzPolynomial K)
  | 0, _, _ => []
  | m + 1, a, b => a :: sRemSBuild m b (sRemSStep a b)

/-- The first `n` terms of `sRemS P Q` packaged as a list (BPR Algorithm 8.19
    output). Computed by a single forward pass (`sRemSBuild`); mirrors
    `Azurite.BPR.SRemSList`. -/
def sRemSList (P Q : AzPolynomial K) (n : ℕ) : List (AzPolynomial K) :=
  sRemSBuild n P Q

/-- One step matches the defining recursion of `sRemS`. -/
private theorem sRemSStep_eq (P Q : AzPolynomial K) (i : ℕ) :
    sRemSStep (sRemS P Q i) (sRemS P Q (i + 1)) = sRemS P Q (i + 2) := by
  rw [sRemSStep, sRemS_succ_succ]

/-- `sRemSBuild` started at terms `i, i+1` reproduces the spec terms. -/
private theorem sRemSBuild_eq (P Q : AzPolynomial K) (n : ℕ) : ∀ i,
    sRemSBuild n (sRemS P Q i) (sRemS P Q (i + 1)) = (List.range' i n).map (sRemS P Q) := by
  induction n with
  | zero => intro i; rfl
  | succ m ih =>
    intro i
    rw [sRemSBuild, sRemSStep_eq, show i + 2 = (i + 1) + 1 from rfl, ih (i + 1),
      List.range'_succ, List.map_cons]

/-- **The fast `sRemSList` equals the spec list** `(List.range n).map (sRemS P Q)`,
    so all spec-level facts transfer to the efficient list. -/
theorem sRemSList_eq (P Q : AzPolynomial K) (n : ℕ) :
    sRemSList P Q n = (List.range n).map (sRemS P Q) := by
  rw [sRemSList, List.range_eq_range']
  exact sRemSBuild_eq P Q n 0

end Azurite.AzPolynomial

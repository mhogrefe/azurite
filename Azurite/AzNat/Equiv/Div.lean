import Azurite.AzNat.Equiv.BodyStep

namespace Azurite.AzNat

/-- `bodyStep` matches what `schoolbookDivMod.go` computes for `j+1` before
    the recursive tail-call. Specifically, `go a b loA loB n (j+1) bn1 inv ...`
    equals `go (bodyStep a b loA loB n j q_init ...) b loA loB n j bn1 inv ...`
    where `q_init` is the trial digit that `go` would pick. -/
private theorem schoolbookDivMod.go_succ_eq_bodyStep
    (a b : Array UInt64) (loA loB n j : Nat) (bn1 inv : UInt64)
    (hA : loA + n + (j + 1) ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n) :
    schoolbookDivMod.go a b loA loB n (j + 1) bn1 inv hA hB h_n_pos
      = schoolbookDivMod.go
          (schoolbookDivMod.bodyStep a b loA loB n j
            (if bn1 ≤ a[loA + n + j]'(by omega) then (0 : UInt64) - 1
             else (UInt64.div2By1 (a[loA + n + j]'(by omega))
                     (a[loA + (n - 1) + j]'(by omega)) bn1 inv).1)
            (by omega) hB)
          b loA loB n j bn1 inv
          (by rw [schoolbookDivMod.bodyStep_size]; omega) hB h_n_pos := by
  conv_lhs => rw [schoolbookDivMod.go]
  rfl

/-- **BZ correctness invariant for `schoolbookDivMod.go`**.

    Pre-condition: the dividend slice `a[loA : loA + n + j]` satisfies the
    Brent-Zimmermann invariant `A < β^j · B`, where `B` is the divisor
    `b[loB : loB + n]` and `β = 2^64`.

    Post-condition: after running `j` body iterations of `go`, the resulting
    array `a'` has the remainder in `a'[loA : loA + n]` (with `R < B`) and
    the `j` quotient digits in `a'[loA + n : loA + n + j]`, satisfying
    `A = Q · B + R`.

    Currently only the `j = 0` base case is proved; the inductive step is
    stubbed pending the `q_init` bounds analysis (Möller-Granlund). -/
private theorem schoolbookDivMod.go_toNat
    (a b : Array UInt64) (loA loB n j : Nat) (bn1 inv : UInt64)
    (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n)
    (h_inv_BZ : toNatLimbsList ((a.toList.drop loA).take (n + j))
                  < 2 ^ (64 * j) * toNatLimbsList ((b.toList.drop loB).take n)) :
    let a' := schoolbookDivMod.go a b loA loB n j bn1 inv hA hB h_n_pos
    toNatLimbsList ((a'.toList.drop loA).take n)
        < toNatLimbsList ((b.toList.drop loB).take n)
      ∧ toNatLimbsList ((a.toList.drop loA).take (n + j))
          = toNatLimbsList ((a'.toList.drop (loA + n)).take j)
              * toNatLimbsList ((b.toList.drop loB).take n)
            + toNatLimbsList ((a'.toList.drop loA).take n) := by
  induction j generalizing a with
  | zero =>
    rw [schoolbookDivMod.go]
    refine ⟨?_, ?_⟩
    · simpa using h_inv_BZ
    · simp [List.take_zero, toNatLimbsList]
  | succ j ih =>
    -- Sketch of inductive step (deferred — requires q_init bounds + bodyStep BZ
    -- preservation, both of which depend on the Möller-Granlund analysis in
    -- `UInt64.Equiv.Div2By1`):
    --
    -- 1. Let `q_init` be the trial digit `go` computes (cf. `go_succ_eq_bodyStep`).
    --    By Möller-Granlund (`div2By1_rtilde_bounds`) plus the divisor-normalized
    --    hypothesis, the true quotient digit `q_true` satisfies
    --    `q_true ≤ q_init.toNat ≤ q_true + 2`, justifying the addback fuel `2`.
    --
    -- 2. Apply `go_succ_eq_bodyStep` to rewrite `go ... (j+1)` as
    --    `go (bodyStep a ...) ... j`.
    --
    -- 3. A `bodyStep_BZ` helper (not yet proved) shows that one body iteration
    --    preserves the BZ invariant for `j` and that the digit stored at
    --    position `loA + n + j` is the true quotient digit, giving the value
    --    identity `A_old = digit · β^j · B + A_new` on the relevant slice.
    --
    -- 4. Apply the IH `ih` to the post-bodyStep array, then combine its value
    --    identity with the bodyStep value identity to derive the conclusion.
    sorry

end Azurite.AzNat

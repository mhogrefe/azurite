/-
  **Algorithm 2.1.7 at limb level**: Garner's CRT reconstruction with
  preconditioning on `AzNat` — the port of the proven reference
  implementation `Azurite.CP.garner`
  (`CrandallPomerance/Chapter2/Algorithm_2_1_7.lean`).

  Step 1 (`garnerPrecomp`) computes the triples
  `(m_i, μ_i, c_i = μ_i^(−1) mod m_i)` once per modulus set, the
  inverse via the extended binary GCD (`AzNat.invMod`); step 2
  (`garnerLoop`, the book's reentry point) folds the Garner updates
  `n += ((n_i − n) c_i mod m_i) · μ_i` over the residues — all
  arithmetic limb-level, no divisions after the precomputation
  beyond the `mod m_i` reductions.

  The correctness bridge (`Azurite/AzNat/Equiv/Garner.lean`) proves
  `(garner ms ns).toNat` equal to the reference on positive pairwise
  coprime moduli, so the reference spec transfers: the result is the
  UNIQUE `n < ∏ ms` with `n ≡ n_i (mod m_i)`.
-/
import Azurite.AzNat.InvMod
import Azurite.AzNat.Div
import Azurite.AzNat.Sub
import Azurite.AzNat.Instances
import Azurite.AzNat.ParseBase
import Azurite.AzNat.ToStringBase

namespace Azurite

namespace AzNat

/-- The inner-loop update of step 2 (the book's
`u := ((nᵢ − n) cᵢ) mod mᵢ; n := n + u μᵢ`, underflow-free). -/
def garnerStep (mᵢ μ c nᵢ x : AzNat) : AzNat :=
  x + ((nᵢ % mᵢ + (mᵢ - x % mᵢ)) * c) % mᵢ * μ

/-- **Step 1 (precomputation)**: the triples `(m_i, μ_i, c_i)` for
`1 ≤ i < r`, driven by the running product `μ` (initially `m_0`). -/
def garnerPrecomp (μ : AzNat) : List AzNat → List (AzNat × AzNat × AzNat)
  | [] => []
  | mᵢ :: ms => (mᵢ, μ, invMod μ mᵢ) :: garnerPrecomp (μ * mᵢ) ms

/-- **Step 2 (the reentry point)**: fold the Garner updates over the
precomputed triples and the residues. -/
def garnerLoop : AzNat → List (AzNat × AzNat × AzNat) → List AzNat → AzNat
  | x, _, [] => x
  | x, [], _ => x
  | x, (mᵢ, μ, c) :: pre, nᵢ :: ns => garnerLoop (garnerStep mᵢ μ c nᵢ x) pre ns

/-- **Algorithm 2.1.7 (Garner) at limb level**: CRT reconstruction
with preconditioning — the unique `n ∈ [0, M−1]` with
`n ≡ nᵢ (mod mᵢ)`. -/
def garner (ms ns : List AzNat) : AzNat :=
  match ms, ns with
  | m₀ :: ms', n₀ :: ns' =>
    garnerLoop (n₀ % m₀) (garnerPrecomp m₀ ms') ns' % (m₀ :: ms').prod
  | _, _ => 0

section Tests

private def parse' (s : String) : AzNat := (AzNat.parse s).get!

-- the classical example: x ≡ 2 (3), 3 (5), 2 (7) ↦ 23, and a reentry
#guard (garner [ofNat 3, ofNat 5, ofNat 7]
  [ofNat 2, ofNat 3, ofNat 2]).toString == "23"
#guard (garner [ofNat 3, ofNat 5, ofNat 7]
  [ofNat 1, ofNat 2, ofNat 3]).toString == "52"
-- multi-limb moduli: 2^67 and 2^67 − 1 are coprime (consecutive)
#guard (garner [parse' "147573952589676412928", parse' "147573952589676412927"]
    [parse' "5", parse' "7"]) % parse' "147573952589676412928" == ofNat 5
#guard (garner [parse' "147573952589676412928", parse' "147573952589676412927"]
    [parse' "5", parse' "7"]) % parse' "147573952589676412927" == ofNat 7

end Tests

end AzNat

end Azurite

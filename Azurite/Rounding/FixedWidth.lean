import Azurite.Rounding.IntIcc

/-!
# `RoundingTarget` instances for `UInt64` and `Int64` (plus `±∞`)

Both are thin specialisations of `intIccBotTopSet` with the appropriate bounds:

* `uInt64BotTopSet` — `[0, 2^64 - 1]` together with `⊥, ⊤`.
* `int64BotTopSet`  — `[-2^63, 2^63 - 1]` together with `⊥, ⊤`.

The rounding-target structure (and the round-to-even tiebreaker) is inherited directly.
-/

namespace Azurite
namespace RoundingTarget

/-- `UInt64` values in `EReal` together with `⊥ = -∞` and `⊤ = +∞`. -/
def uInt64BotTopSet : Set EReal := intIccBotTopSet 0 (2 ^ 64 - 1)

noncomputable instance uInt64BotTopRoundingTarget : RoundingTarget uInt64BotTopSet :=
  inferInstanceAs (RoundingTarget (intIccBotTopSet 0 (2 ^ 64 - 1)))

/-- `Int64` values in `EReal` together with `⊥ = -∞` and `⊤ = +∞`. -/
def int64BotTopSet : Set EReal := intIccBotTopSet (-(2 ^ 63)) (2 ^ 63 - 1)

noncomputable instance int64BotTopRoundingTarget : RoundingTarget int64BotTopSet :=
  inferInstanceAs (RoundingTarget (intIccBotTopSet (-(2 ^ 63)) (2 ^ 63 - 1)))

end RoundingTarget
end Azurite

-- This module is the root of the `AzuriteTests` library: `#guard`-based
-- test suites, kept out of the main `Azurite` library target.
-- Built (and thereby run, since `#guard` checks at elaboration time)
-- via `lake test`.
import Azurite.AzNat.Tests.Conversion
import Azurite.AzNat.Tests.Div
import Azurite.AzNat.Tests.DivRound
import Azurite.AzNat.Tests.GetBits
import Azurite.AzNat.Tests.IsMultipleOfPow2
import Azurite.AzNat.Tests.ModPow2
import Azurite.AzNat.Tests.OfLimbDigits
import Azurite.AzNat.Tests.OfLimbDigitsPow2
import Azurite.AzNat.Tests.RootInt
import Azurite.AzNat.Tests.ShiftRightRound
import Azurite.AzNat.Tests.TrailingZeros

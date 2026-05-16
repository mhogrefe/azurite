import Azurite.AzNat.Conversion
import Azurite.AzNat.ParseBase

namespace Azurite

#guard (0 : UInt64).toAzNat.toNat == 0
#guard (5 : UInt64).toAzNat.toNat == 5
#guard (18446744073709551615 : UInt64).toAzNat.toNat == 18446744073709551615

#guard ((0 : Int64).toAzNatClampNeg).toNat == 0
#guard ((-5 : Int64).toAzNatClampNeg).toNat == 0
#guard ((-9223372036854775808 : Int64).toAzNatClampNeg).toNat == 0
#guard ((5 : Int64).toAzNatClampNeg).toNat == 5
#guard ((9223372036854775807 : Int64).toAzNatClampNeg).toNat == 9223372036854775807

#guard ((0 : Int32).toAzNatClampNeg).toNat == 0
#guard ((-5 : Int32).toAzNatClampNeg).toNat == 0
#guard ((5 : Int32).toAzNatClampNeg).toNat == 5

#guard ((-5 : ISize).toAzNatClampNeg).toNat == 0
#guard ((5 : ISize).toAzNatClampNeg).toNat == 5

#guard (AzNat.parse "123").get!.toUInt64 == 123
#guard (AzNat.parse "18446744073709551617").get!.toUInt64 == 1
#guard (AzNat.parse "18446744073709551616").get!.toInt64 == 0
#guard (AzNat.parse "9223372036854775808").get!.toInt64 == -9223372036854775808

#guard (AzNat.parse "4294967297").get!.toUInt32 == 1
#guard (AzNat.parse "4294967295").get!.toInt32 == -1
#guard (AzNat.parse "2147483648").get!.toInt32 == -2147483648

#guard (AzNat.parse "65537").get!.toUInt16 == 1
#guard (AzNat.parse "65535").get!.toInt16 == -1
#guard (AzNat.parse "32768").get!.toInt16 == -32768

#guard (AzNat.parse "257").get!.toUInt8 == 1
#guard (AzNat.parse "255").get!.toInt8 == -1
#guard (AzNat.parse "128").get!.toInt8 == -128

end Azurite

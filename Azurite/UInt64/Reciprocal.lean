import Azurite.UInt64.ShiftRightRound
import Azurite.UInt64.WideMul

namespace UInt64

/-!
Formalization of Algorithm 2 (RECIPROCAL_WORD) from
"Improved division by invariant integers" by Niels Möller and Torbjörn Granlund.
-/

/-- Lookup table for Algorithm 2 (RECIPROCAL_WORD): entry `i` is
`⌊(2^19 − 3 · 2^8) / (i + 256)⌋` for `i = 0, ..., 255`, i.e. the table indexed by
the 9-bit divisor `d_9` running from 256 to 511 inclusive. All values fit in 11
bits (max = 2045). Written as an explicit literal so that no arithmetic runs at
process initialization — the array is built directly from these constants. -/
def reciprocalTable : Array UInt16 := #[
  2045, 2037, 2029, 2021, 2013, 2005, 1998, 1990, 1983, 1975, 1968, 1960, 1953, 1946, 1938, 1931,
  1924, 1917, 1910, 1903, 1896, 1889, 1883, 1876, 1869, 1863, 1856, 1849, 1843, 1836, 1830, 1824,
  1817, 1811, 1805, 1799, 1792, 1786, 1780, 1774, 1768, 1762, 1756, 1750, 1745, 1739, 1733, 1727,
  1722, 1716, 1710, 1705, 1699, 1694, 1688, 1683, 1677, 1672, 1667, 1661, 1656, 1651, 1646, 1641,
  1636, 1630, 1625, 1620, 1615, 1610, 1605, 1600, 1596, 1591, 1586, 1581, 1576, 1572, 1567, 1562,
  1558, 1553, 1548, 1544, 1539, 1535, 1530, 1526, 1521, 1517, 1513, 1508, 1504, 1500, 1495, 1491,
  1487, 1483, 1478, 1474, 1470, 1466, 1462, 1458, 1454, 1450, 1446, 1442, 1438, 1434, 1430, 1426,
  1422, 1418, 1414, 1411, 1407, 1403, 1399, 1396, 1392, 1388, 1384, 1381, 1377, 1374, 1370, 1366,
  1363, 1359, 1356, 1352, 1349, 1345, 1342, 1338, 1335, 1332, 1328, 1325, 1322, 1318, 1315, 1312,
  1308, 1305, 1302, 1299, 1295, 1292, 1289, 1286, 1283, 1280, 1276, 1273, 1270, 1267, 1264, 1261,
  1258, 1255, 1252, 1249, 1246, 1243, 1240, 1237, 1234, 1231, 1228, 1226, 1223, 1220, 1217, 1214,
  1211, 1209, 1206, 1203, 1200, 1197, 1195, 1192, 1189, 1187, 1184, 1181, 1179, 1176, 1173, 1171,
  1168, 1165, 1163, 1160, 1158, 1155, 1153, 1150, 1148, 1145, 1143, 1140, 1138, 1135, 1133, 1130,
  1128, 1125, 1123, 1121, 1118, 1116, 1113, 1111, 1109, 1106, 1104, 1102, 1099, 1097, 1095, 1092,
  1090, 1088, 1086, 1083, 1081, 1079, 1077, 1074, 1072, 1070, 1068, 1066, 1064, 1061, 1059, 1057,
  1055, 1053, 1051, 1049, 1047, 1044, 1042, 1040, 1038, 1036, 1034, 1032, 1030, 1028, 1026, 1024]

/-- The literal table agrees with the spec `⌊(2^19 − 3 · 2^8) / d_9⌋`. -/
theorem reciprocalTable_eq :
    reciprocalTable =
      Array.ofFn (n := 256) fun i => ((2 ^ 19 - 3 * 2 ^ 8) / (i.val + 256) : Nat).toUInt16 := by
  native_decide

#guard reciprocalTable.size = 256
#guard reciprocalTable[0]! = 2045     -- d_9 = 256
#guard reciprocalTable[255]! = 1024   -- d_9 = 511

/-- `d_0 = d mod 2` — the least significant bit of `d`. -/
@[inline]
def computeD0 (d : UInt64) : UInt64 := d &&& 1

/-- `d_9` — the top 9 bits of `d`. When the top bit of `d` is set,
`d_9 ∈ [256, 511]`. -/
@[inline]
def computeD9 (d : UInt64) : UInt64 := d >>> 55

/-- `d_{40} = ⌊d / 2^{24}⌋ + 1`. -/
@[inline]
def computeD40 (d : UInt64) : UInt64 := (d >>> 24) + 1

/-- `d_{63} = ⌈d / 2⌉`. -/
@[inline]
def computeD63 (d : UInt64) : UInt64 := d.shiftRightRound .Ceiling 1

/-- `v_0 = reciprocalTable[d_9 − 256]` — initial 11-bit reciprocal estimate. -/
@[inline]
def computeV0 (d9 : UInt64) : UInt16 :=
  reciprocalTable[(d9 - 256).toNat]!

/-- `v_1 = 2^{11} v_0 − ⌊2^{−40} v_0^2 d_{40}⌋ − 1` — second reciprocal estimate.
Uses two 64-bit low multiplications: `v_0 · v_0` (≤ 2^22) and `(v_0^2) · d_{40}`
(≤ 2^62). The surrounding `2^{11} v_0` and `2^{−40}` terms are pure bit shifts. -/
@[inline]
def computeV1 (v0 : UInt16) (d40 : UInt64) : UInt64 :=
  let v0 := v0.toUInt64
  let sq := v0 * v0
  let prod := sq * d40
  (v0 <<< 11) - (prod >>> 40) - 1

/-- `v_2 = 2^{13} v_1 + ⌊2^{−47} v_1 (2^{60} − v_1 d_{40})⌋` — third reciprocal
estimate. Uses two 64-bit low multiplications: `v_1 · d_{40}` (≤ 2^60) and
`v_1 · (2^{60} − v_1 d_{40})` (fits in 64 bits because the residual `2^{60} − v_1
d_{40}` is bounded — see Möller–Granlund). -/
@[inline]
def computeV2 (v1 d40 : UInt64) : UInt64 :=
  let e := ((1 : UInt64) <<< 60) - v1 * d40
  let prod := v1 * e
  (v1 <<< 13) + (prod >>> 47)

/-- `e = 2^{96} − v_2 d_{63} + ⌊v_2 / 2⌋ d_0`, computed mod 2^64 in UInt64. A
single low multiplication suffices: `v_2 · d_{63}` (only its low 64 bits matter,
since `2^{96} ≡ 0 (mod 2^{64})`). The `⌊v_2/2⌋ · d_0` term is branch-free: since
`d_0 ∈ {0, 1}`, `(-d_0)` is either `0` or `2^{64}−1`, so AND-ing with it selects
`⌊v_2/2⌋` or `0`. -/
@[inline]
def computeE (v2 d63 d0 : UInt64) : UInt64 :=
  let mask : UInt64 := (0 : UInt64) - d0
  ((v2 >>> 1) &&& mask) - v2 * d63

/-- `v_3 = (2^{31} v_2 + ⌊v_2 e / 2^{65}⌋) mod 2^{64}` — fourth reciprocal
estimate. Uses a single *high* multiplication: with `v_2 · e = hi · 2^{64} + lo`,
we have `⌊v_2 e / 2^{65}⌋ = hi >>> 1`. (The leftover `(hi mod 2)·2^{64} + lo` is
always `< 2^{65}`, so it cannot bump the quotient.) -/
@[inline]
def computeV3 (v2 e : UInt64) : UInt64 :=
  let hi := (wideMul v2 e).1
  (v2 <<< 31) + (hi >>> 1)

/-- `v_4 = (v_3 − ⌊(v_3 + 2^{64} + 1) d / 2^{64}⌋) mod 2^{64}` — the final
reciprocal. Requires a full 128-bit multiplication: expand
`(v_3 + 2^{64} + 1) d = v_3 d + 2^{64} d + d`, so
`⌊(v_3 + 2^{64} + 1) d / 2^{64}⌋ = d + hi + carry`,
where `(hi, lo) = wideMul v_3 d` and `carry` is the overflow of `lo + d`. -/
@[inline]
def computeV4 (v3 d : UInt64) : UInt64 :=
  let (hi, lo) := wideMul v3 d
  let lo' := lo + d
  let carry : UInt64 := if lo' < d then 1 else 0
  v3 - d - hi - carry

/-- Algorithm 2 (RECIPROCAL_WORD) of Möller–Granlund: given a normalized 64-bit
divisor `d` (i.e. `2^{63} ≤ d < 2^{64}`), return `v = ⌊(2^{128} − 1) / d⌋ − 2^{64}`. -/
def reciprocal (d : UInt64) : UInt64 :=
  let d0  := computeD0 d
  let d9  := computeD9 d
  let d40 := computeD40 d
  let d63 := computeD63 d
  let v0  := computeV0 d9
  let v1  := computeV1 v0 d40
  let v2  := computeV2 v1 d40
  let e   := computeE v2 d63 d0
  let v3  := computeV3 v2 e
  computeV4 v3 d

end UInt64

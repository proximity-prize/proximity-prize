import ProximityPrize.SubmissionLower.BU
import ProximityPrize.SubmissionLower.A8
import ProximityPrize.SubmissionLower.AJ
set_option Elab.async false
set_option autoImplicit true
section
namespace FL




def Sg:ℕ→List ℕ
 | 2=>[257,351,441,507,563,612,661,716,764,806,821,871,921,970,1018,1066,1113,1160,1207,1252,1294,1339,1380,1424,1468]
 | 3=>[813,825,873,922,976,1024,1072,1124,1171,1213,1229,1278,1327,1375,1424,1472,1518,1561,1608,1651,1697,1742,1784,1828,1866]
 | 4=>[914,980,1029,1077,1130,1177,1224,1274,1320,1363,1383,1432,1480,1527,1572,1620,1665,1712,1759,1802,1848,1887,1927,1971,2016]
 | 5=>[1072,1135,1182,1229,1262,1308,1352,1400,1444,1487,1506,1552,1598,1644,1690,1735,1779,1821,1862,1903,1947,1991,2029,2072,2115]
 | 6=>[1225,1284,1332,1378,1406,1451,1496,1540,1584,1627,1652,1699,1746,1790,1832,1876,1918,1963,2009,2049,2094,2138,2173,2210,2253]
 | 7=>[1344,1401,1446,1491,1511,1556,1601,1648,1693,1739,1787,1826,1871,1918,1964,2009,2056,2101,2147,2184,2226,2271,2316,2361,2406]
 | 8=>[1491,1546,1592,1639,1656,1702,1748,1794,1835,1881,1928,1973,2019,2066,2112,2159,2194,2239,2285,2332,2378,2424,2470,2515,2560]
 | 9=>[1638,1694,1741,1790,1800,1842,1888,1935,1981,2028,2075,2122,2169,2205,2251,2297,2345,2392,2439,2486,2532,2579]
 | 10=>[1787,1841,1885,1933,1940,1987,2034,2081,2129,2176,2212,2259,2307,2355,2403,2451,2499,2546,2593]
 | 11=>[1929,1987,2035,2084,2086,2134,2182,2218,2266,2313,2362,2411,2459,2508,2556,2604]
 | 12=>[2078,2137,2187,2237,2222,2270,2318,2367,2416,2465,2514,2563,2612]
 | _=>[]
end FL
end
section
namespace jN
open bJ (Valid)
open cS (xQ)
open kX (bw)
open nF (eG)
open FL (Sg)
abbrev unit :ℕ:=0x5af3107a4000
abbrev units (t s :ℕ) :ℕ:=((Sg t)[s]?).getD 0
structure Range where
 lo:ℕ
 hi:ℕ
inductive ot where
 | indexX | indexY | degreeX | degreeY | indexSum
 deriving DecidableEq
structure JT where
 q:ℕ
 r :ℕ
 a :ℕ
 b:ℕ
def JT.TN (z :JT) :ot→ℕ
 | .indexX=>z.q
 | .indexY=>z.r
 | .degreeX=>z.a
 | .degreeY=>z.b
 | .indexSum=>z.q+z.r
abbrev Window:=ot→Range
def dY (w:Window) (z :JT) :Prop :=
 ∀ i,(w i).lo≤z.TN i∧z.TN i≤(w i).hi
abbrev first (t:ℕ) (z :JT) :=eG t z.q z.a
abbrev second (t:ℕ) (z :JT) :=eG t z.r z.b
def ay (x y :ℕ) (w:Window) :Prop :=
  ∀ z,dY w z→Valid (first x z)→Valid (second y z) →
    z.a+z.b≤116→z.q+z.r≤24 → ¬ xQ (first x z) →
    bw (first x z) (first x z)+bw ((first x z).plus (second y z)) (second y z) ≤
      unit*units (x+y) (z.q+z.r)
end jN
end

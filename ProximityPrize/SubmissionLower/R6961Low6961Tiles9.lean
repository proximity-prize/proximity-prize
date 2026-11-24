import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass9

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [1952386055, 1935609867, 1935610891, 1936660491, 1919884303, 1919885327], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1920279567, 1769416723, 1769417747, 1769549843, 1752773655, 1752774679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1752972311, 1736196123, 1736197147, 1736329243, 1719553055, 1853837343], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1853838367, 1837062179, 1837063203, 1837129763, 1820353575, 1820420135], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1820421159, 1803644971, 1803645995, 1803647019, 1786870831, 1786937391], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1786938415, 1770162227, 1770163251, 1770164275, 1753453623, 1753454647], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1753455671, 1736679483, 1686348859, 1669572667, 1535355967, 1535356991], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1501803583, 1485092931, 1485093955, 1401208899, 1384432711, 1099805606291], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099805607315, 1099721651623, 1099721652647, 1099721719207, 1099688095151, 1099688096175], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [38780676539, 8694216, 42247631, 1099553876431], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i3 : checks (tilesOf batches) 117 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 117 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 117 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 117 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 117 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 117 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1852774411, 1835998223, 1835999247, 1836393487, 1819748371, 1819749395], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1819881491, 1803105303, 1803106327, 1803303959, 1870413851, 1870414875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1870546971, 1853770783, 1853837343, 1853838367, 1837062179, 1837063203], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1837129763, 1753244711, 1753311271, 1753312295, 1736536107, 1736537131], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1736538155, 1719761967, 1719828527, 1719829551, 1703053363, 1703054387], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1703055411, 1753453623, 1652791351, 1652792375, 1719902267, 1703126075], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1585686587, 1568910399, 1568911423, 1485026367, 1468315715, 1468316739], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1384431683, 1367655495, 1099822383503, 1099822384527, 1099738428835, 1099738429859], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099738496419, 1099654539703, 1099654540727, 1099654541751, 4387543491, 38730340807], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [25828746699, 17238884811, 8693200, 8692183, 8693207], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i6 : checks (tilesOf batches) 117 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 117 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 117 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 117 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 117 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 117 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1920279567, 1903634451, 1903635475, 1903767571, 1886991383, 1886992407], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1887190039, 1870413851, 1870414875, 1870546971, 863915039, 863981599], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [863982623, 847206435, 847207459, 847274019, 830497831, 830564391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [830565415, 1803644971, 1803645995, 1803647019, 1786870831, 1786937391], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1786938415, 1770162227, 1770163251, 1770164275, 1753453623, 1753454647], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1686346807, 1669570619, 1686348859, 1686349883, 1518578751, 1518579775], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1468249151, 1451538499, 1451539523, 1434763331, 1149551687, 35341290735], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100040422747, 1099772051867, 1099755206047, 1099755207071, 1099755273631, 1099704872363], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099704873387, 4353990091, 42247631, 1099553876431], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i9 : checks (tilesOf batches) 117 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 117 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 117 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 117 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 117 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 117 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1903767571, 1886991383, 1886992407, 1887190039, 1870413851, 1870414875], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1870546971, 1853770783, 1853837343, 1853838367, 1837062179, 1837063203], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1837129763, 1820353575, 1820420135, 1820421159, 1803644971, 1803645995], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1803647019, 1786870831, 1786937391, 1786938415, 1770162227, 1770163251], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1770164275, 1703121975, 1703122999, 1703124023, 1736679483, 1736680507], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1686349883, 1602464831, 1602465855, 1468249151, 1451538499, 1401207875], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1216659523, 1199883335, 1099990090087, 1099990091111, 1099805539731, 1099755206047], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099755207071, 1099620986303, 1099620987327, 8632178127, 1099553876431], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i12 : checks (tilesOf batches) 117 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 117 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 117 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 117 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 117 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1719417879, 1702641691, 1702642715, 1702774811, 1685998623, 1686065183], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1686066207, 1669290019, 1669291043, 1669357603, 1652581415, 1652647975], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1652648999, 1635872811, 1635873835, 1635874859, 1619098671, 1619165231], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1753383983, 1736607795, 1736608819, 1736609843, 1719899191, 1753454647], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1736678455, 1719902267, 1719903291, 1686349883, 1652796479, 1585688639], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1535358015, 1434761283, 1434762307, 1434763331, 1384432711, 1099805607315], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099771984283, 1099771985307, 1099772051867, 1099688097199, 38814236083, 30224377267], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099637764539, 8695240, 42248655, 1099553877455, 17205331411, 4303658455], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8693207], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 117 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 117 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 117 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 117 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 117 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1350453275, 1333677087, 1333743647, 1333744671, 1316968483, 1316969507], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1317036067, 1300259879, 1300326439, 1300327463, 1283551275, 1283552299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1283553323, 1266777135, 1266843695, 1266844719, 1250068531, 1753386035], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1753387059, 1736676407, 1736677431, 1753455671, 1736679483, 1736680507], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1703127099, 1669573695, 1602465855, 1568912447, 1552201795, 1367653443], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1367654467, 1350878279, 39166560607, 26281734495, 1099839094155, 1099839160715], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099839161739, 1099654542775, 1099654609335, 1099620987327, 1099553877455, 25471443], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [12893588951], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 117 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 117 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 117 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 117 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1853838367, 1837062179, 1837063203, 1837129763, 1820353575, 1820420135], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1820421159, 1803644971, 1803645995, 1803647019, 1736539183, 1736605743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1736606767, 1719830579, 1719831603, 1719832627, 1753453623, 1753454647], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1753455671, 1736679483, 1703126075, 1703127099, 1703128127, 1619243071], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1585689663, 1568979011, 1367653443, 1451540547, 1434764359, 1099839094155], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099755274655, 1099755275679, 1099637765563, 1099637832123, 1099604210115, 21517073871], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4320437715, 8695255], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 117 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 117 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 117 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 117 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1132486691, 1115710503, 1115777063, 1115778087, 1099001899, 1099002923], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099003947, 1082227759, 1082294319, 1786938415, 1770162227, 1770163251], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1770164275, 1753453623, 1753454647, 1703124023, 1686347835, 1686348859], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1736681531, 1719905343, 1669574719, 1602466879, 1585756227, 1417985091], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1417986115, 1115997255, 35056148787, 1100073977171, 1099788762519, 1099788829079], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099620988351, 1099621054911, 8632180175, 1099553878479], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 117 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 117 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 117 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 117 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1770089511, 1753313323, 1753314347, 1753315371, 1736539183, 1736605743], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1736606767, 1719830579, 1719831603, 1484951603, 1468240951, 1468241975], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1468242999, 1451466811, 1719903291, 1719904315, 1703128127, 1669574719], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1652798527, 1552201795, 1401207875, 1401208899, 1384432711, 1099805539731], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099805606291, 1099805607315, 17456992663, 1099654609335, 1099570722251, 30106938831], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [17222110671, 42250703, 4303660503, 8695255], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 117 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 117 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 117 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1803647019, 1786870831, 1786937391, 1786938415, 1770162227, 1770163251], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1770164275, 1753453623, 1619236919, 1619237943, 1602461755, 1602462779], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1703127099, 1686350911, 1686351935, 1669575743, 1636087875, 1451539523], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1451540547, 1434764359, 1099755273631, 1099755274655, 1099755275679, 13011032507], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099570723275, 1099553945039, 4320438739, 25473491], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 117 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 117 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 117 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1786938415, 1770162227, 1770163251, 1770164275, 1753453623, 1753454647], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1753455671, 1719902267, 1719903291, 1719904315, 1703128127, 1703129151], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1703130175, 1669642307, 1585757251, 1568981059, 1451541575, 1099738498467], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8765880, 1099621055935, 1099621056959, 1099537168851, 8598626775, 4303662551], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8762839], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 117 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 117 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 117 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1770164275, 1753453623, 1753454647, 1753455671, 1736679483, 1736680507], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1736681531, 1719905343, 1719906367, 1719907391, 1686419523, 1568980035], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1568981059, 1518650439, 1099671389619, 1099637833147, 1099637834171, 8763860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 117 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 117 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 9 where
  orders := orders
  covers := by
    intro a ha box
    change 15+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    · exact Top1.exact a ha h1 (by omega) (by omega)
    · exact Top2.exact a ha h2 (by omega) (by omega)
    · exact Top3.exact a ha h3 (by omega) (by omega)
    · exact Top4.exact a ha h4 (by omega) (by omega)
    · exact Top5.exact a ha h5 (by omega) (by omega)
    · exact Top6.exact a ha h6 (by omega) (by omega)
    · exact Top7.exact a ha h7 (by omega) (by omega)
    · exact Top8.exact a ha h8 (by omega) (by omega)
    · exact Top9.exact a ha h9 (by omega) (by omega)
    · exact Top10.exact a ha h10 (by omega) (by omega)
    · exact Top11.exact a ha h11 (by omega) (by omega)
    · exact Top12.exact a ha h12 (by omega) (by omega)
end Low6961Allocation.Group9

import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass41

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group41
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23612296199, 23578747919, 14955265047, 10626747423, 10610563107, 6298821671], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2003856423, 1936748587, 1869640747, 1802532907, 1735425071, 1685094447], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1634763823, 1584433203, 1534102579, 1500549171, 1450218551, 1416665143], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1383111735, 1332781115, 1820697659, 1787144251, 1736813631, 1703260223], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1669706815, 1619376195, 1602600003, 1569046595, 1535493191, 1501939783], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1485163591, 1451610187, 1100090417531, 1100056862083, 1100023306635, 1099989751187], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099956195739, 411012515, 1099906273703, 1099889495467, 360679855, 1099872717231], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [327124407, 1099839161783, 1099822383547, 4571759043, 1099788828099, 1099772049863], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4521426383, 1099738494415, 1099704938967, 8766061019, 1099671383519, 1099637828071], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8698951147, 1099604272623, 12926808571], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i3 : checks (tilesOf batches) 128 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 128 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 128 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27890489355, 19250230295, 10643523611, 6331782175, 10610564131, 2003855399], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2003856423, 1953525803, 1886417963, 1819310123, 1752202287, 1685094447], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1634763823, 1567655987, 1534102579, 1483771955, 1433441335, 1399887927], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1366334519, 1316003899, 1820697659, 1787144251, 1720036415, 1686483007], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1652929599, 1602598979, 1569045571, 1552269379, 1501938759, 1468385351], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1451609159, 1401278539, 1100107194743, 1100073639295, 1100040083847, 1100006528399], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099972972951, 1099956605339, 411012515, 1099923049891, 1099906271655, 377457067], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099872716207, 4622091703, 1099839160759, 1099822382523, 4571759043, 1099788827075], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099755271627, 4504649171, 1099721716179, 1099688160731, 8749283807, 1099637828071], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8682173935, 1099604272623, 12910031359], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i6 : checks (tilesOf batches) 128 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 128 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 128 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27873715215, 14938488859, 10626748447, 10610564131, 6298822695, 1987080235], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1919972395, 1852864555, 1768979503, 1701871663, 1651541039, 1584433203], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1534102579, 1483771955, 1433441335, 1383110711, 1349557303, 1299226683], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1837474875, 1787144251, 1720036415, 1686483007, 1652929599, 1602598979], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1569045571, 1535492163, 1485161543, 1451608135, 1434831943, 1384501323], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100123971955, 1100090416507, 1100056861059, 1100006528399, 1099972972951, 1099973382551], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099939827103, 411012515, 1099923048867, 1099889493419, 360679855, 1099855937971], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4605314491, 1099822382523, 1099788827075, 4554981831, 1099755271627, 1099721716179], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8782839255, 1099688160731, 8715729383, 1099637828071, 1099587495411, 12943586807], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i9 : checks (tilesOf batches) 128 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 128 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 128 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [23561973779, 14938490907, 14905530403, 6298822695, 1987080235, 1970304043], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1886418987, 1802533935, 1735426095, 1668318255, 1601210419, 1550879795], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1500549171, 1433441335, 1399887927, 1349557303, 1299226683, 1854252091], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1803921467, 1736813631, 1686483007, 1652929599, 1602598979, 1552268355], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1518714947, 1468384327, 1451608135, 1418054727, 1367724107, 1100123971955], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100090416507, 1100040083847, 1100006528399, 1099990159763, 444567963, 1099956604315], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099923048867, 394235303, 1099906270631, 1099872715183, 4638869939, 1099839159735], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4588537279, 1099788827075, 1099755271627, 4521427407, 1099721716179, 8749284831], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099671383519, 1099621050859, 8682174959, 1099570718199, 12893255171], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i12 : checks (tilesOf batches) 128 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 128 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 128 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 128 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [23545199639, 10626749471, 10610565155, 6298823719, 1987081259, 1936750635], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1836088367, 1768980527, 1701872687, 1634764851, 1567657011, 1517326387], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1450218551, 1399887927, 1366334519, 1299226683, 1871029307, 1820698683], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1753590847, 1703260223, 1669706815, 1602598979, 1569045571, 1535492163], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1485161543, 1434830919, 1418054727, 1367724107, 1100123971955, 1100073639295], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100040083847, 1099989751187, 1099990159763, 1099956604315, 427790751, 1099939826079], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [377458091, 1099889493419, 1099855937971, 4605315515, 1099822382523, 1099788827075], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4554982855, 1099738494415, 8782840279, 1099704938967, 1099654606307, 8715730407], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099604273647, 12926810619, 1099553940987], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 128 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 128 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 128 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [19233458203, 14905531427, 6298823719, 1987081259, 1987082283, 1903197231], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1819312175, 1752204335, 1668319283, 1601211443, 1550880819, 1483772983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1433442359, 1383111735, 1316003899, 1904583739, 1854253115, 1787145279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1736814655, 1686484031, 1619376195, 1585822787, 1535492163, 1485161543], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1451608135, 1418054727, 1367724107, 1100107194743, 1100056862083, 1100006529423], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099990159763, 444568987, 1099956604315, 1099923048867, 394236327, 1099889493419], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4638870963, 1099855937971, 1099805605311, 4571761091, 1099772049863, 8799618515], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099721717203, 1099671384543, 8732508643, 1099621051883, 12943588855, 1099570719223], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8758784], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i18 : checks (tilesOf batches) 128 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 128 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 128 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 128 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 128 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [14921716767, 10593788967, 6282047531, 1987082283, 1953528879, 1869643823], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1802535983, 1718650931, 1651543091, 1584435251, 1517327415, 1466996791], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1416666167, 1349558331, 1921360955, 1887807547, 1820699711, 1753591871], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1703261247, 1652930627, 1602600003, 1552269379, 1501938759, 1451608135], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1418054727, 1367724107, 1100073640319, 1100023307659, 1099990159763, 461347223], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099956604315, 411014563, 1099923048867, 4655649199, 1099872716207, 1099839160759], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4588539327, 1099788828099, 8816396751, 1099738495439, 1099704939991, 8749286879], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099654607331, 12977144303, 1099587497459, 1099537164799, 12893257219], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i21 : checks (tilesOf batches) 128 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 128 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 128 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 128 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [14905532451, 6282047531, 1987082283, 1970306095, 1919975471, 1852867631], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1752205363, 1685097523, 1634766899, 1550881847, 1500551223, 1433443383], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1366335547, 1921360955, 1921361979, 1854254143, 1787146303, 1736815679], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1669707843, 1619377219, 1585823811, 1518715975, 1468385351, 1434831943], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1384501323, 1100056863107, 1100006530447, 1099973382551, 427792799, 1099939827103], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099906271655, 377460139, 1099855938995, 4605317563, 1099805606335, 4554984903], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099772050887, 1099721718227, 8782842327, 1099671385567, 8698955243, 1099621052907], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [12926812667, 1099553943035], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i24 : checks (tilesOf batches) 128 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 128 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 128 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 128 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10593791015, 6282049579, 1970307119, 1903199279, 1802537011, 1735429171], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1668321331, 1584436279, 1534105655, 1466997815, 1399889979, 1921360955], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1921361979, 1887808575, 1837477951, 1770370111, 1703262275, 1652931651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1602601027, 1535493191, 1501939783, 1451609159, 1401278539, 1100023308683], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [461348247, 1099956605339, 1099923049891, 394238375, 1099872717231, 4638873011], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099839161783, 4571763139, 1099788829123, 1099738496463, 8799620563, 1099688163803], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8732510691, 1099637831143, 12943590903, 1099570721271, 8760832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [6282049579, 1970307119, 1953530927, 1852868659, 1785760819, 1718652979], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1634767927, 1567660087, 1500552247, 1433444411, 6216328251, 1904585791], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1871032383, 1803924543, 1736816707, 1686486083, 1636155459, 1569047623], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1518716999, 1468386375, 1418055755, 478126483, 427793823, 1099939828127], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099906272679, 4655651247, 1099855940019, 4588541375, 1099805607359, 1099755274699], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8816398799, 1099704942039, 8749288927, 1099654609379, 12977146351, 1099604276719], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099537166847, 12893259267], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1970308143, 1903200307, 1819315251, 1752207411, 1668322359, 1601214519], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1550883895, 1466998843, 6216328251, 1904585791, 1904586815, 1837478975], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1770371139, 1703263299, 1652932675, 1585824839, 1535494215, 1485163591], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1434832971, 444572059, 1099923050915, 377462187, 1099889495467, 4622096823], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099839162807, 1099788830147, 4554986951, 1099738497487, 8782844375, 1099688164827], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8715734503, 1099621054955, 1099570722295, 12926814715], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1785761843, 1701876791, 1634768951, 1567661111, 1500553275, 6216328251], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1904585791, 1904586815, 1871033407, 1803925571, 1736817731, 1686487107], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1619379271, 1569048647, 1518718023, 1451610187, 411017635, 1099906273703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4655652271, 1099855941043, 4588542399, 1099805608383, 1099755275723, 8816399823], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099704943063, 8749289951, 1099654610403, 1099587500531, 1099537167871], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 128 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 41 where
  orders := orders
  covers := by
    intro a ha box
    change 13+a.b≤141 ∧ 7+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group41

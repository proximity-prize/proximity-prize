import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass22

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group22
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2315324421, 10889007113, 2282298381, 2181636111, 1829315599, 1577658385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1409887249, 1275670545, 1158231061, 1057568789, 990460949, 906575897], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [856245273, 805914649, 23692266525, 15068783653, 6462075945, 2150333485], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2150334509, 2116781101, 2032896049, 1982565425, 1932234801, 1865126965], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1831573557, 1781242933, 1730912313, 1697358905, 1663805497, 1613474877], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1579921469, 1546368061, 1512814657, 1479261249, 1462485057, 1428931653], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1395378245, 1378602053, 1345048649, 1328272457, 1311496265, 22886959325], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [27131593961, 27081261301, 27014151429, 31242008853, 31141344557, 31040680261], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [30906461541, 1100220455303, 1100203677067, 672082317, 1100186898831, 1100170120595], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100153145751, 1100119590303, 1100102812067, 574406053, 540850605, 524072369], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4785484217, 4751928769, 4732167621, 9013340617, 8979785169, 13241197017], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13207641569, 13157308909, 17418720757, 17368388097, 21613022733, 4379845145], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [21562690073, 21495580201], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6594041867, 2198413327, 1812538381, 1577658385, 1409887249, 1258893329], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1124676629, 1040791573, 956906517, 873021465, 805913625, 755583001], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [23692266525, 15068783653, 6462075945, 2150333485, 2133557293, 2066449453], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1982564401, 1932233777, 1881903153, 1814795317, 1764464693, 1730911285], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1680580665, 1630250041, 1596696633, 1546366013, 1512812605, 1496036413], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1445705793, 1428929601, 1395376193, 1361822789, 1328269381, 1311493189], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1277939785, 1261163593, 1244387401, 22937290961, 27181925597, 27114815725], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [27047705853, 26963818769, 31174898981, 31057457473, 30906461541, 1100287367543], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100270589307, 1100253811071, 1100237032835, 1100220254599, 672082317, 1100186699151], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100169920915, 1100136365467, 1100119587231, 574404005, 557625769, 4819037617], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4785482169, 4748944833, 9046894017, 8996561357, 8963005909, 13224417757], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13174085097, 17418719733, 17368387073, 21613021709, 4363067933, 21545911837], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [21478801965], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1846092815, 1594435601, 1409887249, 1275670545, 1124676629, 1040791573], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [940129301, 856244249, 789136409, 738805785, 23692266525, 10773816357], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6462074921, 2167109673, 2150333485, 2100002861, 2032895021, 1949009969], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1898679345, 1848348721, 1781240885, 1730910261, 1680579637, 1630249017], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1596695609, 1546364985, 1496034365, 1462480957, 1445704765, 1395374145], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1361820737, 1345044545, 1294713925, 1277937733, 1261161541, 1227608137], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1194054729, 1177278537, 22954068173, 27198702809, 27131592937, 27064483065], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26963818769, 31174898981, 31040680261, 30906461541, 1100354476391, 1100337698155], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100304142707, 1100287364471, 1100270586235, 1100253807999, 1100220252551, 1100203474315], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [655305105, 1100169918867, 1100136363419, 607957405, 574401957, 4835813805], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4785481145, 9046892993, 4715390409, 9013337545, 8963004885, 13207639521], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13157306861, 17401941497, 17351608837, 21579466261, 21512356389], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1275670545, 1141453845, 1040791573, 956906517, 856244249, 789136409], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [738805785, 23692266525, 10773816357, 6462074921, 2167109673, 2150333485], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2066448429, 1999340589, 1932232753, 1865124913, 1814794289, 1747686453], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1697355829, 1647025205, 1596694585, 1546363961, 1512810553, 1462479933], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1428926525, 1395373117, 1345042497, 1328266305, 1294712897, 1261159493], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1227606085, 1210829893, 1177276489, 1143723081, 1126946889, 22954068173], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [27198702809, 27131592937, 27047705853, 26963818769, 31158121769, 31040680261], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100404808027, 1100388029791, 1100354474343, 1100337696107, 1100320917871, 1100287362423], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100270584187, 1100237028739, 1100220250503, 1100186695055, 1100153139607, 607956381], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [574400933, 4835812781, 4785480121, 9046891969, 8996559309, 13241193945], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [13190861285, 17435495921, 17368386049, 17318053389, 21545910813], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [956906517, 873021465, 805913625, 738805785, 23692266525, 10773816357], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6462074921, 2167109673, 2133556269, 2066448429, 1999340589, 1915455537], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1848347697, 1798017073, 1730909237, 1680578613, 1630247989, 1563140153], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1529586745, 1479256121, 1428925501, 1395372093, 1361818685, 1311488065], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1294711873, 1261158465, 1210827845, 1194051653, 1160498245, 1126944841], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1110168649, 1093392457, 22954068173, 27181925597, 27114815725, 27047705853], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100438362451, 1100421584215, 1100404805979, 1100388027743, 1100354472295, 1100337694059], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100304138611, 1100270583163, 1100253804927, 1100220249479, 1100186694031, 641510805], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [607955357, 4852589993, 4819034545, 9063669181, 9013336521, 8963003861], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13207638497, 13157305837, 17385163261, 17318053389, 21545910813, 21478800941], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [755583001, 23692266525, 10773816357, 6462074921, 2167109673, 2150333485], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2066448429, 1999340589, 1915455537, 1848347697, 1781239857, 1714132021], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1663801397, 1613470773, 1546362937, 1512809529, 1462478905, 1412148285], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1378594877, 1345041469, 1294710849, 1261157441, 1227604033, 1194050629], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1160497221, 1143721029, 1093390409, 1076614217, 1043060809, 22937290961], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100488694087, 1100455138639, 1100438360403, 1100404804955, 1100388026719, 1100354471271], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100337693035, 1100304137587, 1100270582139, 1100237026691, 1100203471243, 658288017], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [624732569, 4869367205, 4835811757, 4785479097, 9030113733, 8979781073], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13224415709, 13157305837, 17385163261, 17318053389, 21545910813], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [19397301277, 10773817381, 6462075945, 2150333485, 2066448429, 1999340589], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1915455537, 1848347697, 1781239857, 1714132021, 1663801397, 1613470773], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1546362937, 1496032313, 1462478905, 1395371069, 1361817661, 1328264253], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1277933633, 1244380225, 1210826817, 1160496197, 1143720005, 1110166597], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1059835977, 1043059785, 1026283593, 1100488694083, 1100488693063, 1100471914827], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100438359379, 1100404803931, 1100388025695, 1100354470247, 1100320914799, 1100287359351], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100253803903, 1100220248455, 1100186693007, 624732569, 591177121, 4835811757], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4785479097, 9030113733, 8979781073, 13224415709, 13157305837, 17385163261], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17318053389, 21545910813, 4184620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [15085559841, 6462074921, 2167109673, 2150333485, 2083225645, 1999340589], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1915455537, 1848347697, 1781239857, 1714132021, 1663801397, 1596693557], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1546362937, 1496032313, 1445701689, 1395371069, 1345040445, 1311487037], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1261156417, 1227603009, 1194049601, 1143718981, 1110165573, 1093389381], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1043058761, 1026282569, 992729161, 1100505471291, 1100505470275, 1100488692039], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100455136591, 1100438358355, 1100404802907, 1100371247459, 1100337692011, 1100304136563], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100270581115, 1100237025667, 1100186693007, 641509781, 591177121, 4835811757], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4802256309, 9030113733, 8979781073, 13224415709, 13157305837, 17385163261], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17318053389, 21529133601, 1099532589611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10773818405, 2167109673, 2150333485, 2100002861, 2016117805, 1932232753], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1865124913, 1798017073, 1714132021, 1663801397, 1613470773, 1546362937], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1496032313, 1445701689, 1378593853, 1345040445, 1311487037, 1244379201], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1210825793, 1177272385, 1143718981, 1110165573, 1076612165, 1026281545], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1009505353, 975951945, 1100505471287, 1100505470271, 1100505469251, 1100471913803], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100438358355, 1100404802907, 1100388024671, 1100354469223, 1100320913775, 1100270581115], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100237025667, 1100203470219, 641509781, 591177121, 4835811757, 4785479097], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [9030113733, 8979781073, 13207638497, 13140528625, 17368386049, 17301276177], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [21512356389, 1099549366823, 4183596], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2167109673, 2150333485, 2116780077, 2032895021, 1949009969, 1865124913], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1814794289, 1730909237, 1663801397, 1613470773, 1546362937, 1496032313], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1445701689, 1395371069, 1345040445, 1311487037, 1244379201, 1210825793], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1177272385, 1126941765, 1093388357, 1059834949, 1026281545, 992728137], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [975951945, 1100488694071, 1100522247483, 1100505469251, 1100488691015, 1100455135567], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100421580119, 1100388024671, 1100354469223, 1100320913775, 1100270581115, 1100237025667], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [675065229, 641509781, 4886144417, 4835811757, 4785479097, 9030113733], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8963003861, 13190861285, 13140528625, 17351608837, 17284498965, 1099566144035], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [21495579177, 4183596], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [2049672237, 1949009969, 1881902129, 1814794289, 1730909237, 1680578613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1630247989, 1546362937, 1496032313, 1445701689, 1395371069, 1345040445], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1311487037, 1244379201, 1210825793, 1177272385, 1126941765, 1093388357], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1059834949, 1009504329, 992728137, 959174729, 1100488694067, 1100505470267], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100522246463, 1100488691015, 1100455135567, 1100421580119, 1100388024671, 1100354469223], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100320913775, 1100270581115, 1100237025667, 675065229, 641509781, 4886144417], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4835811757, 9063669181, 9013336521, 13257971157, 13190861285, 13123751413], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [17351608837, 17267721753, 1099582921247, 1099532588587], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1831571505, 1747686453, 1697355829, 1630247989, 1563140153, 1512809529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1462478905, 1395371069, 1345040445, 1311487037, 1261156417, 1210825793], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1177272385, 1126941765, 1093388357, 1059834949, 1009504329, 975950921], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [959174729, 1100488694067, 1100522247479, 1100522246463, 1100488691015, 1100455135567], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100421580119, 1100388024671, 1100354469223, 1100304136563, 1100270581115, 1100237025667], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [675065229, 624732569, 4869367205, 4819034545, 9063669181, 8996559309], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [13241193945, 13174084073, 1099582921247, 1099532588587], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1647025205, 1563140153, 1512809529, 1462478905, 1412148285, 1361817661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1311487037, 1261156417, 1210825793, 1177272385, 1126941765, 1093388357], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1059834949, 1009504329, 975950921, 959174729, 1100488694067, 1100522247479], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100522246463, 1100488691015, 1100455135567, 1100421580119, 1100388024671, 1100354469223], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100304136563, 1100270581115, 1100220248455, 658288017, 624732569, 4869367205], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4819034545, 9046891969, 1099582921247, 1099532588587], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 22 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 5+a.j≤59 ∧ 1+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
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
    · exact Top13.exact a ha h13 (by omega) (by omega)
end Low6960Allocation.Group22

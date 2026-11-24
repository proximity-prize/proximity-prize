import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass10

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27707313159, 1771055123, 1771056147, 1771188243, 1754412055, 1754413079], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1754545175, 1737768987, 1737770011, 1737902107, 1721125919, 1838567455], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1838634015, 1821857827, 1821858851, 1821925411, 1805149223, 1805150247], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1805151271, 1788375083, 1788376107, 1788442667, 1771666479, 1771667503], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1771668527, 1754892339, 1754893363, 1754959923, 1738183735, 1738184759], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1738185783, 1721409595, 1687856187, 1654302779, 1587194943, 1570418751], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1469756479, 1453045827, 1419492419, 1419493443, 1402717255, 1099773492631], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099773493655, 1099773494679, 1099739936159, 1099739937183, 10203572, 38765472187], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099622493627, 1099622494651, 10201540, 1099555383755, 1099538605519], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i3 : checks (tilesOf batches) 116 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 116 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 116 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 116 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 116 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 116 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1921587211, 1904811023, 1904812047, 1905206287, 1888495635, 1888496659], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1888628755, 1871852567, 1871853591, 1871985687, 1855209499, 1855210523], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1855342619, 1838566431, 1838567455, 1838634015, 1821857827, 1821858851], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1821925411, 1805149223, 1805150247, 1805151271, 1788375083, 1788376107], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1788442667, 1771666479, 1771667503, 1771668527, 1754892339, 1754893363], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1754959923, 1738183735, 1738184759, 1738185783, 1721409595, 1704633403], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1687857211, 1637526591, 1553641535, 1553642559, 1369159747, 1436269635], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1436270659, 1419494471, 1099823823243, 1099756715419, 1099756716443, 1099756717467], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099656049075, 1099656050099, 1099572161991, 1099538606543, 10200531], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i6 : checks (tilesOf batches) 116 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 116 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 116 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 116 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 116 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 116 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1905206287, 1888495635, 1888496659, 1888628755, 1871852567, 1871853591], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1871985687, 1855209499, 1855210523, 1855342619, 1838566431, 1838567455], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1838634015, 1821857827, 1821858851, 1821925411, 1805149223, 1805150247], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1805151271, 1788375083, 1788376107, 1788442667, 1771666479, 1771667503], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1771668527, 1754892339, 1754893363, 1654296627, 1637520439, 1637521463], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1637522487, 1721409595, 1721410619, 1721411643, 1654303807, 1637527615], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1603974207, 1553709123, 1553710147, 1402716227, 1385940039, 1099790270867], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099790271891, 1099639273911, 1099639274935, 12978983359, 1099538609599, 1099572163015], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099572164039, 43757003], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i9 : checks (tilesOf batches) 116 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 116 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 116 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 116 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 116 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 116 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1804742675, 1787966487, 1787967511, 1788099607, 1771323419, 1771324443], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1771456539, 1754680351, 1754681375, 1754747935, 1737971747, 1737972771], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1738039331, 1721263143, 1721264167, 1721265191, 1704489003, 1704490027], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1704556587, 1687780399, 1687781423, 1687782447, 1671006259, 1671007283], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1671073843, 1654297655, 1738184759, 1721408567, 1704632379, 1704633403], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1704634427, 1687858239, 1687859263, 1637528639, 1620817987, 1536932931], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1520156739, 1302053959, 1099874157951, 1099672830383, 1099656052147, 43026887107], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [34436963779, 21552136643, 1099572164039, 1099572165063, 8600133075, 4305168851], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [10203600], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i12 : checks (tilesOf batches) 116 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 116 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 116 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 116 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 116 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1687436311, 1670660123, 1670661147, 1670793243, 1654017055, 1654018079], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1654084639, 1637308451, 1637309475, 1637376035, 1620599847, 1805150247], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1805151271, 1788375083, 1788376107, 1788442667, 1771666479, 1771667503], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1771668527, 1754892339, 1754893363, 1520078899, 1503302711, 1503303735], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1503304759, 1486528571, 1671078971, 1671079995, 1654303807, 1704636479], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1687860287, 1654372419, 1520155715, 1520156739, 1503380551, 17408168351], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [43127553451, 1099672829359, 1099672830383, 1099672831407, 8633689547, 1099538610639], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [10204624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i15 : checks (tilesOf batches) 116 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 116 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 116 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 116 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 116 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1586907163, 1570130975, 1570131999, 1570198559, 1553422371, 1553423395], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1553489955, 1536713767, 1536714791, 1536715815, 1519939627, 1519940651], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1520007211, 1503231023, 1503232047, 1503233071, 1486456883, 1486457907], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1486524467, 1704629303, 1704630327, 1704631351, 1687855163, 1687856187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1704634427, 1687858239, 1671082047, 1671083071, 1654372419, 1654373443], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1620820035, 1486603335, 43211442583, 30326617495, 1099689608619, 1099572232647], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [17206842831, 4321948111, 26982863, 1099538611663, 8600136147], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i18 : checks (tilesOf batches) 116 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 116 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 116 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 116 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1217877023, 1201100835, 1201101859, 1201168419, 1184392231, 1184393255], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1184394279, 1167618091, 1167619115, 1167685675, 1150909487, 1771667503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1771668527, 1754892339, 1754893363, 1754959923, 1738183735, 1738184759], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1738185783, 1704632379, 1704633403, 1704634427, 1687858239, 1704636479], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1671083071, 1654372419, 1654373443, 1620820035, 1604043847, 43563767107], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [60604871, 1099572233671, 4321949135, 26983887, 12895101395], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 116 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 116 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 116 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 116 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1821925411, 1805149223, 1805150247, 1805151271, 1788375083, 1788376107], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1788442667, 1771666479, 1771667503, 1771668527, 1754892339, 1754893363], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1754959923, 1738183735, 1738184759, 1738185783, 1721409595, 1721410619], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1671079995, 1654303807, 1654304831, 1654305855, 1637595203, 1637596227], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1687928899, 1587266631, 77383107, 12928657867, 4338727371], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 116 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 116 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 116 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 116 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1066953767, 1050177579, 1050178603, 1050245163, 1033468975, 1033469999], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1033471023, 1016694835, 1016695859, 1016762419, 1637520439, 1637521463], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1637522487, 1620746299, 1620747323, 1620748347, 1704635455, 1704636479], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1570419775, 1553709123, 1553710147, 1687928899, 1671152711, 39386246439], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8717579703, 21568918975], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 116 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 116 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 116 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1788442667, 1771666479, 1771667503, 1771668527, 1754892339, 1754893363], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1754959923, 1738183735, 1738184759, 1738185783, 1721409595, 1721410619], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1721411643, 1704635455, 1704636479, 1704637503, 1687926851, 1687927875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [899399747, 882623559, 5076926747], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 116 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 116 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 116 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1771668527, 1754892339, 1754893363, 1754959923, 1738183735, 1738184759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1738185783, 1721409595, 1721410619, 1587193915, 1570417727, 1570418751], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1570419775, 1553709123, 1687927875, 1687928899, 1016841287, 647742779], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17307511223], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 116 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 116 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 116 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1268420659, 1251644471, 1251645495, 1251646519, 1234870331, 1234871355], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1234872379, 1218096191, 1687859263, 1687860287, 1671149635, 1671150659], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1671151683, 1184613447, 30544728419, 479970659, 12895105491, 4305240531], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 116 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 116 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 10 where
  orders := orders
  covers := by
    intro a ha box
    change 16+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6961Allocation.Group10

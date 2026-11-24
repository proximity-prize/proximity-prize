import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass15

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group15
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [1929448455, 1040257035, 1191318539, 1913264139, 1896946703, 1896947727], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1897538575, 1880762387, 1880763411, 1881354259, 1864578071, 1864579095], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1864907799, 1848197147, 1848198171, 1848395803, 1831619615, 1831620639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1831752735, 1814976547, 1814977571, 1815109667, 1798399015, 1798400039], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1798466599, 1781690411, 1781691435, 1781757995, 1764981807, 1765048367], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1765049391, 1748273203, 1748274227, 1748340787, 1731564599, 1731565623], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1731632183, 1714855995, 1714857019, 1714858043, 1698081855, 1698148415], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1698149439, 1681373251, 1681374275, 1681375299, 1664664647, 1664665671], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1664666695, 1647890507, 858329351, 707335467], by decide +kernel⟩
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
private theorem i43 : checks (tilesOf batches) 116 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 116 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1913264139, 1896946703, 1896947727, 1897538575, 1880762387, 1880763411], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1881354259, 1864578071, 1864579095, 1864907799, 1848197147, 1848198171], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1848395803, 1831619615, 1831620639, 1831752735, 1814976547, 1814977571], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1815109667, 1798399015, 1798400039, 1798466599, 1781690411, 1781691435], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1781757995, 1764981807, 1765048367, 1765049391, 1748273203, 1748274227], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1748340787, 1731564599, 1731565623, 1731632183, 1714855995, 1714857019], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1714858043, 1698081855, 1698148415, 1698149439, 1681373251, 1681374275], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1681375299, 1664664647, 1664665671, 1664666695, 1647890505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i46 : checks (tilesOf batches) 116 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1897538575, 1880762387, 1880763411, 1881354259, 1864578071, 1864579095], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1864907799, 1848197147, 1848198171, 1848395803, 1831619615, 1831620639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1831752735, 1814976547, 1814977571, 1815109667, 1798399015, 1798400039], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1798466599, 1781690411, 1781691435, 1781757995, 1764981807, 1765048367], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1765049391, 1748273203, 1748274227, 1748340787, 1731564599, 1731565623], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1731632183, 1714855995, 1714857019, 1714858043, 1698081855, 1698148415], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1698149439, 1681373251, 1681374275, 1681375299, 1664664647, 1664665669], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1664666693, 1647890505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i49 : checks (tilesOf batches) 116 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1881354259, 1864578071, 1864579095, 1864907799, 1848197147, 1848198171], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1848395803, 1831619615, 1831620639, 1831752735, 1814976547, 1814977571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1815109667, 1798399015, 1798400039, 1798466599, 1781690411, 1781691435], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1781757995, 1764981807, 1765048367, 1765049391, 1748273203, 1748274227], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1748340787, 1731564599, 1731565623, 1731632183, 1714855995, 1714857019], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1714858043, 1698081855, 1698148415, 1698149439, 1681373251, 1681374275], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1681375297, 1664664645, 1664665669, 1664666693, 1647890505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i12 : checks (tilesOf batches) 116 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 116 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 116 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 116 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 116 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 116 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1864907799, 1848197147, 1848198171, 1848395803, 1831619615, 1831620639], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1831752735, 1814976547, 1814977571, 1815109667, 1798399015, 1798400039], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1798466599, 1781690411, 1781691435, 1781757995, 1764981807, 1765048367], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1765049391, 1748273203, 1748274227, 1748340787, 1731564599, 1731565623], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1731632183, 1714855995, 1714857019, 1714858043, 1698081855, 1698148415], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1698149439, 1681373251, 1681374273, 1681375297, 1664664645, 1664665669], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1664666693, 1647890505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i15 : checks (tilesOf batches) 116 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 116 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 116 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 116 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 116 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1848395803, 1831619615, 1831620639, 1831752735, 1814976547, 1814977571], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1815109667, 1798399015, 1798400039, 1798466599, 1781690411, 1781691435], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1781757995, 1764981807, 1765048367, 1765049391, 1748273203, 1748274227], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1748340787, 1731564599, 1731565623, 1731632183, 1714855995, 1714857019], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1714858043, 1698081855, 1698148415, 1698149439, 1681373249, 1681374273], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1681375297, 1664664645, 1664665669, 1664666693, 1631113289, 3789264], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 116 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 116 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 116 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 116 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 116 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1831752735, 1814976547, 1814977571, 1815109667, 1798399015, 1798400039], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1798466599, 1781690411, 1781691435, 1781757995, 1764981807, 1765048367], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1765049391, 1748273203, 1748274227, 1748340787, 1731564599, 1731565623], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1731632183, 1714855995, 1714857019, 1714858043, 1698081855, 1698148415], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1698149439, 1681373249, 1681374273, 1681375297, 1664664645, 1664665669], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1647889477, 1597558857, 1099548971467, 3788240], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 116 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 116 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 116 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 116 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1815109667, 1798399015, 1798400039, 1798466599, 1781690411, 1781691435], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1781757995, 1764981807, 1765048367, 1765049391, 1748273203, 1748274227], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1748340787, 1731564599, 1731565623, 1731632183, 1714855995, 1714857019], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1714858043, 1698081855, 1698148415, 1698149439, 1681373249, 1681374273], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1681375297, 1664664645, 1664665669, 1631112261, 1580781641, 1099565748679], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532193231], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 116 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 116 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 116 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 116 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1798466599, 1781690411, 1781691435, 1781757995, 1764981807, 1765048367], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765049391, 1748273203, 1748274227, 1748340787, 1731564599, 1731565623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1731632183, 1714855995, 1714857019, 1714858043, 1698081855, 1698148415], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1698149437, 1681373249, 1681374273, 1681375297, 1664664645, 1664665669], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1631112261, 1564004425, 1099582525891, 1099532193231], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 116 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 116 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 116 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 116 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1781757995, 1764981807, 1765048367, 1765049391, 1748273203, 1748274227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1748340787, 1731564599, 1731565623, 1731632183, 1714855995, 1714857019], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1714858043, 1698081855, 1698148415, 1698149437, 1681373249, 1681374273], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1681375297, 1664664645, 1664665669, 1614335045, 1564004425, 1099582525891], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099548970443], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 116 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 116 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 116 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1765049391, 1748273203, 1748274227, 1748340787, 1731564599, 1731565623], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1731632183, 1714855995, 1714857019, 1714858043, 1698081855, 1698148415], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1698149437, 1681373249, 1681374273, 1681375297, 1664664645, 1647888453], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1614335045, 1547227209, 1099599303103, 1099548970443, 3787216], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 116 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 116 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 116 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1748340787, 1731564599, 1731565623, 1731632183, 1714855995, 1714857019], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1714858043, 1698081855, 1698148415, 1698149437, 1681373249, 1681374273], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1681375297, 1664664645, 1647888453, 1614335045, 1547227209, 1099599303103], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099548970443, 3787216], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 116 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 116 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 116 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1731632183, 1714855995, 1714857019, 1714858043, 1698081855, 1698148415], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1698149439, 1681373249, 1681374273, 1681375297, 1664664645, 1647888453], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1614335045, 1547227209, 1099599303103, 1099548970443, 3787216], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 116 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 116 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤116) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 15 where
  orders := orders
  covers := by
    intro a ha box
    change 16+a.b≤132 ∧ 3+a.j≤55 ∧ 1+a.t≤14 at box
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
end Low6961Allocation.Group15

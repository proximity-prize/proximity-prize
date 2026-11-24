import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass24

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group24
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [15033371653, 10704854031, 2098145297, 2081369105, 1896820753, 1712272405], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1578055701, 1460616213, 1359953945, 45017482265, 36360450091, 19130258485], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [10523551801, 6211810365, 1900067905, 1900068929, 1849738309, 1816184901], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1799408709, 1749078089, 1715524681, 1698748489, 35051028833, 34967141749], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34849700241, 34715481521, 34547708377, 1099666872803, 1099650094567, 1099616539119], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099582983671, 1099566205435, 1099532649987, 38658125319], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 129 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 129 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 129 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10721630217, 6409888781, 2081369105, 1880043537, 1695495189, 1561278485], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1443838997, 1326399513, 45017482265, 32065482793, 19147034673, 10523550777], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6211809341, 1900066881, 1883290689, 1832960065, 1799406661, 1765853253], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1732299845, 1681969225, 1665193033, 1631639625, 30789615961, 34983918961], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34866477453, 34732258733, 1099733981651, 34564485589, 1099700426203, 1099683647967], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099650092519, 1099616537071, 1099582981623, 1099566203387, 34363158021, 4242948], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 129 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 129 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 129 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [6409888781, 2098146321, 1896820753, 1712272405, 1561278485, 1443838997], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1326399513, 45017482265, 32065482793, 19147034673, 6228583481, 6211808317], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1916843069, 1866512449, 1832959041, 1799405633, 1749075013, 1715521605], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1681968197, 1631637577, 1614861385, 1581307977, 30789615961, 34983918961], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34866477453, 34715481521, 1099784313287, 1099750757839, 1099733979603, 34547708377], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099700424155, 1099666868707, 1099633313259, 1099599757811, 1099566202363, 1099532646915], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 129 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 129 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 129 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1930375185, 1729049621, 1578055701, 1460616213, 1326399513, 45017482265], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [27770515497, 19147033649, 10523549753, 1916841021, 1916842045, 1883288637], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1832958017, 1799404609, 1749073985, 1698743365, 1665189957, 1648413765], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1598083145, 1564529737, 1530976329, 30789615961, 34967141749, 34849700241], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34698704309, 1099834644923, 1099801089475, 1099767534027, 1099733978579, 1099717200343], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099683644895, 34514153953, 1099650089447, 1099599756787, 1099566201339, 1099532645891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1477393429, 1343176729, 45017482265, 27770515497, 19147033649, 6228582457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1933617209, 1916841021, 1916842045, 1866511421, 1799403585, 1765850177], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1732296769, 1681966149, 1648412741, 1614859333, 1564528713, 1530975305], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1497421897, 30772838749, 34950364537, 1099868199347, 1099834643899, 1099801088451], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099767533003, 1099733977555, 1099700422107, 1099666866659, 1099633311211, 1099599755763], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099549423103], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [45017483289, 27770516521, 14852067377, 6228582457, 1933617209, 1916841021], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1900064829, 1849734205, 1782626369, 1749072961, 1698742337, 1648411717], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1614858309, 1581304901, 1530974281, 1497420873, 1480644681, 1099884976559], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099868198323, 1099834642875, 1099801087427, 1099767531979, 1099733976531, 1099700421083], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099650088423, 1099616532975, 1099566200315, 4239876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [40705741853, 23458774061, 14835291189, 6228583481, 1916841021, 1883287613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1832956989, 1782626369, 1732295745, 1698742337, 1631634501, 1598081093], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1564527685, 1514197065, 1480643657, 1447090249, 1099918530983, 1099884975535], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851420087, 1099817864639, 1099784309191, 1099750753743, 1099700421083, 1099666865635], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616532975, 1099582977527, 1099532644867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 129 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [36394000417, 19163808813, 10540324917, 6228583481, 1916841021, 1883287613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1832956989, 1765849153, 1715518529, 1681965121, 1631634501, 1581303877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1547750469, 1497419849, 1463866441, 1430313033, 1099935308195, 1099901752747], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099868197299, 1099834641851, 1099801086403, 1099750753743, 1099717198295, 1099683642847], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099633310187, 1099582977527, 1099532644867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [32082258981, 19147033649, 6228582457, 1933617209, 1916841021, 1883287613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1832956989, 1765849153, 1715518529, 1681965121, 1614857285, 1581303877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1547750469, 1480642633, 1447089225, 1413535817, 1099952085407, 1099918529959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884974511, 1099834641851, 1099801086403, 1099767530955, 1099717198295, 1099683642847], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099633310187, 1099582977527, 1099532644867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [27770517545, 14835291189, 6228583481, 1916841021, 1883287613, 1832956989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765849153, 1715518529, 1681965121, 1614857285, 1581303877, 1530973253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480642633, 1447089225, 1413535817, 1099952085407, 1099918529959, 1099884974511], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851419063, 1099801086403, 1099767530955, 1099717198295, 1099683642847, 1099633310187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099582977527, 1099532644867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [23458776109, 10540325941, 1933617209, 1916841021, 1900064829, 1849734205], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765849153, 1732295745, 1681965121, 1614857285, 1581303877, 1530973253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480642633, 1447089225, 1413535817, 1099952085407, 1099918529959, 1099884974511], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851419063, 1099801086403, 1099767530955, 1099717198295, 1099666865635, 1099633310187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099566200315, 4239876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14852067377, 6228582457, 1933617209, 1916841021, 1900064829, 1849734205], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1782626369, 1732295745, 1681965121, 1614857285, 1581303877, 1530973253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480642633, 1447089225, 1396758601, 1099968862619, 1099918529959, 1099884974511], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851419063, 1099801086403, 1099767530955, 1099717198295, 1099666865635, 1099616532975], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099566200315, 4239876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [10540325941, 6228584505, 1916842045, 1866511421, 1782626369, 1732295745], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1681965121, 1631634501, 1581303877, 1547750469, 1480642633, 1447089225], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1396758601, 1099968862619, 1099918529959, 1099884974511, 1099834641851, 1099801086403], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750753743, 1099717198295, 1099666865635, 1099616532975, 1099549423103], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤129) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 24 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤141 ∧ 5+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group24

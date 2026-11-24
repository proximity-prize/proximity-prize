import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass26

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group26
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23641328645, 23607780365, 14984297493, 6360812573, 6360814621, 27820252193], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [19196770347, 6278319153, 6261543991, 1966578743, 1899470907, 1865917499], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1832364091, 1765256253, 1731702845, 1698149437, 1664596035, 1631042627], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1597489217, 1563935815, 1530382405, 1513606213, 1480052811, 1446499401], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099935241639, 1099901686191, 1099884907955, 1099868129719, 1099834574271, 1099817796035], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [272612811, 4176336, 4517246423, 4483690975, 4450135525, 8694770163], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8661214715, 12922626563], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i3 : checks (tilesOf batches) 130 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 130 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 130 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27919521803, 19279262741, 10672556057, 2065847325, 27820251169, 19196769323], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6278318129, 1983352881, 1966576693, 1949800501, 1899469877, 1832362041], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1798808633, 1765255225, 1698147389, 1664593981, 1631040573, 1597487169], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1563933761, 1530380353, 1496826949, 1463273541, 1446497349, 1396166729], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1379390537, 1100002350487, 1099985572251, 1099952016803, 1099935238567, 1099901683119], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099884904883, 1099851349435, 1099817793987, 289387975, 239055309, 4517244375], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4466911715, 8728323563, 8694768115, 8644435453, 12889070091], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i6 : checks (tilesOf batches) 130 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 130 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 130 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23607780365, 14984297493, 6360812573, 2065847325, 27820251169, 14901802025], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6295094317, 1983351857, 1983352881, 1966576693, 1899468853, 1865915445], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1798807609, 1748476985, 1714923577, 1664592957, 1631039549, 1597486141], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1547155521, 1513602113, 1480048705, 1446495301, 1412941893, 1396165701], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1345835081, 1329058889, 1100052682123, 1100035903887, 1100002348439, 1099985570203], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099952014755, 1099935236519, 1099901681071, 1099868125623, 1099834570175, 289386951], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [239054285, 4517243351, 4483687903, 4433355241, 8677989879, 8644434429], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i9 : checks (tilesOf batches) 130 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 130 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 130 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [19296038929, 10672555033, 6360813597, 27820251169, 14901802025, 6295094317], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1983351857, 1983352881, 1933022261, 1882691637, 1832361013, 1765253177], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1731699769, 1681369145, 1631038525, 1597485117, 1547154493, 1496823873], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1480047681, 1446494273, 1396163653, 1362610245, 1345834053, 1312280649], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1278727241, 1100103013759, 1100069458311, 1100052680075, 1100035901839, 1100002346391], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099968790943, 1099935235495, 1099918457259, 1099884901811, 1099834569151, 289385927], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [255830477, 4500465115, 4466909665, 8711544303, 8661211643, 8610878981], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [14984297493, 6360812573, 2065847325, 27820251169, 14901802025, 6295094317], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1983351857, 1983352881, 1916245045, 1865914421, 1815583797, 1748475961], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1698145337, 1664591929, 1597484093, 1563930685, 1530377277, 1480046657], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1446493249, 1412939841, 1362609221, 1329055813, 1312279621, 1261949001], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1245172809, 1100136568183, 1100119789947, 1100086234499, 1100069456263, 1100035900815], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100002345367, 1099968789919, 1099935234471, 1099901679023, 1099868123575, 1099834568127], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [272607691, 239052241, 4483686879, 4433354217, 8677988855, 8627656193], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [10672556057, 6360814621, 23525284897, 14901802025, 6295094317, 1983351857], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1983352881, 1916245045, 1865914421, 1798806581, 1731698745, 1681368121], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1647814713, 1580706877, 1547153469, 1513600061, 1446492225, 1412938817], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1379385409, 1345832005, 1312278597, 1278725189, 1245171785, 1211618377], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100170122607, 1100136567159, 1100119788923, 1100086233475, 1100052678027, 1100035899791], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100002344343, 1099968788895, 1099918456235, 1099884900787, 1099851345339, 289384903], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [255829453, 4500464091, 4450131429, 8677988855, 8627656193], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [6360814621, 27820252193, 14901803049, 6278318129, 1983352881, 1916245045], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1865914421, 1798806581, 1731698745, 1681368121, 1631037497, 1580706877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1530376253, 1496822845, 1446492225, 1396161601, 1362608193, 1312277573], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1295501381, 1261947973, 1211617353, 1194841161, 1100186899819, 1100170121583], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100136566135, 1100103010687, 1100086232451, 1100052677003, 1100019121555, 1099968788895], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099935233447, 1099901677999, 1099851345339, 306162115, 255829453, 4500464091], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4450131429, 8677988855, 8627656193], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 130 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [23525285921, 14901803049, 6278318129, 1983352881, 1916245045, 1865914421], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1798806581, 1731698745, 1681368121, 1631037497, 1563929661, 1530376253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480045629, 1429715009, 1396161601, 1362608193, 1312277573, 1278724165], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1245170757, 1194840137, 1178063945, 1100203677031, 1100186898795, 1100153343347], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100119787899, 1100086232451, 1100052677003, 1100019121555, 1099985566107, 1099952010659], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099901677999, 1099868122551, 1099817789891, 255829453, 4500464091, 4450131429], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8677988855, 8627656193], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [19213544485, 10590060589, 1983351857, 1983352881, 1933022261, 1865914421], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1815583797, 1731698745, 1681368121, 1631037497, 1563929661, 1530376253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480045629, 1429715009, 1379384385, 1345830977, 1295500357, 1261946949], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1228393541, 1178062921, 1161286729, 1100220454243, 1100203676007, 1100170120559], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100136565111, 1100103009663, 1100069454215, 1100035898767, 1099985566107, 1099952010659], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099901677999, 1099868122551, 306162115, 255829453, 4500464091, 4433354217], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8677988855, 8610878981], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [14901803049, 6278318129, 1983352881, 1949799477, 1882691637, 1815583797], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1748475961, 1698145337, 1647814713, 1580706877, 1530376253, 1480045629], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1429715009, 1379384385, 1345830977, 1295500357, 1261946949, 1228393541], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1178062921, 1144509513, 1100237231455, 1100203676007, 1100170120559, 1100136565111], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100103009663, 1100069454215, 1100035898767, 1099985566107, 1099952010659, 1099901677999], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099851345339, 289384903, 239052241, 4483686879, 4433354217, 8661211643], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8594101769], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [10590061613, 1983352881, 1966576693, 1899468853, 1832361013, 1765253177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1698145337, 1647814713, 1580706877, 1530376253, 1496822845, 1429715009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1396161601, 1345830977, 1295500357, 1261946949, 1228393541, 1178062921], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1144509513, 1100237231455, 1100203676007, 1100170120559, 1100136565111, 1100103009663], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100069454215, 1100019121555, 1099985566107, 1099935233447, 1099901677999, 1099851345339], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [289384903, 239052241, 4466909667, 4416577005, 8644434431], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1983352881, 1966576693, 1916246069, 1849138229, 1765253177, 1714922553], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1664591929, 1597484093, 1547153469, 1496822845, 1429715009, 1396161601], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1345830977, 1295500357, 1261946949, 1228393541, 1178062921, 1144509513], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100237231455, 1100203676007, 1100170120559, 1100136565111, 1100103009663, 1100069454215], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100019121555, 1099985566107, 1099935233447, 1099884900787, 1099834568127, 272607689], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [222275029, 4466909665, 4399799793, 8627657217], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1865915445, 1782030393, 1731699769, 1664591929, 1597484093, 1547153469], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1496822845, 1446492225, 1396161601, 1362608193, 1295500357, 1261946949], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1228393541, 1178062921, 1144509513, 1100237231455, 1100203676007, 1100170120559], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100136565111, 1100103009663, 1100052677003, 1100019121555, 1099968788895, 1099935233447], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884900787, 1099834568127, 272607689, 205497817, 4450132453, 4383022581], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 26 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤141 ∧ 6+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group26

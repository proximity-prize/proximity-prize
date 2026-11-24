import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass32

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group32
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [19362876421, 15034359821, 6427652113, 2115909653, 2099133461, 1948139545], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1830700057, 1730037785, 1612598301, 1528713245, 1461605405, 19247552547], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [10640845863, 27805055019, 19164795959, 6263121979, 6246346815, 1934604355], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1901050947, 1867497539, 1817166919, 1783613511, 1766837319, 1716506699], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1699730507, 22082901375, 22015791503, 21931904417, 26126207419, 26025543123], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099701409251, 1099684631015, 25908101613, 1099651075567, 1099634297331, 1099600741883], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099567186435, 1099533630987, 30068850191], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i3 : checks (tilesOf batches) 131 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 131 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 131 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [15051134985, 10722617361, 2115908629, 2115909653, 2099133461, 1931362329], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1813922841, 1696483353, 1595821085, 1511936029, 1428050973, 19247552547], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [10640845863, 27805055019, 14869828663, 6263120955, 1951378495, 1951379519], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1917826111, 1867495491, 1833942083, 1800388675, 1750058055, 1716504647], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1682951239, 1649397835, 1615844427, 17821488501, 22032568715, 21948681631], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [26159761843, 26042320335, 1099785295311, 1099751739863, 1099734961627, 1099701406179], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [25924878827, 1099667850731, 1099634295283, 1099600739835, 1099567184387, 1099533628939], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [25773882893], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i6 : checks (tilesOf batches) 131 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 131 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 131 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [10739393549, 6427652113, 2115909653, 2115910677, 1948139545, 1813922841], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1713260569, 1579043869, 1495158813, 1411273757, 19247552547, 10640845863], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [23510087723, 14886604851, 6263119931, 1968154683, 1951378495, 1917825087], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1867494463, 1817163843, 1783610435, 1750057027, 1682949191, 1666172999], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1632619591, 1582288971, 1548735563, 17838265713, 22049345927, 21965458843], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21848017333, 1099852404159, 1099818848711, 26042320335, 1099785293263, 1099751737815], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099734959579, 1099684626919, 25908101615, 1099651071471, 1099617516023, 1099583960575], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099533627915], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i9 : checks (tilesOf batches) 131 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 131 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 131 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [6427652113, 2115909653, 2115910677, 1981693977, 1847477273, 1713260569], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1595821085, 1511936029, 1428050973, 19247552547, 10640845863, 23510087723], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [14886604851, 6263119931, 1968154683, 1917824063, 1867493439, 1833940031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1766832195, 1733278787, 1699725379, 1649394759, 1615841351, 1582287943], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1531957323, 1498403915, 17821488501, 22032568715, 21948681631, 1099902735795], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21848017333, 1099869180347, 1099835624899, 1099802069451, 1099768514003, 26008765911], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099734958555, 1099701403107, 1099667847659, 25874547191, 1099617514999, 1099583959551], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099533626891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i12 : checks (tilesOf batches) 131 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 131 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 131 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [2115910677, 2015248409, 1864254489, 1746815001, 1612598301, 1528713245], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1428050973, 19247552547, 10640845863, 23510087723, 10591637555, 6279896119], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1968153659, 1968154683, 1901046847, 1850716223, 1800385599, 1733277763], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1699724355, 1666170947, 1615840327, 1565509703, 1531956295, 1498402891], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1464849483, 17821488501, 22015791503, 21931904417, 1099936290219, 1099902734771], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099885956535, 21814462909, 1099852401087, 1099802068427, 1099768512979, 25991988699], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099734957531, 1099701402083, 1099651069423, 1099600736763, 25840992765, 1099550404103], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1763592217, 1646152733, 1545490461, 1444828189, 19247552547, 10640845863], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [23510087723, 10591637555, 6279896119, 1968153659, 1951377467, 1884269631], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1833939007, 1783608383, 1716500547, 1682947139, 1632616515, 1582285895], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1548732487, 1515179079, 1464848459, 1431295051, 17804711289, 21999014291], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099969844643, 21898349993, 1099936289195, 1099902733747, 1099869178299, 26092652995], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099835622851, 1099802067403, 1099751734743, 1099718179295, 1099667846635, 1099617513975], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099567181315, 5220876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1478382621, 19247552545, 10640845863, 23510087723, 10591637555, 6279896119], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1968153659, 1934600251, 1867492415, 1817161791, 1766831167, 1699723331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1666169923, 1615839299, 1565508679, 1515178055, 1481624647, 1431294027], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1397740619, 17771156865, 1100003399067, 1099969843619, 1099936288171, 1099902732723], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099852400063, 1099818844615, 1099768511955, 1099734956507, 1099684623847, 1099634291187], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099583958527, 1099533625867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 131 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [14952587297, 27805052971, 14886603827, 6279896119, 1968153659, 1934600251], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1867492415, 1817161791, 1766831167, 1699723331, 1649392707, 1599062083], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1548731463, 1498400839, 1464847431, 1414516811, 1380963403, 1100020176279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099986620831, 1099953065383, 1099919509935, 1099869177275, 1099835621827, 1099785289167], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099734956507, 1099684623847, 1099634291187, 1099583958527, 1099533625867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10640845861, 23510087723, 10591637555, 6279896119, 1968153659, 1951377467], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1867492415, 1817161791, 1766831167, 1699723331, 1649392707, 1599062083], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1531954247, 1498400839, 1448070215, 1397739595, 1364186187, 1100036953491], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100003398043, 1099969842595, 1099919509935, 1099885954487, 1099835621827, 1099785289167], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099734956507, 1099684623847, 1099634291187, 1099583958527, 5220876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [23510087723, 14886604851, 6263119931, 1951377467, 1884269631, 1817161791], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1766831167, 1699723331, 1649392707, 1599062083, 1531954247, 1498400839], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1448070215, 1397739595, 1364186187, 1100036953491, 1100003398043, 1099969842595], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099919509935, 1099885954487, 1099835621827, 1099785289167, 1099734956507, 1099684623847], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099634291187, 1099567181315, 5220876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19198346287, 10574862391, 1968153659, 1968154683, 1884269631, 1833939007], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1766831167, 1699723331, 1649392707, 1599062083, 1531954247, 1498400839], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1448070215, 1397739595, 1347408971, 1100053730703, 1100003398043, 1099969842595], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099919509935, 1099885954487, 1099835621827, 1099785289167, 1099734956507, 1099684623847], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099617513975, 1099567181315], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14886604851, 6263119931, 1968154683, 1901046847, 1833939007, 1783608383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1699723331, 1649392707, 1599062083, 1531954247, 1498400839, 1448070215], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1397739595, 1347408971, 1100053730703, 1100003398043, 1099969842595, 1099919509935], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099885954487, 1099835621827, 1099785289167, 1099734956507, 1099667846635, 1099617513975], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099550404103], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 32 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group32

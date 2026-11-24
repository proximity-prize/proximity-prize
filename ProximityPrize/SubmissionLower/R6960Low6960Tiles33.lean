import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass33

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group33
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [19329846277, 15001329677, 10689589265, 2082880533, 2066104345, 2032550939], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1898334233, 1780894749, 1697009693, 1613124637, 1529239585, 1462131745], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1395023905, 14902518823, 27771827243, 14853378099, 10524860475, 1918151743], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1918152767, 1901376575, 1851045955, 1817492547, 1783939139, 1733608519], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1700055111, 1683278919, 1632948299, 1616172107, 26395631987, 26328522115], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30556379539, 30489269667, 30405382583, 30321495499, 1099752068559, 1099735290323], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099701734875, 1099684956639, 34515798499, 1099651401191, 1099617845743, 1099584290295], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099550734847, 34381579779, 5551620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i51 : checks (tilesOf batches) 129 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19313072137, 10689588241, 6377846805, 2066104345, 2015773721, 1898334233], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764117533, 1680232477, 1596347421, 1495685153, 1428577313, 1361469473], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [10607551527, 27771826219, 14853377075, 6246669367, 6229894203, 1918151743], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1884598335, 1834267711, 1783937091, 1750383683, 1716830275, 1666499655], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1649723463, 1616170055, 1582616651, 1549063243, 26429186411, 26362076539], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [26294966667, 30506046879, 30422159795, 1099819177407, 30338272711, 1099785621959], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099768843723, 1099735288275, 1099718510039, 1099684954591, 34515798499, 1099651399143], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099617843695, 1099584288247, 34398356991, 1099533955587], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [15001330701, 6377845781, 2082880533, 2066104345, 2032550937, 1898334233], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1780894749, 1680232477, 1596347421, 1495685153, 1411800097, 1361469473], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [10607551527, 27771826219, 14853377075, 6246669367, 1934926907, 1934927931], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1884597311, 1834266687, 1800713279, 1750382659, 1700052035, 1666498627], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1616168007, 1599391815, 1565838407, 1515507787, 1498731595, 22134219115], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [26378853751, 26294966667, 26211079583, 30422159795, 1099869509043, 1099852730807], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099819175359, 1099785619911, 30321495499, 1099768841675, 1099735286227, 1099701730779], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [30220831203, 1099651398119, 1099617842671, 1099584287223, 34381579779, 1099533954563], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i49 : checks (tilesOf batches) 129 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [10689589265, 6377847829, 2066105369, 1931888665, 1797671965, 1697009693], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1596347421, 1495685153, 1428577313, 1344692257, 10607551527, 27771826219], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [14853377075, 6246669367, 1934926907, 1918150715, 1851042879, 1800712255], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1767158847, 1700051011, 1666497603, 1632944195, 1582613575, 1549060167], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1515506759, 1481953355, 1448399947, 22150996327, 26362076539, 26294966667], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [26211079583, 1099919840679, 1099886285231, 1099869506995, 30405382583, 1099835951547], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099802396099, 1099768840651, 30304718287, 1099735285203, 1099701729755, 1099651397095], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [30187276779, 1099617841647, 1099567508987, 5548548], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i52 : checks (tilesOf batches) 129 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [6377847829, 2066105369, 1965443097, 1831226397, 1713786909, 1613124637], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1512462369, 1428577313, 1361469473, 10607551527, 27771826219, 14853377075], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6246669367, 1934926907, 1901373499, 1834265663, 1783935039, 1733604415], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1683273795, 1649720387, 1599389763, 1549059143, 1515505735, 1481952327], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1448398923, 1414845515, 22134219115, 26362076539, 26278189455, 1099953395103], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [26194302371, 1099919839655, 1099903061419, 1099869505971, 30388605371, 1099835950523], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099802395075, 1099752062415, 30271163863, 1099718506967, 1099684951519, 1099634618859], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [30153722355, 1099584286199, 1099533953539], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1998997529, 1848003613, 1747341341, 1646679069, 1529239585, 1445354529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1378246689, 10607551527, 27771826219, 14853377075, 6246669367, 1934926907], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1884596283, 1817488447, 1767157823, 1716827199, 1666496579, 1616165955], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1582612547, 1532281927, 1498728519, 1465175111, 1414844491, 1381291083], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [22117441903, 26345299327, 26261412243, 1099986949527, 1099953394079, 1099919838631], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30455715243, 1099886283183, 1099852727735, 1099819172287, 30355050947, 1099785616839], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099735284179, 30254386651, 1099701728731, 1099651396071, 1099601063411, 34415135227], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099550730751], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1663456285, 1562794017, 1478908961, 1395023905, 10607551525, 27771826219], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [14853377075, 6246669367, 1934926907, 1884596283, 1817488447, 1767157823], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1716827199, 1649719363, 1616165955, 1565835331, 1515504711, 1481951303], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1448397895, 1398067275, 1364513867, 26395631987, 26311744903, 1100003726739], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [26227857819, 1099970171291, 1099936615843, 1099903060395, 30438938031, 1099869504947], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099835949499, 1099785616839, 1099752061391, 1099701728731, 1099651396071, 1099601063411], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099550730751], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 129 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1411801121, 10607551525, 27771826219, 14853377075, 6246669367, 1934926907], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1884596283, 1817488447, 1767157823, 1716827199, 1649719363, 1599388739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1565835331, 1498727495, 1465174087, 1431620679, 1381290059, 1347736651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [26378854775, 1100020503951, 1099986948503, 1099953393055, 1099919837607, 1099886282159], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099835949499, 1099802394051, 1099752061391, 1099701728731, 1099651396071, 1099601063411], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099550730751], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [27788602407, 14853376051, 6246668343, 1934925883, 1934926907, 1901373499], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1817488447, 1767157823, 1716827199, 1649719363, 1599388739, 1565835331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1498727495, 1465174087, 1414843463, 1364512843, 1330959435, 1100037281163], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100003725715, 1099970170267, 1099919837607, 1099886282159, 1099835949499, 1099802394051], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099752061391, 1099701728731, 1099651396071, 1099601063411, 1099533953539], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [23476860971, 10558410803, 6246669367, 1934926907, 1901373499, 1834265663], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1767157823, 1716827199, 1649719363, 1599388739, 1565835331, 1498727495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1465174087, 1414843463, 1364512843, 1330959435, 1100037281163, 1100003725715], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099970170267, 1099919837607, 1099886282159, 1099835949499, 1099802394051, 1099752061391], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099701728731, 1099651396071, 1099584286199, 1099533953539], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19165119535, 6246668343, 1934925883, 1934926907, 1918150715, 1834265663], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1783935039, 1733604415, 1666496579, 1616165955, 1565835331, 1498727495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1465174087, 1414843463, 1364512843, 1330959435, 1100037281163, 1100003725715], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099970170267, 1099919837607, 1099886282159, 1099835949499, 1099785616839, 1099735284179], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099684951519, 1099634618859, 1099584286199, 5548548], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14853378099, 6229893179, 1934927931, 1851042879, 1800712255, 1733604415], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1666496579, 1616165955, 1565835331, 1515504711, 1465174087, 1414843463], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1364512843, 1330959435, 1100037281163, 1100003725715, 1099970170267, 1099919837607], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099869504947, 1099835949499, 1099785616839, 1099735284179, 1099684951519, 1099617841647], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099567508987], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 33 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group33

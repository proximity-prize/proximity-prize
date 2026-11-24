import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass42

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group42
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23778167815, 32335537167, 23695279131, 15071796259, 6465088551, 2153346091], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2153347115, 19317554223, 10710847539, 6399106103, 2087363643, 2087364667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2037034047, 1986703423, 1953150015, 1902819395, 1869265987, 1902952515], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1852621895, 1819068487, 1785515079, 1099753639411, 1099720083963, 1099686395395], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099686528515, 1099652839947, 1099652973067, 1099619284499, 1099585729051, 1099535396391], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 138 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 138 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 138 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32352311307, 28007020567, 19383538719, 6465087527, 2153345067, 2153346091], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2136569899, 19317554223, 10710847539, 2104138807, 2087362619, 2053809211], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2003478587, 1936370751, 1886040127, 1852486719, 1802156099, 1751825475], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1785512003, 1735181383, 1701627975, 1668074567, 1099871079895, 1099837524447], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099803835879, 1099803968999, 1099770413551, 1099753503219, 1099719947771, 1099686392323], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099636059663, 1099585727003, 1099535394343, 5863976], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 138 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 138 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 138 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32335537167, 23695279131, 15071796259, 6465088551, 2153346091, 2103015467], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15022586927, 10710846515, 2104137783, 2104138807, 2037030971, 1986700347], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1936369723, 1869261887, 1818931263, 1768600639, 1718270019, 1667939395], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1701625923, 1634518087, 1600964679, 1567411271, 1099971743167, 1099938187719], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099904632271, 1099887721939, 1099854299611, 1099837389279, 1099803833831, 1099753501171], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099703168511, 1099652835851, 1099602503191, 1099551046179, 1099552170531], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 138 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 138 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 138 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [32318763027, 19383537695, 10760053799, 2153345067, 2153346091, 2103015467], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15022586927, 6415879219, 2104136759, 2104137783, 2070584375, 2003476539], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1936368699, 1886038075, 1802153023, 1751822399, 1701491775, 1651161155], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1600830531, 1634517059, 1567409223, 1533855815, 1500302407, 1100038852015], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100005296567, 1099971741119, 1099954830787, 1099921408459, 1099904498127, 1099870942679], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099820610019, 1099770277359, 1099703167487, 1099652834827, 1099585724955, 1099551046179], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099535392295], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i12 : checks (tilesOf batches) 138 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 138 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 138 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [28007021591, 15071795235, 6465087527, 2153345067, 2153346091, 2103015467], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15022586927, 6415879219, 2104136759, 2104137783, 2053807159, 1969922107], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1902814267, 1852483643, 1768598591, 1718267967, 1667937343, 1600829507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1550498883, 1567408195, 1517077575, 1466746951, 1433193543, 1100105960863], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100072405415, 1100022072755, 1100005162423, 1099988517307, 1099954829763, 1099904497103], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099854164443, 1099803831783, 1099736721911, 1099686389251, 1099619279379, 1099551046179], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099552169507], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i15 : checks (tilesOf batches) 138 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 138 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 138 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [23695280155, 10776829987, 6465088551, 2153346091, 2136569899, 15022586927], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6415879219, 2104136759, 2104137783, 2053807159, 1969922107, 1886037051], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1835706427, 1751821375, 1684713535, 1634382911, 1567275075, 1516944451], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1533853763, 1466745927, 1416415303, 1382861895, 1100156292499, 1100122737051], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100072404391, 1100038716847, 1100022071731, 1099988384187, 1099938051527, 1099887718867], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099820608995, 1099753499123, 1099703166463, 1099619279379, 1099552169507, 5863976], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [19383538719, 10760054823, 2153346091, 2153347115, 15022586927, 6415879219], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2104136759, 2104137783, 2053807159, 1969922107, 1886037051, 1818929211], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1735044159, 1684713535, 1617605695, 1550497859, 1500167235, 1500299331], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1433191495, 1399638087, 1349307463, 1100189846923, 1100139514263, 1100105958815], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100055494059, 1100055626155, 1100005161399, 1099954828739, 1099887718867, 1099837386207], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099770276335, 1099703166463, 1099619279379, 1099552169507], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [15071797283, 6448312363, 2153347115, 15022586927, 6415879219, 2104136759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2104137783, 2070584375, 1986699323, 1902814267, 1835706427, 1751821375], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1684713535, 1617605695, 1533720643, 1483390019, 1500299331, 1416414279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1366083655, 1315753031, 1100223401347, 1100173068687, 1100122736027, 1100072271271], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100055626155, 1100021938611, 1099954828739, 1099887718867, 1099820608995, 1099753499123], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099686389251, 1099602502167, 1099535392295], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10760055847, 2153347115, 19317554223, 6415880243, 2104137783, 2104138807], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2003476539, 1919591483, 1852483643, 1751821375, 1684713535, 1617605695], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1533720643, 1483390019, 1483522115, 1416414279, 1366083655, 1315753031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100223401347, 1100173068687, 1100122736027, 1100072271271, 1100072403367, 1100021938611], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099954828739, 1099887718867, 1099820608995, 1099736721911, 1099669612039, 1099585724955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2153347115, 19317554223, 6415880243, 2104137783, 2104138807, 2037030971], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1953145915, 1869260859, 1768598591, 1701490751, 1634382911, 1550497859], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1483390019, 1500299331, 1416414279, 1366083655, 1298975815, 1100240178559], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100173068687, 1100122736027, 1100072271271, 1100055626155, 1100005161399, 1099938051527], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099870941655, 1099803831783, 1099719944699, 1099636057615, 1099552170531], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [15022588975, 6399104055, 2104138807, 2053808187, 1969923131, 1886038075], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1802153023, 1718267967, 1651160127, 1567275075, 1500167235, 1500299331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1416414279, 1366083655, 1298975815, 1100240178559, 1100173068687, 1100122736027], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100055494059, 1100055626155, 1099988384187, 1099921274315, 1099854164443, 1099770277359], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099703167487, 1099619280403, 1099535393319], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [10710847539, 2104138807, 2087362619, 2003477563, 1919592507, 1818930239], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1735045183, 1667937343, 1584052291, 1516944451, 1517076547, 1433191495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1366083655, 1315753031, 1100223401347, 1100173068687, 1100105958815, 1100038716847], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100038848943, 1099971606975, 1099904497103, 1099837387231, 1099753500147, 1099669613063], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099585725979], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((42 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 42 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤141 ∧ 8+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group42

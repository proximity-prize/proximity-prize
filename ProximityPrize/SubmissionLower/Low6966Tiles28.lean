import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass28
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group28
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27736607751, 40707172371, 86996045855, 44365489211, 35372683559, 30943638823], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39198102823, 13159939471, 1100088659343, 13327635883, 13210265003, 13092828587], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099803444691, 1099803511251, 34600783327, 4419007967, 1099753111007, 1099753112031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25893762555, 13008933371, 4419003899, 4368674299, 43056706047, 1099618891263], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099618892287, 40152591, 40153615, 4301562391], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 133 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 133 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 133 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36344436747, 53122645015, 86929141803, 10173596743, 30943637795, 30708830499], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30541132067, 39214661011, 30591313299, 8915300759, 8814640535, 13226971583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8881742271, 8781082047, 1099870554563, 1099870621123, 1099820219855, 1099820220879], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099820221903, 38862264807, 1099719555559, 1099685998063, 1099685999087, 1099686000111], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17320609271, 4368671239, 73705991, 30088062483, 8613304851], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 133 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 133 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 133 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40639931407, 61461122079, 74044311603, 30675274027, 26262939947, 9150186795], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35137801567, 26480898399, 8881744291, 8764306851, 1100004770211, 1099937662387], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099937663411, 1099937729971, 13226970559, 8881741247, 1099820217807, 1099820218831], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099820219855, 43123746283, 1099702774251, 1099702775275, 1099702776299, 4368670215], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [73704967, 21531685387, 12941756939, 4318337555, 38661006871], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 133 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 133 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 133 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40707305491, 61394081827, 61176190007, 26296423731, 21900865843, 4804888883], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30893234515, 22236264787, 21984678227, 8797860251, 1100038323611, 1100038324635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100038325659, 1099954440623, 1099954507183, 8781081011, 8898449871, 8797855183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099820217807, 1099820218831, 1099736328675, 1099736329699, 1099736330723, 43056706047], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4385447427, 90482179, 17236720139, 8646856203], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 133 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 133 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 133 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44801145879, 74010617895, 31312818239, 26849929495, 26548077847, 26279649559], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8848194923, 1100239653227, 1100239654251, 8982405523, 8848190867, 1100071877011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099971214763, 1099971215787, 1099971216811, 38946291155, 26061465043, 13176636883], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8864962003, 1099803438547, 1099803439571, 1099803440595, 4385448435, 1099669219827], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56926731, 56927755, 4301559319, 4301561367], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44750948379, 69715719211, 22773282883, 26699003163, 26397085979, 26179054875], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100172544379, 1100172545403, 8915299711, 1100155763071, 1100155764095, 1100155765119], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100155766143, 9015890355, 8881741235, 4536445363, 38963071435, 21800120779], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099820216783, 1099820217807, 1099685997039, 1099685998063, 13008865787, 4402224635], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099635664379, 38661147159, 6594071, 6595095], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53005407263, 69615126579, 1449446471, 26548078859, 22051792139, 17656233227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35003651455, 22118889855, 1100155764095, 1100155765119, 1100155766143, 1100155767167], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8898520471, 1100055097751, 1100055098775, 1100055099799, 1100004773283, 8932004295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4637105607, 224699875, 1099736328675, 1099736329699], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57149513763, 56797403191, 22085343519, 21884088607, 1100558420255, 1100558421279], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30842904927, 22135669087, 8831414659, 1100138986883, 1100138987907, 1100138988931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8965626291, 4603553203, 1099937656243, 1099887325631, 1099887326655, 1099887327679], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17287053823, 8697189887, 107259391, 1099618888191, 40149519], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57065630759, 44013167675, 17673004347, 17471682875, 1100440980795, 30809419087], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17874259279, 17639448911, 1100138985859, 1100138986883, 1100138987907, 1100138988931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100138989955, 1099937658291, 4637106623, 4502890943, 1099887325631, 1099669219827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099669220851, 13025644023, 4435779063, 25860206083, 12975311363, 23373331], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [56998590507, 31212154943, 26548009283, 17823929667, 17605896515, 8898526547], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100340316499, 1100340317523, 1100021546399, 1100021547423, 1100021548447, 4603554219], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099971211691, 1099971212715, 1099971213739, 8831407583, 4519666143, 1099652442615], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099652443639, 21582019071, 12975378943, 8596525591, 6595095, 6596119], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61142631471, 14216904771, 22404105507, 17874263331, 17656230179, 1100138988931], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100138989955, 1100138990979, 4586779031, 1100055099799, 1100055100823, 1100055101847], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8848186827, 4486113739, 1099753107935, 1099753108959, 124037627, 1099635666427], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17270277635, 8680413699, 56927755], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [56830890035, 5694081095, 22236336419, 17756891427, 13327711523, 1100088655247], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088656271, 1100088657295, 1100055103895, 1100055104919, 4620331439, 1099954434479], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099954435503, 1099954436527, 13143085531, 4553220571, 107260415, 1099618889215], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52535991351, 22068567335, 17605899559, 1100524865831, 1100524866855, 4586780047], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088655247, 1100088656271, 1100088657295, 8982404535, 4603554231, 1099920880055], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099786663383, 1099786664407, 90483203, 1099602112003, 4301561367, 6596119], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 28 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group28

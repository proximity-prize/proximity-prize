import ProximityPrize.SubmissionLower.R6960Low6960RetainedCount
import ProximityPrize.SubmissionLower.R6960Low6960Mass12

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [15117323271, 32114613263, 82648644631, 69965679667, 39732788499, 35337430291], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35136243987, 30421921119, 1100305059167, 8896753079, 8829712823, 8745829815], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17503390159, 13141384655, 1099768186335, 1099768187359, 1099684297203, 1099684298227], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099684299251, 38793387515, 30186890751, 21580318207, 4400524803, 105559555], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8645090831, 4350192143, 38676088343, 17184687643], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 134 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 134 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 134 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27936757771, 44648051735, 86910459939, 27251029055, 31126348055, 35052290327], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34901435671, 13208495515, 8846488995, 8762605987, 1100019846563, 39112160687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30522432943, 17570496959, 13208491455, 1099835294159, 1099835295183, 1099835296207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099751405027, 1099751406051, 1099751407075, 4450788843, 4417301995, 72003083], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099583631883, 8645088783, 4350124559, 38692723219, 38447635, 17201397271], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 134 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 134 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 134 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32266003471, 57164121115, 82565299247, 1565117511, 30807653655, 30623243543], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17738349847, 35169518939, 26563012955, 13191716255, 8829644191, 8762603935], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100036621727, 1100036622751, 1099902406079, 13225199051, 8913524171, 1099852069323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099852070347, 1099852071371, 1099784957403, 1099784958427, 1099784959451, 4434010603], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099717781995, 55157263, 1099566786063, 25774549531, 4299789851, 4824603], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 134 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 134 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 134 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36427149331, 69797565469, 56929851445, 31109502243, 26613347619, 26361762083], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21831986495, 9014265151, 8812866967, 1100070173079, 1100070174103, 1100070175127], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100003067303, 1100003068327, 1100003069351, 9014186419, 8863194547, 4517898675], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099835290063, 1099835291087, 1099717781995, 1099717848555, 17369167341, 13057493487], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4383677943, 1099667449335, 38759903747, 55156239, 55157263, 8594754073], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4299789851], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 134 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 134 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 134 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40521055255, 86742688805, 22771513409, 26965599475, 26646905075, 30639955185], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100187614587, 1100187615611, 1100187616635, 1100187617659, 1100187618683, 9047743871], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8896751999, 1100170769791, 1100170836351, 13241975239, 8896745927, 1099851999691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099852000715, 1099852067275, 38927678935, 189373935, 1099701002735, 1099701003759], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25808102931, 4333343249, 38378001, 38659309083], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48742025241, 86709270569, 1414122565, 30908315887, 30656731373, 22016538861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100221167987, 1100221169011, 1100221170035, 1100221171059, 1100221172083, 13258824063], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8863197567, 1100170769791, 35001813379, 22117051779, 1100053400987, 13241976251], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8879969723, 1099885554115, 1099885555139, 1099885621699, 1099784888795, 1099784889819], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4400453123, 105487875, 12923274771], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61308294173, 65351946289, 22133903633, 26177284369, 9081373969, 31008838971], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22301603131, 17822158139, 8879974773, 1100204324215, 1100204390775, 1100204391799], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100204392823, 1100120507787, 1100120508811, 1100120509835, 4534673843, 1099902331327], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099902332351, 1099902398911, 8879967703, 4517894615, 1099701002735, 1099701003759], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17285281281, 8695417345, 55155213, 1099566784015], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [73975226401, 39749986361, 26915201291, 22385491211, 26328208649, 17453134145], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100422497603, 1100422498627, 1100422499651, 1100137214343, 1100137280903, 1100137281927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100137282951, 1100137283975, 9030964627, 8846418321, 1100086881683, 1099818443219], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099818444243, 1099818445267, 13107756517, 8812858855, 122264061, 1099633892863], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65469246501, 35471797309, 22519639331, 22217786659, 21966200097, 13158167881], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100388943179, 1100388944203, 1100388945227, 1100103726479, 1100103727503, 1100103728527], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100103729551, 8863194521, 1100053326235, 1100053327259, 1100053328283, 13141312983], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4585002455, 256482783, 1099768111583, 1099768112607, 12906497559], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69663619113, 18426215489, 26613348623, 22117127437, 21915872525, 1100237948271], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100237949295, 1100237950319, 8812866937, 1100187613563, 1100187614587, 1100187615611], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8930301355, 4568228265, 1099986217387, 1099952663987, 1099952730547, 1099952731571], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17453054427, 8863190491, 1099701002735, 1099701003759, 122264061, 122265087], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69613356077, 5625202757, 26529531141, 26277945605, 17604132101, 1100237946223], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100237947247, 1100237948271, 8930304385, 8796089729, 1100154059139, 1100137286023], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100137287047, 1099935886775, 1099935953335, 1099935954359, 13258753471, 8863192511], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099801666007, 1099801667031, 1099801668055, 4400453123, 105487875, 12889720347], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65301614641, 26412093701, 26177285381, 1100674156807, 1100674157831, 8896753001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100254722411, 1100254723435, 1100254724459, 1100254725483, 9064518051, 8863194529], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100019771811, 1099935886775, 1099935953335, 1099935954359, 222928357, 1099734557159], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099734558183, 4316566037, 21600789], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 12 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤136 ∧ 6+a.j≤57 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group12

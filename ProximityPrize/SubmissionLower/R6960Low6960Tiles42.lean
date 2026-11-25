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
  ⟨unpack [28073069575, 45002729491, 87080457247, 40221976635, 39617779003, 35155180859], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34953929019, 8865433011, 13244211659, 13143617995, 8798323147, 1099736796663], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25978109435, 13093214715, 43140917759, 1099703239167, 1099703240191, 1099703241215], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4436242955, 4369136139, 57391647, 1099569020447, 34400130595, 25810336291], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8630544931], by decide +kernel⟩
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
  ⟨unpack [36647213067, 49130257431, 86963153959, 14552907843, 31111867687, 35037809959], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30625476903, 13143617967, 17555951051, 8949244363, 8865426891, 1099887788499], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099887789523, 1099887790547, 1099887791571, 38997016027, 30407222747, 1099770345967], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099770346991, 4369133071, 1099636127247, 17220404771, 8630542883, 40611363], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [40612387, 8613698087], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
  ⟨unpack [40892245007, 53173701663, 82567594031, 30893768983, 30658961687, 13563052311], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34920156583, 26313585063, 9033130407, 8932535719, 8798321063, 1099988452795], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099988453819, 1099988454843, 1099854232027, 1099854233051, 1099854234075, 13210652127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8848580063, 1099720011259, 1099720012283, 1099720013307, 107719187, 4352286239], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4335576607, 42973144615, 21481746987, 12891884075, 7054891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
  ⟨unpack [40909221907, 53073106979, 69682695219, 26548538651, 26280110363, 9200977179], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34953779603, 22035398035, 8982866327, 8848651671, 1100139446679, 1100038784431], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100038785455, 1100038786479, 8949241303, 4587168215, 1099871008215, 1099871009239], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099871010263, 1099736787447, 1099736788471, 1099736789495, 17253957147, 8664027675], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4335575583, 30105229859, 21515368995, 7053867, 7054891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
  ⟨unpack [44986285079, 52938958887, 52603558967, 22018694455, 17606358327, 1100542101815], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100542102839, 26531686775, 17891493239, 13428758903, 1100105889183, 1100105890207], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100105891231, 1100105892255, 1100105893279, 4604012987, 1099988447675, 4503280123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4453016059, 38846021119, 25961260543, 1099669678599, 1099669679623, 12925437475], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4335506979, 40608291, 40609315], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
  ⟨unpack [40792049691, 52838297643, 44013626427, 17673397563, 13294614843, 1100525324603], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100525325627, 26565243235, 17841163619, 13378429283, 1100105890207, 1100105891231], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100105892255, 1100105893279, 1100022002099, 1100022003123, 4536836571, 1099854227931], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099854228955, 13026102787, 4436172291, 90940951, 38728649243, 21515301411], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12925438499, 4318730791, 23831079], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
  ⟨unpack [40657900575, 48526621743, 35457248319, 13344943431, 8966094151, 1100474992967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100474993991, 22219947363, 13546198371, 13311321443, 1100089114019, 1100089115043], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100089116067, 1100005225911, 1100005226935, 4570457547, 1099921337803, 1099921338827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34551125503, 21666363903, 8731137539, 4402684419, 1099636124175, 8680804887], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57385503, 57386527, 23764519], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
  ⟨unpack [44667723811, 52569934899, 14183809091, 22236794155, 17723729195, 13311392043], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100256889211, 1100256890235, 1100156221843, 1100156222867, 1100156223891, 1100156224915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4654278063, 4553682351, 1100038780335, 30524662207, 17639834047, 8882132451], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4503282147, 1099770342895, 1099770343919, 1099669678599, 90939927, 90940951], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4301952555, 6987307], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
  ⟨unpack [48711101479, 48224705591, 1399573575, 17874722083, 17623134499, 8982873379], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100223333763, 1100223334787, 30692437383, 13579750791, 4620792207, 1100172999055], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100173000079, 1100173001103, 1100139449751, 4704607691, 4587234763, 1099921337803], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099837452767, 1099837453791, 107718163, 1099619346963, 25827044895, 12942215711], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [48593729579, 39651551291, 17673398571, 13244284203, 1100592434475, 26464581999], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13562975599, 9100240239, 1100223331715, 1100223332739, 1100223333763, 1100223334787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100089110947, 1100089111971, 1100089112995, 4469794283, 1099787120107, 8697583123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4385907219, 21565700631, 8680804887, 1099602569751, 7053867, 7054891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [48459514927, 26884092991, 9033200971, 1100458213707, 1100458214731, 1100458215755], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100458216779, 22287123795, 13546200403, 13311389011, 1100005227959, 4536905147], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099988448699, 1099988449723, 4536835571, 4469794291, 1099736788471, 1099736789495], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17270736407, 8664029719, 57386527, 57387551, 4301953579], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [44130996275, 18411666499, 17958605135, 13445539151, 9033200975, 1100323996011], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100323997035, 1100323998059, 1100323999083, 1099988448699, 1099988449723, 1099988450747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4604011991, 1099871006167, 1099871007191, 13026103819, 4436238859, 40610339], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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

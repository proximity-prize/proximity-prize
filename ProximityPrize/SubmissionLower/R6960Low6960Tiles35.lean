import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass35

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group35
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27787070471, 44801009683, 87029928991, 48627230779, 43728131375, 39299088687], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17572669831, 17455234439, 4654289287, 30239457739, 17354564043, 4469669323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4436182475, 4385852875, 47419173327, 1099619292639, 1099602513379, 1099602514403], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4369004007, 34416823787, 38711876075, 40551919, 1099552180719, 25776718327], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17186790903, 8596861431, 4301962743], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 125 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 125 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 125 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36394965003, 65756150807, 86979804207, 5912514635, 30860148019, 34869910835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21985083699, 43627461975, 35037604183, 17472003503, 13093155247, 8747860399], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4469738927, 1099686401487, 4385849815, 1099652843991, 1099636067803, 1099636068827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4385780195, 4369005027, 40550895, 1099552179695, 42973207027, 21498531315], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12891825655, 4301961719], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 125 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 125 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 125 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40690459663, 86912420895, 57066168379, 43879124243, 35171825939, 34970574099], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21750202723, 17488780711, 13109932455, 8764637607, 8714374567, 1099719953863], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099719954887, 1099719955911, 157991379, 1099669620179, 1099669621203, 30189058519], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17321007575, 4402557407, 4369005023, 42973285875, 4318670323, 23771635], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [23772659, 47251400183, 30071683575], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 125 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 125 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 125 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44885094419, 86912556067, 39970189375, 39567383831, 35088008471, 39131392279], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4603957627, 13277702539, 13143488907, 13042829707, 4436183475, 25978045895], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13093151175, 1099719954887, 1099719955911, 4436113867, 4385849803, 1099652843991], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099652845015, 47335289315, 1099602510307, 1099602511331, 4352225771, 4318738927], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34383356403, 6994423, 6995447], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 125 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 125 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 125 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [49029266455, 86895848487, 22890987587, 35272486167, 30776267031, 30591791383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13143486871, 8798192023, 8731151767, 1099770285499, 1099770286523, 1099770287547], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47469510083, 21683081667, 8814963139, 4385849803, 1099703175627, 4419335639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4369071575, 1099602511331, 57327083, 1099568955883, 34383359475, 17186787831], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8596858359, 4301960695], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 125 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 125 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 125 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53173372955, 86845586479, 5828628555, 30960745747, 34920242451, 22035415315], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17522335131, 8915628443, 8798191003, 8731150747, 43308763555, 30423938467], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099770287547, 1099753507263, 1099753508287, 1099753509311, 1099686329807, 1099686396367], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099686397391, 17237120491, 4352225771, 57326059, 8630413807], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 125 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 125 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 125 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 125 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 125 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65739641887, 69749675063, 26447746351, 26246492463, 9116962095, 43610756443], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30658822491, 8882074019, 8764636579, 4469737891, 1099820618159, 1099820619183], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099686329807, 1099686396367, 1099686397391, 1099686398415, 1099686399439, 13042819539], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25827049963, 12942155243, 4352225771, 57326059], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 125 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 125 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 125 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 125 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 125 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [74161872931, 48442681403, 39466787127, 26548406583, 26296821047, 17488789851], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100172940635, 4503224743, 1099854170535, 1099854171559, 1099854172583, 13143483831], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4570330551, 4469669303, 1099636065755, 90881507, 1099602510307, 25793497587], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8596858359, 4301894135], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 125 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 125 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 125 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 125 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69900528679, 39919857727, 35121491267, 22236664131, 26229713219, 13143491951], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100089054575, 4469736879, 1099820617135, 1099820618159, 13126707635, 4553554355], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4452893107, 124436955, 1099636065755, 1099636066779, 8630413807, 4335449583], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [23772659], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [82584172587, 14351452231, 35238934807, 30709161239, 26263272727, 8865299855], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4469737895, 1099854172583, 1099854173607, 17472003507, 8848519603, 4402626003], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099669620179, 1099669621203, 1099669622227, 34416982507, 40549871, 40550895], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4318671347, 4318738931], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78289208367, 5828628555, 30944036123, 30658897179, 17723671835, 4520002975], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099887725983, 13210592683, 8848520619, 4520001963, 1099770286523, 1099770287547], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099652843991, 90882531, 1099602511331, 4352226795, 57327083, 25810273775], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12925379055], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [74011086899, 26615517475, 26347154723, 13445482787, 4469737899, 1099837395371], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099837396395, 13143485871, 8764636591, 1099652843991, 1099652845015, 4402626011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099636065755, 21515309551, 12925381103, 4335516143, 6996471], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 35 where
  orders := orders
  covers := by
    intro a ha box
    change 16+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group35

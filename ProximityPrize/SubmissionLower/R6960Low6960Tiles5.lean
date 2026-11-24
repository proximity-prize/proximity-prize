import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass5

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2181106693, 1023479817, 5670966283, 19211164685, 57044840465, 87060277285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31662324801, 35469857025, 43842090293, 39530619189, 35084798269, 39161736509], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17502416313, 13106790849, 8795115969, 25907726829, 17317864941, 4349153781], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099616147959, 8660894201, 4349152761, 1099549038087, 38675112457, 8610560521], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20631049, 20632073, 38658183693, 47248194061, 4298819085], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i51 : checks (tilesOf batches) 131 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14580193289, 27902552081, 86841705497, 69947791413, 39798785277, 35436981501], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43691512061, 30420876637, 39111039393, 21864419761, 17502415281, 13106789813], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811892149, 1099884583351, 4433034733, 4399482349, 1099649699311, 1099649700335], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649701359, 34413768193, 12939012609, 4349082113, 20629001, 20630025], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i54 : checks (tilesOf batches) 131 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27684185101, 61357047833, 86926195757, 10221113417, 30923980069, 34967428389], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26344014117, 43741561153, 35151834433, 8811823537, 8761560497, 17485569465], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13140341177, 1099767142867, 43171194329, 1099716808159, 1099716809183, 1099716810207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399481321, 1099666475499, 17284239861, 4382634489, 4365859321, 38708662785], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30118803969, 12922234373, 37405189, 1099549033991, 4298816013], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i49 : checks (tilesOf batches) 131 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36157206545, 78352700445, 61307592761, 35386512665, 30991087897, 30756280601], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21898049877, 9046708565, 8795044285, 8728004029, 43271926209, 17452014017], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8878927297, 1099817472455, 1099817473479, 1099817474503, 1099700028899, 1099700029923], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700030947, 4365859313, 1099632919027, 25857391097, 17267529209, 8627268101], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315593221, 20559369, 3848717, 3849741], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i52 : checks (tilesOf batches) 131 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40452570133, 82563916837, 39967044669, 35319473421, 35101575437, 39144959245], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4634367353, 17519193477, 13140345221, 8828670341, 21797308865, 13190668737], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834249667, 43255152069, 1099817402823, 1099817469383, 1099817470407, 1099817471431], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783919055, 1099783920079, 4516852185, 4432968153, 30169065973, 70892029], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [70958589, 8593711629, 4298747405], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [61357180953, 82564187181, 5842261065, 35084797205, 26411051285, 22015493397], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39513704769, 30873645377, 8778270105, 1100002021787, 8946035121, 8811820465], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4483301809, 1099851027903, 1099851028927, 17485566405, 8895702469, 1099800693195], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800694219, 1099700027875, 1099700028899, 4382635497, 1099666406891, 54113793], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565742595, 30102024709, 20558345], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61390935069, 78252511281, 26561974549, 26360720661, 17737304341, 39396332877], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26545192269, 1099985176991, 1099985243551, 1099985244575, 1099985245599, 1099985246623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13140340133, 8778268069, 13123557845, 8778262997, 1099750292951, 1099750359511], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750360535, 4382635493, 70891005, 1099582519807, 38708663809, 4332300805], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37335557, 25790283273], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 131 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65602150433, 61173375033, 22099304757, 21914827061, 9063485749, 35218874685], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511639869, 8811821473, 1099968398755, 1099968399779, 1099968466339, 1099934912939], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934913963, 1099934914987, 13090005453, 4516852173, 1099733514715, 1099733515739], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733582299, 21595981297, 12989341169, 4349079041, 37336581, 34363367949], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8593710605, 4298746381], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74024381477, 39866381373, 31058128153, 30773054745, 30538247449, 13123571041], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13224226189, 8845376909, 1100052285839, 1099985243551, 1099985244575, 1099985245599], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968469407, 17485565381, 13123559877, 1099783847375, 1099783848399, 1099783914959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4432966113, 1099699960291, 8644043265, 4349079041, 37336581, 30085246473], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69779879977, 31326780481, 26729675049, 26427757865, 26209726761, 8811826545], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136241523, 8946037141, 8811822485, 1100018731415, 1099934911915, 1099934912939], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934913963, 17418458569, 8828594633, 1099783847375, 1099783848399, 1099783914959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [137999853, 1099649628655, 12922230277, 8627267077, 37335557, 55816], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 131 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78218888237, 10019786825, 30890427657, 30655685897, 21981938953, 8795047301], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13274555801, 8878929305, 4533633433, 1099968467363, 1099968468387, 1099934914979], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867802043, 1099867803067, 21730198993, 13140336081, 1099750359511, 1099750360535], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [188331489, 1099699960291, 1099699961315, 4382633465, 55816, 55820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73940766769, 1496963145, 30773055761, 26293612817, 13425560849, 8962814353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828599697, 1100035508627, 1100018797975, 1100018798999, 1100018800023, 1099867806131], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17519120829, 8929256893, 1099783847375, 1099783848399, 1099783914959, 4382634477], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649628655, 37335557, 37336581, 55816, 55820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65384389685, 26444602653, 21998713117, 9113817373, 8828598685, 1099985175967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099985176991, 1099985243551, 1099985244575, 1099985245599, 1099934914975, 13207444929], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811818433, 1099733514715, 1099733515739, 1099733582299, 4382633465, 87668217], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [55812, 55816, 55820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤131) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 5 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤136 ∧ 3+a.j≤57 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group5

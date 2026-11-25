import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass9

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2264992773, 1023479819, 10821964811, 27784912909, 57313868821, 108434715689], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31275618561, 39514043689, 47818906921, 13694127401, 43641027961, 35068078457], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17636695477, 17519325621, 4701537717, 4433169901, 1099733718511, 1099733719535], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43154616817, 13056511481, 8694510089, 4399545865, 1099582721555, 1099582722579], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37471769, 37538329, 8593694241], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 136 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 136 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 136 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19060037641, 40385195025, 125345813533, 14549699653, 39882872029, 52365393117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26780283101, 26293665189, 21898107301, 43422920113, 17535670733, 8912613841], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811953617, 4483434961, 4449948117, 1099834382807, 1099666608639, 1099666609663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649829379, 1099649830403, 34480871941, 4349214217, 1099616208395, 17250818573], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8677731853, 37469721, 37470745, 17183775265, 3914272], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 136 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 136 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 136 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27936105485, 57230049305, 104022308905, 35302963469, 39312792845, 22216951053], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39429947753, 30840220009, 13375282605, 13257911725, 8912616877, 8728070593], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918267843, 1099918268867, 1099767204327, 1099767270887, 1099767271911, 17385032177], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666537983, 1099666539007, 1099666540031, 8660954633, 104577545, 25823749653], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315655709, 20690461], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 136 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 136 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 136 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36342018065, 61474952221, 78403637297, 26511774009, 30555155769, 13459246393], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35168605537, 22283843937, 13207580081, 8845508017, 1099985308083, 1099901423047], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901489607, 1099901490631, 1099901491655, 34581393901, 17401811437, 8811947501], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716869619, 1099716870643, 1099716871667, 4416320001, 1099649759747, 20689440], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 136 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 136 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 136 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44697402389, 69897316389, 48506711101, 30991149377, 26528549185, 22099436865], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17536105837, 8946176365, 43355880889, 4516986309, 1099901420999, 1099901422023], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901423047, 1099901489607, 1099901490631, 1099901491655, 8895833561, 8761618905], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17351477753, 4466580985, 1099666537983, 1099666539007, 4365988357, 1099632982535], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37466649, 37467673, 42970136093, 30068533793], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48875128857, 78353168425, 22904751173, 26780137765, 30722856229, 13626946853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795178397, 1100069196191, 1100069197215, 1100069263775, 39195134369, 26310373793], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13274617285, 8912545221, 4617646533, 1099851089363, 1099851090387, 1099851091411], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4449876441, 1099817533915, 1099649759747, 1099649760771, 4349208085, 4332432917], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565872663, 4332359193, 20688416], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57230316573, 82530765873, 30857071889, 30639041809, 13526355217, 35118273901], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22233512301, 13207580061, 8845507997, 1100069194143, 1100002086319, 1100002087343], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002153903, 1100002154927, 17468920273, 8895833553, 1099800755679, 1099800756703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800757727, 4433097197, 1099733645807, 71021073, 1099582649875, 12922294809], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8627397145, 20688413], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 136 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57213673505, 69729818677, 26427889961, 22015554857, 13408914729, 35068010861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22183249261, 1100018863531, 1100018864555, 1100018931115, 1100018932139, 8845505965], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002083247, 1100002084271, 1100002085295, 13173956041, 4634422729, 1099733644783], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733645807, 1099733646831, 8660950545, 4365986321, 34397053465, 21512226329], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20689437], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65619192869, 48389270589, 30940818757, 26444664133, 17787693381, 17569660241], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8962953553, 1100002087343, 1100002153903, 1100002154927, 4533763505, 1099985307059], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985308083, 1099985309107, 8795171289, 4466652633, 17418587625, 4533690857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733646831, 1099733647855, 1099632981511, 1099632982535, 4382763533, 87798285], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30102089241], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69813565481, 31360465985, 26746583345, 26444666161, 13576614193, 13140476281], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100220191099, 1100203414907, 1100153084283, 1099951751611, 1099951752635, 1099951753659], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951754683, 13207508437, 8879056341, 4516983257, 1099817531867, 1099817532891], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [71021073, 1099582649875, 1099549170199, 25790413341, 4315653661, 20688413], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3986976, 55840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65535444013, 22820865093, 26595657017, 26327294265, 9248161081, 1100153080203], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153081227, 1100153082251, 1100136306059, 1100119595403, 8979653057, 8862281153], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918195139, 1099817532891, 1099817533915, 1099817534939, 21612889601, 8727993857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382764549, 1099632981511, 20688413, 20689437, 55836, 3910176], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3986976, 55840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69729816625, 5792060489, 26545328421, 26293742885, 9197832485, 8979721637], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828729765, 1100035638695, 1099985376691, 1099951823283, 1099951753659, 1099951754683], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951755707, 17435365857, 8845501921, 1099783977443, 1099783978467, 1099783979491], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [121352709, 1099632981511, 55836, 12888740385, 8593842721, 3911200], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65418075189, 26427890981, 26193082661, 4869313829, 8946170253, 8811955597], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136305039, 1099985376691, 1099951823283, 13224287685, 8862281157, 1099901420999], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901422023, 1099901423047, 1099767200231, 1099767201255, 1099767202279, 4382764553], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099616204299, 8627396121, 4332431897, 55836, 3912224, 55840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 9 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤138 ∧ 4+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group9

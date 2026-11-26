import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Mass8
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231438341, 989925385, 10771633163, 27751358477, 82630687765, 78571408433], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35520254203, 43976441101, 35453888781, 30706142561, 34783079777, 4953264481], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13207580105, 8895905225, 13039880649, 43154617833, 4399614449, 25874370045], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13006252541, 1099616276995, 1099616278019, 34447385093, 54315533, 1099565944335], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38691803667, 25790481941, 4315725333, 20760085, 17183777305, 4298947097], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 134 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19127212041, 36241222673, 86925987869, 52919116857, 39681610005, 35269409045], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47802129685, 8996572549, 17670315421, 17519325597, 17418732957, 43238436309], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4466722265, 38909909469, 1099716939243, 1099716940267, 1099716941291, 30219598321], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17351547377, 8761684465, 4433165809, 1099599496711, 1099599497735, 38708795917], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8610688533, 20758037, 20759061, 25773703705], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27952948237, 57230114841, 86976722985, 10254797893, 30957730093, 30739700013], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30572001581, 39396458857, 30806665577, 13157317033, 13056657833, 17452210641], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845503953, 1099800824279, 1099800825303, 1099800826327, 1099800827351, 4449941997], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700158959, 1099700159983, 21562624517, 4332498449, 4332500497, 8610619925], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20758037, 42953287193], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 134 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36342083601, 69913957405, 65602689077, 35286046013, 26696317245, 30655812925], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21931734353, 9114013009, 8828794305, 4517052865, 1099884710339, 17468986829], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8862280141, 1099817602515, 1099817603539, 1099817604563, 43137839597, 1099649827323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649828347, 4382832125, 1099633049087, 8627464721, 12905584149, 8610620949], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20755989, 20757013], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i52 : checks (tilesOf batches) 134 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48807820309, 82614512677, 27199716417, 31091879193, 30806740249, 30639107353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39245462925, 30655669645, 8778468761, 13174025637, 8845573541, 4533832101], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851157963, 1099851158987, 17502473677, 8912609741, 1099750492643, 1099750493667], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733712359, 1099733713383, 1099733714407, 4466650605, 4416386541, 54310413], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565939215, 21512291857, 4298944025], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57230247961, 82564317229, 5859168329, 30924177685, 34900451605, 17787766037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39396460905, 30739624297, 13325017497, 13157249433, 8845574553, 1099985374635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884712387, 1099884713411, 1099784045019, 1099784046043, 1099784047067, 4500271581], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416387549, 17385099749, 1099633048063, 1099633049087, 4382762501, 4382830085], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25823965709, 17234103821, 37533201, 8593842713], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61424686109, 74008006705, 26545393953, 30555221281, 9214676257, 35185448277], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26562099541, 13190802841, 8845573529, 1100052482459, 1099918265787, 1099918266811], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918267835, 1099784043995, 1099784045019, 1099784046043, 13140465117, 8795170269], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4449939941, 1099733711335, 54309389, 1099565938191, 4332430865, 4315721233], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25790413333, 3976729], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69846982689, 52667458617, 35269337393, 26562102577, 30538375473, 17552884041], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100388029771, 13257908645, 8879059365, 8795241893, 1100002150823, 1100002151847], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002152871, 1099784043995, 1099784045019, 1099784046043, 4416385517, 1099700156911], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21629666801, 8761613809, 4399540737, 34413830669, 54309389, 1099565938191], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21478737433], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69813496869, 39883288637, 31024770349, 26528615725, 26293807405, 13190874469], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100270589287, 8929388973, 8795174317, 1099968594351, 1099951818163, 1099951819187], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951820211, 1099951821235, 4416386529, 1099750489571, 17401875941, 8811946469], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382830081, 1099616269827, 1099616270851, 30085377557, 3976729, 3977753], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74041489449, 22854484033, 26763360545, 26495063329, 22049173793, 1100102814095], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102815119, 1100102816143, 1100102817167, 8845504941, 4533829037, 1099968595375], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190796753, 8845501905, 1099716935147, 1099716936171, 4416385517, 1099700156911], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [54309389, 1099565938191, 25807190545, 4332430865, 4315721233, 3976729], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69763367981, 14314883141, 26612434217, 26344071465, 21914959145, 8845573525], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035705247, 1100035706271, 1100035707295, 1100035708319, 13207577013, 8811950517], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099800821207, 1099800822231, 1099800823255, 4416385517, 1099700156911, 21629666805], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8744836597, 4382763525, 54309389, 1099565938191], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73940897841, 30806806801, 30555222289, 4986818833, 13190803849, 8845574537], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119592331, 1099918266811, 1099918267835, 17536094661, 8895833541, 1099851153867], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851154891, 1099851155915, 4483428821, 1099800820183, 1099800821207, 87863813], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [87864837, 4332430865, 4332498449], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61156727861, 26377624877, 21931735341, 4869378349, 8862349725, 1100035704223], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035705247, 1100035706271, 1099918266811, 1099918267835, 13224353217, 4634422721], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4567381441, 1099750489571, 1099750490595, 87864837, 1099599493639, 8610618901], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4315720213, 20754965], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 8 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤136 ∧ 4+a.j≤57 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group8

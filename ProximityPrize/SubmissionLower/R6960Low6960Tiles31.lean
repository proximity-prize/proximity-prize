import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass31

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group31
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [19261623303, 36544258063, 87027762203, 65805129783, 43960976683, 39582331179], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30573107587, 21916072323, 4853715331, 8779577839, 4484613615, 4434284015], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34498612731, 21597297151, 13007434239, 34431791627, 21546964491, 1099583837707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38653459, 1099550282259, 47249437211], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32198432779, 53221537815, 87061720103, 23124033603, 35287362879, 35019002175], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30606669119, 43424168363, 34834376107, 13158430147, 8762803663, 4451062223], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21731512799, 13124807135, 1099667722743, 1099667723767, 4367173115, 1099650944507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4383947271, 4350394887, 43021507083, 1099567057423, 21873175, 21874199], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12889991707], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36561167375, 65771096091, 82699782195, 30824696123, 30623443259, 13527533883], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43709385055, 30841402719, 13175138755, 8846686659, 4534945219, 1099801939415], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099801940439, 1099801941463, 17352660467, 1099634165247, 1099634166271, 4367170051], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099617387011, 8662067723, 4367169035, 42971318807, 21872151, 30069716507], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40755867667, 74193459235, 57064267835, 39548705087, 26663944511, 26412358975], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21832186211, 4769829219, 8829909435, 8729249211, 1099801940439, 1099801941463], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13158358491, 8779509211, 1099768382943, 1099768383967, 1099768384991, 156088823], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099667717623, 1099667718647, 47316546059, 4367166987, 4333614603, 34381455895], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21496628759, 21870103], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44900105239, 69898561575, 44212923455, 35169855811, 26479398211, 26261367107], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17453401455, 1099952932275, 1099952933299, 1099952934323, 1099952935347, 1099952936371], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8930503099, 8829908411, 4501389755, 43155799531, 17369435631, 8779506159], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099701273071, 156087799, 1099667716599, 1099667717623, 30153599495, 21563738631], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4350389775], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48977102875, 82565494825, 14366328903, 31025953043, 30740814099, 30539561235], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13158365575, 1099986487723, 1099986488747, 1099986489771, 1099986490795, 13309352375], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8913725879, 8779511223, 43340351931, 30422037947, 1099852267979, 1099852269003], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4417500647, 1099734826471, 13024138747, 4383877639, 88977927, 88978951], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099600607751, 25808303635, 12923474451, 42954541595], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53104432159, 82498455601, 30908582155, 26429139211, 17755325707, 39213159831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26294844823, 1100070372759, 1100070373783, 1100070374807, 1100070375831, 1100070376855], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8947280299, 8813065643, 1099986485675, 13158357463, 4417500643, 1099751603683], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4400654851, 105755139, 1099617383939, 1099617384963, 21496561175, 12906698263], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4299990555], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61459619875, 61174684725, 22134103347, 21916071219, 9081572659, 35136299363], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22234760547, 8846620063, 1100036817311, 1100036818335, 1100036819359, 1099986488747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099986489771, 1099986490795, 13124804051, 4534873555, 4417500639, 1099768380895], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099634161151, 1099634162175, 8645287439, 4333545999, 55423503, 21479851547], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4300057115], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61392579623, 48356894777, 17738541383, 17537219911, 4736274759, 30891732311], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22184430935, 17721763159, 8779578783, 1100036819359, 1100036820383, 1099952935347], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099952936371, 1099835488719, 1099835489743, 1099835490767, 1099835491791, 8796284379], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4484608475, 17285549571, 8678842883, 72200715, 1099583829515, 55422479], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4299989529, 4300057115], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65553397801, 31311312963, 26714208571, 26378736955, 17704988987, 8880244079], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100238147951, 1100238148975, 1099936155063, 1099936156087, 1099936157111, 4568428987], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4501387707, 1099919376827, 13208688079, 8846616015, 1099701271023, 1099701272047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [122532351, 1099634161151, 4350322191, 55422479], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73958786093, 10004253767, 26730988819, 26412294419, 26177486099, 13141654903], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100053597595, 1100053598619, 1100053599643, 9047941551, 8880172463, 4551719343], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099936154039, 1099936155063, 1099936156087, 1099701271023, 1099701272047, 4434275831], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099667715575, 21614069243, 8729173499, 5090843, 5091867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65436028977, 5726064715, 26529730855, 22033509671, 17570776357, 1100137481607], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100137482631, 1100137483655, 1100020044195, 1100020045219, 8880172463, 4568496559], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099969708463, 17436545503, 8796284383, 1099684493811, 1099684494835, 4383945207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [55423503, 1099567052303, 4333544979, 4316835347, 5090841], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 31 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group31

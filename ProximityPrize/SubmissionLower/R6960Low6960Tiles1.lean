import ProximityPrize.SubmissionLower.R6960Low6960RetainedCount
import ProximityPrize.SubmissionLower.R6960Low6960Mass1

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group1
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2248215557, 1040257033, 4613805065, 18774694925, 82378240017, 87026729005], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [5993059401, 19009770587, 35738169549, 35671463117, 60854270157, 31241736453], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34833085757, 26427554173, 22015219069, 21881073021, 13089883569, 8794844641], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4483103201, 4449616353, 1099766945251, 1099766946275, 1099750164967, 1099750165991], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099750167015, 17300887041, 8694180353, 34447054345, 1099599168011, 1099599169035], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [53983761, 53984785, 4332172821, 42969805337, 25773308445, 4298549789], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4298617373], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i3 : checks (tilesOf batches) 135 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 135 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 135 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10117191691, 23456130061, 65517534229, 86942776365, 10187362377, 35436510493], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31091417373, 30823121193, 39144759593, 17770662185, 39295261049, 17535771041], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13156922785, 13089883553, 1099867608523, 1099867609547, 1099817272791, 1099817273815], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817274839, 1099817275863, 21730001377, 13140138465, 4432770533, 1099750161895], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099750162919, 4449544697, 4382437881, 1099599165963, 53916177, 53982737], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [38691543573, 30101758485], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 135 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 135 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 135 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23456130061, 52850736149, 86875598889, 22904423493, 30957269269, 30772859157], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43355844885, 35218472273, 30873379153, 17518997881, 8811693469, 1100052156831], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052157855, 1100035381663, 13274288577, 8945836481, 8811621825, 1099850758607], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850759631, 1099850826191, 1099817272791, 1099817273815, 1099817274839, 38876030441], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21646115309, 4382436857, 1099666208251, 53915153, 1099565543955, 30101758485], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [17200153113, 4315324953, 20359705, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 135 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 135 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 135 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36006014993, 82530030621, 56978875449, 31275898109, 35185128701, 43473213693], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21780415821, 17636366717, 17502219645, 13123371389, 1100068934043, 1100035380635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001827227, 39194735005, 1099934712251, 1099934713275, 1099934714299, 1099934715323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21847373253, 13257510341, 4516654541, 1099850757583, 1099850758607, 1099850759631], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8761286125, 4432767469, 1099615875591, 53914129, 1099565542931, 55824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55828, 4315323929, 20358681, 54808, 55832, 54812], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i12 : checks (tilesOf batches) 135 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 135 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 135 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44462128149, 86774868005, 31360138305, 31074642169, 39312460025, 39127986425], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17502220653, 8845182329, 8794919289, 39261846913, 26427483521, 17669917081], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13240737177, 8912285081, 1099934716335, 1099901162927, 1099867609519, 1099934713275], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934714299, 1099934715323, 1099917867455, 1099917868479, 1099917935039, 1099733315051], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733316075, 1099733317099, 17384702445, 8727731697, 188131825, 55812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55816, 54796, 55820, 8643843601, 54800, 55824], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [38691618325, 4332102165, 53780, 54804, 55828, 53784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54808, 55832, 53788, 54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i15 : checks (tilesOf batches) 135 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 135 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 135 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48673409049, 86758225961, 14281002053, 35168418041, 34967231737, 26310263033], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35084388721, 26444262769, 8828404093, 13274291597, 13156920717, 8794848653], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035378583, 1100001825175, 1099951494551, 1099917941143, 1099934714299, 13291063741], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8928991677, 1099901091267, 1099901157827, 1099901158851, 4449545681, 1099833980371], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099833981395, 4432766445, 1099666206203, 1099666207227, 55800, 55804], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54784, 55808, 54788, 55812, 54792, 55816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [53772, 54796, 55820, 8627067409, 53913105, 1099565541907], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53776, 54800, 55824, 25806859797, 52756, 53780], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54804, 55828, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4298545693, 3580445, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i18 : checks (tilesOf batches) 135 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 135 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 135 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65517933597, 73907016757, 30655419661, 26276705549, 9163952397, 31108125989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26645591333, 26377228581, 8861955465, 1100135973259, 1100102419851, 1100102486411], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068933003, 1099951493531, 1099917940123, 1099867609499, 8861953437, 13223956921], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8878727609, 1099850758607, 1099850759631, 1099766869475, 1099766870499, 1099766871523], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55792, 55796, 21629335033, 13022629369, 55800, 54780], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55804, 4399211009, 1099632650755, 54784, 55808, 53764], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54788, 55812, 53768, 54792, 55816, 4365655565], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53772, 54796, 55820, 52752, 53776, 54800], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55824, 52756, 53780, 54804, 55828, 1099532060187], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 12888477213], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [3581469, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i21 : checks (tilesOf batches) 135 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 135 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 135 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 135 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 135 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65518067745, 61106069561, 26276634917, 26108935461, 1100337371431, 30973976873], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26494599465, 26293411113, 8845180281, 1100152818043, 1100102487419, 1100068934011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018603387, 1100035307939, 8945769897, 8845175209, 1100001752491, 1099934645691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934712251, 1099934713275, 17468588505, 8861881817, 1099733314027, 1099733315051], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733316075, 55788, 55792, 54772, 55796, 54776], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55800, 54780, 55804, 4382433793, 53760, 54784], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55808, 30168867333, 53764, 54788, 55812, 52744], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53768, 54792, 55816, 52748, 53772, 54796], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55820, 52752, 53776, 54800, 55824, 51732], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 20357657, 20358681], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 8593511965], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i24 : checks (tilesOf batches) 135 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 135 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 135 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 135 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78218554405, 35504109633, 31041154305, 30772858113, 34782686465, 8845250901], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13274361193, 13123370345, 8794918249, 1099834055063, 1099934715295, 1099901161887], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099850831263, 1100018531751, 1100018532775, 1100001822119, 1099951491495, 13341396397], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8945769901, 8828397997, 1099867534795, 1099867535819, 55780, 1099733314027], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733315051, 1099733316075, 55784, 25974566381, 13089737197, 55788], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54768, 55792, 54772, 55796, 54776, 55800], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [53756, 54780, 55804, 53760, 54784, 55808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4399209989, 104244741, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 52748, 53772], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54796, 55820, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55824, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 4298545693], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65467938857, 35504109633, 26628815141, 26343675173, 21931405605, 13089818965], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102490455, 1100068931979, 1100018601355, 1099968270731, 1099917940107, 8828400021], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085640599, 1100068864407, 1100018533783, 9046431153, 8912282033, 4566986161], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099833980371, 1099833981395, 55780, 55784, 54764, 55788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54768, 55792, 21646113269, 8761217525, 1099682983415, 1099682984439], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54772, 55796, 53752, 54776, 55800, 53756], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54780, 55804, 4399211009, 1099632650755, 53760, 54784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55808, 52740, 53764, 54788, 55812, 52744], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53768, 54792, 55816, 52748, 53772, 54796], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55820, 1099548837395, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55824, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 3580445], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [3581469, 1099515281951, 50716, 51740, 52764, 53788], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73906947117, 14197115973, 30806344965, 26360521989, 26176045317, 8845181289], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035378563, 1099985047939, 1099951494531, 1099901163907, 8979391893, 8828400021], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085640599, 1099984978347, 1099985044907, 1099917937067, 17602807225, 8962546105], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099833979347, 1099833980371, 1099833981395, 55776, 55780, 55784], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54764, 55788, 54768, 55792, 4399212021, 1099682983415], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [53748, 54772, 55796, 53752, 54776, 55800], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [53756, 54780, 55804, 52736, 53760, 54784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55808, 52740, 53764, 54788, 55812, 52744], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53768, 54792, 55816, 51724, 52748, 53772], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54796, 55820, 53913105, 1099565541907, 51728, 52752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53776, 54800, 55824, 4332100117, 4315324949, 51732], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 51736, 52760], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53784, 54808, 55832, 3580445, 1099515281951, 50716], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73873461297, 1396103241, 26545000705, 26310192385, 17669998849, 1100119263611], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068932987, 1100018602363, 1099968271739, 13156920709, 1100152749447, 1100135973255], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085642631, 1099800500635, 13240734141, 8878727613, 4483100105, 1099867534795], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867535819, 55776, 55780, 54760, 55784, 54764], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55788, 54768, 55792, 53748, 54772, 55796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099666206203, 1099666207227, 53752, 54776, 55800, 53756], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54780, 55804, 52736, 53760, 54784, 55808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4399211013, 104245765, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 51724, 52748], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53772, 54796, 55820, 1099548837395, 51728, 52752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53776, 54800, 55824, 12922032661, 51732, 52756], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53780, 54804, 55828, 51736, 52760, 53784], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54808, 55832, 1099515281951, 50716, 51740, 52764], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53788, 54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65333926965, 26394074385, 26176043281, 4818654481, 8878733685, 1100152751479], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102420855, 1100085710199, 1100035379575, 1099867608467, 1099817277843, 8979324329], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8861952425, 1100001752491, 1099917867455, 1099917868479, 1099917935039, 55772], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [55776, 55780, 54760, 55784, 204909037, 1099716537839], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716538863, 54764, 55788, 54768, 55792, 53748], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54772, 55796, 53752, 54776, 55800, 53756], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54780, 55804, 52736, 53760, 54784, 55808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099532061191, 52740, 53764, 54788, 55812, 4382432777], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [87467529, 52744, 53768, 54792, 55816, 51724], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 1099548837395, 51728], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 51732, 52756], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53780, 54804, 55828, 51736, 52760, 53784], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54808, 55832, 50716, 51740, 52764, 53788], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54812, 55836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤135) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 1 where
  orders := orders
  covers := by
    intro a ha box
    change 1+a.b≤136 ∧ 3+a.j≤57 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group1

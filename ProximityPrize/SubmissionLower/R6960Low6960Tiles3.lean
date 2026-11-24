import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass3

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2214661125, 1040257033, 4613805065, 22985907213, 78217753621, 87060348973], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6026679369, 19043456089, 39848850673, 39748525297, 31208313093, 30789698885], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39128114501, 13526158661, 43573653881, 17502283193, 13157054905, 8828537273], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099699901931, 1099699968491, 25907660277, 13022765557, 1099649567223, 1099649568247], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649569271, 34480676345, 25890816505, 4399348221, 4365795837, 8643981833], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [42969870865, 20496913, 20497937], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i51 : checks (tilesOf batches) 133 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10503198731, 27549836301, 74057334809, 86976530481, 39698055445, 35302631701], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35000847669, 34833150261, 5003334965, 13190541737, 13106725289, 8778207657], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43322058169, 21746912721, 13123429841, 38926424533, 1099767009755, 4416127457], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733453283, 1099733454307, 1099733456355, 1099733522915, 4432901621, 4365794805], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30185777657, 21595916793, 1099599234563, 54050313, 1099565679115, 8627201549], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4332237325, 38674977297, 42953163285, 12888613397], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27549836301, 57129123865, 86909286441, 14448839749, 30923847965, 34967296285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30588517661, 39463240017, 30873512273, 8912420253, 13056395677, 17519057329], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13140209073, 43322058169, 1099884452287, 1099834116555, 1099834117579, 1099834118603], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834119627, 21629471213, 1099683118575, 1099683119599, 1099683120623, 8694312433], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [154712561, 8660689413, 4332236301, 37271053, 42953090581, 38658200085], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [25773373973, 12888544789], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 133 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36106809361, 78302237725, 61273907257, 35436778765, 30957402381, 35000850701], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26092223821, 1100354214223, 13089947037, 1100018666911, 1100018667935, 1100018668959], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13324753321, 8962681257, 8878863785, 39060648373, 1099800560083, 1099800561107], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800562131, 25957923301, 13089871333, 154711537, 1099666340339, 1099666341363], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365789701, 70824453, 34380012049, 21478473237, 4298679829], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 133 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44512525333, 78302439461, 39916581949, 31041218837, 30789699861, 30638844181], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17401694573, 39228423565, 30638630285, 13173762465, 8845310369, 8744650145], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985113511, 1099985114535, 1099951561127, 17518987717, 13140204997, 1099834115531], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834116555, 1099834117579, 1099733449187, 1099733450211, 1099733451235, 4449676777], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099699893739, 17267394049, 8660688389, 4365789701, 20492817, 1099532196371], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48740648985, 82530433065, 18576033861, 30940625161, 30739437833, 34799597833], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13190543733, 39262046593, 26394063233, 1100052220311, 1100052221335, 1100052222359], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018668951, 1099985115543, 13274421677, 8895572397, 8811754925, 1099867668931], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867669955, 17401613789, 1099716670951, 1099716671975, 1099716672999, 4416121337], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [121156089, 1099532196363, 4332167693, 1099532195347, 55824, 38658198037], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12888542741, 8593579541, 55828], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61323695133, 78218825777, 26528289037, 30588513549, 13475826957, 35235452221], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26578614589, 13173763469, 8845311373, 1100085774735, 1100018666911, 1100001890719], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951560095, 1099918006687, 13207311813, 8828462533, 1099817336271, 1099817337295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817338319, 4449677781, 1099783780823, 1099616006655, 1099616007679, 21562292737], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12972429825, 4382565889, 87600641, 1099532196355, 1099548972555, 55816], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55820, 34380011025, 55824, 4298678805, 1099515417111, 54804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55828], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 133 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61323829281, 65417878581, 26343808293, 21931473189, 9096974629, 30957330753], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26477953345, 8828533141, 1100052219287, 1100052220311, 1100052221335, 1099951559075], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918005667, 1099867675043, 13190536625, 8811687345, 1099800558035, 1099800559059], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800560083, 4416122345, 1099699893739, 17351213549, 13039539693, 1099548973563], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4399277565, 1099532195335, 55812, 54046217, 1099565675019, 55816], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099548971535, 54796, 55820, 54800, 55824, 8593577493], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4298678805, 54804, 55828], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65535044645, 48338742333, 30923844913, 26444467505, 21998577969, 13274431813], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8945979717, 1099951559071, 1099918005663, 1099867675039, 1099985109415, 1099985110439], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985111463, 1099968335271, 8845240753, 4550342065, 1099934776755, 17435168213], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8794907093, 4382567921, 1099666339315, 1099666340339, 1099548973559, 25857256961], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17267395073, 1099532195331, 55808, 55812, 4348944905, 4332235273], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099565675019, 53768, 54792, 55816, 1099532194319, 54796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55820, 54800, 55824, 8593579541, 3713557, 3714581], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [52756, 53780, 54804, 55828], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69729417257, 31259540545, 26695989533, 26444469533, 26226438429, 8845315425], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102556003, 8912351629, 8811756941, 1100085774735, 1099985112483, 1099934781859], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884451235, 13240866241, 8828462529, 1099850890695, 1099850891719, 1099850892743], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416123357, 1099750226399, 1099548973555, 21579069949, 12989207037, 4399277565], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [104377853, 1099616006655, 1099616007679, 1099548972543, 55804, 55808], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55812, 53768, 54792, 55816, 1099515417103, 54796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55820, 53776, 54800, 55824, 52756, 53780], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54804, 55828], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65451295789, 22753559621, 26561840421, 26293477669, 17653284133, 1100085776763], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035446139, 1100001892731, 8761425305, 1100035443099, 1100001889691, 9013010853], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845241765, 8761424293, 1099850892743, 1099800558035, 1099800559059, 1099800560083], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17384768997, 13039540709, 4432899557, 1099716670951, 1099532196339, 1099548972539], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55800, 55804, 55808, 53764, 54788, 55812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54046217, 1099565675019, 53768, 54792, 55816, 8627132941], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4332234253, 1099515417103, 54796, 55820, 52752, 53776], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54800, 55824, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73890304049, 1429723209, 26561843461, 26360655109, 17686841605, 1100136106371], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102552963, 1100052222339, 1100001891715, 8929127829, 8828533141, 1100052219287], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817343395, 17468723653, 8828462533, 1099800558035, 1099800559059, 1099800560083], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [188264937, 1099699893739, 1099548973551, 1099548972539, 55800, 55804], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382565889, 87600641, 55808, 53764, 54788, 55812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [53768, 54792, 55816, 12922098189, 4332167693, 1099515417103], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54796, 55820, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [52756, 53780, 54804, 55828], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65350769717, 26410917141, 26192886037, 4869117205, 8895576445, 8794981757], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068999551, 1099867674019, 1099817343395, 13207313841, 8811687345, 1099934778803], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934779827, 1099901226419, 1099834112459, 1099834113483, 1099834114507, 4432899561], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099699893739, 1099548973551, 1099548972539, 55800, 55804, 8677465601], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382566913, 55808, 53764, 54788, 55812, 53768], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54792, 55816, 37270029, 1099515417103, 54796, 55820], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 52756, 53780], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54804, 55828], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 3 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤136 ∧ 3+a.j≤57 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group3

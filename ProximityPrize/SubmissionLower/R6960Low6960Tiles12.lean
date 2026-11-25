import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
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
  ⟨unpack [2315324421, 1023479817, 10167456779, 27600166925, 82596936725, 87060483121], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31325753601, 39815494917, 35470468357, 47952857349, 39061076297, 17452087725], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13106793901, 1100052290991, 21965015473, 17586233777, 17468863921, 43372523973], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817405927, 1099817406951, 1099817407975, 1099817474535, 1099767073267, 4500076025], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4432969209, 1099733517819, 30185842193, 21595981329, 8694309397, 8677600789], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [34430475805, 70893085, 1099582521887, 12905389609, 42953159213, 4298747437], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [3782189, 3783213], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [15033374731, 31979481105, 86892169241, 69931015221, 35587770633, 39564176649], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47852262665, 26159465817, 17720448413, 17535904157, 13207453085, 8744717753], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001958331, 1100001959355, 38993668573, 1099834183139, 1099834184163, 1099834185187], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30353616357, 17485565413, 1099783847407, 1099783848431, 1099783849455, 1099783850479], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8778263029, 4466521589, 38792337933, 8644043297, 54113825, 1099565742627], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4332301861, 25773436461, 17183574573], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27818533901, 65601749017, 86926196781, 10153940041, 30890426661, 34917032229], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26310460709, 39614300469, 31007795509, 8811824553, 1100069065131, 13291266477], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13140275629, 8828600749, 1099968402883, 1099968403907, 1099968470467, 1099834183139], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800625643, 1099800626667, 1099800627691, 17452009965, 8862080493, 4483297773], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783846383, 1099783847407, 38876227065, 4416186897, 25857321497, 17267459609], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [34430406173, 70890013, 1099582518815], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40318021649, 82597402657, 57046181945, 31259318545, 35168549137, 39211998481], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17552754013, 1100387834207, 1100354280799, 13375151513, 13224160665, 13123567001], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39245263265, 1100001955259, 1100001956283, 1100001957307, 21847570901, 13257707989], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884510679, 1099884511703, 1099884512727, 1099884513751, 4500073965, 1099783845359], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783846383, 4416119313, 4382632465, 1099565740579, 20556329, 20557353], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532262955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48740514837, 82580761637, 35672079425, 31091682577, 30806543633, 34883546385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39396261245, 30722581885, 13073240445, 13224160657, 13123566993, 1100169727379], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052287919, 1100052288943, 1100001958319, 1099968404911, 17535897029, 8929190341], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099918065103, 1099918066127, 1099918067151, 1099918068175, 4500073957, 1099817399783], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817400807, 17334568457, 4382564889, 87665177, 87666201, 1099599295003], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30135510557, 8660752925, 1099549040159, 1099549039143, 56872, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57179719705, 86791979053, 10036499529, 30940758277, 30722728197, 30555029765], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35235514717, 26595388765, 13140345213, 1100253614463, 13240934821, 8862085541], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8795045285, 1100035511719, 1100001958311, 1099968404903, 1099985177023, 1099985178047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13240863193, 8929188313, 1099867733467, 1099867734491, 1099867735515, 1099800621547], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099800622571, 1099800623595, 4432897533, 1099716734463, 1099532262935, 1099549039135], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56860, 4332299809, 56864, 25806990885, 1099549038119, 56868], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55848, 56872, 4298676781, 4298744365, 3779117, 55852], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65602016285, 78235735093, 30722725141, 34766107925, 4919515413, 35285849401], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26629011769, 13207385465, 13106791801, 1100203283835, 1099934849455, 1099901296047], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035507635, 1100035508659, 1100035509683, 1100001956275, 13308040629, 8912414133], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4583895477, 1099934841291, 1099934842315, 1099934843339, 1099716735487, 1099716736511], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4399343109, 1099683180039, 21629467145, 13006049801, 1099532262927, 1099549039127], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 34447185433, 56856, 4365853213, 56860, 54110753], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532260899, 55840, 56864, 55844, 56868, 8610419241], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4315455017, 1099532259883, 54824, 55848, 56872, 54828], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61374292001, 69679356981, 26394205469, 30454364445, 4869183773, 31007793485], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22283714893, 22032128333, 13173897597, 1100253612415, 1100253613439, 1100203282815], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100152952191, 1099918072235, 1099884518827, 8778199477, 1099951619527, 1099951620551], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951621575, 8945965525, 4600669653, 4533628373, 1099817399783, 1099817400807], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549040135, 1099549039119, 17301013009, 8711083537, 1099632848403, 1099632849427], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56848, 56852, 1099549038107, 55832, 56856, 55836], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56860, 54109729, 54110753, 55840, 56864, 1099549037095], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54820, 55844, 56868, 54824, 55848, 56872], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4298744365, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74024381477, 44077397053, 26914155801, 30772988185, 26343942425, 17485645133], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100287170895, 1100253617487, 1100136170907, 1100136171931, 1100119395739, 1100069065115], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018734491, 8929192357, 8828597669, 1100085838247, 17552607685, 8962743749], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834176995, 1099834178019, 1099834179043, 4432964089, 1099733512699, 1099532262915], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549039115, 56840, 56844, 56848, 1099549038103, 55828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 55832, 56856, 70887965, 1099582516767, 55836], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56860, 12938938913, 8627198497, 54109729, 1099549037091, 54816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55840, 56864, 54820, 55844, 56868, 54824], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55848, 56872, 25773436461, 4298676781, 4298744365, 52780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69779879977, 35554638913, 26729675049, 26427757865, 26209726761, 13106793825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100152954211, 8895639957, 8811822485, 1100152949143, 1100102618523, 1100052287899], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001957275, 1099968403867, 13240931785, 8828528073, 1099918065103, 1099918066127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099918067151, 1099834175971, 1099834176995, 1099834178019, 1099549040127, 4399343109], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099683180039, 1099532261899, 56840, 56844, 21595912721, 12989272593], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099549038099, 55824, 56848, 55828, 56852, 55832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56856, 1099549037087, 54812, 55836, 56860, 4349076001], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54110753, 54816, 55840, 56864, 54820, 55844], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56868, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8593642029, 4298677805, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78218888237, 14214025289, 30890427657, 26410984713, 30454366473, 13173899625], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119396747, 1100069066123, 1100018735499, 1099968404875, 8996300197, 8845308325], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085837223, 1100035506611, 1100035507635, 1100035508659, 1100001955251, 17569383889], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8979519953, 1099817398759, 1099817399783, 1099817400807, 1099549040123, 1099549039111], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56836, 4432963081, 1099666402827, 56840, 56844, 1099549038099], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55824, 56848, 55828, 56852, 55832, 56856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099549037087, 54812, 55836, 56860, 54816, 55840], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56864, 54820, 55844, 56868, 52776, 53800], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54824, 55848, 56872, 3778093, 3779117, 52780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82413195313, 35101577461, 30605358325, 9248036085, 13190608249, 8845378937], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186505595, 1100018734487, 1099968403863, 1099918073239, 13408637353, 9046630825], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8878861737, 1100001953211, 1100001954235, 1099968400827, 1099951618503, 1099951619527], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951620551, 4432965105, 1099767068147, 1099549040123, 1099549039111, 56836], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840, 56844, 1099549038099, 55824, 56848, 1099616071191], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099616072215, 55828, 56852, 4382564889, 87665177, 55832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56856, 1099549037087, 54812, 55836, 56860, 54816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55840, 56864, 54820, 55844, 56868, 12905386537], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 52780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69629025333, 30672395537, 26209729809, 4869183761, 8912485757, 1100253612415], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100220059007, 1100169728383, 1100119397759, 1099934849439, 1099884518815, 13308042661], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895638949, 8795044261, 1099918067151, 1099867732443, 1099867733467, 1099867734491], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4432965105, 1099767068147, 1099549040123, 1099532261895, 56836, 56840], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8694308365, 4382632461, 55820, 56844, 1099549038099, 55824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56848, 1099616072215, 55828, 56852, 55832, 56856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099549037087, 54812, 55836, 56860, 54816, 55840], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56864, 37333541, 37334565, 54820, 55844, 56868], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4315455017, 4315522601, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56872, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 12 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group12

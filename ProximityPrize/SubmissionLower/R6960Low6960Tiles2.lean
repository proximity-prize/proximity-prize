import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Mass2
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group2
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231438341, 1040257033, 4613805065, 18892200973, 56977600529, 87009814565], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31611862081, 19060167769, 31225024773, 39681143077, 35386448165, 35118153009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34967298353, 13073106357, 4533573045, 13224026565, 13140210117, 8794915269], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733454311, 1099733455335, 25974636009, 17351219689, 1099683124723, 1099683125747], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649499643, 1099649500667, 1099649567227, 4382503429, 4365728261, 17200290325], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8593583641, 3652121, 3653145], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i51 : checks (tilesOf batches) 134 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10301806603, 27549836301, 69795856409, 86976463917, 1698158665, 39614103837], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31091550493, 30789699889, 34866637105, 13509315889, 39144397221, 13240871341], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895576493, 13039551917, 1099850896843, 1099800495575, 1099800496599, 1099800563159], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800564183, 21679737313, 13089874401, 1099750234595, 137869817, 1099649498619], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649499643, 38742016517, 4365726213, 30085048853, 17200220693, 12905324053], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4315393557, 3651097], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i54 : checks (tilesOf batches) 134 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27549836301, 57095503897, 86892443689, 14415219781, 30940625177, 39195089177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26343883033, 39463174473, 30856669513, 13375019421, 13224028573, 13123434909], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8761362853, 1099934782903, 1099934783927, 39060579769, 1099817273811, 1099817340371], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817341395, 4432837081, 1099783717339, 1099783718363, 17367992813, 4466387441], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4416057841, 1099632720383, 1099632721407, 30135380489, 34413497869, 37204497], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099548833299, 8610356757], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 134 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40183607313, 78285461537, 57012495417, 31192078605, 30957402381, 34967230733], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21814033749, 4734834005, 39295398273, 13324687777, 13156919713, 8845244833], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985044907, 1099985045931, 1099985046955, 1099985113515, 1099884451267, 1099867675075], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750160867, 1099750161891, 1099750162915, 21696444901, 13106581989, 4499941861], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4416057829, 87536133, 1099599164935, 8627134989, 4298613273, 3648025], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3649049, 55832], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 134 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44462128149, 78302439461, 39899739197, 31041218837, 26561775893, 30622000405], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13173769577, 1100186375531, 1100152822123, 39295466881, 30688961921, 13190473117], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8862021021, 8761360797, 1099951492531, 1099951559091, 1099850826187, 1099850827211], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850828235, 17451878869, 8845172181, 1099750159843, 1099750160867, 1099750161891], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4466387433, 1099716604395, 17284105729, 1099548908039, 1099548907023, 55824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8610356757, 20425237, 20426261, 55828, 30068270617, 8593578521], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54808, 55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48707029017, 86758225961, 14281002053, 35168418041, 34967231737, 26343883001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35034122617, 26444328313, 8828469637, 13324688781, 13156920717, 8828468621], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052155799, 1100001825175, 1100001891735, 1099968338327, 17535764925, 1099884382659], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850825163, 1099850826187, 1099850827211, 4499942865, 1099817268691, 1099817269715], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8711020025, 4382501369, 1099599163911, 55812, 55816, 1099548905999], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54796, 55820, 37202449, 37203473, 54800, 55824], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [12905253397, 8610355733, 54804, 55828, 4298614297, 1099515350555], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53784, 54808, 55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61323695133, 78201983025, 26545066249, 30571670793, 13458984201, 35235452221], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22384245053, 13173697925, 8845245829, 1100136040839, 1100018601367, 1099985047959], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985114519, 1099934783895, 13224022469, 8828395973, 1099867602375, 1099867603399], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867604423, 4499942861, 1099834045903, 1099834046927, 55804, 4399276545], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [104311297, 1099615940099, 1099615941123, 55808, 55812, 1099532128779], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54792, 55816, 54796, 55820, 34396788241, 1099548904979], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [53776, 54800, 55824, 53780, 54804, 55828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [21478406681, 8593510937, 4298612249, 53784, 54808, 55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61323829281, 65384258613, 26343742749, 21931407645, 9096909085, 30974107969], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22250029377, 22015220033, 8828467597, 1100102485391, 1100085709199, 1100035378575], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934716315, 1099934782875, 1099901229467, 8794911145, 8929057221, 4634158533], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4516720069, 1099850825163, 1099850826187, 1099766937055, 1099766938079, 55800], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17300881917, 8710952445, 1099632717311, 1099632718335, 55804, 1099548905987], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54784, 55808, 54788, 55812, 54792, 55816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532127759, 53772, 54796, 55820, 53776, 54800], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55824, 52756, 53780, 54804, 55828, 4298613273], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [3648025, 1099515349531, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78218554405, 35537729601, 31091551489, 30806478081, 30571670785, 8845249885], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085713247, 13190475133, 8845245821, 1100136040831, 1099951492511, 1099901161887], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901228447, 17518988725, 8895504821, 1099901156799, 1099901157823, 1099901158847], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4499942857, 1099850823115, 1099850824139, 1099548908011, 55796, 25907523065], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [13022693881, 55800, 1099632717311, 1099632718335, 1099548905983, 54780], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55804, 4399276545, 104311297, 54784, 55808, 54788], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55812, 8660687369, 1099548904971, 53768, 54792, 55816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53772, 54796, 55820, 53776, 54800, 55824], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099532126743, 52756, 53780, 54804, 55828, 52760], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53784, 54808, 55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65467938857, 35520952385, 26662435109, 26377295141, 21931405605, 13106661721], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085713243, 1100035377555, 1099985046931, 1099934716307, 1099934782867, 8878797205], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068928919, 1100068929943, 1100068930967, 13224023481, 8828396985, 1099766936031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099766937055, 1099766938079, 1099548908007, 55792, 4432831989, 1099666271735], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55796, 1099548905979, 54776, 55800, 21595847165, 12989141501], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54780, 55804, 54784, 55808, 1099548904967, 53764], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54788, 55812, 53768, 54792, 55816, 4348944909], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53772, 54796, 55820, 1099548903955, 52752, 53776], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54800, 55824, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8593510937, 4298612249, 3648025, 52760, 53784, 54808], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65451295789, 22719939653, 26511443237, 26293477669, 17653284133, 1100068934003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018603379, 1100018669939, 1100052151707, 1100052152731, 1100052153755, 1100001823131], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951492507, 8962613669, 8845241765, 1100001819047, 17451877849, 8861948377], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399279589, 1099733382631, 1099548906991, 55788, 55792, 55796], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099548905979, 54776, 55800, 54780, 55804, 4382500353], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099615940099, 1099615941123, 54784, 55808, 1099548904967, 53764], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54788, 55812, 53768, 54792, 55816, 53772], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54796, 55820, 1099548903955, 52752, 53776, 54800], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55824, 52756, 53780, 54804, 55828, 3647001], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [3648025, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73873461297, 1429723209, 30772924673, 30538117377, 9180795137, 13207318901], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828469621, 1100102487415, 1099934716307, 1099934782867, 1099817343395, 13341462957], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8945836461, 8828464557, 1099951489459, 1099951490483, 1099901159859, 1099867601351], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867602375, 204975593, 1099716604395, 1099716605419, 55788, 55792], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55796, 1099532128763, 54776, 55800, 54780, 55804], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [53760, 54784, 55808, 4382499333, 87534085, 1099548904967], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [53764, 54788, 55812, 53768, 54792, 55816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53772, 54796, 55820, 1099548903955, 52752, 53776], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54800, 55824, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52760, 53784, 54808, 55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65333926965, 26394074385, 26176043281, 4852274449, 13140212085, 1100152818039], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102487415, 1100052156791, 1099884451227, 1099850897819, 9029721513, 8861952425], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4550276521, 1099934711223, 1099934712247, 1099934713271, 1099716605419, 1099716606443], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4432833005, 1099699827183, 55788, 55792, 54772, 55796], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532128763, 54776, 55800, 54780, 55804, 53760], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54784, 55808, 1099548904967, 53764, 54788, 55812], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [53768, 54792, 55816, 53772, 54796, 55820], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [37202449, 37203473, 1099548903955, 52752, 53776, 54800], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55824, 8610356757, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52760, 53784, 54808, 55832], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 2 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤136 ∧ 3+a.j≤57 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group2

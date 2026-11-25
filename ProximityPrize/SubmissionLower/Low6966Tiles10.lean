import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass10

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2332101637, 1057034251, 10201011211, 23657521165, 82580092949, 87094036529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39916157185, 39748657409, 35469791499, 30806608209, 30638909777, 17787636049], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190670813, 8845375965, 8761492957, 1099834184167, 1099834250727, 1099834251751], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21663091205, 13073162757, 34531140105, 21646312969, 1099683186187, 1099683187211], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099683188235, 34480591381, 43053823513, 4365859357, 1099599299103, 4332302889], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3783217, 3784241], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 140 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 140 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 140 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [15083706379, 36106676241, 86925790237, 61424967737, 35554217237, 35336319253], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47835485461, 21847721329, 17737225637, 17552681381, 13207453093, 39178152373], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934846415, 1099934847439, 1099934848463, 1099934915023, 4432969205, 1099767072247], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767073271, 25974764033, 17384902145, 8778263041, 4449744385, 38758783513], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616075291, 1099616076315, 37336617, 37337641, 8610488877, 4298747441], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 140 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 140 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 140 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27868865549, 57213141017, 86976526377, 14499236933, 30974310701, 34967361837], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30571805997, 39513702757, 30856800613, 13140344233, 13341596097, 13173828033], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845375937, 1099951623627, 1099951624651, 1099951625675, 1099951692235, 1099817403883], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817404907, 1099716737539, 1099716738563, 1099716739587, 43120862725, 17351346697], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4466518537, 4416188937, 30118734373, 37335593, 37336617, 42953156145], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8593710641], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 140 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 140 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 140 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36308332561, 82614113309, 57079735353, 35503953169, 31058196753, 39262329105], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21814165861, 1100371056999, 13425482149, 13240936869, 13140343205, 1100018731451], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018732475, 1100018733499, 1100018734523, 38976893413, 4449745381, 1099834180071], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834181095, 4516850173, 4432966141, 21679798785, 13089935873, 1099666405903], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666406927, 70890017, 1099582518819, 34413697573, 8627266089], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 140 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 140 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 140 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [52951596053, 82614382633, 27199586369, 31041351965, 30789832989, 34849992989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39496924521, 30856799593, 13207384469, 8878932377, 1100152950171, 1100152951195], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100152952219, 1100136176027, 13308039629, 8945967565, 8845372877, 1099850957283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850958307, 1099850959331, 1099834178023, 1099834179047, 17351345673, 4382633485], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666404879, 4349076005, 4332300837, 1099565740583, 30101956137, 3779121], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3780145, 1099515484723], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57213274137, 82564120621, 10103607369, 30923981077, 34917032213, 22049047829], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35218737509, 30823312741, 13324820893, 13157052829, 8828600733, 1100119395747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035510711, 1100018734519, 1099985181111, 1099884511707, 1099884512731, 1099884513755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4500074977, 1099850955235, 1099850956259, 17452010981, 8711152137, 4382633481], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099632850455, 25857322525, 17267460637, 70888993, 1099582517795, 8627265065], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37333545, 1099549039147, 1099515483699], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57213408285, 78269221937, 1580849225, 30823386393, 34833214745, 9231257881], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35185251689, 22317267305, 13240937869, 8912485773, 8811825549, 1100001957303], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968399815, 1099968400839, 1099968401863, 1099934915015, 13291262417, 8895635921], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867733471, 1099867734495, 1099867735519, 4516851173, 1099834176999, 1099834178023], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382630429, 87665181, 87666205, 1099599295007, 1099532260911, 55852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [34363364913, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 140 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69846786081, 56945517625, 31125168433, 26612236593, 26360651057, 21864429893], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9029931333, 8845375909, 1100102616487, 1100102617511, 1100102618535, 1100035510707], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985180083, 1099934849459, 13207379393, 8845372865, 1099834178023, 1099834179047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834180071, 21679866365, 8811747837, 4399410689, 1099716736515, 4432963089], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549039131, 87666205, 1099599295007, 1099549038119, 55844, 55848], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55852, 30068400689, 17183572529, 8593643057, 1099515482675, 54832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69846920229, 44127727677, 26830269749, 26545195317, 26293609781, 13291340121], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8929268057, 1100035510703, 1099985180079, 1099934849455, 8962745781, 8845373877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035505591, 1100001952191, 1100001953215, 1100001954239, 1100001955263, 17452009969], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8828526065, 1099767067127, 1099767068151, 1099767069175, 4382632465, 1099549039127], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549038115, 55840, 55844, 37333545, 37334569, 55848], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8610487853, 1099532259887, 54828, 55852, 54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74041292841, 27098923073, 26813561121, 30705947937, 26243282209, 1100203282819], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100152952195, 1100119398787, 8946038165, 8811823509, 1100169727383, 13341595069], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8929191357, 4634292669, 1099934843343, 1099934844367, 1099934845391, 1099800623599], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800624623, 4432963089, 137997841, 1099649626643, 1099649627667, 1099532261911], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21562423837, 12972495389, 1099549038111, 55836, 55840, 55844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099549037099, 54824, 55848, 4315521581, 54828, 55852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74007807021, 14297910341, 26679346461, 26394206493, 26192952605, 8912485765], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100236835207, 1100152950171, 1100102619547, 1100052288923, 1100001958299, 9029853621], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8862084533, 4567185845, 1099901288919, 1099901289943, 17418454521, 8828525049], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4432965113, 1099750290939, 1099750291963, 1099750292987, 1099549039123, 87666205], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599295007, 1099549038111, 55836, 4365854241, 55840, 55844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099549037099, 54824, 55848, 54828, 55852, 54832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73957543985, 1530517577, 30806610197, 26327167253, 13459115285, 8929194397], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828599709, 1100136171935, 1100119395747, 1100069065123, 1100018734499, 1099918137787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535898057, 8895636937, 1099884510683, 1099884511707, 1099884512731, 1099783844339], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783845363, 1099783846387, 4416185877, 121220629, 1099549038111, 55836], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12955718177, 4365853217, 55840, 55844, 1099549037099, 54824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55848, 54828, 55852, 54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61173308469, 1530517577, 22166347057, 26176173361, 9080262961, 13157119381], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169725335, 1100169726359, 1100169727383, 1100035510699, 1099985180075, 1099901360571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8962743769, 8828594649, 1099884508635, 1099884509659, 1099884510683, 1099884511707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382632469, 1099632849431, 55832, 1099549038111, 55836, 55840], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55844, 1099549037099, 54824, 55848, 20556333, 20557357], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54828, 55852, 54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52633774137, 22015420737, 17603084609, 4751742273, 1100085838251, 1100085839275], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085840299, 1100085841323, 1100035510699, 1099951625651, 1099901295027, 8878860741], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4567184837, 1099968396743, 1099683182091, 1099683183115, 4432964109, 137998861], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099532261907, 55832, 1099549038111, 55836, 55840, 55844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549037099, 54824, 55848, 54828, 55852, 3779121], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3780145, 45616, 54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 10 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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
    · exact Top14.exact a ha h14 (by omega) (by omega)
end Low6966Allocation.Group10

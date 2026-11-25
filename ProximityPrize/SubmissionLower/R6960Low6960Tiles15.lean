import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass15

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group15
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2264992773, 1023479817, 14630458379, 36123452429, 86992963609, 70065429557], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35570651395, 43943020833, 35353294113, 43641379105, 26142819705, 43406210485], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21814221257, 17452216777, 8811955669, 8761692629, 1099834383831, 1099649831427], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649832451, 1099649833475, 8677732877, 8661024269, 4349282829, 38725575185], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25840749073, 12905588253, 20761117, 20762141, 4298948129, 4298950177], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 136 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19194320905, 40401972241, 86993163293, 57197307961, 39681676581, 39430159653], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43507164453, 13274763649, 17603208621, 17452218797, 13123767725, 43406208437], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30303485409, 17452211681, 1099784052195, 1099750493675, 1099750494699, 1099750495723], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750496747, 38876355053, 4500208113, 4466721265, 4399614449, 1099599497743], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644178453, 38675241501, 25790415389, 20759069, 20760093], by decide +kernel⟩
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
private theorem i54 : checks (tilesOf batches) 136 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32029811725, 65685832729, 86976726061, 5976610889, 35101705521, 39145089329], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13526356273, 39564166473, 35168742729, 17536100777, 13157252521, 8845577641], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099800828383, 1099800829407, 43204879845, 17435365861, 13106914789, 1099750493675], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750494699, 1099750495723, 4433100269, 4399613421, 4433098241, 1099616273931], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616274955, 30152486413, 17267592717, 71089681, 71090705, 8610620957], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4315656733], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 136 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36358795281, 74175370269, 69880880181, 39564236085, 30890556725, 26377624909], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30454561101, 4869380429, 8912615853, 8811955629, 8761692589, 1099817603547], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817604571, 1099817605595, 1099817606619, 13157244385, 8811949537, 1099767268839], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767269863, 1099767270887, 43154616817, 25924632061, 13039802877, 154909181], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666537983, 1099666604543, 34430606865, 4332432921, 37467673], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i52 : checks (tilesOf batches) 136 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48858151957, 82648067109, 35722542145, 31091813665, 30840294689, 30639041825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13090147721, 1100153150859, 43506875801, 30638893465, 13207580077, 8845508013], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8744847789, 1099935045055, 1099935046079, 1099834378711, 1099834379735, 1099834380759], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17468919261, 13123690973, 1099733646831, 1099733647855, 1099733714415, 4416319997], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666536959, 17217260057, 8627397145, 4332432921, 20690461, 42953358881], by decide +kernel⟩
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
private theorem i55 : checks (tilesOf batches) 136 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57246959641, 86859284525, 10120582217, 30940889365, 30739702037, 30572003605], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39413238125, 30756335981, 13123699089, 8812024209, 13257908665, 8879059385], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8761621945, 1099951824315, 1099884712395, 1099884713419, 1099884714443, 1099867933135], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867934159, 1099767201255, 1099767202279, 1099767268839, 17401811433, 4382765569], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649759747, 30118933013, 8644175381, 37466649, 37467673, 17183773217], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61475017757, 78302974001, 1564204109, 30773186849, 30555156769, 13442470177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39413306721, 26528546145, 13207581081, 8845509017, 1100085972379, 1100018930091], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018931115, 1100018932139, 1099901492679, 13224286669, 8879057357, 1099817533915], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817600475, 1099817601499, 4433098217, 1099750424043, 1099599427087, 1099599428111], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349209109, 54243861, 38692017689, 21512224281, 12922361369, 4298876449], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 136 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65652613153, 65468473401, 26360848693, 26176372021, 4818983221, 35235782985], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26528548169, 13090143641, 1100085972379, 1100086038939, 1100086039963, 1099968600503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968601527, 13190799813, 8811950533, 1099867864527, 1099867865551, 1099867866575], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867933135, 4382765565, 1099666536959, 21612889601, 12989472257, 4349210129], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565872663, 34380276253, 8610618909, 4315654685, 3912225], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69863828517, 48389271613, 31041547577, 26511772985, 22049106233, 17552884049], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8946177361, 1100018931115, 1100018932139, 1100018933163, 4533764525, 1100002085295], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002151855, 1100002152879, 8912611781, 4567315909, 1099901418951, 1099750425067], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750491627, 17401810413, 8811946477, 1099616204299, 1099616205323, 4332432917], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3911201, 3912225], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74058201129, 31343689793, 26813692197, 26511775013, 26276966693, 8862289269], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100237035895, 1100220259703, 8962945441, 8828730785, 1100052416931, 1099951820219], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951821243, 1099951822267, 13190731225, 8879056345, 1099800755679, 1099800756703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800823263, 4382765565, 1099666536959, 54243861, 1099565872663, 25773636129], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4298876449, 3911201, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74024715309, 18542677061, 30907401505, 26394404129, 26193150241, 8879063433], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136304015, 1100136370575, 1100136371599, 1100136372623, 1100119596431, 13207578041], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811951545, 1099851088339, 1099851089363, 1099851155923, 21696775661, 13090135533], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716867571, 1099716868595, 1099716869619, 4399541769, 8593841697, 4298877473], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78219087921, 1497095245, 30857072909, 26377629965, 17737436429, 1100102749591], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102816151, 1100102817175, 1100102818199, 8962945441, 8828730785, 1100052416931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951824311, 17536029133, 8946165197, 1099800755679, 1099800756703, 1099800823263], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399542781, 1099666536959, 37466649, 37467673, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69696330805, 26495065377, 26260257057, 9130726689, 8912615833, 8778401177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100086038939, 1100035708327, 1100035709351, 1100018933159, 1099884643787, 1099884710347], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884711371, 13224353233, 8828726737, 1099750423019, 1099750424043, 1099750425067], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382764557, 87799309, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 15 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group15

import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass6

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2264992773, 1040257033, 4966192137, 22985907213, 86723802133, 87043573809], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1731714125, 31593796781, 39932736733, 39798791389, 52331578589, 31258710277], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34816375109, 26259916189, 17653277085, 17502287261, 8845314485, 8778208693], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767010791, 1099767011815, 8761423341, 4432904685, 1099733458415, 34564562417], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25957925361, 1099699898871, 1099699899895, 1099699900919, 43020203537, 12955656721], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8643981841, 70828561, 1099582457363, 12938878485, 37273113, 42969870877], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [25773441569, 4298682913, 3717665], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10519975947, 27549836301, 69795856409, 86976463917, 5942794313, 39664501021], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31091550493, 30806477105, 39111272753, 13492539697, 17519061409, 13140213153], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845315489, 39094199737, 1099834120663, 1099834121687, 38959978969, 4466458081], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783783907, 1099783784931, 1099783785955, 1099783786979, 1099783788003, 17435101669], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [13123427813, 4483165685, 4449678837, 1099599232527, 1099599233551, 38725307921], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [25823704597, 20493853, 20494877, 8593579553, 4298615329], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27549836301, 52901199897, 86892442665, 22921267269, 35185259801, 35000850713], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34849930521, 39446528353, 30806403425, 13156990353, 8778206625, 1100052224419], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052225443, 13324753333, 13156985269, 8811690421, 39094199737, 1099850894803], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850895827, 1099850896851, 1099834115543, 1099834116567, 17451878881, 4399348205], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733451247, 4466387449, 4382503417, 1099616008715, 1099616009739, 70824465], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [70825489, 30118668821, 38658199073, 8593579553], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36123586577, 78302237725, 65535320121, 35403158797, 35168483597, 34984074509], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26109002053, 1100387769671, 8828469657, 1100085775771, 1100085776795, 1100085777819], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069001627, 13307977125, 13156986277, 8794914213, 43355681209, 21813950929], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13224022481, 1099834116567, 1099817336283, 1099817337307, 1099817338331, 4449611241], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099750159851, 1099750226411, 30168931849, 4382499341, 4348946957, 70824465], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56856, 42969870877, 20425245, 20491805, 56860, 55840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44512525333, 86808487973, 35638393921, 31141882113, 35101444353, 39144828161], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828540277, 17519062393, 17384849785, 39278755213, 30638630285, 1100001886639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001887663, 1100001888687, 1100001889711, 1100001890735, 1099968337331, 1099934783923], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901230515, 17602873781, 13224091061, 4550274509, 4466390477, 1099867667919], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099683116539, 1099683117563, 17300882949, 8677465609, 104311305, 87535117], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099599229455, 56848, 56852, 30101890585, 55832, 56856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8610355741, 55836, 56860, 3647009, 54816, 55840], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52901333017, 82513656877, 18559257669, 30907071753, 34933742857, 30521409801], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35168340321, 26561768801, 13123436921, 1100102554003, 1100069000595, 1100035447187], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985116563, 13291134357, 13173763477, 8811691413, 1099968334263, 1099968335287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867667919, 1099867668943, 1099867669967, 17451878869, 4449611229, 1099800491487], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099800558047, 8727797241, 4382501369, 1099632783879, 56836, 56840], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56844, 70756881, 1099582385683, 55824, 56848, 55828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56852, 17217063449, 54808, 55832, 56856, 4315389469], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [20424221, 54812, 55836, 56860, 25773370913, 53792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54816, 55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61340472349, 82480238641, 30772924677, 34816307461, 9197573381, 35235452225], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26544994625, 17468731765, 8845247861, 1100203217271, 1100001891739, 1099968338331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934784923, 13257577905, 8912348593, 1099968333239, 1099968334263, 1099968335287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4533498301, 1099934710207, 1099934711231, 1099934777791, 1099683049979, 1099683116539], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21629401597, 13039538685, 4399277569, 1099649494531, 56832, 56836], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55816, 56840, 4382499341, 55820, 56844, 54800], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55824, 56848, 34413565461, 54804, 55828, 56852], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54808, 55832, 56856, 20425245, 53788, 54812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55836, 56860, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65551687713, 65384325177, 30554890529, 26142556449, 1100404546851, 31057994033], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22384312625, 26343807281, 8828469629, 1100186439039, 1100152885631, 1100102555007], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069001599, 8828466585, 1099951555003, 1099951556027, 1099951557051, 13207312829], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8811686333, 1099834045911, 1099834046935, 1099834113495, 188197365, 1099699826167], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099699827191, 56824, 56828, 56832, 55812, 56836], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55816, 56840, 17267327501, 8677463565, 4382499341, 54796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55820, 56844, 54800, 55824, 56848, 54804], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55828, 56852, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 30068335137, 52768], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53792, 54816, 55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74007538725, 44060554301, 26863693077, 30772922645, 30538115349, 13207325001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100270328139, 1100219997515, 13224094089, 8845244809, 1100152817035, 1100085774747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068998555, 1100018667931, 1099968337307, 17535764929, 8945900993, 1099884378571], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884445131, 1099884446155, 4483164637, 1099800490463, 1099800491487, 56820], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56824, 56828, 55808, 56832, 55812, 56836], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54792, 55816, 56840, 87534093, 1099599162895, 54796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55820, 56844, 54800, 55824, 56848, 53780], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54804, 55828, 56852, 17217063449, 4332166681, 37201433], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 25790148125, 53788], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54812, 55836, 56860, 52768, 53792, 54816], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78218688553, 26981352517, 30990956805, 30689040645, 26276772101, 1100169663851], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119333227, 1100069002603, 8878799233, 1100186371459, 1100186438019, 1100152884611], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100102553987, 13307910557, 8945904029, 8811689373, 1099884446155, 1099834045911], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834046935, 1099834113495, 21730064869, 13140201957, 56816, 4399278581], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099699827191, 56820, 56824, 55804, 56828, 55808], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56832, 4416053765, 55812, 56836, 54792, 55816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56840, 54796, 55820, 56844, 70756881, 1099582385683], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 53780, 54804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55828, 56852, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 52768], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53792, 54816, 55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
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
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73940567085, 18475371589, 26679280909, 26410918157, 26209664269, 8878800249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100219992443, 1100169661823, 1100119331199, 1100069000575, 1100035447167, 1099985116543], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [9013010857, 8845241769, 1100018596267, 1099917999555, 1099918000579, 1099918001603], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17418323433, 8828459497, 1099750157803, 1099750158827, 1099750159851, 56816], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56820, 56824, 55804, 56828, 55808, 56832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54788, 55812, 56836, 54792, 55816, 56840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54796, 55820, 56844, 4332168721, 53776, 54800], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55824, 56848, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 20424221, 20425245], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 52768], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53792, 54816, 55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73907081265, 5674358857, 26561843465, 26327035145, 21897922825, 1100219926899], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100219993459, 1100169662835, 1100119332211, 8962682257, 8811690385, 1100119328147], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918006679, 1099884453271, 13257576905, 8878793161, 1099884378571, 1099884445131], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884446155, 1099733380591, 1099733381615, 1099733448175, 56816, 56820], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55800, 56824, 55804, 56828, 55808, 56832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54788, 55812, 56836, 54792, 55816, 56840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54796, 55820, 56844, 4365722129, 70756881, 53776], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54800, 55824, 56848, 53780, 54804, 55828], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56852, 53784, 54808, 55832, 56856, 1099532126751], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 52768], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53792, 54816, 55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69595339829, 26478025993, 26259994889, 9113687305, 8895576449, 1100186371459], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186438019, 1100152884611, 1100102553987, 1100018668939, 1099968338315, 1099934784907], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [9029787061, 8862017973, 4516722101, 1099867667919, 1099867668943, 1099733448175], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733449199, 56816, 56820, 4399278585, 1099683049979, 55800], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56824, 55804, 56828, 55808, 56832, 54788], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55812, 56836, 54792, 55816, 56840, 54796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55820, 56844, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53979669, 54046229, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 52764, 53788], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54812, 55836, 56860, 4298612257, 3647009, 52768], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53792, 54816, 55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56811169849, 22032066853, 21847589157, 4768454949, 8811692417, 1100152884611], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102553987, 1100052223363, 1099901229467, 1099867676059, 8912349613, 8761357741], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951555003, 1099951556027, 1099951557051, 1099817268699, 1099817335259, 1099817336283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56816, 56820, 55800, 56824, 4382501373, 87536125], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55804, 56828, 55808, 56832, 54788, 55812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56836, 54792, 55816, 56840, 54796, 55820], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56844, 53776, 54800, 55824, 56848, 53979669], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54046229, 37270037, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 52764, 53788], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54812, 55836, 56860, 45600, 52768, 53792], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54816, 55840, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 6 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group6

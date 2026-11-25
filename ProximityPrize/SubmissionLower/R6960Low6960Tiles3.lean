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
  ⟨unpack [2248215557, 1006702601, 4597027849, 18841869325, 44361134097, 133935553569], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1681382477, 19093722199, 39714905313, 48036611297, 39430042849, 31275356413], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39429615973, 30839888229, 17451955613, 13106661789, 1100052224415, 21964883361], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13375020449, 9046568353, 1099817339351, 1099817340375, 1099817341399, 1099817342423], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21729999329, 4466391521, 1099766940131, 1099767006691, 1099767012835, 1099582388751], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099582455311, 4348947985, 53982737, 17200288281, 4315391513], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i51 : checks (tilesOf batches) 135 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10268252171, 27499504653, 57095503897, 104022046761, 1614273613, 35185260813], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39245421837, 22149580045, 39463240009, 26662365513, 39177951645, 17535770013], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190541725, 8845246877, 1099968335283, 1099968336307, 1099968337331, 1099968338355], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834121683, 21730067925, 1099783717343, 1099783783903, 1099783784927, 4432835049], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733383659, 1099733384683, 8761351669, 4466387445, 38725239309, 70758925], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099582387727, 17216996885, 37198357, 38658054685], by decide +kernel⟩
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
private theorem i54 : checks (tilesOf batches) 135 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23489750029, 52850801685, 108199505961, 5842131017, 35285856497, 43573941489], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22216687857, 35218537809, 26628809041, 17636431241, 13257582985, 8945908105], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018599335, 1100018600359, 1100018666919, 1100018667943, 1100018668967, 1099901229503], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867676095, 21746777553, 1099766938083, 1099766939107, 1099766940131, 4483164645], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099750158823, 1099750159847, 21662737905, 8744506873, 4449608185, 21511962133], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37202453, 37203477, 56852, 56856, 16833052], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [31912439825, 61323628573, 86808693809, 30789700877, 34849860877, 13492539661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35218673981, 22401021245, 17451953541, 13089882501, 1100035445155, 1100001891747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968338339, 1099934784931, 1099934712251, 1099934713275, 1099934779835, 1099934780859], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13291130301, 8912281021, 8828463549, 1099867600331, 1099867601355, 1099867602379], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38993539533, 154642937, 1099666271739, 1099666272763, 56840, 30135376397], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4365721101, 70755853, 56844, 16833040, 16833044, 33609240], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [17183439389, 33609244], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 135 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40318221333, 74007405605, 52633644093, 26846848277, 30789632277, 26394140949], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17569398085, 13207327045, 1100035445143, 1100001891735, 1099968338327, 1099934784919], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39144537509, 1100018597287, 1100018598311, 1100018599335, 1100018600359, 1100018666919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8912282029, 8828464557, 1099985041839, 17552540101, 8962610629, 1099733380587], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733381611, 1099733382635, 4416053757, 137865725, 56828, 56832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833028, 16833032, 33609228, 33609232, 50385428, 25790080537], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385432, 38658129437, 20423196, 50385436], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48673474585, 78252242985, 27014906949, 26695989517, 30672262413, 13576353037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35084454257, 22199692657, 8845247857, 1100119265651, 1100119332211, 1100085778803], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035448179, 13274355105, 8895505825, 4600607137, 1099968267699, 1099934714291], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934780851, 1099951487415, 1099951488439, 1099951489463, 13089801709, 4416054765], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716603375, 1099716604399, 1099716605423, 56816, 56820, 56824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833020, 8711017985, 4382499329, 16833024, 1099532128775, 33609220], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [33609224, 1099582384655, 50385420, 50385424, 50385428, 20423193], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [20424217, 1099532126747, 67161624, 67161628], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 135 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 135 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 135 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52884755485, 78185203761, 9935770697, 30756079877, 30571669765, 9231124741], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30856598881, 22233249121, 8979392897, 8895575425, 1100169593219, 1100152817027], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968337295, 1099934783887, 1099901230479, 1099968268707, 1099968335267, 1099918004643], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13324684717, 8929058221, 1099850823119, 1099850824143, 1099850825167, 4416055777], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099766936035, 56812, 56816, 16833012, 16833016, 33609212], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4416052737, 121087489, 1099632716291, 1099632717315, 33609216, 50385412], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385416, 50385420, 1099548903955, 67161616, 67161620, 21495182873], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8610287129, 20421145, 67161624, 3720732, 83937820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i21 : checks (tilesOf batches) 135 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 135 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 135 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 135 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 135 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65518133281, 65350770745, 30538113305, 26125779225, 1100320595227, 30974042409], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26477887785, 13677010217, 8828469617, 1100102487411, 1100068934003, 1100069000563], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018669939, 8912350605, 1100119259535, 1100119260559, 1099985043887, 1099951490479], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901159855, 17485431253, 8878724565, 1099783712223, 1099783713247, 1099783714271], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532131807, 56804, 4483162601, 1099733379563, 56808, 16833004], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833008, 16833012, 1099532128763, 33609208, 33609212, 1099548904963], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385408, 30168932869, 50385412, 50385416, 1099548903951, 67161612], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [67161616, 67161620, 20423193, 20424217, 1099532125723, 83937816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8593577501, 83937820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i24 : checks (tilesOf batches) 135 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 135 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 135 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 135 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57028930597, 61072581689, 26259924253, 26092224797, 1100270263583, 26595257669], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22132656453, 9314935109, 8845246829, 1100102487407, 1100068933999, 1100069000559], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018669935, 8878796181, 1100085705111, 1100085706135, 1099985043887, 1099934713263], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884382639, 1099548909015, 1099783712223, 1099783713247, 1099783714271, 56800], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [13123357157, 4533426661, 56804, 16833000, 16833004, 16833008], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4432830965, 1099683047927, 1099532128759, 33609204, 33609208, 1099548904959], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385404, 50385408, 50385412, 1099548903947, 67161608, 25840414221], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [67161612, 67161616, 1099548902935, 83937812, 20423193, 20424217], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [83937816, 83937820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65468004393, 39732033601, 26612103461, 22132659493, 17720323365, 17451958597], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828474693, 1099968337283, 1099918006659, 1099884453251, 1100136038795, 1100085708171], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035377547, 1099985046923, 1099985113483, 8794910121, 1100001819051, 1100001820075], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8945833413, 4634157509, 4533496261, 1099783713247, 1099783714271, 56796], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56800, 16832996, 16833000, 16833004, 21662956017, 8778060273], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609200, 33609204, 33609208, 1099532127743, 50385404, 1099632716291], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099632717315, 50385408, 67161604, 1099532126731, 67161608, 67161612], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937808, 1099532125719, 83937812, 20423193, 20424217, 83937816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [3644956, 100714012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69662377005, 22652831813, 26561774865, 26343809297, 13475757329, 1100152819043], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102488419, 1100085777763, 1100052224355, 1100001893731, 8945836445, 8845241757], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052150687, 1100035374499, 1100035375523, 1099985044899, 1099917937059, 17485432273], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4617312721, 56792, 1099783712223, 1099783713247, 1099783714271, 56796], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56800, 16832996, 16833000, 33609196, 1099532128755, 33609200], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4449608181, 1099683047927, 33609204, 50385400, 1099532127743, 50385404], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385408, 1099548903943, 67161604, 67161608, 67161612, 83937808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099532125719, 83937812, 83937816, 12888475165, 3642908, 20423196], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [100714012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61139619889, 18391419973, 26377294117, 21931404581, 9096906021, 1100068933995], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100052223339, 1100018669931, 1099968339307, 8878796181, 1100085705111, 1100085706135], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085707159, 1099985044899, 1099917937059, 1099918003619, 13257576889, 8845173177], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56792, 1099783712223, 1099783713247, 1099783714271, 56796, 56800], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16832996, 16833000, 33609196, 1099532128755, 33609200, 33609204], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4432830969, 1099666270715, 50385400, 50385404, 50385408, 1099548903943], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [67161604, 67161608, 67161612, 83937808, 8627130901, 4332166677], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099532125719, 83937812, 83937816, 3647004, 100714012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65300372533, 1329060941, 26377297161, 26176043273, 4835497225, 8912353645], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203148655, 1100152818031, 1100085710191, 1100052156783, 1099901228431, 1099850897807], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817344399, 9029721501, 8895572381, 1100052149663, 1099917932991, 1099917934015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099917935039, 56792, 56796, 16832992, 16832996, 221751785], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733380587, 1099733381611, 16833000, 33609196, 1099532128755, 33609200], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609204, 1099548904955, 50385400, 50385404, 50385408, 67161604], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4382498313, 87533065, 1099532126731, 67161608, 67161612, 83937808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099548902935, 83937812, 83937816, 83937820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 3 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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

import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass2

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
  ⟨unpack [2264992773, 1006702601, 4597027849, 18741140493, 40166764561, 133901932577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [5925951561, 14815466581, 39748393177, 48053321945, 39446753497, 31292068093], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39345729917, 17468666265, 17384850841, 22015213981, 21813893533, 1099867604431], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867605455, 1099867606479, 1099867607503, 1099867608527, 1099850832339, 1099850833363], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34631604705, 21746777569, 4499878369, 4466391521, 1099783717347, 13073029617], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4499876337, 1099599165967, 1099599166991, 53981717, 53982741, 12888479265], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [3581472], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10066860043, 27432330253, 57061883929, 108266616873, 39413053697, 47768248577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13626691841, 35302424897, 26712630593, 35117668717, 17586037121, 17485444481], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4684499329, 556875165, 1099968270775, 1099968271799, 1099968272823, 1099934719415], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21847441849, 9029720505, 4483102157, 1099867602383, 1099867603407, 1099867604431], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783719395, 1099783720419, 4533429733, 4449545701, 1099666273791, 1099666274815], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [87469581, 87536141, 17233707541, 53909013, 1099532131871, 20358688], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27432330253, 57028329497, 103938095145, 1530321997, 35185195257, 43506834681], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17871325433, 35302359353, 26729407801, 17569258881, 17451889025, 8895579521], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39211509149, 1100052156835, 1100001826211, 1099968272803, 1099834056127, 17586028993], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8979322305, 8727736773, 1099901156807, 1099901157831, 1099867604431, 1099867605455], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099867606479, 8761287137, 1099783646691, 1099750093291, 1099750159851, 1099750160875], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4365656589, 87468557, 56844, 16833040, 16833044, 33609240], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [34379943453, 33609244, 12888404513, 8593511969, 20357664, 33609248], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [31862042641, 57078927389, 91053262897, 39262128385, 43355844865, 1100555476227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30973972809, 22367400265, 17518997861, 17401562469, 1100169599335, 17653139861], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13240737173, 8912285077, 1100068930975, 1100068931999, 1100052155807, 1100001825183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099968271775, 1099951421883, 1099951488443, 1099951489467, 30470648257, 1099766869479], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099766870503, 1099766937063, 4516650477, 4432766445, 56828, 56832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833028, 12989139465, 104241673, 16833032, 33609228, 70690321], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099582319123, 33609232, 50385428, 50385432, 50385436, 21478339105], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [67161632], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44428573717, 69762770981, 52616801341, 30906935585, 30672193825, 17804142881], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21797190977, 8962692417, 35067542905, 26477814137, 1100119195027, 1100119196051], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100119262611, 1100085709203, 1100052155795, 1100001825171, 1099917940127, 1099884386719], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850833311, 13324618165, 8979388853, 8828396981, 1099951419835, 1099951420859], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099951421883, 17401478637, 1099716535795, 1099716536819, 1099716537843, 56816], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56820, 16833016, 16833020, 33609216, 33609220, 50385416], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385420, 50385424, 4348877333, 53912085, 67161620, 67161624], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937820, 4298543649, 83937824], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52817381401, 82463259693, 18492083269, 30873451773, 34900122877, 9331720445], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35168209229, 22367399245, 13274291585, 13156920705, 1100186303875, 1100085710211], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035379587, 1100001826179, 1099968272771, 1099934719363, 1099985043891, 1099968267699], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099917937075, 13291062721, 8912213441, 1099901087175, 1099901088199, 1099901089223], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099901090247, 4483097057, 1099783645667, 56808, 56812, 16833008], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833012, 33609208, 33609212, 50385408, 50385412, 50385416], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [67161612, 34430274065, 4365653521, 4332101137, 1099582318099, 67161616], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937812, 83937816, 20356637, 20357661, 83937820, 100714016], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52851135517, 78168361009, 9918927945, 30772857089, 34799462657, 4969647361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30890087769, 18022102361, 13257582957, 13123369325, 1100186372463, 1099934717323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901163915, 1099867610507, 1099901160871, 1099850830247, 1100018530731, 1100018531755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018598315, 1099968267691, 13341395373, 8945768877, 4634092973, 1099884309963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884310987, 1099884312011, 56800, 56804, 16833000, 16833004], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609200, 33609204, 50385400, 50385404, 1099649426947, 1099649427971], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385408, 4415986181, 121020933, 67161604, 67161608, 67161612], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937808, 83937812, 100714008, 12905253405, 100714012, 30068200993], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [100714016], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57045573665, 73856686133, 30655486209, 26243152129, 9147241729, 26695852357], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22233251141, 13609833797, 8845179253, 1100135974263, 1100119263607, 1100085710199], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035379575, 1099917940107, 1099867609483, 1099834056075, 8945837457, 4600541585], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099968199095, 1099968265655, 1099951489463, 56792, 1099800424927, 1099800425951], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56796, 16832992, 16832996, 1099750090219, 1099750091243, 1099750092267], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833000, 33609196, 33609200, 8744506869, 188129781, 50385396], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385400, 17334369789, 8744505853, 50385404, 67161600, 67161604], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937800, 1099532060175, 83937804, 83937808, 100714004, 100714008], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [20356637, 100714012, 117490208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57028930597, 61038961721, 26259858709, 21864300821, 4785166613, 26595257669], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22099036485, 9264537925, 1100169527671, 1100119197047, 1100119263607, 1100068932983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018602359, 1099985048951, 8861953421, 1100135971215, 1100119195023, 1099834055055], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800501647, 1099850755539, 1099850756563, 1099850757587, 56788, 56792], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [13140068829, 4583758301, 16832988, 16832992, 16832996, 4432765417], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099750091243, 33609192, 33609196, 50385392, 50385396, 50385400], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [67161596, 67161600, 67161604, 1099548837387, 83937800, 21562224141], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [12972295693, 87466509, 1099599095311, 83937804, 83937808, 1099548836375], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [100714004, 100714008, 20354589, 100714012, 3653152, 117490208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61206525993, 43976602685, 26544929069, 22099105069, 17686768941, 17485447477], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8895583541, 1100119196035, 1100102485379, 1100052154755, 1100001824131, 1099951493507], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099917940099, 1099867609475, 1099834056067, 4550208937, 1100018529707, 1100018530731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001754539, 8912213445, 4600537541, 1099901086151, 56784, 56788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16832984, 16832988, 16832992, 33609188, 21679667689, 8828391913], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099750092267, 1099750093291, 33609192, 50385388, 50385392, 50385396], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [67161592, 67161596, 67161600, 83937796, 83937800, 83937804], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [70689297, 1099582318099, 100714000, 53911061, 1099532059159, 100714004], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [100714008, 17200151069, 20352541, 117490204, 3653152, 117490208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61156262957, 31175589953, 26477888805, 22015222053, 13391804709, 13089818957], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085713231, 1100035382607, 1100052154755, 1100001824131, 1099951493507, 1099901162883], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052085155, 1100035308963, 1100018598307, 1099968267683, 8895504809, 4550208937], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018529707, 56780, 13223953873, 8912278993, 56784, 56788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16832984, 16832988, 33609184, 33609188, 1099750092267, 1099750093291], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609192, 50385388, 50385392, 4399210997, 1099699759607, 50385396], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [67161592, 67161596, 67161600, 83937796, 83937800, 83937804], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [70689297, 1099582318099, 100714000, 100714004, 100714008, 117490204], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4298544673, 3579424, 3653152, 117490208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65350635569, 14113230921, 26427560209, 26209529105, 4885760273, 1100018602355], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099968271731, 1099917941107, 1099884387699, 8945839485, 8811624829, 1100119262591], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099917937059, 1099867606435, 13240734129, 8878727601, 1099968199095, 1099968265655], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934712247, 56780, 56784, 1099833978327, 1099833979351, 1099833980375], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16832980, 16832984, 16832988, 33609184, 33609188, 33609192], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [50385388, 50385392, 50385396, 4399211001, 1099682982395, 67161592], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [67161596, 67161600, 83937796, 8694174217, 4382432777, 83937800], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937804, 100714000, 1099565540887, 100714004, 100714008, 117490204], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [20356640, 117490208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65300372533, 1295440973, 26377297161, 26176043273, 4835497225, 8878733677], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100135974255, 1100136040815, 1100085710191, 1100035379567, 1099800501639, 1099850831247], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099800500623, 9029721501, 8861952413, 1100068861343, 1099968199095, 1099968265655], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951489463, 56780, 56784, 16832980, 16832984, 16832988], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783645667, 1099783646691, 1099783647715, 33609184, 33609188, 33609192], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [50385388, 50385392, 50385396, 67161592, 67161596, 67161600], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099548837383, 83937796, 4399209993, 104244745, 83937800, 83937804], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [100714000, 100714004, 100714008, 100714012, 117490208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 2 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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

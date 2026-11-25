import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass12

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2281769989, 1006702601, 14613681163, 28020057101, 86908944409, 74309997621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35604205823, 44026839309, 39648193805, 26427954541, 26277032301, 13408914797], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845505001, 8761621993, 4483500521, 1099750494703, 1099750495727, 1099750496751], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34531339773, 21646512637, 12989475341, 43037245969, 4366056981, 4332504597], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565944347, 20760097, 20761121], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 137 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 137 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 137 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19177543689, 40385195025, 86976386077, 52935895097, 39664899361, 39430159649], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43507164449, 8996573577, 17603208617, 17452218793, 13123767721, 43439762865], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26075626973, 17485765085, 1099784048103, 38909909481, 4500208109, 4466721261], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750492655, 1099750494703, 1099750495727, 1099750496751, 8677731857, 38725573141], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54313497, 1099565942299, 4315724321], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 137 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 137 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 137 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [28003279885, 57230049305, 86976657449, 14532987973, 35168745773, 34967559469], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26327367981, 39446790505, 30856997225, 8828731829, 17519320513, 13140472257], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867934163, 1099867935187, 1099867936211, 1099867937235, 21679999473, 4399612401], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733715443, 4449874433, 154909185, 154975745, 1099616272911, 1099616273935], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12939141653, 42953352741, 21478738469, 8593842725, 4298878501], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 137 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 137 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 137 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36342018065, 78403228701, 61341278265, 35437040933, 35168745765, 34967559461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26092487005, 8828731821, 8761691565, 1100018932143, 13325016505, 8962944441], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845507001, 1099834379739, 1099834380763, 1099834381787, 26025294313, 17401877993], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767268843, 1099767269867, 43188171245, 1099700091387, 1099700157947, 1099700158971], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365987349, 71022101, 12905584161, 8593843749], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 137 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 137 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 137 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48841374741, 82631289893, 31461129281, 31091813661, 30840294685, 30639041821], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845577617, 1100136372627, 39262240149, 30672446869, 13207580073, 8845508009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8778467753, 1099867936211, 17502473689, 8912609753, 1099834378715, 1099834379739], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834380763, 1099767201259, 1099767267819, 1099767268843, 4466650617, 4382766585], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599427091, 1099599493651, 17250813461, 3911205, 3912229], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 137 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 137 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 137 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48875128857, 82597804073, 18643339333, 35185522969, 30739701017, 30555225369], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13140475281, 39211977121, 30555074977, 1100052483495, 1100052484519, 1100052485543], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052486567, 13274684861, 8895835581, 8778398141, 1099867932115, 1099867933139], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17418588641, 1099750423023, 1099750489583, 1099750490607, 4382764553, 1099632981515], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25823965721, 17234103833, 8627397149, 20688417, 20689441], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 137 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 137 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 137 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61458240541, 78286196785, 30773186845, 30555156765, 9214611741, 39413306717], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26528546141, 13207581077, 8845509013, 1100119592343, 1099985375671, 1099985376695], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985377719, 13224286665, 8879057353, 1099851153879, 1099851154903, 1099851155927], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783976423, 1099783977447, 1099783978471, 4382763537, 87798289, 38725572117], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21545778709, 12955915797, 4332430877], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 137 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 137 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 137 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 137 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 137 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69880537121, 56945648697, 35286114617, 26578879801, 26327294265, 21864627525], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4802270533, 8795176357, 1100052482471, 1100052483495, 1100052484519, 9013273025], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8862281153, 4516985281, 1099935045059, 1099935046083, 1099834376667, 1099834377691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700091387, 1099700157947, 21629666813, 8761613821, 4382764549, 1099649758727], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34413830681, 37465629, 37466653, 17183704613, 8593840677], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 137 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 137 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 137 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 137 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78319545381, 35621877825, 31125368089, 30823517465, 30571932953, 13090147697], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13241134485, 8862285205, 1100119525783, 1100052483495, 1100052484519, 1100052485543], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052486567, 17536028113, 8946164177, 1099834310107, 1099834376667, 1099834377691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4483427821, 1099750421999, 1099750423023, 30118931993, 37465629, 37466653], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69813565481, 31360465985, 26746583345, 26478286129, 22032396593, 8862288249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100237034875, 1100237035899, 8845504953, 1099968527803, 1099968528827, 1099968595387], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951819199, 1099951820223, 1099951821247, 13190731229, 8845501917, 188461561], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700090363, 1099700091387, 25807190557, 4332430877, 37465629], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78252573741, 10053472329, 30940955921, 30655816977, 21998847249, 8795178385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13291464097, 8895837601, 1100069192099, 1100035707307, 1100035708331, 1100035709355], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918263751, 1099918264775, 1099918265799, 21747107301, 13106912741, 1099750421999], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750423023, 1099750489583, 4382764549, 8627396125, 4332431901, 37466653], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78219087921, 30840295693, 30588711181, 9231388941, 13224358285, 8845509005], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153146767, 1100035707307, 1100035708331, 1100018932139, 17536029129, 8946165193], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884642767, 1099884709327, 1099884710351, 4483428833, 1099800754659, 1099800755683], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [87798289, 1099599427091, 17200550433, 4315653665, 20688417, 55844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65434917941, 26444733737, 26209925417, 4852536617, 8912615829, 1100119524759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119525783, 1100119592343, 1100119593367, 1100002153907, 1099985377715, 13224353229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828726733, 1099783977447, 1099783978471, 1099784045031, 4382764553, 1099632981515], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8610618913, 4315654689, 20689441, 55844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52650682425, 21998774597, 17586438469, 4768716101, 1100035637675, 1100035638699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035705259, 1100035706283, 1100035707307, 1099968599483, 1099968600507, 8912611781], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4567315909, 1099918196167, 1099632981515, 1099633048075, 4365986325, 71021077], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 12 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group12

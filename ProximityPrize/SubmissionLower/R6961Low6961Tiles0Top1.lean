import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass0

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2197883909, 704712713, 4496364553, 4412480525, 30350451725, 82126390297], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [100736045, 13439017005, 1294636085, 1261082677, 1261149237, 1227595833], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1194042425, 1194108985, 402723901, 167843901, 1160555581, 1143779389], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1127003197, 1093449793, 1076673601, 1076740161, 1059963973, 1043187781], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1026411589, 9496370249, 1026478153, 1227805769, 623827017, 607050829], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [31039434837, 1099730458731, 1101057511579, 1101057512603, 1101057513627, 1101057514651], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1101057515675, 1101057713307, 1101057714331, 1101024226459, 1101024227483, 1101024294043], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [69158402201, 35736786081, 40115769525, 34715057377, 1100571375879, 1100571376903], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100571377927, 1100571444487, 1100571445511, 1100554669319, 1100554670343, 4767865145], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099984457023, 1100352993603, 1100352994627, 1100352995651, 1100352996675, 1100352997699], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100352998723, 1100018010435, 1099850240323, 1100169002311, 1100101894471, 1100051563847], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100219332939, 1100286440783, 17384257869, 1100252885331, 1100303150423, 1100202485083], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100202486107, 1100168929635, 1100152150375, 1100152151399, 1100118529391, 17535179117], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8827950449, 4432249217, 4348430741, 36688277, 8760765857, 4415469985], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [3133857, 86950309, 87016869, 53463461, 19910053, 3133860], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [3133864, 3133868, 87020973, 36690349, 3136940, 3132848], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [3133872, 3136944, 3131829, 3132852, 3133876, 3136948], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [3132856, 3133880, 3135928, 3136952, 53461437, 19908029], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [3131836, 3132860, 3133884, 3135932, 3136956, 86948289], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53394881, 3131840, 3132864, 3133888, 3135936, 3136960], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [3131844, 3132868, 3133892, 3134916, 3135940, 3136964], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [3130824, 3131848, 3132872, 3133896, 3134920, 3135944], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [3136968, 103724493, 3130828, 3131852, 3132876, 3133900], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [3134924, 3135948, 3136972, 36683217, 3130832, 3131856], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [3132880, 3133904, 3134928, 3135952, 3136976, 3129812], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [3130836, 3131860, 3132884, 3133908, 3134932, 3135956], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [3136980, 3129816, 3130840, 3131864, 3132888, 3133912], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [3134936, 3135960, 3136984, 3128797, 3129820, 3130844], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [3131868, 3132892, 3133916, 3134940, 3135964, 3136988], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [3129824, 3130848, 3131872, 3132896, 3133920, 3134944], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [3135968, 3136992, 3128804, 3129828, 3130852, 3131876], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [3132900, 3133924, 3134948, 3135972, 3136996, 3128808], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [3129832, 3130856, 3131880, 3132904, 3133928, 3134952], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [3135976, 3137000, 3128812, 3129836, 3130860, 3131884], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [3132908, 3133932, 3134956, 3135980, 3137004, 120499697], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [3128816, 3129840, 3130864, 3131888, 3132912, 3133936], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [3134960, 3135984, 3137008, 36681205, 3127796, 3128820], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [3129844, 3130868, 3131892, 3132916, 3133940, 3134964], by decide +kernel⟩
private def p38 : P :=
  ⟨unpack [3135988, 3137012, 3127800, 3128824, 3129848, 3130872], by decide +kernel⟩
private def p39 : P :=
  ⟨unpack [3131896, 3132920, 3133944, 3134968, 3135992, 3137016], by decide +kernel⟩
private def p40 : P :=
  ⟨unpack [3127804, 3128828, 3129852, 3130876, 3131900, 3132924], by decide +kernel⟩
private def p41 : P :=
  ⟨unpack [3133948, 3134972, 3135996, 3137020, 21544996353, 4365133313], by decide +kernel⟩
private def p42 : P :=
  ⟨unpack [3126785, 3127808, 3128832, 3129856, 3130880, 3131904], by decide +kernel⟩
private def p43 : P :=
  ⟨unpack [3132928, 3133952, 3134976, 3136000, 3137024, 43002981893], by decide +kernel⟩
private def p44 : P :=
  ⟨unpack [53457413, 3127812, 3128836, 3129860, 3130884, 3131908], by decide +kernel⟩
private def p45 : P :=
  ⟨unpack [3132932, 3133956, 3134980, 3136004, 3202564, 3126792], by decide +kernel⟩
private def p46 : P :=
  ⟨unpack [3127816, 3128840, 3129864, 3130888, 3131912, 3132936], by decide +kernel⟩
private def p47 : P :=
  ⟨unpack [3133960, 3134984, 3136008, 3202568, 77329021453, 3126796], by decide +kernel⟩
private def p48 : P :=
  ⟨unpack [3127820, 3128844, 3129868, 3130892, 3131916, 3132940], by decide +kernel⟩
private def p49 : P :=
  ⟨unpack [3133964, 3134988, 3136012, 3202572, 3126800, 3127824], by decide +kernel⟩
private def p50 : P :=
  ⟨unpack [3128848, 3129872, 3130896, 3131920, 3132944, 3133968], by decide +kernel⟩
private def p51 : P :=
  ⟨unpack [3134992, 3136016, 3202576], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40, p41, p42, p43, p44, p45, p46, p47, p48, p49, p50, p51]
private theorem i3 : checks (tilesOf batches) 132 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 132 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 132 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤55) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1
end Low6961Allocation.Group0

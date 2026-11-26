import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass3
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2315324421, 1040257033, 4613805065, 18673966093, 86622810129, 87026664493], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [5959440457, 19026547803, 35754881217, 39865701569, 52398488769, 31308845317], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34833019197, 9231062333, 22098967953, 21914490257, 17552485777, 8828338609], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8778075569, 1099867544027, 1099867545051, 1099833986531, 1099833987555, 1099833988579], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34648249829, 21780265445, 4516589037, 4432705005, 1099783650799, 1099783651823], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099783652847, 1099783653871, 13089740285, 8727668221, 38775435793, 1099632653843], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099632654867, 4348814881, 37072421, 37073445, 12905189929, 30068136493], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [9932576779, 27415487501, 82479300633, 82681434161, 35570598125, 35403097325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43657627885, 34782688565, 4936096053, 35302086989, 34983656857, 17736960409], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13341334937, 13240741273, 13106527645, 13039488413, 1099951427015, 1099951428039], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951429063, 1099867544019, 1099833990611, 1099884248535, 1099884315095, 1099884316119], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884317143, 26058384873, 17468522985, 4432702961, 1099766806003, 1099766807027], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8710888969, 4382370313, 25890611729, 1099615810071, 8643778081, 53848609], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099565477411, 56864, 56868, 4315259433, 55848, 56872], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27415487501, 52833959961, 86858757161, 22870804549, 30957270289, 34967098641], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34849798417, 35285582161, 26645456209, 13156858249, 13039487381, 1100052093335], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018539927, 39278552473, 13324555685, 13207184805, 8845112741, 1099984980415], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984981439, 1099951428031, 1099917874623, 1099917869519, 1099917870543, 1099817137639], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817138663, 1099817205223, 17451745769, 4466255349, 1099750026743, 1099750027767], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8710886929, 4382368273, 56848, 56852, 55832, 56856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55836, 56860, 1099565476387, 54816, 55840, 56864], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [25806792229, 54820, 55844, 56868, 20292137, 20293161], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 12888343085, 8593445421], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40099590161, 86774667297, 52683844669, 31225501941, 35201906933, 43473149173], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21730019665, 35168072045, 30873310573, 17602747765, 17485377909, 13123306869], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052092307, 1100018538899, 1099984985491, 1100035311027, 1100035312051, 1100001758643], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951428019, 17636227521, 13274222017, 4516590017, 1099968133571, 1099968134595], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099968135619, 8811552221, 4483033565, 1099733250555, 1099733251579, 56836], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56840, 21612492301, 1099649362447, 1099649363471, 55820, 56844], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55824, 56848, 4382367253, 104179221, 54804, 55828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56852, 54808, 55832, 56856, 53788, 54812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55836, 56860, 8643776033, 4348811809, 53792, 54816], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55840, 56864, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 3514925], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48606034965, 82513390629, 35587931201, 31024311553, 30789569793, 30621871361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35235249501, 26628677981, 8845118825, 1100135979371, 1100102425963, 13173632393], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828337545, 1100119132555, 1099984981419, 1099951428011, 1099901097387, 13307776433], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8928927153, 8845109681, 1099951357383, 1099951358407, 1099951424967, 1099901023699], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099901024723, 17468521961, 1099766802931, 1099766803955, 1099766804979, 56824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56828, 55808, 56832, 4432698885, 1099682915847, 55812], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56836, 54792, 55816, 56840, 54796, 55820], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56844, 54800, 55824, 56848, 53780, 54804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55828, 56852, 8677331481, 53784, 54808, 55832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56856, 1099531995679, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56860, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [20291113, 20292137, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55848, 56872, 25773236781, 51756, 52780, 53804], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52834093081, 86724607021, 14230605897, 35134799093, 39178248437, 22032009461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35184920913, 22400888145, 17518862709, 13173634421, 8811562357, 1100018536847], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099984983439, 1099951430031, 1099917876623, 1099968136623, 1099968203183, 1099934649775], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13408437681, 13207115185, 1099984909759, 1099984910783, 1099984911807, 1099951358399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4566918601, 1099934576075, 1099934577099, 56816, 56820, 55800], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56824, 55804, 56828, 8727664129, 188064257, 54784], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55808, 56832, 54788, 55812, 56836, 53768], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54792, 55816, 56840, 1099649361423, 1099649362447, 53772], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54796, 55820, 56844, 53776, 54800, 55824], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56848, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [34446985753, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099548771871, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56860, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56864, 4332033573, 37068325, 51748, 52772, 53796], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54820, 55844, 56868, 1099531993643, 50728, 51752], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 50732], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52867847197, 86691121201, 1396038733, 35034138865, 34866506993, 13492408561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30906799453, 22233118045, 13257518445, 8895446381, 1100169464175, 1100135910767], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035314055, 1099984983431, 1099951430023, 13408439701, 9029590421, 8912218517], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817213343, 1100001689019, 1099951358395, 1099951424955, 1099934578123, 1099934579147], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817134567, 1099817135591, 1099817136615, 56808, 56812, 55792], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56816, 55796, 56820, 54776, 55800, 56824], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54780, 55804, 56828, 4432698881, 1099699693059, 54784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55808, 56832, 1099531996679, 53764, 54788, 55812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56836, 53768, 54792, 55816, 56840, 1099548772879], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 52752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 21562160661, 8694107669], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4399143445, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [37069349, 1099548770855, 50724, 51748, 52772, 53796], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54820, 55844, 56868, 30084912681, 50728, 51752], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 17183307309], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [12888410669, 50732, 51756, 52780, 53804, 54828], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65501224993, 65350639673, 26310123801, 26142424345, 4818655513, 26846716197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26544864549, 26326898981, 8845114741, 1100119132535, 1100119199095, 1100068868471], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035315063, 1099833989531, 1099800436123, 1100119127455, 1100119128479, 8979257773], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8861885869, 1100052017583, 1100001689015, 1099951358391, 1099951424951, 17502076385], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8878592481, 56800, 56804, 55784, 56808, 55788], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56812, 1099766801907, 1099766802931, 1099766803955, 55792, 56816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54772, 55796, 56820, 54776, 55800, 56824], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 53760, 54784], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55808, 56832, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099548772875, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4382367245, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 51732], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 51736], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 51740], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 1099548770851], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [56864, 37068325, 37069349, 50724, 51748, 52772], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 25789948457, 8610222633], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56872, 1099515215407, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65467739173, 52516072509, 26729344289, 26461047073, 22015157537, 21830679849], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8962561321, 1100203015555, 1100152684931, 1100102354307, 1100052023683, 1100052090243], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001759619, 1099951428999, 1099901098375, 1099867544967, 8895440293, 1100085572007], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100085573031, 1100085574055, 13274221001, 8861817289, 56796, 56800], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55780, 56804, 55784, 56808, 55788, 56812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099766801907, 1099766802931, 1099766803955, 54768, 55792, 56816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54772, 55796, 56820, 53752, 54776, 55800], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56824, 53756, 54780, 55804, 56828, 53760], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54784, 55808, 56832, 1099548772871, 52740, 53764], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54788, 55812, 56836, 21629267465, 13039339017, 52744], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 4432697869, 137732621], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 1099548771859], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099548770847, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55836, 56860, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [54816, 55840, 56864, 50724, 51748, 52772], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 4315256361, 1099531992619], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [49704, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [55848, 56872, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65451096105, 39731902529, 26611972385, 26343609633, 21914497313, 13156862277], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169533767, 1100119203143, 1100018469259, 1100018535819, 1099968205195, 1099917874571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845111693, 1100152683919, 1100102353295, 1100052022671, 9046365613, 8912216493], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4566920621, 1099917800911, 1099917801935, 56792, 56796, 56800], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55780, 56804, 55784, 56808, 17451743725, 8861814253], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54764, 55788, 56812, 1099766803955, 1099766804979, 54768], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55792, 56816, 54772, 55796, 56820, 53752], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54776, 55800, 56824, 4399145469, 1099716471295, 53756], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54780, 55804, 56828, 53760, 54784, 55808], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56832, 1099548772871, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56836, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 1099548771859], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [87400985, 1099599029787, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55832, 56856, 4365589021, 1099548770847, 50716, 51740], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 50720], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56868, 1099531992619, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 49708, 50732], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21]
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
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82396152877, 9868530761, 30890165485, 30655423725, 26243089645, 8828339553], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119200099, 13223896445, 8878667133, 1100169462143, 1099968206207, 1099917875583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884322175, 1099984913823, 1099968203167, 1099917872543, 17585964469, 8962480565], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951355335, 1099951356359, 1099917802951, 4533364177, 1099901021651, 1099901022675], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56792, 56796, 55776, 56800, 55780, 56804], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55784, 56808, 54764, 55788, 56812, 54768], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55792, 56816, 53748, 54772, 55796, 56820], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 53756, 54780], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55804, 56828, 52736, 53760, 54784, 55808], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56832, 52740, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 1099649361423], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099649362447, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56844, 4415920657, 120955409, 1099548771859, 51728, 52752], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 51732, 52756], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 12972230169, 4382365209], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099548770847, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55836, 56860, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54816, 55840, 56864, 50724, 51748, 52772], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 1099531992619, 49704], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [56872, 49708, 50732, 51756, 52780, 53804], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82362667057, 35034206441, 34799400169, 4936030441, 13257520469, 13106529621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119201111, 1099884321159, 1099833990535, 13425217933, 13207118221, 8861888909], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052022671, 1100001692047, 1099984981391, 1099934650767, 1100001689011, 1099951358387], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901022675, 1099901023699, 1099901024723, 56788, 56792, 4550140381], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099850688991, 1099850690015, 56796, 55776, 56800, 55780], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56804, 54760, 55784, 56808, 54764, 55788], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56812, 54768, 55792, 56816, 53748, 54772], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55796, 56820, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 52736, 53760], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54784, 55808, 56832, 1099531995655, 52740, 53764], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54788, 55812, 56836, 52744, 53768, 54792], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55816, 56840, 51724, 52748, 53772, 54796], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55820, 56844, 8710885905, 4399144465, 1099548771859, 51728], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 51732], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 51736], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 1099582252575], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099548770847, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55836, 56860, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54816, 55840, 56864, 50724, 51748, 52772], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 1099531992619, 49704], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [56872, 3513901, 3514925, 49708, 50732, 51756], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69544877109, 26427497725, 26243086589, 9113556221, 8895445361, 1100169463155], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119132531, 1100068801907, 1100052091251, 1099951428991, 1099917875583, 1099867544959], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [9012813213, 8895441309, 1100119127455, 1099984910783, 1099968134591, 1099901026751], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56788, 56792, 56796, 55776, 56800, 55780], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56804, 1099800357355, 1099800358379, 1099800359403, 54760, 55784], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56808, 54764, 55788, 56812, 54768, 55792], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56816, 53748, 54772, 55796, 56820, 1099531996667], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 53756, 54780], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55804, 56828, 52736, 53760, 54784, 55808], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56832, 4449476101, 154510853, 1099531995655, 52740, 53764], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54788, 55812, 56836, 52744, 53768, 54792], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55816, 56840, 51724, 52748, 53772, 54796], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55820, 56844, 1099548771859, 51728, 52752, 53776], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54800, 55824, 56848, 51732, 52756, 53780], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54804, 55828, 56852, 51736, 52760, 53784], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54808, 55832, 56856, 1099548770847, 50716, 51740], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 50720], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56868, 49704, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54824, 55848, 56872, 3513901, 3514925, 42540], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [1099515215407, 49708, 50732, 51756, 52780, 53804], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [54828, 55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56760707129, 22015158553, 21847458073, 4768323865, 1100219793783, 1100152685943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102355319, 1100102421879, 1100035314039, 1100001760631, 1099850766735, 1099800436111], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895441309, 1100119127455, 1100119128479, 1100102352287, 56788, 56792], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56796, 55776, 56800, 55780, 56804, 221620713], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [154512873, 104182249, 55784, 56808, 54764, 55788], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56812, 54768, 55792, 56816, 53748, 54772], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55796, 56820, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 53760, 54784], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55808, 56832, 45572, 1099548772871, 52740, 53764], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54788, 55812, 56836, 45576, 52744, 53768], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54792, 55816, 56840, 45580, 52748, 53772], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54796, 55820, 56844, 44560, 45584, 1099548771859], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [44564, 45588, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55828, 56852, 44568, 45592, 51736, 52760], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 44572, 45596], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56860, 43552, 44576, 45600, 1099548770851, 50720], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [43556, 44580, 45604, 50724, 51748, 52772], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 43560, 44584], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [45608, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [55848, 56872, 43564, 44588, 45612, 1099515215407], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [49708, 50732, 51756, 52780, 53804, 54828], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [55852, 56876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24]
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 3 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group3

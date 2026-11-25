import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass1

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group1
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2348878853, 822153225, 4546696201, 22314490893, 86505436181, 87110486065], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10520106059, 1647631437, 27080930473, 35318878377, 73889969321, 22970110161], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [27047373017, 30454103381, 35084399997, 26310056317, 21864166781, 17870901649], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13508896145, 1100051959223, 1100052025783, 1100052026807, 1100052027831, 1099901033947], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8777938397, 1099884184031, 1099884185055, 1099884186079, 21813544421, 13106387457], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8761158145, 30235699725, 1099682854415, 1099682855439, 1099682856463, 8643569193], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [34413441577, 17216869933, 4331973165, 37007917], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i3 : checks (tilesOf batches) 141 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 141 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 141 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 141 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 141 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 141 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 141 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [9328465929, 22851953677, 65232124949, 87060085805, 14381469769, 23053998269], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22836559065, 30923379929, 48271226073, 34832885061, 21880949061, 26678669657], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17736684969, 9163598249, 1100102289835, 1100085513643, 1100052025779, 1100001695155], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099968141747, 1099934588339, 13223830969, 13089682873, 1100035179963, 30487508433], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17535571409, 1099817072111, 1099817073135, 1099817074159, 1099817075183, 4449413645], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099682853391, 56856, 56860, 17266986529, 55840, 56864], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55844, 56868, 12938679849, 4348749353, 54824, 55848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56872, 54828, 55852, 56876, 12904981041, 54832], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55856, 56880, 25773027893, 34363109941, 3452469, 1099515153975], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53812, 54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i6 : checks (tilesOf batches) 141 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 141 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 141 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 141 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 141 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 141 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 141 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [22851953677, 48270359573, 86640520229, 31427117121, 30755744985, 52281052377], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22668852493, 22400619789, 26695378265, 13391457665, 26528087425, 13123240329], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100102291851, 1100068738443, 1100068805003, 1100035251595, 17720121741, 17485245837], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984847303, 1099984848327, 1099951294919, 1099900964295, 8777936345, 1099900959195], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099900960219, 17468315117, 8895228397, 30302959101, 1099699629579, 1099699630603], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099699631627, 56840, 56844, 13005789713, 4382304785, 1099531933203], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55824, 56848, 55828, 56852, 1099548709403, 54808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55832, 56856, 54812, 55836, 56860, 54816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55840, 56864, 1099548708391, 53796, 54820, 55844], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56868, 53783081, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [21511619117, 53804, 54828, 55852, 56876, 8610159153], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4315194929, 1099531930163, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56880, 12888201781, 52788, 53812, 54836, 55860], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i9 : checks (tilesOf batches) 141 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 141 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 141 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 141 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 141 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 141 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [39747203089, 82278242337, 57012299833, 30906603717, 48237672645, 26846310681], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [18323688729, 21931206997, 17535648085, 8895386965, 13458497937, 30755877265], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951363491, 1099901032867, 1099867479459, 1100085510575, 1100051957167, 1100001626543], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951295919, 1099951362479, 17636233653, 13156722101, 1099984844231, 1099984845255], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099984846279, 4516521465, 1099766738427, 1099766739451, 56824, 56828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55808, 56832, 55812, 56836, 55816, 56840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54796, 55820, 56844, 54800, 55824, 56848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54804, 55828, 56852, 1099531931163, 53784, 54808], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55832, 56856, 25873625629, 8693899805, 4398935581, 53788], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54812, 55836, 56860, 52768, 53792, 54816], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55840, 56864, 12955390501, 4365525541, 1099531930151, 52772], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 52776, 53800], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54824, 55848, 56872, 17216654893, 51756, 52780], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 20228657, 1099531929139], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51760, 52784, 53808, 54832, 55856, 56880], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51764, 52788, 53812, 54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i12 : checks (tilesOf batches) 141 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 141 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 141 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 141 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 141 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 141 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44042501141, 82278443045, 39882831937, 30806075593, 48069970121, 22652140829], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22316733725, 13257455977, 13106465129, 1100051962219, 1100052028779, 13374680445], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26494532989, 17636235665, 13173501329, 1100001626531, 1099951295907, 1099900965283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901031843, 1099984846279, 1099951292871, 1099900962247, 4499746265, 1099900958171], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099900959195, 17485092329, 8895228393, 1099531934191, 56812, 56816], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30319736309, 55796, 56820, 55800, 56824, 55804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56828, 8794642945, 4449412609, 1099548709379, 54784, 55808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56832, 54788, 55812, 56836, 54792, 55816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56840, 1099682852367, 1099682853391, 1099548708367, 53772, 54796], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55820, 56844, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 1099548707355, 52760], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 52764, 53788], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54812, 55836, 56860, 52768, 53792, 54816], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55840, 56864, 1099548706343, 51748, 52772, 53796], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54820, 55844, 56868, 53782057, 1099565410859, 51752], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 8626935341], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [1099531928115, 50736, 51760, 52784, 53808, 54832], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55856, 56880, 17183168053, 4298271285, 30068142645, 12888347189], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [4298416693, 50740, 51764, 52788, 53812, 54836], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]
private theorem i15 : checks (tilesOf batches) 141 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 141 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 141 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 141 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 141 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 141 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44093098009, 82647610409, 27014710341, 31091356965, 26494539045, 26226176293], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22417328429, 17971503405, 1100119068019, 1100068737395, 1100018406771, 1100018473331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968142707, 8912155029, 1100186172823, 1100135842199, 1100068734359, 1100018403735], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13223826901, 8811488725, 56800, 1099850625511, 1099850626535, 1099850627559], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56804, 56808, 13123019245, 30370066925, 1099548710383, 55788], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56812, 55792, 56816, 55796, 56820, 1099531932155], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54776, 55800, 56824, 54780, 55804, 56828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 1099531931143, 53764], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54788, 55812, 56836, 53768, 54792, 55816], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56840, 4382303757, 1099682852367, 52748, 53772, 54796], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55820, 56844, 21629061649, 1099548707347, 52752, 53776], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54800, 55824, 56848, 52756, 53780, 54804], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55828, 56852, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56856, 12988944925, 1099548706335, 51740, 52764, 53788], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54812, 55836, 56860, 51744, 52768, 53792], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54816, 55840, 56864, 70559269, 1099582188071, 51748], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 8643568169], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [4348603945, 4348748329, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54824, 55848, 56872, 1099531928111, 50732, 51756], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 50736], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [51760, 52784, 53808, 54832, 55856, 56880], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [49716, 50740, 51764, 52788, 53812, 54836], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22]
private theorem i18 : checks (tilesOf batches) 141 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 141 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 141 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 141 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 141 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52532237341, 82547083313, 5640607817, 22400619789, 22132321549, 30957208845], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26393945365, 26175914261, 8828273017, 1100051959163, 1100001628539, 1099951297915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867478415, 1099817147791, 9046158765, 26343537069, 8928863661, 8794714541], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100068732335, 1099968070071, 1099917739447, 1099850631607, 56792, 56796], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099867402723, 1099867403747, 1099867404771, 56800, 13139940837, 1099548710375], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55780, 56804, 55784, 56808, 17485092333, 8895228397], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55788, 56812, 1099548709363, 54768, 55792, 56816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54772, 55796, 56820, 54776, 55800, 56824], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099548708351, 53756, 54780, 55804, 56828, 4432635393], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099733184003, 53760, 54784, 55808, 56832, 53764], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54788, 55812, 56836, 1099548707339, 52744, 53768], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54792, 55816, 56840, 52748, 53772, 54796], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55820, 56844, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56848, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56852, 1099531929115, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55832, 56856, 30168806941, 51740, 52764, 53788], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54812, 55836, 56860, 50720, 51744, 52768], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 8660489765, 4348748325], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [1099582188071, 1099548705319, 50724, 51748, 52772, 53796], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [54820, 55844, 56868, 50728, 51752, 52776], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 50732, 51756], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 49712], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56880, 3449397, 3450421, 1099515149879, 49716, 50740], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [51764, 52788, 53812, 54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24]
private theorem i21 : checks (tilesOf batches) 141 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 141 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 141 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 141 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 141 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [56743452705, 73940441141, 22333579517, 35352770813, 26427432213, 30420482325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4768192789, 13173569901, 1100135844207, 1100085513583, 1100035182959, 1099984852335], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099850701195, 1099817147787, 9029524917, 8861821365, 1100051953079, 1100051954103], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018400695, 1099951292855, 1099884185015, 13290791373, 30504284621, 56788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56792, 55772, 56796, 1099531933155, 55776, 56800], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55780, 56804, 54760, 55784, 56808, 13190271469], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099531932143, 54764, 55788, 56812, 54768, 55792], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56816, 53748, 54772, 55796, 56820, 1099766737403], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099766738427, 1099766739451, 1099531931131, 53752, 54776, 55800], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56824, 53756, 54780, 55804, 56828, 52736], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 1099548707335, 52740], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 52744, 53768], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54792, 55816, 56840, 52748, 53772, 54796], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55820, 56844, 1099548706323, 51728, 52752, 53776], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54800, 55824, 56848, 51732, 52756, 53780], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54804, 55828, 56852, 51736, 52760, 53784], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54808, 55832, 56856, 50716, 51740, 52764], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 4365525537, 1099548705315], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56864, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [55844, 56868, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [54824, 55848, 56872, 49708, 50732, 51756], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 12904981041], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [1099531927091, 49712, 50736, 51760, 52784, 53808], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [54832, 55856, 56880, 3449397, 3450421, 49716], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [50740, 51764, 52788, 53812, 54836, 55860], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26]
private theorem i24 : checks (tilesOf batches) 141 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 141 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 141 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 141 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65182460965, 52566338621, 26477554909, 39496812765, 17669796149, 17502094645], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4617197877, 1100085511559, 1100018403719, 1099968073095, 1099917742471, 1099867411847], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099850701191, 1099800370567, 13357903241, 26444201353, 13324491177, 8878533033], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100085507503, 1100085508527, 1100035177903, 1099968070063, 56780, 56784], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56788, 55768, 56792, 1099531933151, 55772, 56796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55776, 56800, 54756, 55780, 56804, 1099531932139], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54760, 55784, 56808, 54764, 55788, 56812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4432636401, 1099800293875, 53744, 54768, 55792, 56816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099548708343, 53748, 54772, 55796, 56820, 53752], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54776, 55800, 56824, 8777788925, 26007992829, 53756], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54780, 55804, 56828, 1099548707331, 52736, 53760], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54784, 55808, 56832, 52740, 53764, 54788], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55812, 56836, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56840, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56844, 1099548706323, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55824, 56848, 8727599637, 137668117, 1099649296919, 1099649297943], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [1099548705311, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55836, 56860, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54816, 55840, 56864, 50724, 51748, 52772], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 49704, 50728], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [4331826733, 30101698093, 8626935341, 48684, 49708, 50732], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [1099531927091, 49712, 50736, 51760, 52784, 53808], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [54832, 55856, 56880, 49716, 50740, 51764], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [52788, 53812, 54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27]
private theorem i27 : checks (tilesOf batches) 141 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 141 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 141 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 141 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69846595625, 35487202369, 26830010681, 26377098553, 21864100153, 13106465105], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018407763, 1100018474323, 1100001626507, 1099934518667, 1099884188043, 1099833857419], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8861823385, 1100119063963, 1100051956123, 1099984848283, 13257381325, 8828265933], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099531934159, 56780, 56784, 55764, 56788, 1099531933147], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55768, 56792, 1099884179935, 1099884180959, 1099884181983, 55772], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56796, 54752, 55776, 56800, 1099548709351, 54756], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55780, 56804, 54760, 55784, 56808, 54764], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55788, 56812, 1099548708339, 53744, 54768, 55792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56816, 53748, 54772, 55796, 56820, 53752], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54776, 55800, 56824, 52732, 53756, 54780], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55804, 56828, 1099531930115, 52736, 53760, 54784], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55808, 56832, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56836, 4399080969, 1099699629579, 51720, 52744, 53768], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54792, 55816, 56840, 1099548706319, 51724, 52748], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 51728, 52752], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 51732, 52756], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 50712, 51736], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 1099548705311], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56860, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [55840, 56864, 70559269, 1099582188071, 50724, 51748], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 8643712553], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [4348748329, 49704, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [54824, 55848, 56872, 48684, 49708, 50732], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [1099531927091, 49712, 50736, 51760, 52784, 53808], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [54832, 55856, 56880, 49716, 50740, 51764], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [52788, 53812, 54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27]
private theorem i30 : checks (tilesOf batches) 141 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 141 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 141 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 141 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69796398125, 22652635205, 26645464369, 22098977073, 21813770545, 1100051960163], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099984852323, 1099934521699, 1099934588259, 8845048197, 1100068734343, 1100001626503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951295879, 1099984845255, 1099934514631, 1099867406791, 8878531017, 4533300681], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099968067019, 1099548711371, 56776, 56780, 56784, 1099548710359], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55764, 56788, 55768, 56792, 55772, 56796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54752, 55776, 56800, 1099531932135, 54756, 55780], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56804, 54760, 55784, 56808, 53740, 54764], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55788, 56812, 1099548708339, 53744, 54768, 55792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56816, 53748, 54772, 55796, 56820, 53752], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54776, 55800, 56824, 1099548707327, 52732, 53756], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54780, 55804, 56828, 52736, 53760, 54784], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55808, 56832, 21679539717, 8744377861, 1099716406791, 1099716407815], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52740, 53764, 54788, 55812, 56836, 51720], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 1099548706319], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51724, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099666074131, 51728, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [56848, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56852, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55832, 56856, 1099548705311, 50716, 51740, 52764], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 50720, 51744], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 50724], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [49704, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [55848, 56872, 4331970093, 37004845, 48684, 49708], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [56876, 1099531927091, 49712, 50736, 51760, 52784], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [53808, 54832, 55856, 56880, 49716, 50740], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [51764, 52788, 53812, 54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27]
private theorem i33 : checks (tilesOf batches) 141 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 141 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 141 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78185009201, 1295309901, 30873391365, 26293285125, 17602759941, 1100051959151], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099984851311, 1099934520687, 1099934587247, 8962486661, 1100202950023, 1100135842183], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068734343, 1100001626503, 1099766816135, 56772, 13341266377, 8895308233], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4533300681, 56776, 56780, 56784, 1099548710359, 55764], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56788, 55768, 56792, 55772, 56796, 1099867403747], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099867404771, 1099548709347, 54752, 55776, 56800, 54756], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55780, 56804, 54760, 55784, 56808, 53740], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54764, 55788, 56812, 1099548708339, 53744, 54768], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55792, 56816, 53748, 54772, 55796, 56820], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 1099548707327, 52732], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 52736, 53760], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54784, 55808, 56832, 1099716406791, 1099716407815, 52740], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 51720, 52744], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 1099548706319, 51724], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 51728], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 4432634389], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099649296919, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56852, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55832, 56856, 1099548705311, 50716, 51740, 52764], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 50720, 51744], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 50724], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [49704, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [55848, 56872, 48684, 49708, 50732, 51756], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 1099531927091], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [49712, 50736, 51760, 52784, 53808, 54832], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [55856, 56880, 49716, 50740, 51764, 52788], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [53812, 54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27]
private theorem i36 : checks (tilesOf batches) 141 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 141 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 141 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69611920437, 26477763853, 21964765453, 13291016461, 1099968074099, 1099917743475], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099901032819, 1099850702195, 8845048197, 1100068734343, 1100018403719, 1099951295879], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [9046302137, 8861821369, 1100035175867, 1099984845255, 1099951291847, 1099867406791], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56772, 56776, 56780, 55760, 56784, 1099548710359], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55764, 56788, 55768, 56792, 55772, 56796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099548709347, 54752, 55776, 56800, 54756, 55780], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56804, 54760, 55784, 56808, 53740, 54764], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55788, 56812, 1099548708339, 53744, 54768, 55792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56816, 53748, 54772, 55796, 56820, 53752], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54776, 55800, 56824, 1099749960191, 1099749961215, 1099749962239], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52732, 53756, 54780, 55804, 56828, 1099531930115], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52736, 53760, 54784, 55808, 56832, 52740], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 51720, 52744], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 1099548706319, 51724], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 51728], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 51732], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 50712], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [1099548705311, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55836, 56860, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54816, 55840, 56864, 50724, 51748, 52772], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 4348747305, 53782057], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [49704, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [55848, 56872, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 1099531927091, 49712], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [56880, 49716, 50740, 51764, 52788, 53812], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27]
private theorem i39 : checks (tilesOf batches) 141 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 141 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 141 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56810973241, 22048647461, 21813838117, 4650752293, 1100202951035, 1100135843195], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068735355, 1100001627515, 1099934519675, 1099884189051, 1099850701183, 1099800370559], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8912153009, 1100068730291, 1100068731315, 1100035177907, 56772, 56776], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56780, 55760, 56784, 1099548710359, 55764, 56788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55768, 56792, 55772, 56796, 1099548709347, 54752], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55776, 56800, 54756, 55780, 56804, 54760], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55784, 56808, 53740, 54764, 55788, 56812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099548708339, 53744, 54768, 55792, 56816, 53748], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54772, 55796, 56820, 53752, 54776, 55800], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56824, 52732, 53756, 54780, 55804, 56828], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [221555201, 137670145, 70562305, 1099548707331, 52736, 53760], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54784, 55808, 56832, 52740, 53764, 54788], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55812, 56836, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56840, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56844, 1099548706323, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55824, 56848, 45588, 51732, 52756, 53780], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54804, 55828, 56852, 45592, 51736, 52760], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 45596, 50716], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [45600, 1099548705315, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54816, 55840, 56864, 44580, 45604, 50724], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [44584, 45608, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [54824, 55848, 56872, 44588, 45612, 49708], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [56876, 44592, 45616, 1099531927091, 49712, 50736], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [51760, 52784, 53808, 54832, 55856, 56880], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [44596, 45620, 49716, 50740, 51764, 52788], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [53812, 54836, 55860, 56884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28]
private theorem i42 : checks (tilesOf batches) 141 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 141 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤141) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 1 where
  orders := orders
  covers := by
    intro a ha box
    change 1+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group1

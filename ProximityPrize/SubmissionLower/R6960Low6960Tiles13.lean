import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass13

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2264992773, 14781517835, 32097247245, 138147020827, 18861835333, 40084455621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [48305563845, 43943696581, 17620310453, 13241462197, 8929787317, 30454737349], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21864876485, 38994055635, 8694909401, 1099817932251, 43138234869, 1099700488695], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700489719, 1099700490743, 4349607433, 1099616601611, 8678125069, 4366383629], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549491739, 20932125, 8594170401, 21084704], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 136 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [23640872971, 40570400785, 121084925985, 10271902789, 35638696169, 48054041833], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30941424873, 26226949549, 17603533229, 13140798909, 8829124029, 1099935369663], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817930203, 1099817931227, 1099817932251, 43238830557, 1099683708411, 1099683709435], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683710459, 8694902269, 155302397, 21545884177, 12939467285, 4349602325], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332827161, 34380602909, 21495841309], by decide +kernel⟩
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32214885389, 57280906265, 95483165741, 30958058781, 34967887133, 22099837213], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39363233141, 26495315317, 13308566961, 13157576113, 8829124017, 1099968924087], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968925111, 1099968926135, 1099968927159, 1099734040047, 1099734041071, 1099734042095], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17368648181, 4483821045, 4399937013, 43020723729, 71415313, 1099583044115], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8627723801, 37857817, 25773888033], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i49 : checks (tilesOf batches) 136 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36476760081, 65703269405, 69830874165, 26394727745, 26227028289, 9147895105], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35236107601, 26562427217, 8862609841, 8795569585, 1099985701299, 1099885039051], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099885040075, 1099885041099, 13191124441, 8812275161, 1099767594471, 1099767595495], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767596519, 4399935989, 1099700484599, 34447634957, 21546105361, 71340561], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4366378513, 4332826129, 1099583043091, 21081629, 21082653], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 136 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44731415573, 69897775141, 44228914237, 30941210945, 26478610753, 17838417217], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17502943601, 8913014129, 39061306817, 30471513537, 4517378497, 1099918590403], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918591427, 1099918592451, 1099918593475, 1099918594499, 1099918595523, 4567639521], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4500598241, 1099784369635, 17402202605, 4517305837, 1099683707387, 1099683708411], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54560277, 54636053, 54637077], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53069891609, 91087535149, 1598149705, 35185917189, 34951110917, 13610632453], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39279413641, 26411430281, 13308567957, 13140799893, 1100103139735, 1099968923063], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968924087, 1099968925111, 1099968926135, 1099885041099, 17502866893, 4500599253], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834702295, 1099834703319, 4450198013, 4416711165, 1099616596491, 1099616597515], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12905909789, 21011997, 21080605, 21081629, 38658787873], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57247552541, 74025176113, 1581372489, 30740024613, 26277358885, 9198225701], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35101889905, 22217128305, 8912940449, 8829122977, 1100052809123, 1099952146875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099952147899, 1099952148923, 1099901818311, 13258232265, 8896160201, 1099801147871], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099801148895, 1099801149919, 4416712177, 1099717260787, 71413265, 1099583042067], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349534741, 54635029], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 136 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65653071905, 56946040889, 22032720197, 21831399749, 4769042757, 35185844553], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26478609737, 8829122973, 1100069586335, 1100069587359, 1100069588383, 1099952148923], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099952149947, 8862605773, 4534087117, 1099868255695, 1099817925083, 1099817926107], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817927131, 17368647157, 8778717685, 104967689, 1099616596491, 30135968273], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71336465, 4366378513], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65602808869, 44128250941, 30924434753, 22233976129, 17804862785, 13291796825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13174425945, 1100052810147, 1100052811171, 1100052812195, 1100052813219, 1099935365567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935366591, 1099935367615, 1099935368639, 4584416729, 4517375449, 1099817924059], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17318317561, 4466975225, 25841069585, 17251207697, 71413265, 1099583042067], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21011997, 4303392], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69797181481, 27099446337, 26730199341, 22233978157, 13593783597, 8896232833], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100187027843, 1100187028867, 1100187029891, 1100187030915, 1099868257743, 1099868258767], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099868259791, 4517375449, 1099817924059, 1099817925083, 13124015589, 4550862309], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [71413265, 1099583042067, 21529328149, 12939465237, 4235808], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65519060013, 18559845445, 26545653045, 22099829045, 9231710517, 1100119917971], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119918995, 1100119920019, 1100119921043, 1100119922067, 8896160205, 4534087117], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099868255695, 1099851479507, 1099851480531, 1099851481555, 17385358833, 8795494897], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [104967689, 1099616596491, 4332824089], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65468796977, 5758832713, 26478612781, 22015946029, 9164670253, 1100019257771], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100019258795, 8845831601, 4550932913, 1099985699251, 1099952145851, 1099952146875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099952147899, 17435759065, 4601193945, 4433489393, 1099717260787, 1099717261811], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717262835, 54636053, 1099566264855, 12922688025, 37790233], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61157055541, 26361175341, 21898508589, 4836151597, 8862677397, 1100103140759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100103141783, 1100103142807, 1099985703347, 1099985704371, 13207903677, 8812277181], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817925083, 1099817926107, 1099817927131, 4416712181, 1099700483575, 8678055437], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4383156749, 54637077], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 13 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤138 ∧ 5+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group13

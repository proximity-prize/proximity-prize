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
  ⟨unpack [23692250119, 40723031055, 87012035615, 44465430587, 39650086187, 31043581227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39264490795, 13142441383, 21799474623, 13159214527, 4435066343, 4401579495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43055851007, 8662920707, 4351179267, 1099601462787, 1099601463811, 56279563], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17219294735, 8629365263, 22657555, 22724115, 30070568471, 4300846615], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 133 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 133 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 133 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36326807563, 53155413015, 86961975339, 6012126279, 30993248555, 34969522475], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22084695339, 39180320155, 30590592411, 17504440767, 13142435263, 8780363199], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099886608831, 38878255587, 1099735680483, 1099735681507, 1099685279215, 1099685280239], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099685281263, 8662918655, 106541567, 17236002315, 12924328463, 4317620755], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 133 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 133 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 133 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40672699407, 61477112863, 69815732275, 26463471931, 26262218043, 9166242107], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39348161891, 26480178531, 8914576819, 8797139379, 1099936939443, 1099853119943], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099853120967, 1099853121991, 13108810211, 8763580899, 1099718832615, 1099718833639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718834663, 43106182643, 89763331, 34415727115, 21514188303, 12924325391], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4334395919, 39430671], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 133 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 133 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 133 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40723296275, 57215834147, 61209022515, 22151729463, 21967251767, 9099133239], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35036485999, 22151724399, 8830691759, 1099953714607, 1099953715631, 1099953716655], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099936940467, 1099937007027, 1099937008051, 8847463899, 4552499675, 190425579], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099702054379, 1099702055403, 43039142403, 30087274003, 17202445843, 8612581907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 133 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 133 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 133 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44800359447, 65537402919, 35607062587, 30909294899, 26413140275, 17756169523], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13142440295, 1100255775079, 1099987270055, 1099987271079, 1099987272103, 1099987338663], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4586055103, 1099886603711, 1099886604735, 1099886605759, 13192694223, 8864242127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38945504723, 30338934227, 12991366655, 72984071, 1099584612871, 4317616659], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [22651411, 25775531543, 17185669655], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [40656586779, 61259280427, 31295319103, 26631172411, 22118174011, 17689060667], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8881027431, 1100255708519, 1100255775079, 1099953715631, 1099953716655, 1099953717679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4586055095, 1099920158135, 1099920159159, 1099920160183, 13125586391, 4569275863], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38777801211, 106538495, 1099618167295, 21530964491, 12941036043, 4317616659], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48827159583, 65369769007, 5726913607, 22386607379, 22084623635, 21883368723], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8830694775, 1100188598647, 34885490075, 22000728475, 1100020893087, 1100020894111], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8931351975, 4586056103, 1099987268007, 1099936937395, 1099936938419, 1099936939443], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8763576815, 1099685276143, 1099685277167, 4418280955, 123315707], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [48726564899, 56796614707, 1448724551, 22185283867, 21933697307, 9065578779], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30674411911, 17789649287, 8881023371, 1100104709515, 1100104710539, 1100104711563], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100087935375, 1100087936399, 1100004116899, 8931349959, 4569276871, 1099802716627], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099802717651, 1099802718675, 56205835, 56206859], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [52820274215, 43978891323, 17722614067, 13276656947, 1100473812275, 1100473813299], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26564062555, 17873537371, 13394025819, 1100071155091, 1100071156115, 1100071157139], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100071158163, 1099920158135, 1099920159159, 4569275863, 4435060183, 123315707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099634944507, 12974590467, 4384725507], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [52736456747, 31194655807, 22336207179, 17823207755, 13377316171, 8964912463], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100356370767, 1100356371791, 1100356372815, 1099970491819, 1099970492843, 1099970493867], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4535723459, 1099869826499, 1099869827523, 13041766887, 4451836391, 1099618167295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8629359119, 4334394895, 39429647], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [56863720495, 14182628419, 22353052967, 17806433575, 13377319207, 1100171821435], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100171822459, 1100171889019, 1100020822431, 1100020823455, 1100020824479, 1100020825503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8864243135, 4485392831, 1099685276143, 1099685277167, 17303111163, 8679692795], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [89761283, 4317616659, 22651411], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [60990918705, 26497028355, 17772948739, 9132687619, 1100121489799, 1100121490823], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100121557383, 4619611539, 1100071155091, 1100071156115, 1100071157139, 13259805107], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8864244147, 1099735608803, 1099735609827, 4418281975, 1099651721719, 8629359119], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4334394895, 5875223], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 15 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤136 ∧ 7+a.j≤57 ∧ 2+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
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
end Low6960Allocation.Group15

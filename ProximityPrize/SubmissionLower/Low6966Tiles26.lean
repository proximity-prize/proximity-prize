import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass26
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group26
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23708437511, 40890278927, 87129017375, 48860602427, 43911040327, 35287759175], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39280811335, 8964457919, 21815795167, 13175535071, 4384343579, 89378331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34431831583, 47283319335, 30103665191, 21513804327, 8628909607, 4334010919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38659973679], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i51 : checks (tilesOf batches) 139 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36443723787, 57500253207, 87078958123, 6196217927, 35237426503, 34985843015], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17873157447, 43525160359, 34935433639, 17520826847, 13158755807, 4518493679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4485006831, 43155986943, 1099651337743, 21564067355, 1099584226847, 1099584227871], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8645684771, 4333943331, 39043623, 5421615, 5422639], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i46 : checks (tilesOf batches) 139 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40823170063, 65838730271, 69949492275, 26513345883, 26295314779, 9199338843], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39448366451, 30825018739, 8947673563, 8813458907, 4484940251, 1099785554415], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099785555439, 1099668046347, 1099668112907, 17319499279, 4367496723, 1099634490899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43055392279, 38975015, 38976039, 30086886955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i49 : checks (tilesOf batches) 139 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40924164115, 69982771235, 52853578807, 35287619923, 26647493971, 22168050003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17638273395, 9031566707, 1099852596703, 1099852663263, 1099852664287, 8763126243], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099835817443, 1099835818467, 13108419067, 8746347003, 139638287, 1099651267087], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4350716451, 55751203, 21513731623, 12923868711], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45001227287, 65704716327, 40019011643, 30959167835, 22285486427, 22000279899], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13225867651, 4652714371, 1099886148055, 1099886149079, 1099886150103, 1099886151127], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8947671515, 4602375643, 4501714395, 1099869440475, 1099869441499, 43139350019], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099651266063, 17252321823, 8662457887, 38972967, 38973991], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53222197275, 69798427695, 14450606147, 26731380019, 26429462835, 21983573299], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39196707247, 30539805103, 8847013295, 1100003590587, 1100003591611, 1100003592635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100003659195, 13242636755, 8847010259, 1099785483759, 1099785484783, 1099785485807], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4401048083, 1099634487827, 12974133787, 25825473059, 12940578339, 4317159979], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [5417519, 5418543], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53171999775, 73959245875, 26681051415, 26395911447, 13527859479, 39230330279], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26278460839, 9031558575, 8863789487, 1100053921199, 1100037145011, 1100037146035], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100037147059, 1100037213619, 13091641843, 1099768705523, 1099768706547, 1099768707571], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4350716443, 21530508835, 12940645923, 4333938215, 22195755], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53088182307, 61158233143, 22268712239, 22017125679, 9149007151, 35002474903], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22067381655, 8880565683, 1100037142963, 1100037143987, 1100037145011, 1100020368823], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100020369847, 1100020436407, 8863784431, 4518488559, 1099735151099, 1099735152123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17218766375, 8628902439, 38971943, 38972967], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57198668839, 44129428539, 17738933591, 13292976471, 1100423022935, 1100423023959], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30875348335, 17973742959, 17654980975, 1100003588539, 1100003589563, 1100003590587], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100003591611, 1099852592607, 8863785443, 4501712355, 106081815, 1099617710615], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4333937191, 38971943, 12890246703, 8595349039], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [57114851371, 31345193023, 26647492959, 17906636127, 17655048543, 8930901363], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100305582451, 1100305583475, 1099953257927, 1099953258951, 1099953259975, 4635929043], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4501713363, 1099902925267, 1099684819463, 1099684820487, 13024531983, 4434601487], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38972967], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73942467629, 1582484551, 26798490895, 22251938063, 22000351503, 8863791503], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100188140943, 1100188141967, 1099970104771, 8981225931, 4619152843, 1099936478667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099902925267, 1099902926291, 1099902927315, 21647951367, 8763121159, 89304603], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099600933403, 22194731], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61158232113, 1582484551, 26546901291, 22017125675, 9132229931, 8914120111], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100053920175, 1100053921199, 1100053922223, 1100053923247, 1100053924271, 1099970104771], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17436873191, 8813454823, 1099718373887, 1099718374911, 4367492639, 72527391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12923867687, 4333937191], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52618697781, 22134496571, 17655051579, 4803709243, 4619154863, 1100053921199], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100053922223, 1100053923247, 1100020369847, 1100020436407, 13175528923, 4568821211], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099718374911, 1099718375935, 72527391, 1099584156191, 8645680675, 4333939235], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [5417519], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 26 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group26

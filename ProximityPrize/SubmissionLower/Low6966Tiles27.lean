import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass27
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group27
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27802733575, 45118793747, 82968794143, 44649980987, 48005272935, 35154068839], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21816256979, 13226394067, 38878252527, 51578811931, 42972244511], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i51 : checks (tilesOf batches) 136 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36612085771, 53440691223, 87129747499, 10508420167, 39482519891, 30808840531], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22135028051, 47535504863, 38945713631, 13058619891, 21598149127, 13008286215], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4351248915, 25809229339, 4317692447, 5949987, 5951011], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
private theorem i46 : checks (tilesOf batches) 136 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [45001221135, 65923141663, 65738870835, 26463474031, 26262220143, 4972005743], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43609641351, 30724881799, 13125660135, 8797208039, 47417992699, 73058835], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099584687635, 17236074007, 4334468635, 39503387, 8595878435], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
private theorem i49 : checks (tilesOf batches) 136 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [45135769619, 74278263843, 44398322747, 39532780883, 30842324307, 17689060759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13276658071, 4737124759, 4485462519, 4418355703, 1099651795459, 1099651796483], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25859556879, 12974662159, 8662987283, 56279575, 1099567908375, 47267066399], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45152746519, 82683717671, 23091329091, 39616735531, 30859104555, 26396438827], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8931357123, 8813985223, 4485466567, 21715587563, 8830691819, 1099702127095], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099702128119, 4384800255, 1099668571647, 34432641555, 21547814419, 4351243799], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56278551, 1099567907351], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [45085771803, 69916324907, 23040997443, 30976472395, 22285948235, 22051138891], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4535797179, 1099953786299, 8864247255, 4569348567, 4468687319, 1099702127095], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099651793411, 1099651794435, 17269626383, 8679696911, 42988947995, 4334466587], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39501339], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53273121823, 69798955059, 1750715463, 26681575735, 26396435767, 13494763831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43341206975, 26195034559, 4502241739, 1099886676427, 13175989711, 4602836431], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4535795151, 1099752459755, 1099668571647, 1099618237963, 1099618238987, 12957883923], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4351176215, 4317689371, 42972173855, 5944867, 5945891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57400451107, 57014786103, 22218905939, 21933699411, 4888119635, 39230857627], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22051064219, 8881025475, 4569349571, 1099920229827, 1099786013155, 1099786014179], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [12991439367, 1099635015175, 1099635016199, 4401574411, 106609163, 8595808803], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4300844579], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57283013671, 44230550587, 17756169583, 13310212463, 4753901935, 35036556675], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22084620675, 4535794135, 1099836342743, 1099836343767, 1099802790367, 1099802791391], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8763582971, 4435129851, 1099584683539, 17236070935, 8646141463, 22722079], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [22723103], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61410277419, 27235300415, 30892652895, 22168574303, 17672286559, 8797210015], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099853120979, 1099853122003, 1099853123027, 4619612631, 4535794135, 1099836342743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17303181831, 4418285063, 73054739, 1099584683539], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [57132155951, 18712476739, 26564134247, 17856831847, 17588401511, 1099987339699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099987340723, 4602836427, 4519017931, 1099886675403, 1099651792387, 1099651793411], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [12991439371, 4401574411, 56277527], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [57014718515, 5945018439, 22353056079, 22034360655, 13343768911, 4519018943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099853122003, 1099853123027, 8914577879, 4569282007, 4485463511, 1099702126071], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099635015175, 1099635016199, 4317689371, 21480706595, 5944867, 5945891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52719819831, 22202129747, 17672287571, 4871342419, 4636390859, 4535795147], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099886675403, 1099802790367, 1099802791391, 13024992771, 8696475139, 123387399], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099635016199, 4317621791, 4317689375], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 27 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group27

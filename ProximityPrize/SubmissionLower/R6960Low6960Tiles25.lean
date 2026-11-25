import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass25

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group25
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [14865271815, 36543470607, 82933596187, 74562375731, 52416168283, 43843286363], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34884395431, 17754867111, 38977539555, 51627767323, 30102888999, 17218060839], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47249058351], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
private theorem i51 : checks (tilesOf batches) 139 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32281729035, 53439117335, 87212190759, 23408787523, 43776109923, 35102431587], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26445462883, 51879426527, 17318657543, 4417049107, 30169995799, 17285102103], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47315950111, 42970869291, 8611352107], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40805278735, 78605208605, 65838225461, 48121269591, 39481212247, 26378347915], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21949170059, 13057311231, 4484157951, 47366284817, 34431335965, 21546508831], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [12956580383, 47265830443, 4316383785, 4641325, 4642351], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
private theorem i49 : checks (tilesOf batches) 139 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [45067087891, 82833202209, 44497677373, 43876703563, 35169470795, 17670974899], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13275349427, 4735816115, 51678097935, 30203480591, 17318652431, 8695235091], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4366716435, 1099583378975, 38194725, 38195751, 38675899945, 8611348011], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4639277], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 139 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45134461973, 87061194789, 27435252801, 39665690943, 30941679933, 34934731069], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13275345353, 13090800081, 4534489553, 4467376645, 4400269829, 1099650486799], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099650487823, 25874960915, 13006908945, 47299313185, 54970913, 1099566599715], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4316380713, 25774363181], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53372209177, 86994156589, 6128259145, 35320462647, 30807466293, 22150496565], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47634794963, 34716482003, 8812610009, 4517711321, 17469645289, 8879715817], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099700819459, 4400267793, 122079761, 1099633708563, 1099633709587, 17251540509], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34381003307, 4637229, 4638253], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61710619677, 74210054193, 30824239441, 26361573713, 9248820561, 43574711705], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30673174937, 13141127649, 8762278369, 1099767926259, 1099767927283, 1099767928307], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17335427593, 4400267789, 1099650484751, 8628057633, 21414441, 21415465], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30069260845, 4299535917, 4299603501], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [70099361825, 52919837753, 43692220783, 26562825581, 21999495557, 17553539461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100220913031, 4551197153, 4500933089, 1099835036131, 13057239557, 4467309061], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099616930327, 1099616931351, 38709453345, 25824627233, 54968865, 54969889], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12889466413], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [82749451301, 27351366721, 39615360313, 26697045305, 30656540985, 4551266749], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13225013705, 8846164425, 8762346953, 1099751149047, 1099717595647, 1099717596671], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4417045001, 1099667261963, 21563282969, 8678387225, 4366645789, 34414489121], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21529727521, 21414441, 21415465], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [82715965481, 14600751173, 35370793269, 30824242485, 26344799541, 8913272257], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4484155873, 1099835036131, 1099835037155, 17452867053, 8862937581, 4383424017], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [122078737, 1099633707539, 1099633708563, 34381003305, 4316380713], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82682479661, 1816515657, 31075829041, 26562831665, 22100164913, 8846164425], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4534488521, 17402537457, 8779053553, 1099717596671, 1099684040199, 1099684041223], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [155633161, 1099667261963, 4349868577, 54968865, 30102816293, 12906243625], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4316313129], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [74159722545, 30891348293, 26378350917, 9265597765, 13174682073, 4584751577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4517710297, 1099801481707, 1099801482731, 21613548045, 13023685133, 1099633707539], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099633708563, 4349868577, 54968865, 54969889], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61375487029, 26462166369, 21982722401, 4937142625, 8862939613, 4551263709], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099851812319, 1099717595647, 1099717596671, 17335426569, 8745497097, 71747101], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099583375903, 4349935137], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 25 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 6+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group25

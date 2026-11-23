import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass3

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2164329477, 5620568075, 23271381001, 57179516945, 87094224933, 18962299969], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39480682821, 39279497541, 22150035781, 35168391497, 43708265813, 39413506389], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25958388189, 17368526301, 8711553517, 121621997], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 130 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 130 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 130 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [23271381001, 48774131729, 87027048481, 27434791997, 39530946865, 35101903153], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34917428529, 43523780993, 39228956033, 38993861049, 17469189561, 8812216781], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [255839693, 25924831717, 17334969829, 8627665409, 25790612997, 4315923973], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i6 : checks (tilesOf batches) 130 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 130 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 130 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32080339981, 65686029337, 78454096941, 30806934849, 30605681985, 9281914177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43725112649, 35118608713, 17418855877, 8828926405, 4383032809, 1099650026987], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43054081521, 21562824181, 34397319681, 8627596801, 4332698113, 4315922945], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [37734913, 38675370501, 4178441, 4179465], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 130 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 130 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 130 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40469409809, 74175633441, 48607567929, 39480547641, 30840488249, 17670447489], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17536300417, 4718512513, 43238633925, 8745039321, 4450140633, 1099650025963], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099650026987, 25857720821, 17267858933, 8644375033, 38692216321, 4315921921], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099549361667, 4299076105, 4299143689, 4178441], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44714376213, 74158991397, 31545208893, 35185649977, 26511969593, 30538574137], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4584360353, 13207775661, 8845703597, 8778663341, 43272256957, 1099700356575], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099650025963, 1099650026987, 21596311021, 12989670893, 4382964205, 121618925], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4349408765, 34397252097, 20954629, 8594040329, 4299076105], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57247156249, 82581291053, 30941151513, 34917425433, 9349023001, 43557407085], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30723044717, 17536295329, 8912811425, 8812151201, 1099750690259, 1099717132763], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099717133787, 1099717134811, 17301411309, 4382963185, 104840689, 8661150201], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [42987112961, 4109833, 4176393], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57264133149, 69797121073, 30706273589, 22032526645, 9198028085, 39279285621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26394525045, 8862477757, 4533959101, 4450075069, 1099784243659, 1099784244683], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17402075601, 1099666801127, 1099666802151, 71219705, 71286265, 4332629505], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [37664257, 12889004553, 8594041353], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65669652513, 48473350201, 35152093517, 26495190349, 21948637537, 17536301409], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100220452195, 4533959097, 1099851284923, 1099851351483, 1099851352507, 13090333141], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4517179861, 87996917, 1099599691255, 21529200125, 12939337213, 4299075081], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78319741989, 22938499137, 35269537049, 30773383449, 26344337689, 1099952016803], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8912810405, 8778595749, 1099935238567, 17469116869, 13107111365, 1099733843415], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099733909975, 1099733910999, 30152617461, 17267789301, 87995893, 87996917], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8644371965, 4349407741], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69813762089, 18660310081, 30907529521, 26428152113, 21982262577, 1099935239591], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828925357, 4500406701, 1099901684143, 17402075601, 8778591697, 1099683578339], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099683579363, 138328553, 1099650022891, 30119131645, 4332629505, 37664257], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12889004553, 8594041353], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74008134701, 1665059909, 30890820893, 26394600733, 13526548765, 13190997429], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795370933, 1099851284923, 1099851351483, 1099851352507, 1099733913047, 25908053477], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13040001509, 4382963177, 1099650022891, 4332630529, 37730817, 21478868489], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12889005577], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65485377585, 26478416177, 22015749425, 9181250865, 8896032181, 8761817525], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099817797059, 1099817798083, 1099817799107, 17368453597, 8778589661, 171882977], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099683577315, 1099683578339, 4332630529], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52717984821, 22066077009, 17636963665, 4785621329, 4567512513, 4466851265], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099817797059, 1099784243659, 1099784244683, 13056777697, 8728260065, 121617901], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099633246703, 4315852293, 20887045, 20953605], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 3 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤132 ∧ 4+a.j≤55 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group3

import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass16

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group16
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [6425873413, 23590409225, 44915829777, 87178434593, 48876530749, 52265376085], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43625254229, 26026097093, 4551267781, 51644673513, 38692818425, 25807992313], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 128 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 128 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 128 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27885770761, 49093555221, 87128171557, 36025186369, 48004031821, 39330288973], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [51745338833, 21680799185, 4500936145, 34431407601, 21546580465], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 128 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 128 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 128 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 128 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40620532749, 82799447069, 65804672053, 52315639101, 39447658813, 26294462849], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21915682177, 51661448677, 12973426157, 4383495661, 47282674169, 34381072893], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21479468545], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i9 : checks (tilesOf batches) 128 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 128 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 128 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44899119121, 87027440673, 44464123965, 48104627505, 39414172977, 17553536425], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13208308137, 373741993, 51661451749, 34464959977, 21580132841, 8628128249], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4333164025, 42954155521], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i12 : checks (tilesOf batches) 128 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 128 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 128 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 128 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45016890389, 87010797605, 31629556801, 43809663281, 35119207729, 34901178673], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17486494133, 13090868665, 30169994729, 17285166569, 4383493613, 4349941229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21419517, 21420541, 42954222081, 8594573825], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i15 : checks (tilesOf batches) 128 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 128 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 128 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [61660088345, 86960604205, 1799739465, 35219801389, 30773979437, 17872308525], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [52030491017, 39128956297, 8745568725, 4433827285, 21630396889, 13023756761], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [38196729, 1099549825531, 38676037117, 21496243709, 8611348989, 4316384765], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [51544082945, 12889538049], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 128 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 128 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 128 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 128 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 128 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65854526493, 74142880821, 30790686021, 26344797509, 9265664325, 47836190069], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34951431541, 17352275409, 8745568721, 105305577, 1099616934379, 21529799157], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4333160953, 38195705, 8611348989], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 128 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 128 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 128 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 128 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 128 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65837883425, 61358710841, 26395124065, 21932391777, 4870034785, 47802704245], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30639690101, 13057310161, 4484156881, 1099600156143, 1099600157167, 17218056697], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47265899005, 4316382717, 30069330433, 4640257, 4641281], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 128 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 128 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 128 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 128 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [70015478821, 44329906237, 43625180509, 26462165341, 17603868041, 13241862537], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100019587467, 4433824225, 4366717409, 12956644849, 4366714353, 54972917], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099566601719, 42954223105], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [86910203945, 14516866117, 39598651677, 35052101917, 22133720349, 8846230973], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21731058117, 13141195205, 4433826253, 1099734374863, 71750129, 1099583378931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4316383741, 38659258881], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 128 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74159588397, 14516866117, 35169535297, 26445457729, 21965948225, 8863008185], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4433826253, 1099734374863, 21580130789, 8712012261, 71750129, 1099583378931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21417469, 17184500225, 8594570753], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78353961009, 30958457133, 30656540973, 9315995949, 17469714877, 8846230973], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [155636189, 1099667264991, 1099667266015, 4316382717, 21417469], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 128 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65586568245, 26495720781, 22033054029, 9181778253, 13074086357, 4484155861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [155636189, 1099667264991, 1099667266015, 25791143421], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52802332729, 26294462825, 17620714857, 1100153805163, 8745567701, 4417049045], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21580130793, 8695235049, 54972917, 1099566601719, 21417469], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i42 : checks (tilesOf batches) 128 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 128 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 16 where
  orders := orders
  covers := by
    intro a ha box
    change 14+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group16

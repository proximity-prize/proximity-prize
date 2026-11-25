import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass33

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group33
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23607970823, 40705991695, 87045458975, 57232760891, 43844390195, 39432124723], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21933564299, 21816195467, 4720218507, 8763521503, 4451780063, 4435070431], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34466134511, 21581307375, 1099601401331, 47300552187, 8646079995, 22662659], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [22663683, 38660214279, 5817863, 5884423], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 129 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 129 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 129 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36326545419, 57399917591, 87028954155, 14534887495, 35170710843, 34935904571], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26295713083, 43458510223, 39113353615, 8830631355, 21732301255, 13092041159], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4418226643, 1099735618003, 1099735619027, 43106179555, 1099601332723, 1099601399283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4334338551, 8646078971, 4351114747, 34399021567, 21514128895, 22595075], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12890711559], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 129 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 129 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 129 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40672437263, 86928018463, 57098543163, 43894656279, 35254597911, 35019791639], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17554784619, 1100171761003, 17504443831, 13125595575, 4485333447, 1099785882055], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099785883079, 1099785949639, 30171167215, 17286339055, 47334106611, 4384666099], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4367890931, 1099584553463, 1099584554487, 38710695419, 8595746311, 5814791], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [5815815], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 129 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 129 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 129 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44867072019, 86911376419, 40002629695, 39599758615, 35120383255, 39146989847], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4602777987, 17538001295, 13142375823, 8813858191, 1099785883079, 25976866255], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13125591503, 4435000783, 1099752326607, 1099752327631, 1099752395215, 1099752396239], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [47417995743, 4434997735, 4384668135, 1099601330675, 34415731195, 39369215], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099550998015, 21497349635, 12907486723], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44900891671, 86877890599, 27168062531, 35355191571, 30842195219, 34868800787], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13259812239, 13108821395, 8746749331, 1099836214715, 1099836215739, 1099836282299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4435000779, 1099769103819, 1099769104843, 21698678223, 13075260879, 43072699883], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4384667115, 1099618106863, 1099618107887, 8629298687, 4334334463, 34382244355], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [22592003, 21480640007], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53155416091, 86827695151, 5844291659, 31009963279, 34952682767, 22051078415], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8780300699, 1099970432411, 43391469983, 30489867679, 13310074271, 13175926175], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8813854111, 1099819504063, 1099819505087, 1099769104843, 1099718770135, 1099718771159], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718772183, 4434996711, 4384667111, 17269560819, 39368191, 39369215], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30070502919, 4300777991], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57316299807, 78254541875, 30791863575, 26345975063, 13477923095, 39213946243], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26329120131, 8948067747, 8813853091, 1099936875939, 1099920099751, 1099920100775], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099920101799, 1099920168359, 17420556743, 1099701991899, 1099701992923, 1099701993947], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4351110651, 56145403, 12907485699, 4317555203], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 129 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61460340771, 61192182839, 22134889783, 21933634871, 9065516343, 39297835363], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22168439139, 8830629287, 4502110631, 1099920099751, 1099903323563, 1099903324587], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099903391147, 13058482647, 4485329367, 1099701993947, 1099701994971, 1099668437475], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099668438499, 38693986815, 8612520451, 4317556227, 5813767], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69849017383, 39868411967, 35187420471, 22285881655, 22017452343, 13209485667], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100205314403, 1100205315427, 1099869766067, 1099869767091, 1099869768115, 1099869769139], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8897735099, 4552439227, 4451777979, 1099668438499, 17236005371, 8646075899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56145403, 1099567774203, 34399022591, 5812743], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69798754347, 27084176451, 30959630639, 26413078831, 21967189295, 1100087872895], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100087873919, 1100087874943, 8830629287, 4502110631, 1099920099751, 17420556747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8780295627, 1099701993947, 1099701994971, 1099668437475, 1099668438499, 4351110651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56145403, 30070503943, 12890708487, 8595745287], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78237762607, 5793960011, 30959633679, 26429859087, 21983969551, 8813855115], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100037541259, 13209478575, 8813852079, 1099869770163, 1099869836723, 1099802657219], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099802658243, 1099802659267, 25909757415, 13024928231, 4384667111, 1099651661287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4334334463, 39369215], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65470369843, 5793960011, 26530517295, 22017453359, 17605117231, 1099987207575], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099987208599, 1099987209623, 8914513331, 4552440243, 1099869766067, 1099869770163], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099869836723, 17319825895, 12991374823, 89700851, 1099601329651, 8612521475], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4317557251], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 33 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group33

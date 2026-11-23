import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass7

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23508093959, 36361413647, 82633639963, 48542816311, 39516457235, 30876332307], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34919715091, 17421153647, 17471476123, 8881546651, 8780886427, 4435656107], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099786536363, 4385321419, 1099652315595, 1099635539407, 1099635540431, 25860010455], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17253371351, 38694504931, 4334920163, 4318144995, 40022499, 1099551651299], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12891295211, 8596332011, 6400491, 6467051], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 122 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 122 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 122 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 122 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 122 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 122 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32082630667, 44616267799, 86844990503, 14350923843, 30943372555, 34953266443], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30557710603, 13109406083, 17504961947, 13142956443, 1099820087715, 1099820088739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820089763, 1099820090787, 38946093479, 30356234663, 4435585467, 1099719356859], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099719423419, 8663439835, 4334921179, 17236591071, 56798687, 23176679], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [23177703, 8596329963], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 122 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 122 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 122 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 122 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 122 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 122 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36361413647, 65554434075, 65454180403, 35171158315, 26547809579, 22101920043], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21934219563, 13310736683, 1099887196563, 1099887197587, 1099887198611, 1099887199635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8814436763, 4485918107, 1099853575579, 13059066307, 8713771459, 1099652246987], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099652313547, 107062739, 1099618691539, 4334918115, 39952867, 25792900583], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 122 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 122 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 122 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 122 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 122 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 122 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40488939539, 69732096035, 44096855095, 30960146711, 26480703767, 22051591447], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17454705995, 4636983627, 4502695311, 1099903907215, 1099903973775, 1099903974799], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099836866975, 1099836867999, 8881542563, 4536246691, 4452362659, 17353963971], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13025512899, 1099685867971, 38795096523, 1099652245963, 1099652246987, 56730079], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099568358879, 8613105127, 4301363691], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 122 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 122 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 122 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40472362007, 73943311399, 26984098879, 30909818119, 26447217927, 26245964039], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088524131, 1100088525155, 1100088526179, 8898322811, 8764108155, 1099987794299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099803241895, 1099803242919, 1099803309479, 13159663019, 8831210923, 157393351], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099669022151, 1099669023175, 38795099595, 25876784595, 17286922707, 4318139879], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [23174631], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 122 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 122 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 122 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 122 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 122 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44549359643, 86643733547, 30926664927, 34902938847, 13528840415, 13310727523], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13142959459, 8780887395, 1099987861883, 1099987862907, 1099887130003, 1099887196563], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099887197587, 34701461915, 26094890395, 4469138851, 1099820019107, 1099820020131], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13142952367, 4435581387, 140616139, 1099635467727, 1099635468751, 21481156075], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12891293163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 122 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 122 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 122 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 122 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48676688927, 69564597295, 26480772347, 22034882811, 13394622715, 34835682679], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21934143863, 1100004571511, 1100004638071, 1100004639095, 1100004640119, 8847991171], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099954236803, 1099954237827, 1099954238851, 8881541543, 4553022887, 1099685799363], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099685800387, 17202969063, 8613105127, 23174631, 23175655, 34365986283], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 122 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 122 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 122 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 122 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [56998256675, 48240826423, 17723136295, 17521814823, 1100340117799, 1100340184359], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30792376635, 22085140795, 4536249723, 1099987793275, 1099987794299, 1099987860859], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8780880299, 4435584427, 1099736133047, 1099736134071, 17286857167, 8680216015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099635467727, 1099635468751, 73507291, 4318139879, 23174631, 30071087595], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17186259435], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 122 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 122 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 122 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 122 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [56947993639, 35439813691, 26547809587, 22034811187, 17588920627, 8915105087], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100239520063, 1100239521087, 1099903907215, 1099903973775, 1099903974799, 4586578327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4469139863, 1099870351767, 13092620731, 8730548667, 1099685800387, 1099685801411], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4351695327, 56730079, 1099568358879], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 122 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 122 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 122 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61108811819, 18411009087, 22353508631, 17874063639, 17656030487, 1100071680359], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100071746919, 1100071747943, 1100071748967, 4586579339, 1099920682379, 1099920683403], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099920684427, 8780878271, 4485914047, 107062739, 1099618691539, 21481159147], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 122 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 122 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 122 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69531042863, 26564658419, 26279518451, 9149988083, 8965431663, 8797662575], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100038125935, 1099987860859, 1099987861883, 1099987862907, 1099820019107, 1099820020131], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820086691, 17404298675, 8780880307, 140617163, 1099652245963, 4334918115], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39952867, 17186260459], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 122 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 122 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 122 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [56730030131, 22135476491, 21900667147, 4804690187, 8847993203, 1100021347699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100021348723, 1100021415283, 1099937530247, 1099937531271, 13126177195, 4536246699], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099752909235, 1099752910259, 1099752911283, 8613106151, 4318141927, 23176679], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 7 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group7

import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass4

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [5670833157, 23624029195, 44815166481, 87128102945, 31814036541, 43759196489], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35169469769, 34968217929, 35135229265, 47483728337, 21663951325, 8762278369], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27902613515, 49026511893, 87061062693, 18996312129, 39514629437, 35102362941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26445394237, 47550838209, 17335431649, 30169927153, 17285098993, 4383426037], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [42953808393, 8594506249], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 130 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36443005965, 74259777561, 61509636145, 43775904069, 35186177349, 26294393213], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21898835325, 13023688165, 4450534885, 21529663997, 12939801085, 47282398721], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4299538953], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
private theorem i49 : checks (tilesOf batches) 130 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40738435089, 78487836705, 40185865273, 39514560829, 30924833085, 30690025789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8913273257, 17402470869, 13057242581, 4333094393, 8628057601, 4333093377], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47265624581, 21350917], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44899449877, 86943688741, 14617459777, 39548184865, 30874505505, 26428616993], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13141127617, 4433756641, 1099683973603, 21630325221, 13040462309, 47383133673], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34431266297, 4333091329, 21348869, 21349893], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57381898265, 78404223021, 30891213109, 30656471349, 9349480757, 43473979789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34833855885, 17436025285, 8862938565, 4366647789, 1099633641967, 17234696701], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30102746625, 21512885761, 38126081, 1099549754883, 8611278341, 4299536905], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61559559197, 61358641201, 26411766105, 21965876569, 4920296793, 43557934453], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30656397685, 13074017745, 4500864465, 1099616863731, 1099616864755, 12973285877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8628056577, 30086038021, 21347845, 21348869, 42954020361], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65753997345, 44329836601, 39363633505, 26462095713, 17637352837, 17486428549], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4534417873, 4450533841, 1099751082451, 12973352437, 4383421941, 71680505], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099583309307, 25774295561], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74159451173, 23073174589, 35236441401, 26545983801, 26294398265, 13174681017], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8779054525, 1099834968511, 4366646765, 1099633640943, 21563216373, 12956576245], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4333091329, 38126081, 8594500105, 4299535881], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78353823785, 6027527237, 35236509989, 26529275173, 17838684453, 4584749509], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4484088261, 17368915421, 8779051485, 1099667196391, 88457717, 1099600086519], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30136302073, 17251473913], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74075702317, 30924834093, 26411836717, 9332703533, 13157836233, 8812606921], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [172343777, 1099683972579, 1099683973603, 25824626173, 12939731453, 4333090305], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [38125057], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61325086769, 26462097745, 21982653777, 4937074001, 13090794957, 4500864461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099633640943, 1099633641967, 21546439161, 12956576249, 4333091329, 38126081], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [48574471221, 22016204149, 13376009589, 4786079093, 8678389229, 122012141], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099633640943, 1099633641967, 17251474937, 8661611001, 21347845], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 4 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤132 ∧ 5+a.j≤55 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group4

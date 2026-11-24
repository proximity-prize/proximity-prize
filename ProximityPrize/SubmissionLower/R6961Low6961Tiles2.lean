import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass2

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group2
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [10502933509, 1898125323, 1881349135, 1881350159, 1882137615, 1865361427], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1865362451, 1865887763, 1849111575, 1849112599, 1614494743, 1597718555], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1597719579, 1597917211, 1581141023, 1581142047, 1581339679, 1564563491], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1564564515, 1564696611, 1547920423, 1547921447, 1547988007, 1531211819], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1531278379, 1531279403, 1514503215, 87397138477, 68959240597, 13124748693], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [68942314905], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 115 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 115 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 115 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 115 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 115 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 115 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 115 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36224309257, 61895031829, 87329962025, 5944036421, 69043124609, 21798567297], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [68791385533, 55856077257], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 115 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 115 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 115 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 115 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 115 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 115 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [49026114573, 1346458655, 1329682467, 1329683491, 1329815587, 1313039399], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1313040423, 1313106983, 1296330795, 1296397355, 1296398379, 1279622191], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1279688751, 1279689775, 1262913587, 1262914611, 1262981171, 1246204983], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1699190839, 1699257399, 1682481211, 1682482235, 44648933433, 69177202017], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [60218156473, 60134496717], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 115 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 115 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 115 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 115 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 115 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 115 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [53405495313, 87212385317, 27435579457, 64882304353, 47702517089], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i12 : checks (tilesOf batches) 115 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 115 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 115 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 115 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 115 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 115 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [57667173397, 1346729003, 1346730027, 1329953839, 1330020399, 1330021423], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1313245235, 1313246259, 1313312819, 1296536631, 1296537655, 1296604215], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1279828027, 1279829051, 1279830075, 1263053887, 1263054911, 1263055935], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1246345283, 1246346307, 1246347331, 14533903429, 60537009517, 34767352173], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [222903756], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 115 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 115 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 115 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 115 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 115 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1748912155, 1732135967, 1732136991, 1732334623, 1715558435, 1715559459], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1715691555, 1698915367, 1698916391, 1698982951, 1682206763, 1682273323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1682274347, 1665498159, 1665564719, 82884068397, 56292377953, 21932784993], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [64496421309], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 115 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 115 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 115 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 115 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 115 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61895431197, 70116675633, 51863261569, 13208634753, 64462935493], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i21 : checks (tilesOf batches) 115 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 115 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 115 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 115 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1464033315, 1447257127, 1447258151, 1447324711, 1430548523, 1430615083], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1430616107, 1413839919, 1413906479, 1413907503, 1397131315, 1397132339], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1397198899, 1380422711, 1380423735, 1380490295, 1363714107, 1363715131], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [44598601785, 64748085633, 47551521153, 38588869, 47249596877], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 115 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 115 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 115 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 115 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1279552551, 1262776363, 1262842923, 1262843947, 1246067759, 1246134319], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1246135343, 1229359155, 1229360179, 1229426739, 1212650551, 1212651575], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1212718135, 1195941947, 1195942971, 1699260475, 1682484287, 1682485311], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1682486335, 1665775683, 23140613185, 60620893529], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 115 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 115 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 115 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 115 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1313175595, 1296399407, 1296465967, 1296466991, 1279690803, 1279691827], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1279758387, 1262982199, 1262983223, 1263049783, 1246273595, 1246274619], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1246275643, 1229499455, 1229500479, 1229501503, 1212790851, 1212791875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1212792899, 14533903429, 56275597669, 34800841061], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 115 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 115 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 115 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78572323885, 1632292937, 56275600733, 21949562205, 55856235977], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 115 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 115 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 115 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [70066343985, 51913593205, 13258966389], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 115 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 115 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 115 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [57332505653, 206216607, 206217631, 206218655, 1099717847455, 1099717848479], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099717915039, 1099717916063, 1099717917087, 1099717918111, 1099717919135, 1099717920159], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099717921183, 4501261725], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 115 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 115 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤115) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 2 where
  orders := orders
  covers := by
    intro a ha box
    change 17+a.b≤132 ∧ 3+a.j≤55 ∧ 1+a.t≤14 at box
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
end Low6961Allocation.Group2

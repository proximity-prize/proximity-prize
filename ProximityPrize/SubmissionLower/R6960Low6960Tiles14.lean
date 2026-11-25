import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass14

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group14
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [15150812165, 36560509967, 66022359067, 87262855215, 39380812151, 30740621687], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9316190583, 52114506139, 9164977561, 25808185883, 38389273, 34380979741], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 136 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32315545611, 45117814807, 112696976423, 1984483403, 44044739871, 43793223967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [18191269151, 30304408043, 17419579883, 8661878291, 42970987037], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i46 : checks (tilesOf batches) 136 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40805540879, 57550064671, 82816893997, 35169731923, 34934925651, 5155442003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47685389755, 34800631227, 17469843935, 13141392863, 38726280721, 4350059029], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8611544607, 4316580383, 4837920], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 136 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [45050572819, 78555274273, 44464318523, 43809856847, 30908320079, 17671170471], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17520246183, 1100036559271, 8745762299, 4417243643, 47349772809, 30103079451], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [38390299, 1099550019099, 38676095517, 17201474079, 4299800097, 4834848], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 136 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45067549719, 74277152805, 35908005949, 39464560983, 26563023191, 13711748439], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13191724467, 4618571187, 4450795007, 4383688191, 1099650682371, 1099650683395], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47316286993, 21529924117, 12940061205, 55166487, 1099566795287, 34397974041], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21608989], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [49178167323, 91222276137, 1799934025, 35354212643, 35035520289, 13711819041], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17570504135, 13208498631, 47484062187, 4467573227, 1099751344619, 1099751345643], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099684237819, 30136564241, 71866897, 8645095957, 4333354519, 1099566794263], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21610016], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61660550173, 69898506289, 26546245965, 26294660429, 9232304461, 43574973839], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26395246989, 8947019213, 8846424525, 1099868784079, 1099751344619, 1099751345643], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099751346667, 12990324233, 4383685133, 88719885], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65838211105, 52852924473, 39380672885, 26479135095, 21982913909, 17587354997], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100237885815, 4534681049, 4450797017, 1099818454491, 13090989555, 4501124593], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099650680323, 1099650681347, 55164437, 1099566793239, 25774557729], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [70015806501, 35840897085, 39414295903, 26428806493, 13275541921, 13141393825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100053336483, 4450796001, 1099784899043, 1099784900067, 21613811199, 8745758205], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4417239553, 1099617124875, 1099617125899, 34414751253, 21529924117, 4827680], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21608992], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69965543465, 23056661569, 35136108887, 26412096853, 9299343701, 4568237501], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099935894975, 1099935895999, 17385954803, 8779313649, 4366908929, 1099650680323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099650681347, 30136564241, 71866897, 55164437, 1099566793239, 4299797025], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4831776], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69898437677, 10272426053, 30908319051, 26378544457, 5105107273, 1099818453467], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099818454491, 1099818455515, 13174875613, 8812869085, 1099600347663, 1099600348687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25824888341, 55091733, 4350129685, 55164437], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65620316209, 1749602377, 26546245969, 26277883217, 4970891601, 13158100429], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8796093901, 1099734569455, 1099701012983, 1099701014007, 4383686145, 1099650680323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21563478541, 12973615629, 4366907921, 38388249], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [57097559093, 22167461221, 17704727909, 9098086757, 1099784899043, 1099784900067], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099784901091, 8796091877, 4450796005, 17268514317, 8678650381, 88719885], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099600348687, 38387225], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 14 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤138 ∧ 6+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group14

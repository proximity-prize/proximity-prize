import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass30

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group30
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [10905848837, 28070647819, 44882605079, 87128236067, 35991630911, 39531405643], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35085584715, 39179365707, 1099952477639, 13275344331, 13141130699, 8846233035], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43255870951, 25975622139, 13107570171, 4433755659, 4400268811, 1099667262987], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099667264011, 38726230559, 38192679, 38193703, 4316313131, 21479328303], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12889465391, 4299603503], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [28070647819, 44815496215, 87027572771, 35890967615, 35387433267, 35135915315], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34934663475, 8863010223, 13275343295, 8913271231, 8812611007, 43322979799], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21747762671, 13157899759, 1099767927283, 1099767928307, 1099751146999, 1099751148023], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099751149047, 4366645775, 1099650482703, 4366642719, 4333090335, 54967843], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34380931627, 21345835, 21346859], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36476757007, 65737017369, 82682480689, 30807394615, 30606141751, 13510232375], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39564888407, 30874431831, 13208234427, 8846162363, 4534420923, 1099918921167], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918922191, 1099918923215, 17436021227, 8862934507, 1099751146999, 1099751148023], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099734301179, 1099734302203, 1099734303227, 43104871947, 4383420939, 25858175513], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17268248091, 54899235, 1099566528035, 8611275307, 4566573], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36628148243, 74176091165, 61325155381, 35404141879, 26747304247, 26478941495], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21932388695, 13292128597, 1100002806203, 1100002807227, 1100002808251, 1100002809275], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812605895, 1099952405959, 1099952406983, 1099952408007, 13174609379, 8829380067], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717521919, 1099717522943, 1099717523967, 4366640671, 71675423, 21529655841], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12939792929, 4316308009], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40722054167, 82615165989, 35706418237, 31176353051, 35068806425, 30622918937], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8846166401, 1100237690243, 13208234401, 8846162337, 1100103402915, 1099969251779], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099969252803, 1099969253827, 17620567493, 9030638023, 8913266119, 1099834964451], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834965475, 1099834966499, 1099767853555, 1099767854579, 38826753541, 4400195095], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [105229847, 30102742567], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53103773721, 86826384429, 5843046473, 35169467661, 34917884173, 17788421389], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39313295763, 26428535187, 13292052885, 13157904789, 8795832725, 1100103470499], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099986031039, 1099986032063, 1099935629771, 1099935630795, 1099935697355, 13275270609], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8946818515, 1099868516827, 1099868517851, 1099868518875, 1099868519899, 4416973305], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [88451609, 1099600080411, 4316306985, 21341737], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61475738653, 74025504817, 26512494885, 26277621029, 13409569061, 35219658081], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26512423267, 8930045345, 8812607905, 1100103402915, 1100086626727, 1100086693287], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100086694311, 1100086695335, 8946750937, 8829379033, 1099868518875, 1099868519899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099868520923, 1099751075319, 1099751076343, 1099751077367, 21579987477, 8695091733], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4400194069, 105228821], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61459095585, 61207714869, 26311171385, 21882059065, 4802859321, 30924759393], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22234235233, 17771567457, 8812607901, 1100120180127, 1100120181151, 1100120247711], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100019585463, 1100019586487, 8812604861, 1099885296087, 1099885297111, 1099885298135], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8846154225, 4500858353, 1099751075319, 1099751076343, 1099751077367, 17268245017], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8678381081, 38118949, 38119973], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78320266277, 31344343105, 31109311769, 30773841177, 26294398233, 1100287953271], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100287954295, 1100288020855, 1100288021879, 13157903769, 1100136955291, 1100136956315], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100136957339, 13325602245, 8980372933, 4635077061, 1099851739615, 1099851740639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851741663, 25874886165, 12990056981, 88451609, 1099600080411, 4333084197], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38118949], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69814286377, 27082931265, 26730527025, 22234305841, 26227354929, 1100254398847], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100254399871, 1100254466431, 1100254467455, 8930045345, 8795830689, 1100103402915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099885296087, 1099885297111, 1099885298135, 8879642089, 4584743401, 4484082153], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099751076343, 1099751077367, 21563210265, 12956504601, 88451609, 1099600080411], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12889461293], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74008658989, 10054126661, 26663421213, 26395058461, 26177027357, 8879717761], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100237621635, 1100086693287, 1100086694311, 1100086695335, 9013928373, 8846159285], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100019513783, 1099935628747, 1099935629771, 1099935630795, 17419240949, 8829377013], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099751075319, 1099751076343, 1099751077367, 4333086237, 21341737, 21342761], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73958395953, 26562760981, 30539033877, 9181711637, 13225012617, 8846163337], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100204067211, 1100086693287, 1100086694311, 1100086695335, 1099935628747, 1099935629771], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935630795, 13258494421, 8879710677, 4500860381, 1099851740639, 1099851741663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633634835, 1099633635859, 4366639645, 71674397], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 30 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group30

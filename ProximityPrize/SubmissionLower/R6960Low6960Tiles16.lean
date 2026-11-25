import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass16

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group16
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23490268167, 40722572303, 142527515679, 48407530719, 56678907103, 31060243679], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34751151531, 21866324395, 13125466575, 8796948943, 38777392619, 47317208567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21513778685, 4317432323, 22467075], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
private theorem i51 : checks (tilesOf batches) 129 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36326348811, 44951026711, 108352596007, 1800785995, 39633185043, 43626303763], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [18024348947, 26094178743, 13226061239, 8746614239, 4418095583, 43105982947], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47317206519, 1099567649275, 34398828031, 39242239, 1099550871039, 17185479175], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4300652039, 5686788], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i46 : checks (tilesOf batches) 129 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40689017871, 61577448479, 78438959155, 30774954307, 30573701443, 9233156419], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43542269307, 30657509755, 13175728575, 8847276479, 4518757823, 1099685088735], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099685089759, 17286142447, 38727198197, 72795639, 1099584424439, 4334205439], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39240191, 8595615239], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i49 : checks (tilesOf batches) 129 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44900495379, 74194050083, 48558810171, 39482187071, 30791730495, 17672021367], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13293173111, 8964721015, 1099735419347, 1099735420371, 1099735421395, 4468423131], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4401316315, 47384244711, 25876071919, 12991177199, 4401312239, 72794615], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099584423415, 34365268487, 22460932], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i52 : checks (tilesOf batches) 129 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44917472279, 74160629799, 35724243007, 35220842811, 26513542459, 17856571707], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13175799175, 4602645895, 4451646927, 1099752195535, 1099752196559, 1099735420371], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099735421395, 8763320799, 4468422111, 43055726063, 21581106671, 106276333], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [72793591, 1099584422391], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44900894747, 65637872683, 31446119487, 30841992527, 22117913935, 13511273807], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8914386315, 8813726091, 1099802528195, 1099802529219, 1099802530243, 1099701861851], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099701862875, 1099701863899, 8696278503, 139901415, 17302918635, 4418021867], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43055794671, 4317426179], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53121799199, 74009774131, 1582682187, 26630981923, 30590477603, 9249932579], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39113086363, 26228325787, 13226059171, 8847209891, 1099936743843, 1099802527171], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099802528195, 1099802529219, 1099785753031, 4418090467, 1099668307427, 12974397939], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4367690231, 4367757815, 22460931], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57265905699, 61208827959, 22151469371, 21933437243, 9098938683, 39230595451], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22067579259, 8847208875, 4535532971, 1099903190443, 1099852859831, 1099852860855], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099852861879, 13024731615, 1099651530215, 1099651531239, 4418089451, 123124203], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8612323843, 22457859, 38660235783], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61409946663, 44146403387, 35069848923, 22117912923, 17672022363, 17470700891], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100238737755, 4569087395, 1099936744867, 1099936745891, 1099936746915, 8780098003], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4468422099, 1099651530215, 1099651531239, 17252585975, 8662656503, 39237119], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39238143, 22458883, 34365271559], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65570764843, 27100821571, 30875547967, 22134692159, 13494497599, 8864055683], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100070964611, 1100070965635, 1099785748935, 1099785749959, 1099785750983, 4518752723], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4418091475, 17319696863, 173387231, 89569779, 1099601198579, 30087084547], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12907289091, 22456833], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61292643375, 18594775107, 26563872071, 22050873671, 9165977927, 1099987076503], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099987077527, 1099987078551, 1099987079575, 13091840467, 4518752723, 4418091475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099735417299, 89569779, 1099601198579, 25775408647, 8595546631, 5680644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65436618803, 1532350539, 26547097895, 22050876711, 9199600935, 8880762291], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4569086387, 1099869634995, 1099836081595, 1099836082619, 1099836083643, 1099836084667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21614662115, 8729766371, 72792567, 1099584421367, 56014331, 17185477127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8595547655, 5681668], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 16 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤138 ∧ 6+a.j≤58 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group16

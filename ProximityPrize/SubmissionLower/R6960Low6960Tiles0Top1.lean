import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass0

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2298547205, 721489929, 4513141769, 4412480525, 26005021709, 77797605401], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099864022063, 1101391011887, 78016711729, 352392257, 1100031793219, 13942727753], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [18439681097, 18072000585, 18825157765, 30989633681, 35083610257, 23153677465], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [35686518969, 39043304669, 34681369821, 1100454156579, 1100420603171, 8962040097], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17400902957, 1100521195823, 1100470865199, 1100437311791, 1100454155567, 17568533821], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [13206528317, 1100504346943, 22148573505, 9246966081, 1100336641383, 1100336642407], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100336643431, 1100336644455, 1100336645479, 35134065009, 17920570745, 1100236054911], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100236055935, 1100202502527, 1100168798607, 1100168865167, 1100168866191, 1100168867215], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8928333213, 1100101687711, 1100101688735, 13139411425, 21762829797, 4482437617], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [34563625465, 1099699248639, 1099665627655, 1099632071183, 1099615294995, 1099598515735], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [12921374241, 36476449, 1099548183075, 1099531479591], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i3 : checks (tilesOf batches) 138 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 138 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 138 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤58) :
    Covered orders a ∨ Low6960Gate.Gated ((0 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

end Low6960Allocation.Group0

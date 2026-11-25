import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part588
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1242
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1306
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1370
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1434
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1498
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1562
import ProximityPrize.SubmissionLower.KoalaTaperTransfer
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRaw
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins0

-- merged module Low48PrimaryPivotBins3Part1626
section Merged_Low48PrimaryPivotBins3Part1626

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1626 : binChunk w3 1626 4 = 120032404970 := by decide +kernel
private theorem leaf1630 : binChunk w3 1630 4 = 121160404459 := by decide +kernel
private theorem leaf1634 : binChunk w3 1634 4 = 122221701776 := by decide +kernel
private theorem leaf1638 : binChunk w3 1638 4 = 123261945799 := by decide +kernel
private theorem leaf1642 : binChunk w3 1642 4 = 124281688820 := by decide +kernel
private theorem leaf1646 : binChunk w3 1646 4 = 125281634175 := by decide +kernel
private theorem leaf1650 : binChunk w3 1650 1 = 31474423420 := by decide +kernel
private theorem batch3_1630_1638 : binChunk w3 1630 8 = 243382106235 :=
  binChunk_join (w := w3) (start := 1630) (left := 4) (right := 4) (x := 121160404459) (y := 122221701776) leaf1630 leaf1634
private theorem batch3_1626_1638 : binChunk w3 1626 12 = 363414511205 :=
  binChunk_join (w := w3) (start := 1626) (left := 4) (right := 8) (x := 120032404970) (y := 243382106235) leaf1626 batch3_1630_1638
private theorem batch3_1638_1646 : binChunk w3 1638 8 = 247543634619 :=
  binChunk_join (w := w3) (start := 1638) (left := 4) (right := 4) (x := 123261945799) (y := 124281688820) leaf1638 leaf1642
private theorem batch3_1646_1651 : binChunk w3 1646 5 = 156756057595 :=
  binChunk_join (w := w3) (start := 1646) (left := 4) (right := 1) (x := 125281634175) (y := 31474423420) leaf1646 leaf1650
private theorem batch3_1638_1651 : binChunk w3 1638 13 = 404299692214 :=
  binChunk_join (w := w3) (start := 1638) (left := 8) (right := 5) (x := 247543634619) (y := 156756057595) batch3_1638_1646 batch3_1646_1651
theorem batch3_1626_1651 : binChunk w3 1626 25 = 767714203419 :=
  binChunk_join (w := w3) (start := 1626) (left := 12) (right := 13) (x := 363414511205) (y := 404299692214) batch3_1626_1638 batch3_1638_1651

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBins3Part1626

-- merged module Low48PrimaryPivotBins3
section Merged_Low48PrimaryPivotBins3

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem window3_1306_1434 : binChunk w3 1306 128 = 259342027810 :=
  binChunk_join (w := w3) (start := 1306) (left := 64) (right := 64) (x := 40502154112) (y := 218839873698) batch3_1306_1370 batch3_1370_1434
private theorem window3_1242_1434 : binChunk w3 1242 192 = 260726461076 :=
  binChunk_join (w := w3) (start := 1242) (left := 64) (right := 128) (x := 1384433266) (y := 259342027810) batch3_1242_1306 window3_1306_1434
private theorem window3_1434_1562 : binChunk w3 1434 128 = 1698101321440 :=
  binChunk_join (w := w3) (start := 1434) (left := 64) (right := 64) (x := 589827520782) (y := 1108273800658) batch3_1434_1498 batch3_1498_1562
private theorem window3_1562_1651 : binChunk w3 1562 89 = 2424003467786 :=
  binChunk_join (w := w3) (start := 1562) (left := 64) (right := 25) (x := 1656289264367) (y := 767714203419) batch3_1562_1626 batch3_1626_1651
private theorem window3_1434_1651 : binChunk w3 1434 217 = 4122104789226 :=
  binChunk_join (w := w3) (start := 1434) (left := 128) (right := 89) (x := 1698101321440) (y := 2424003467786) window3_1434_1562 window3_1562_1651
private theorem window3_1242_1651 : binChunk w3 1242 409 = 4382831250302 :=
  binChunk_join (w := w3) (start := 1242) (left := 192) (right := 217) (x := 260726461076) (y := 4122104789226) window3_1242_1434 window3_1434_1651
theorem binCompute3 : binCompute w3 = 4382831250302 := by
  exact (binCompute_eq_chunk w3 1242 (by decide) (by decide)).trans window3_1242_1651

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBins3

-- merged module KoalaTaperTransferReceipt
section Merged_KoalaTaperTransferReceipt

set_option Elab.async false
namespace KoalaTaperTransfer
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget Low48PrimaryPivot
open PolynomialDifferential ReedSolomon.HiddenDerivative

theorem node_rank (x y : Geom) :
    Module.finrank Geom
      (LinearMap.range ((localConstraintAt 3000 x y).domRestrict
        (TaperNormalize.space cap))) ≤ localRank := by
  apply node_rank_of_receipts x y
  · rw [rawWindow_w0, rawWindow_w2, rawWindow_w3]
  · have h0 := debit_le_binCompute w0 (by decide)
    have h2 := debit_le_binCompute w2 (by decide)
    have h3 := debit_le_binCompute w3 (by decide)
    rw [binCompute0] at h0
    rw [binCompute2] at h2
    rw [binCompute3] at h3
    omega

#print axioms node_rank
end KoalaTaperTransfer

end Merged_KoalaTaperTransferReceipt

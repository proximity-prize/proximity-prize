import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

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

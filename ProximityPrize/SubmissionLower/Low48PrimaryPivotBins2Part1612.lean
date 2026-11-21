import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1612 : binChunk w2 1612 4 = 265657093856 := by decide +kernel
private theorem leaf1616 : binChunk w2 1616 4 = 266973447960 := by decide +kernel
private theorem leaf1620 : binChunk w2 1620 4 = 268293156998 := by decide +kernel
private theorem leaf1624 : binChunk w2 1624 4 = 269615915976 := by decide +kernel
private theorem leaf1628 : binChunk w2 1628 4 = 270942029888 := by decide +kernel
private theorem leaf1632 : binChunk w2 1632 4 = 272271498734 := by decide +kernel
private theorem leaf1636 : binChunk w2 1636 4 = 273604017520 := by decide +kernel
private theorem leaf1640 : binChunk w2 1640 4 = 274939891240 := by decide +kernel
private theorem leaf1644 : binChunk w2 1644 4 = 276279119894 := by decide +kernel
private theorem leaf1648 : binChunk w2 1648 3 = 208090086344 := by decide +kernel
private theorem batch2_1612_1620 : binChunk w2 1612 8 = 532630541816 :=
  binChunk_join (w := w2) (start := 1612) (left := 4) (right := 4) (x := 265657093856) (y := 266973447960) leaf1612 leaf1616
private theorem batch2_1624_1632 : binChunk w2 1624 8 = 540557945864 :=
  binChunk_join (w := w2) (start := 1624) (left := 4) (right := 4) (x := 269615915976) (y := 270942029888) leaf1624 leaf1628
private theorem batch2_1620_1632 : binChunk w2 1620 12 = 808851102862 :=
  binChunk_join (w := w2) (start := 1620) (left := 4) (right := 8) (x := 268293156998) (y := 540557945864) leaf1620 batch2_1624_1632
private theorem batch2_1612_1632 : binChunk w2 1612 20 = 1341481644678 :=
  binChunk_join (w := w2) (start := 1612) (left := 8) (right := 12) (x := 532630541816) (y := 808851102862) batch2_1612_1620 batch2_1620_1632
private theorem batch2_1632_1640 : binChunk w2 1632 8 = 545875516254 :=
  binChunk_join (w := w2) (start := 1632) (left := 4) (right := 4) (x := 272271498734) (y := 273604017520) leaf1632 leaf1636
private theorem batch2_1644_1651 : binChunk w2 1644 7 = 484369206238 :=
  binChunk_join (w := w2) (start := 1644) (left := 4) (right := 3) (x := 276279119894) (y := 208090086344) leaf1644 leaf1648
private theorem batch2_1640_1651 : binChunk w2 1640 11 = 759309097478 :=
  binChunk_join (w := w2) (start := 1640) (left := 4) (right := 7) (x := 274939891240) (y := 484369206238) leaf1640 batch2_1644_1651
private theorem batch2_1632_1651 : binChunk w2 1632 19 = 1305184613732 :=
  binChunk_join (w := w2) (start := 1632) (left := 8) (right := 11) (x := 545875516254) (y := 759309097478) batch2_1632_1640 batch2_1640_1651
theorem batch2_1612_1651 : binChunk w2 1612 39 = 2646666258410 :=
  binChunk_join (w := w2) (start := 1612) (left := 20) (right := 19) (x := 1341481644678) (y := 1305184613732) batch2_1612_1632 batch2_1632_1651

end Low48PrimaryPivot

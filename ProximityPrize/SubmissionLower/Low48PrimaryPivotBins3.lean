import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1242
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1306
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1370
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1434
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1498
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1562
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1626

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem window3_1306_1434 : binChunk w3 1306 128 = 259342027810 :=
  binChunk_join (w:=w3) (start:=1306) (left:=64) (right:=64) (x:=40502154112) (y:=218839873698) batch3_1306_1370 batch3_1370_1434
private theorem window3_1242_1434 : binChunk w3 1242 192 = 260726461076 :=
  binChunk_join (w:=w3) (start:=1242) (left:=64) (right:=128) (x:=1384433266) (y:=259342027810) batch3_1242_1306 window3_1306_1434
private theorem window3_1434_1562 : binChunk w3 1434 128 = 1698101321440 :=
  binChunk_join (w:=w3) (start:=1434) (left:=64) (right:=64) (x:=589827520782) (y:=1108273800658) batch3_1434_1498 batch3_1498_1562
private theorem window3_1562_1651 : binChunk w3 1562 89 = 2424003467786 :=
  binChunk_join (w:=w3) (start:=1562) (left:=64) (right:=25) (x:=1656289264367) (y:=767714203419) batch3_1562_1626 batch3_1626_1651
private theorem window3_1434_1651 : binChunk w3 1434 217 = 4122104789226 :=
  binChunk_join (w:=w3) (start:=1434) (left:=128) (right:=89) (x:=1698101321440) (y:=2424003467786) window3_1434_1562 window3_1562_1651
private theorem window3_1242_1651 : binChunk w3 1242 409 = 4382831250302 :=
  binChunk_join (w:=w3) (start:=1242) (left:=192) (right:=217) (x:=260726461076) (y:=4122104789226) window3_1242_1434 window3_1434_1651
theorem binCompute3 : binCompute w3 = 4382831250302 := by
  exact (binCompute_eq_chunk w3 1242 (by decide) (by decide)).trans window3_1242_1651

end Low48PrimaryPivot

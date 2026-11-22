import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1434 : binChunk w3 1434 4 = 24064734637 := by decide +kernel
private theorem leaf1438 : binChunk w3 1438 4 = 25576581181 := by decide +kernel
private theorem leaf1442 : binChunk w3 1442 4 = 27133543108 := by decide +kernel
private theorem leaf1446 : binChunk w3 1446 4 = 28734742961 := by decide +kernel
private theorem leaf1450 : binChunk w3 1450 4 = 30379207821 := by decide +kernel
private theorem leaf1454 : binChunk w3 1454 4 = 32065951564 := by decide +kernel
private theorem leaf1458 : binChunk w3 1458 4 = 33793894992 := by decide +kernel
private theorem leaf1462 : binChunk w3 1462 4 = 35561861724 := by decide +kernel
private theorem leaf1466 : binChunk w3 1466 4 = 37368669244 := by decide +kernel
private theorem leaf1470 : binChunk w3 1470 4 = 39213041036 := by decide +kernel
private theorem leaf1474 : binChunk w3 1474 4 = 41093601436 := by decide +kernel
private theorem leaf1478 : binChunk w3 1478 4 = 43008974252 := by decide +kernel
private theorem leaf1482 : binChunk w3 1482 4 = 44957686568 := by decide +kernel
private theorem leaf1486 : binChunk w3 1486 4 = 46938163420 := by decide +kernel
private theorem leaf1490 : binChunk w3 1490 4 = 48948835036 := by decide +kernel
private theorem leaf1494 : binChunk w3 1494 4 = 50988031802 := by decide +kernel
private theorem batch3_1434_1442 : binChunk w3 1434 8 = 49641315818 :=
  binChunk_join (w := w3) (start := 1434) (left := 4) (right := 4) (x := 24064734637) (y := 25576581181) leaf1434 leaf1438
private theorem batch3_1442_1450 : binChunk w3 1442 8 = 55868286069 :=
  binChunk_join (w := w3) (start := 1442) (left := 4) (right := 4) (x := 27133543108) (y := 28734742961) leaf1442 leaf1446
private theorem batch3_1434_1450 : binChunk w3 1434 16 = 105509601887 :=
  binChunk_join (w := w3) (start := 1434) (left := 8) (right := 8) (x := 49641315818) (y := 55868286069) batch3_1434_1442 batch3_1442_1450
private theorem batch3_1450_1458 : binChunk w3 1450 8 = 62445159385 :=
  binChunk_join (w := w3) (start := 1450) (left := 4) (right := 4) (x := 30379207821) (y := 32065951564) leaf1450 leaf1454
private theorem batch3_1458_1466 : binChunk w3 1458 8 = 69355756716 :=
  binChunk_join (w := w3) (start := 1458) (left := 4) (right := 4) (x := 33793894992) (y := 35561861724) leaf1458 leaf1462
private theorem batch3_1450_1466 : binChunk w3 1450 16 = 131800916101 :=
  binChunk_join (w := w3) (start := 1450) (left := 8) (right := 8) (x := 62445159385) (y := 69355756716) batch3_1450_1458 batch3_1458_1466
private theorem batch3_1434_1466 : binChunk w3 1434 32 = 237310517988 :=
  binChunk_join (w := w3) (start := 1434) (left := 16) (right := 16) (x := 105509601887) (y := 131800916101) batch3_1434_1450 batch3_1450_1466
private theorem batch3_1466_1474 : binChunk w3 1466 8 = 76581710280 :=
  binChunk_join (w := w3) (start := 1466) (left := 4) (right := 4) (x := 37368669244) (y := 39213041036) leaf1466 leaf1470
private theorem batch3_1474_1482 : binChunk w3 1474 8 = 84102575688 :=
  binChunk_join (w := w3) (start := 1474) (left := 4) (right := 4) (x := 41093601436) (y := 43008974252) leaf1474 leaf1478
private theorem batch3_1466_1482 : binChunk w3 1466 16 = 160684285968 :=
  binChunk_join (w := w3) (start := 1466) (left := 8) (right := 8) (x := 76581710280) (y := 84102575688) batch3_1466_1474 batch3_1474_1482
private theorem batch3_1482_1490 : binChunk w3 1482 8 = 91895849988 :=
  binChunk_join (w := w3) (start := 1482) (left := 4) (right := 4) (x := 44957686568) (y := 46938163420) leaf1482 leaf1486
private theorem batch3_1490_1498 : binChunk w3 1490 8 = 99936866838 :=
  binChunk_join (w := w3) (start := 1490) (left := 4) (right := 4) (x := 48948835036) (y := 50988031802) leaf1490 leaf1494
private theorem batch3_1482_1498 : binChunk w3 1482 16 = 191832716826 :=
  binChunk_join (w := w3) (start := 1482) (left := 8) (right := 8) (x := 91895849988) (y := 99936866838) batch3_1482_1490 batch3_1490_1498
private theorem batch3_1466_1498 : binChunk w3 1466 32 = 352517002794 :=
  binChunk_join (w := w3) (start := 1466) (left := 16) (right := 16) (x := 160684285968) (y := 191832716826) batch3_1466_1482 batch3_1482_1498
theorem batch3_1434_1498 : binChunk w3 1434 64 = 589827520782 :=
  binChunk_join (w := w3) (start := 1434) (left := 32) (right := 32) (x := 237310517988) (y := 352517002794) batch3_1434_1466 batch3_1466_1498

end Low48PrimaryPivot

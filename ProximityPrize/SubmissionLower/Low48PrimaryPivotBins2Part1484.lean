import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1420

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1484 : binChunk w2 1484 4 = 225089963977 := by decide +kernel
private theorem leaf1488 : binChunk w2 1488 4 = 226352518683 := by decide +kernel
private theorem leaf1492 : binChunk w2 1492 4 = 227606421745 := by decide +kernel
private theorem leaf1496 : binChunk w2 1496 4 = 228853551405 := by decide +kernel
private theorem leaf1500 : binChunk w2 1500 4 = 230095471695 := by decide +kernel
private theorem leaf1504 : binChunk w2 1504 4 = 231333432437 := by decide +kernel
private theorem leaf1508 : binChunk w2 1508 4 = 232569284225 := by decide +kernel
private theorem leaf1512 : binChunk w2 1512 4 = 233804563443 := by decide +kernel
private theorem leaf1516 : binChunk w2 1516 4 = 235040492265 := by decide +kernel
private theorem leaf1520 : binChunk w2 1520 4 = 236278851800 := by decide +kernel
private theorem leaf1524 : binChunk w2 1524 4 = 237520482374 := by decide +kernel
private theorem leaf1528 : binChunk w2 1528 4 = 238765162888 := by decide +kernel
private theorem leaf1532 : binChunk w2 1532 4 = 240013198336 := by decide +kernel
private theorem leaf1536 : binChunk w2 1536 4 = 241264588718 := by decide +kernel
private theorem leaf1540 : binChunk w2 1540 4 = 242519029040 := by decide +kernel
private theorem leaf1544 : binChunk w2 1544 4 = 243776824296 := by decide +kernel
private theorem batch2_1484_1492 : binChunk w2 1484 8 = 451442482660 :=
  binChunk_join (w := w2) (start := 1484) (left := 4) (right := 4) (x := 225089963977) (y := 226352518683) leaf1484 leaf1488
private theorem batch2_1492_1500 : binChunk w2 1492 8 = 456459973150 :=
  binChunk_join (w := w2) (start := 1492) (left := 4) (right := 4) (x := 227606421745) (y := 228853551405) leaf1492 leaf1496
private theorem batch2_1484_1500 : binChunk w2 1484 16 = 907902455810 :=
  binChunk_join (w := w2) (start := 1484) (left := 8) (right := 8) (x := 451442482660) (y := 456459973150) batch2_1484_1492 batch2_1492_1500
private theorem batch2_1500_1508 : binChunk w2 1500 8 = 461428904132 :=
  binChunk_join (w := w2) (start := 1500) (left := 4) (right := 4) (x := 230095471695) (y := 231333432437) leaf1500 leaf1504
private theorem batch2_1508_1516 : binChunk w2 1508 8 = 466373847668 :=
  binChunk_join (w := w2) (start := 1508) (left := 4) (right := 4) (x := 232569284225) (y := 233804563443) leaf1508 leaf1512
private theorem batch2_1500_1516 : binChunk w2 1500 16 = 927802751800 :=
  binChunk_join (w := w2) (start := 1500) (left := 8) (right := 8) (x := 461428904132) (y := 466373847668) batch2_1500_1508 batch2_1508_1516
private theorem batch2_1484_1516 : binChunk w2 1484 32 = 1835705207610 :=
  binChunk_join (w := w2) (start := 1484) (left := 16) (right := 16) (x := 907902455810) (y := 927802751800) batch2_1484_1500 batch2_1500_1516
private theorem batch2_1516_1524 : binChunk w2 1516 8 = 471319344065 :=
  binChunk_join (w := w2) (start := 1516) (left := 4) (right := 4) (x := 235040492265) (y := 236278851800) leaf1516 leaf1520
private theorem batch2_1524_1532 : binChunk w2 1524 8 = 476285645262 :=
  binChunk_join (w := w2) (start := 1524) (left := 4) (right := 4) (x := 237520482374) (y := 238765162888) leaf1524 leaf1528
private theorem batch2_1516_1532 : binChunk w2 1516 16 = 947604989327 :=
  binChunk_join (w := w2) (start := 1516) (left := 8) (right := 8) (x := 471319344065) (y := 476285645262) batch2_1516_1524 batch2_1524_1532
private theorem batch2_1532_1540 : binChunk w2 1532 8 = 481277787054 :=
  binChunk_join (w := w2) (start := 1532) (left := 4) (right := 4) (x := 240013198336) (y := 241264588718) leaf1532 leaf1536
private theorem batch2_1540_1548 : binChunk w2 1540 8 = 486295853336 :=
  binChunk_join (w := w2) (start := 1540) (left := 4) (right := 4) (x := 242519029040) (y := 243776824296) leaf1540 leaf1544
private theorem batch2_1532_1548 : binChunk w2 1532 16 = 967573640390 :=
  binChunk_join (w := w2) (start := 1532) (left := 8) (right := 8) (x := 481277787054) (y := 486295853336) batch2_1532_1540 batch2_1540_1548
private theorem batch2_1516_1548 : binChunk w2 1516 32 = 1915178629717 :=
  binChunk_join (w := w2) (start := 1516) (left := 16) (right := 16) (x := 947604989327) (y := 967573640390) batch2_1516_1532 batch2_1532_1548
theorem batch2_1484_1548 : binChunk w2 1484 64 = 3750883837327 :=
  binChunk_join (w := w2) (start := 1484) (left := 32) (right := 32) (x := 1835705207610) (y := 1915178629717) batch2_1484_1516 batch2_1516_1548

end Low48PrimaryPivot

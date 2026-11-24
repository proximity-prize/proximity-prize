import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part588

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1548 : binChunk w2 1548 4 = 245037974486 := by decide +kernel
private theorem leaf1552 : binChunk w2 1552 4 = 246302174616 := by decide +kernel
private theorem leaf1556 : binChunk w2 1556 4 = 247569729680 := by decide +kernel
private theorem leaf1560 : binChunk w2 1560 4 = 248840639678 := by decide +kernel
private theorem leaf1564 : binChunk w2 1564 4 = 250114599616 := by decide +kernel
private theorem leaf1568 : binChunk w2 1568 4 = 251391914488 := by decide +kernel
private theorem leaf1572 : binChunk w2 1572 4 = 252672584294 := by decide +kernel
private theorem leaf1576 : binChunk w2 1576 4 = 253956304040 := by decide +kernel
private theorem leaf1580 : binChunk w2 1580 4 = 255243378720 := by decide +kernel
private theorem leaf1584 : binChunk w2 1584 4 = 256533808334 := by decide +kernel
private theorem leaf1588 : binChunk w2 1588 4 = 257827287888 := by decide +kernel
private theorem leaf1592 : binChunk w2 1592 4 = 259124122376 := by decide +kernel
private theorem leaf1596 : binChunk w2 1596 4 = 260424311798 := by decide +kernel
private theorem leaf1600 : binChunk w2 1600 4 = 261727551160 := by decide +kernel
private theorem leaf1604 : binChunk w2 1604 4 = 263034145456 := by decide +kernel
private theorem leaf1608 : binChunk w2 1608 4 = 264344094686 := by decide +kernel
private theorem batch2_1548_1556 : binChunk w2 1548 8 = 491340149102 :=
  binChunk_join (w := w2) (start := 1548) (left := 4) (right := 4) (x := 245037974486) (y := 246302174616) leaf1548 leaf1552
private theorem batch2_1556_1564 : binChunk w2 1556 8 = 496410369358 :=
  binChunk_join (w := w2) (start := 1556) (left := 4) (right := 4) (x := 247569729680) (y := 248840639678) leaf1556 leaf1560
private theorem batch2_1548_1564 : binChunk w2 1548 16 = 987750518460 :=
  binChunk_join (w := w2) (start := 1548) (left := 8) (right := 8) (x := 491340149102) (y := 496410369358) batch2_1548_1556 batch2_1556_1564
private theorem batch2_1564_1572 : binChunk w2 1564 8 = 501506514104 :=
  binChunk_join (w := w2) (start := 1564) (left := 4) (right := 4) (x := 250114599616) (y := 251391914488) leaf1564 leaf1568
private theorem batch2_1572_1580 : binChunk w2 1572 8 = 506628888334 :=
  binChunk_join (w := w2) (start := 1572) (left := 4) (right := 4) (x := 252672584294) (y := 253956304040) leaf1572 leaf1576
private theorem batch2_1564_1580 : binChunk w2 1564 16 = 1008135402438 :=
  binChunk_join (w := w2) (start := 1564) (left := 8) (right := 8) (x := 501506514104) (y := 506628888334) batch2_1564_1572 batch2_1572_1580
private theorem batch2_1548_1580 : binChunk w2 1548 32 = 1995885920898 :=
  binChunk_join (w := w2) (start := 1548) (left := 16) (right := 16) (x := 987750518460) (y := 1008135402438) batch2_1548_1564 batch2_1564_1580
private theorem batch2_1580_1588 : binChunk w2 1580 8 = 511777187054 :=
  binChunk_join (w := w2) (start := 1580) (left := 4) (right := 4) (x := 255243378720) (y := 256533808334) leaf1580 leaf1584
private theorem batch2_1588_1596 : binChunk w2 1588 8 = 516951410264 :=
  binChunk_join (w := w2) (start := 1588) (left := 4) (right := 4) (x := 257827287888) (y := 259124122376) leaf1588 leaf1592
private theorem batch2_1580_1596 : binChunk w2 1580 16 = 1028728597318 :=
  binChunk_join (w := w2) (start := 1580) (left := 8) (right := 8) (x := 511777187054) (y := 516951410264) batch2_1580_1588 batch2_1588_1596
private theorem batch2_1596_1604 : binChunk w2 1596 8 = 522151862958 :=
  binChunk_join (w := w2) (start := 1596) (left := 4) (right := 4) (x := 260424311798) (y := 261727551160) leaf1596 leaf1600
private theorem batch2_1604_1612 : binChunk w2 1604 8 = 527378240142 :=
  binChunk_join (w := w2) (start := 1604) (left := 4) (right := 4) (x := 263034145456) (y := 264344094686) leaf1604 leaf1608
private theorem batch2_1596_1612 : binChunk w2 1596 16 = 1049530103100 :=
  binChunk_join (w := w2) (start := 1596) (left := 8) (right := 8) (x := 522151862958) (y := 527378240142) batch2_1596_1604 batch2_1604_1612
private theorem batch2_1580_1612 : binChunk w2 1580 32 = 2078258700418 :=
  binChunk_join (w := w2) (start := 1580) (left := 16) (right := 16) (x := 1028728597318) (y := 1049530103100) batch2_1580_1596 batch2_1596_1612
theorem batch2_1548_1612 : binChunk w2 1548 64 = 4074144621316 :=
  binChunk_join (w := w2) (start := 1548) (left := 32) (right := 32) (x := 1995885920898) (y := 2078258700418) batch2_1548_1580 batch2_1580_1612

end Low48PrimaryPivot

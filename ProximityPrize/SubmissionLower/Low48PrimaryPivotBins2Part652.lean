import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part588

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf652 : binChunk w2 652 4 = 408322484 := by decide +kernel
private theorem leaf656 : binChunk w2 656 4 = 458432021 := by decide +kernel
private theorem leaf660 : binChunk w2 660 4 = 511353901 := by decide +kernel
private theorem leaf664 : binChunk w2 664 4 = 566014369 := by decide +kernel
private theorem leaf668 : binChunk w2 668 4 = 622420876 := by decide +kernel
private theorem leaf672 : binChunk w2 672 4 = 680604369 := by decide +kernel
private theorem leaf676 : binChunk w2 676 4 = 740577657 := by decide +kernel
private theorem leaf680 : binChunk w2 680 4 = 802387728 := by decide +kernel
private theorem leaf684 : binChunk w2 684 4 = 866066253 := by decide +kernel
private theorem leaf688 : binChunk w2 688 4 = 931623625 := by decide +kernel
private theorem leaf692 : binChunk w2 692 4 = 999110604 := by decide +kernel
private theorem leaf696 : binChunk w2 696 4 = 1068559585 := by decide +kernel
private theorem leaf700 : binChunk w2 700 4 = 1139978449 := by decide +kernel
private theorem leaf704 : binChunk w2 704 4 = 1213421824 := by decide +kernel
private theorem leaf708 : binChunk w2 708 4 = 1288922829 := by decide +kernel
private theorem leaf712 : binChunk w2 712 4 = 1366486737 := by decide +kernel
private theorem batch2_652_660 : binChunk w2 652 8 = 866754505 :=
  binChunk_join (w := w2) (start := 652) (left := 4) (right := 4) (x := 408322484) (y := 458432021) leaf652 leaf656
private theorem batch2_660_668 : binChunk w2 660 8 = 1077368270 :=
  binChunk_join (w := w2) (start := 660) (left := 4) (right := 4) (x := 511353901) (y := 566014369) leaf660 leaf664
private theorem batch2_652_668 : binChunk w2 652 16 = 1944122775 :=
  binChunk_join (w := w2) (start := 652) (left := 8) (right := 8) (x := 866754505) (y := 1077368270) batch2_652_660 batch2_660_668
private theorem batch2_668_676 : binChunk w2 668 8 = 1303025245 :=
  binChunk_join (w := w2) (start := 668) (left := 4) (right := 4) (x := 622420876) (y := 680604369) leaf668 leaf672
private theorem batch2_676_684 : binChunk w2 676 8 = 1542965385 :=
  binChunk_join (w := w2) (start := 676) (left := 4) (right := 4) (x := 740577657) (y := 802387728) leaf676 leaf680
private theorem batch2_668_684 : binChunk w2 668 16 = 2845990630 :=
  binChunk_join (w := w2) (start := 668) (left := 8) (right := 8) (x := 1303025245) (y := 1542965385) batch2_668_676 batch2_676_684
private theorem batch2_652_684 : binChunk w2 652 32 = 4790113405 :=
  binChunk_join (w := w2) (start := 652) (left := 16) (right := 16) (x := 1944122775) (y := 2845990630) batch2_652_668 batch2_668_684
private theorem batch2_684_692 : binChunk w2 684 8 = 1797689878 :=
  binChunk_join (w := w2) (start := 684) (left := 4) (right := 4) (x := 866066253) (y := 931623625) leaf684 leaf688
private theorem batch2_692_700 : binChunk w2 692 8 = 2067670189 :=
  binChunk_join (w := w2) (start := 692) (left := 4) (right := 4) (x := 999110604) (y := 1068559585) leaf692 leaf696
private theorem batch2_684_700 : binChunk w2 684 16 = 3865360067 :=
  binChunk_join (w := w2) (start := 684) (left := 8) (right := 8) (x := 1797689878) (y := 2067670189) batch2_684_692 batch2_692_700
private theorem batch2_700_708 : binChunk w2 700 8 = 2353400273 :=
  binChunk_join (w := w2) (start := 700) (left := 4) (right := 4) (x := 1139978449) (y := 1213421824) leaf700 leaf704
private theorem batch2_708_716 : binChunk w2 708 8 = 2655409566 :=
  binChunk_join (w := w2) (start := 708) (left := 4) (right := 4) (x := 1288922829) (y := 1366486737) leaf708 leaf712
private theorem batch2_700_716 : binChunk w2 700 16 = 5008809839 :=
  binChunk_join (w := w2) (start := 700) (left := 8) (right := 8) (x := 2353400273) (y := 2655409566) batch2_700_708 batch2_708_716
private theorem batch2_684_716 : binChunk w2 684 32 = 8874169906 :=
  binChunk_join (w := w2) (start := 684) (left := 16) (right := 16) (x := 3865360067) (y := 5008809839) batch2_684_700 batch2_700_716
theorem batch2_652_716 : binChunk w2 652 64 = 13664283311 :=
  binChunk_join (w := w2) (start := 652) (left := 32) (right := 32) (x := 4790113405) (y := 8874169906) batch2_652_684 batch2_684_716

end Low48PrimaryPivot

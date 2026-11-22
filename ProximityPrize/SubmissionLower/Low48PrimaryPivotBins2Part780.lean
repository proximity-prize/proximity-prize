import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf780 : binChunk w2 780 4 = 3035646861 := by decide +kernel
private theorem leaf784 : binChunk w2 784 4 = 3156379689 := by decide +kernel
private theorem leaf788 : binChunk w2 788 4 = 3279859596 := by decide +kernel
private theorem leaf792 : binChunk w2 792 4 = 3406124769 := by decide +kernel
private theorem leaf796 : binChunk w2 796 4 = 3535159537 := by decide +kernel
private theorem leaf800 : binChunk w2 800 4 = 3667052928 := by decide +kernel
private theorem leaf804 : binChunk w2 804 4 = 3801843853 := by decide +kernel
private theorem leaf808 : binChunk w2 808 4 = 3939513265 := by decide +kernel
private theorem leaf812 : binChunk w2 812 4 = 4080154924 := by decide +kernel
private theorem leaf816 : binChunk w2 816 4 = 4223808465 := by decide +kernel
private theorem leaf820 : binChunk w2 820 4 = 4370451369 := by decide +kernel
private theorem leaf824 : binChunk w2 824 4 = 4520183755 := by decide +kernel
private theorem leaf828 : binChunk w2 828 4 = 4673073376 := by decide +kernel
private theorem leaf832 : binChunk w2 832 4 = 4829155515 := by decide +kernel
private theorem leaf836 : binChunk w2 836 4 = 4988605195 := by decide +kernel
private theorem leaf840 : binChunk w2 840 4 = 5151542736 := by decide +kernel
private theorem batch2_780_788 : binChunk w2 780 8 = 6192026550 :=
  binChunk_join (w := w2) (start := 780) (left := 4) (right := 4) (x := 3035646861) (y := 3156379689) leaf780 leaf784
private theorem batch2_788_796 : binChunk w2 788 8 = 6685984365 :=
  binChunk_join (w := w2) (start := 788) (left := 4) (right := 4) (x := 3279859596) (y := 3406124769) leaf788 leaf792
private theorem batch2_780_796 : binChunk w2 780 16 = 12878010915 :=
  binChunk_join (w := w2) (start := 780) (left := 8) (right := 8) (x := 6192026550) (y := 6685984365) batch2_780_788 batch2_788_796
private theorem batch2_796_804 : binChunk w2 796 8 = 7202212465 :=
  binChunk_join (w := w2) (start := 796) (left := 4) (right := 4) (x := 3535159537) (y := 3667052928) leaf796 leaf800
private theorem batch2_804_812 : binChunk w2 804 8 = 7741357118 :=
  binChunk_join (w := w2) (start := 804) (left := 4) (right := 4) (x := 3801843853) (y := 3939513265) leaf804 leaf808
private theorem batch2_796_812 : binChunk w2 796 16 = 14943569583 :=
  binChunk_join (w := w2) (start := 796) (left := 8) (right := 8) (x := 7202212465) (y := 7741357118) batch2_796_804 batch2_804_812
private theorem batch2_780_812 : binChunk w2 780 32 = 27821580498 :=
  binChunk_join (w := w2) (start := 780) (left := 16) (right := 16) (x := 12878010915) (y := 14943569583) batch2_780_796 batch2_796_812
private theorem batch2_812_820 : binChunk w2 812 8 = 8303963389 :=
  binChunk_join (w := w2) (start := 812) (left := 4) (right := 4) (x := 4080154924) (y := 4223808465) leaf812 leaf816
private theorem batch2_820_828 : binChunk w2 820 8 = 8890635124 :=
  binChunk_join (w := w2) (start := 820) (left := 4) (right := 4) (x := 4370451369) (y := 4520183755) leaf820 leaf824
private theorem batch2_812_828 : binChunk w2 812 16 = 17194598513 :=
  binChunk_join (w := w2) (start := 812) (left := 8) (right := 8) (x := 8303963389) (y := 8890635124) batch2_812_820 batch2_820_828
private theorem batch2_828_836 : binChunk w2 828 8 = 9502228891 :=
  binChunk_join (w := w2) (start := 828) (left := 4) (right := 4) (x := 4673073376) (y := 4829155515) leaf828 leaf832
private theorem batch2_836_844 : binChunk w2 836 8 = 10140147931 :=
  binChunk_join (w := w2) (start := 836) (left := 4) (right := 4) (x := 4988605195) (y := 5151542736) leaf836 leaf840
private theorem batch2_828_844 : binChunk w2 828 16 = 19642376822 :=
  binChunk_join (w := w2) (start := 828) (left := 8) (right := 8) (x := 9502228891) (y := 10140147931) batch2_828_836 batch2_836_844
private theorem batch2_812_844 : binChunk w2 812 32 = 36836975335 :=
  binChunk_join (w := w2) (start := 812) (left := 16) (right := 16) (x := 17194598513) (y := 19642376822) batch2_812_828 batch2_828_844
theorem batch2_780_844 : binChunk w2 780 64 = 64658555833 :=
  binChunk_join (w := w2) (start := 780) (left := 32) (right := 32) (x := 27821580498) (y := 36836975335) batch2_780_812 batch2_812_844

end Low48PrimaryPivot

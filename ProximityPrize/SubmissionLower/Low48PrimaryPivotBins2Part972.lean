import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf972 : binChunk w2 972 4 = 13691872814 := by decide +kernel
private theorem leaf976 : binChunk w2 976 4 = 14094768023 := by decide +kernel
private theorem leaf980 : binChunk w2 980 4 = 14509585818 := by decide +kernel
private theorem leaf984 : binChunk w2 984 4 = 14936669298 := by decide +kernel
private theorem leaf988 : binChunk w2 988 4 = 15376236443 := by decide +kernel
private theorem leaf992 : binChunk w2 992 4 = 15828767766 := by decide +kernel
private theorem leaf996 : binChunk w2 996 4 = 16294623470 := by decide +kernel
private theorem leaf1000 : binChunk w2 1000 4 = 16774033015 := by decide +kernel
private theorem leaf1004 : binChunk w2 1004 4 = 17267499562 := by decide +kernel
private theorem leaf1008 : binChunk w2 1008 4 = 17775400418 := by decide +kernel
private theorem leaf1012 : binChunk w2 1012 4 = 18297976427 := by decide +kernel
private theorem leaf1016 : binChunk w2 1016 4 = 18835753494 := by decide +kernel
private theorem leaf1020 : binChunk w2 1020 4 = 19389126030 := by decide +kernel
private theorem leaf1024 : binChunk w2 1024 4 = 19958346167 := by decide +kernel
private theorem leaf1028 : binChunk w2 1028 4 = 20543962650 := by decide +kernel
private theorem leaf1032 : binChunk w2 1032 4 = 21146386994 := by decide +kernel
private theorem batch2_972_980 : binChunk w2 972 8 = 27786640837 :=
  binChunk_join (w := w2) (start := 972) (left := 4) (right := 4) (x := 13691872814) (y := 14094768023) leaf972 leaf976
private theorem batch2_980_988 : binChunk w2 980 8 = 29446255116 :=
  binChunk_join (w := w2) (start := 980) (left := 4) (right := 4) (x := 14509585818) (y := 14936669298) leaf980 leaf984
private theorem batch2_972_988 : binChunk w2 972 16 = 57232895953 :=
  binChunk_join (w := w2) (start := 972) (left := 8) (right := 8) (x := 27786640837) (y := 29446255116) batch2_972_980 batch2_980_988
private theorem batch2_988_996 : binChunk w2 988 8 = 31205004209 :=
  binChunk_join (w := w2) (start := 988) (left := 4) (right := 4) (x := 15376236443) (y := 15828767766) leaf988 leaf992
private theorem batch2_996_1004 : binChunk w2 996 8 = 33068656485 :=
  binChunk_join (w := w2) (start := 996) (left := 4) (right := 4) (x := 16294623470) (y := 16774033015) leaf996 leaf1000
private theorem batch2_988_1004 : binChunk w2 988 16 = 64273660694 :=
  binChunk_join (w := w2) (start := 988) (left := 8) (right := 8) (x := 31205004209) (y := 33068656485) batch2_988_996 batch2_996_1004
private theorem batch2_972_1004 : binChunk w2 972 32 = 121506556647 :=
  binChunk_join (w := w2) (start := 972) (left := 16) (right := 16) (x := 57232895953) (y := 64273660694) batch2_972_988 batch2_988_1004
private theorem batch2_1004_1012 : binChunk w2 1004 8 = 35042899980 :=
  binChunk_join (w := w2) (start := 1004) (left := 4) (right := 4) (x := 17267499562) (y := 17775400418) leaf1004 leaf1008
private theorem batch2_1012_1020 : binChunk w2 1012 8 = 37133729921 :=
  binChunk_join (w := w2) (start := 1012) (left := 4) (right := 4) (x := 18297976427) (y := 18835753494) leaf1012 leaf1016
private theorem batch2_1004_1020 : binChunk w2 1004 16 = 72176629901 :=
  binChunk_join (w := w2) (start := 1004) (left := 8) (right := 8) (x := 35042899980) (y := 37133729921) batch2_1004_1012 batch2_1012_1020
private theorem batch2_1020_1028 : binChunk w2 1020 8 = 39347472197 :=
  binChunk_join (w := w2) (start := 1020) (left := 4) (right := 4) (x := 19389126030) (y := 19958346167) leaf1020 leaf1024
private theorem batch2_1028_1036 : binChunk w2 1028 8 = 41690349644 :=
  binChunk_join (w := w2) (start := 1028) (left := 4) (right := 4) (x := 20543962650) (y := 21146386994) leaf1028 leaf1032
private theorem batch2_1020_1036 : binChunk w2 1020 16 = 81037821841 :=
  binChunk_join (w := w2) (start := 1020) (left := 8) (right := 8) (x := 39347472197) (y := 41690349644) batch2_1020_1028 batch2_1028_1036
private theorem batch2_1004_1036 : binChunk w2 1004 32 = 153214451742 :=
  binChunk_join (w := w2) (start := 1004) (left := 16) (right := 16) (x := 72176629901) (y := 81037821841) batch2_1004_1020 batch2_1020_1036
theorem batch2_972_1036 : binChunk w2 972 64 = 274721008389 :=
  binChunk_join (w := w2) (start := 972) (left := 32) (right := 32) (x := 121506556647) (y := 153214451742) batch2_972_1004 batch2_1004_1036

end Low48PrimaryPivot

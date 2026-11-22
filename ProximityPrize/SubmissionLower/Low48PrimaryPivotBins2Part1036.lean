import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1036 : binChunk w2 1036 4 = 21765882523 := by decide +kernel
private theorem leaf1040 : binChunk w2 1040 4 = 22403020918 := by decide +kernel
private theorem leaf1044 : binChunk w2 1044 4 = 23058230798 := by decide +kernel
private theorem leaf1048 : binChunk w2 1048 4 = 23731786583 := by decide +kernel
private theorem leaf1052 : binChunk w2 1052 4 = 24424282986 := by decide +kernel
private theorem leaf1056 : binChunk w2 1056 4 = 25136165730 := by decide +kernel
private theorem leaf1060 : binChunk w2 1060 4 = 25867720235 := by decide +kernel
private theorem leaf1064 : binChunk w2 1064 4 = 26619564342 := by decide +kernel
private theorem leaf1068 : binChunk w2 1068 4 = 27392160878 := by decide +kernel
private theorem leaf1072 : binChunk w2 1072 4 = 28185806167 := by decide +kernel
private theorem leaf1076 : binChunk w2 1076 4 = 29001141274 := by decide +kernel
private theorem leaf1080 : binChunk w2 1080 4 = 29838646130 := by decide +kernel
private theorem leaf1084 : binChunk w2 1084 4 = 30698627867 := by decide +kernel
private theorem leaf1088 : binChunk w2 1088 4 = 31581750870 := by decide +kernel
private theorem leaf1092 : binChunk w2 1092 4 = 32488512174 := by decide +kernel
private theorem leaf1096 : binChunk w2 1096 4 = 33419229623 := by decide +kernel
private theorem batch2_1036_1044 : binChunk w2 1036 8 = 44168903441 :=
  binChunk_join (w := w2) (start := 1036) (left := 4) (right := 4) (x := 21765882523) (y := 22403020918) leaf1036 leaf1040
private theorem batch2_1044_1052 : binChunk w2 1044 8 = 46790017381 :=
  binChunk_join (w := w2) (start := 1044) (left := 4) (right := 4) (x := 23058230798) (y := 23731786583) leaf1044 leaf1048
private theorem batch2_1036_1052 : binChunk w2 1036 16 = 90958920822 :=
  binChunk_join (w := w2) (start := 1036) (left := 8) (right := 8) (x := 44168903441) (y := 46790017381) batch2_1036_1044 batch2_1044_1052
private theorem batch2_1052_1060 : binChunk w2 1052 8 = 49560448716 :=
  binChunk_join (w := w2) (start := 1052) (left := 4) (right := 4) (x := 24424282986) (y := 25136165730) leaf1052 leaf1056
private theorem batch2_1060_1068 : binChunk w2 1060 8 = 52487284577 :=
  binChunk_join (w := w2) (start := 1060) (left := 4) (right := 4) (x := 25867720235) (y := 26619564342) leaf1060 leaf1064
private theorem batch2_1052_1068 : binChunk w2 1052 16 = 102047733293 :=
  binChunk_join (w := w2) (start := 1052) (left := 8) (right := 8) (x := 49560448716) (y := 52487284577) batch2_1052_1060 batch2_1060_1068
private theorem batch2_1036_1068 : binChunk w2 1036 32 = 193006654115 :=
  binChunk_join (w := w2) (start := 1036) (left := 16) (right := 16) (x := 90958920822) (y := 102047733293) batch2_1036_1052 batch2_1052_1068
private theorem batch2_1068_1076 : binChunk w2 1068 8 = 55577967045 :=
  binChunk_join (w := w2) (start := 1068) (left := 4) (right := 4) (x := 27392160878) (y := 28185806167) leaf1068 leaf1072
private theorem batch2_1076_1084 : binChunk w2 1076 8 = 58839787404 :=
  binChunk_join (w := w2) (start := 1076) (left := 4) (right := 4) (x := 29001141274) (y := 29838646130) leaf1076 leaf1080
private theorem batch2_1068_1084 : binChunk w2 1068 16 = 114417754449 :=
  binChunk_join (w := w2) (start := 1068) (left := 8) (right := 8) (x := 55577967045) (y := 58839787404) batch2_1068_1076 batch2_1076_1084
private theorem batch2_1084_1092 : binChunk w2 1084 8 = 62280378737 :=
  binChunk_join (w := w2) (start := 1084) (left := 4) (right := 4) (x := 30698627867) (y := 31581750870) leaf1084 leaf1088
private theorem batch2_1092_1100 : binChunk w2 1092 8 = 65907741797 :=
  binChunk_join (w := w2) (start := 1092) (left := 4) (right := 4) (x := 32488512174) (y := 33419229623) leaf1092 leaf1096
private theorem batch2_1084_1100 : binChunk w2 1084 16 = 128188120534 :=
  binChunk_join (w := w2) (start := 1084) (left := 8) (right := 8) (x := 62280378737) (y := 65907741797) batch2_1084_1092 batch2_1092_1100
private theorem batch2_1068_1100 : binChunk w2 1068 32 = 242605874983 :=
  binChunk_join (w := w2) (start := 1068) (left := 16) (right := 16) (x := 114417754449) (y := 128188120534) batch2_1068_1084 batch2_1084_1100
theorem batch2_1036_1100 : binChunk w2 1036 64 = 435612529098 :=
  binChunk_join (w := w2) (start := 1036) (left := 32) (right := 32) (x := 193006654115) (y := 242605874983) batch2_1036_1068 batch2_1068_1100

end Low48PrimaryPivot

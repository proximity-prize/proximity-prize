import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1242

section Pack_Low48PrimaryPivotBins2Part1036

set_option Elab.async false
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
end Pack_Low48PrimaryPivotBins2Part1036

section Pack_Low48PrimaryPivotBins2Part1100

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1100 : binChunk w2 1100 4 = 34374602309 := by decide +kernel
private theorem leaf1104 : binChunk w2 1104 4 = 35355286640 := by decide +kernel
private theorem leaf1108 : binChunk w2 1108 4 = 36361887072 := by decide +kernel
private theorem leaf1112 : binChunk w2 1112 4 = 37395427926 := by decide +kernel
private theorem leaf1116 : binChunk w2 1116 4 = 38456782253 := by decide +kernel
private theorem leaf1120 : binChunk w2 1120 4 = 39546659641 := by decide +kernel
private theorem leaf1124 : binChunk w2 1124 4 = 40666193844 := by decide +kernel
private theorem leaf1128 : binChunk w2 1128 4 = 41816349067 := by decide +kernel
private theorem leaf1132 : binChunk w2 1132 4 = 42997884911 := by decide +kernel
private theorem leaf1136 : binChunk w2 1136 4 = 44211957681 := by decide +kernel
private theorem leaf1140 : binChunk w2 1140 4 = 45459517836 := by decide +kernel
private theorem leaf1144 : binChunk w2 1144 4 = 46741297444 := by decide +kernel
private theorem leaf1148 : binChunk w2 1148 4 = 48058439224 := by decide +kernel
private theorem leaf1152 : binChunk w2 1152 4 = 49411883580 := by decide +kernel
private theorem leaf1156 : binChunk w2 1156 4 = 50802372449 := by decide +kernel
private theorem leaf1160 : binChunk w2 1160 4 = 52231102488 := by decide +kernel
private theorem batch2_1100_1108 : binChunk w2 1100 8 = 69729888949 :=
  binChunk_join (w := w2) (start := 1100) (left := 4) (right := 4) (x := 34374602309) (y := 35355286640) leaf1100 leaf1104
private theorem batch2_1108_1116 : binChunk w2 1108 8 = 73757314998 :=
  binChunk_join (w := w2) (start := 1108) (left := 4) (right := 4) (x := 36361887072) (y := 37395427926) leaf1108 leaf1112
private theorem batch2_1100_1116 : binChunk w2 1100 16 = 143487203947 :=
  binChunk_join (w := w2) (start := 1100) (left := 8) (right := 8) (x := 69729888949) (y := 73757314998) batch2_1100_1108 batch2_1108_1116
private theorem batch2_1116_1124 : binChunk w2 1116 8 = 78003441894 :=
  binChunk_join (w := w2) (start := 1116) (left := 4) (right := 4) (x := 38456782253) (y := 39546659641) leaf1116 leaf1120
private theorem batch2_1124_1132 : binChunk w2 1124 8 = 82482542911 :=
  binChunk_join (w := w2) (start := 1124) (left := 4) (right := 4) (x := 40666193844) (y := 41816349067) leaf1124 leaf1128
private theorem batch2_1116_1132 : binChunk w2 1116 16 = 160485984805 :=
  binChunk_join (w := w2) (start := 1116) (left := 8) (right := 8) (x := 78003441894) (y := 82482542911) batch2_1116_1124 batch2_1124_1132
private theorem batch2_1100_1132 : binChunk w2 1100 32 = 303973188752 :=
  binChunk_join (w := w2) (start := 1100) (left := 16) (right := 16) (x := 143487203947) (y := 160485984805) batch2_1100_1116 batch2_1116_1132
private theorem batch2_1132_1140 : binChunk w2 1132 8 = 87209842592 :=
  binChunk_join (w := w2) (start := 1132) (left := 4) (right := 4) (x := 42997884911) (y := 44211957681) leaf1132 leaf1136
private theorem batch2_1140_1148 : binChunk w2 1140 8 = 92200815280 :=
  binChunk_join (w := w2) (start := 1140) (left := 4) (right := 4) (x := 45459517836) (y := 46741297444) leaf1140 leaf1144
private theorem batch2_1132_1148 : binChunk w2 1132 16 = 179410657872 :=
  binChunk_join (w := w2) (start := 1132) (left := 8) (right := 8) (x := 87209842592) (y := 92200815280) batch2_1132_1140 batch2_1140_1148
private theorem batch2_1148_1156 : binChunk w2 1148 8 = 97470322804 :=
  binChunk_join (w := w2) (start := 1148) (left := 4) (right := 4) (x := 48058439224) (y := 49411883580) leaf1148 leaf1152
private theorem batch2_1156_1164 : binChunk w2 1156 8 = 103033474937 :=
  binChunk_join (w := w2) (start := 1156) (left := 4) (right := 4) (x := 50802372449) (y := 52231102488) leaf1156 leaf1160
private theorem batch2_1148_1164 : binChunk w2 1148 16 = 200503797741 :=
  binChunk_join (w := w2) (start := 1148) (left := 8) (right := 8) (x := 97470322804) (y := 103033474937) batch2_1148_1156 batch2_1156_1164
private theorem batch2_1132_1164 : binChunk w2 1132 32 = 379914455613 :=
  binChunk_join (w := w2) (start := 1132) (left := 16) (right := 16) (x := 179410657872) (y := 200503797741) batch2_1132_1148 batch2_1148_1164
theorem batch2_1100_1164 : binChunk w2 1100 64 = 683887644365 :=
  binChunk_join (w := w2) (start := 1100) (left := 32) (right := 32) (x := 303973188752) (y := 379914455613) batch2_1100_1132 batch2_1132_1164

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part1100

section Pack_Low48PrimaryPivotBins2Part1164

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1164 : binChunk w2 1164 4 = 53699082124 := by decide +kernel
private theorem leaf1168 : binChunk w2 1168 4 = 55207118657 := by decide +kernel
private theorem leaf1172 : binChunk w2 1172 4 = 56756487777 := by decide +kernel
private theorem leaf1176 : binChunk w2 1176 4 = 58348266593 := by decide +kernel
private theorem leaf1180 : binChunk w2 1180 4 = 59983315826 := by decide +kernel
private theorem leaf1184 : binChunk w2 1184 4 = 61662969685 := by decide +kernel
private theorem leaf1188 : binChunk w2 1188 4 = 63388351061 := by decide +kernel
private theorem leaf1192 : binChunk w2 1192 4 = 65160358278 := by decide +kernel
private theorem leaf1196 : binChunk w2 1196 4 = 66980377377 := by decide +kernel
private theorem leaf1200 : binChunk w2 1200 4 = 68849576001 := by decide +kernel
private theorem leaf1204 : binChunk w2 1204 4 = 70768889970 := by decide +kernel
private theorem leaf1208 : binChunk w2 1208 4 = 72739757253 := by decide +kernel
private theorem leaf1212 : binChunk w2 1212 4 = 74763390245 := by decide +kernel
private theorem leaf1216 : binChunk w2 1216 4 = 76840762166 := by decide +kernel
private theorem leaf1220 : binChunk w2 1220 4 = 78973363009 := by decide +kernel
private theorem leaf1224 : binChunk w2 1224 4 = 81162449921 := by decide +kernel
private theorem batch2_1164_1172 : binChunk w2 1164 8 = 108906200781 :=
  binChunk_join (w := w2) (start := 1164) (left := 4) (right := 4) (x := 53699082124) (y := 55207118657) leaf1164 leaf1168
private theorem batch2_1172_1180 : binChunk w2 1172 8 = 115104754370 :=
  binChunk_join (w := w2) (start := 1172) (left := 4) (right := 4) (x := 56756487777) (y := 58348266593) leaf1172 leaf1176
private theorem batch2_1164_1180 : binChunk w2 1164 16 = 224010955151 :=
  binChunk_join (w := w2) (start := 1164) (left := 8) (right := 8) (x := 108906200781) (y := 115104754370) batch2_1164_1172 batch2_1172_1180
private theorem batch2_1180_1188 : binChunk w2 1180 8 = 121646285511 :=
  binChunk_join (w := w2) (start := 1180) (left := 4) (right := 4) (x := 59983315826) (y := 61662969685) leaf1180 leaf1184
private theorem batch2_1188_1196 : binChunk w2 1188 8 = 128548709339 :=
  binChunk_join (w := w2) (start := 1188) (left := 4) (right := 4) (x := 63388351061) (y := 65160358278) leaf1188 leaf1192
private theorem batch2_1180_1196 : binChunk w2 1180 16 = 250194994850 :=
  binChunk_join (w := w2) (start := 1180) (left := 8) (right := 8) (x := 121646285511) (y := 128548709339) batch2_1180_1188 batch2_1188_1196
private theorem batch2_1164_1196 : binChunk w2 1164 32 = 474205950001 :=
  binChunk_join (w := w2) (start := 1164) (left := 16) (right := 16) (x := 224010955151) (y := 250194994850) batch2_1164_1180 batch2_1180_1196
private theorem batch2_1196_1204 : binChunk w2 1196 8 = 135829953378 :=
  binChunk_join (w := w2) (start := 1196) (left := 4) (right := 4) (x := 66980377377) (y := 68849576001) leaf1196 leaf1200
private theorem batch2_1204_1212 : binChunk w2 1204 8 = 143508647223 :=
  binChunk_join (w := w2) (start := 1204) (left := 4) (right := 4) (x := 70768889970) (y := 72739757253) leaf1204 leaf1208
private theorem batch2_1196_1212 : binChunk w2 1196 16 = 279338600601 :=
  binChunk_join (w := w2) (start := 1196) (left := 8) (right := 8) (x := 135829953378) (y := 143508647223) batch2_1196_1204 batch2_1204_1212
private theorem batch2_1212_1220 : binChunk w2 1212 8 = 151604152411 :=
  binChunk_join (w := w2) (start := 1212) (left := 4) (right := 4) (x := 74763390245) (y := 76840762166) leaf1212 leaf1216
private theorem batch2_1220_1228 : binChunk w2 1220 8 = 160135812930 :=
  binChunk_join (w := w2) (start := 1220) (left := 4) (right := 4) (x := 78973363009) (y := 81162449921) leaf1220 leaf1224
private theorem batch2_1212_1228 : binChunk w2 1212 16 = 311739965341 :=
  binChunk_join (w := w2) (start := 1212) (left := 8) (right := 8) (x := 151604152411) (y := 160135812930) batch2_1212_1220 batch2_1220_1228
private theorem batch2_1196_1228 : binChunk w2 1196 32 = 591078565942 :=
  binChunk_join (w := w2) (start := 1196) (left := 16) (right := 16) (x := 279338600601) (y := 311739965341) batch2_1196_1212 batch2_1212_1228
theorem batch2_1164_1228 : binChunk w2 1164 64 = 1065284515943 :=
  binChunk_join (w := w2) (start := 1164) (left := 32) (right := 32) (x := 474205950001) (y := 591078565942) batch2_1164_1196 batch2_1196_1228

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part1164

section Pack_Low48PrimaryPivotBins2Part1228

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1228 : binChunk w2 1228 4 = 83409033426 := by decide +kernel
private theorem leaf1232 : binChunk w2 1232 4 = 85714655637 := by decide +kernel
private theorem leaf1236 : binChunk w2 1236 4 = 88080618453 := by decide +kernel
private theorem leaf1240 : binChunk w2 1240 4 = 90507880408 := by decide +kernel
private theorem leaf1244 : binChunk w2 1244 4 = 92996880168 := by decide +kernel
private theorem leaf1248 : binChunk w2 1248 4 = 95546444995 := by decide +kernel
private theorem leaf1252 : binChunk w2 1252 4 = 98154542085 := by decide +kernel
private theorem leaf1256 : binChunk w2 1256 4 = 100819492631 := by decide +kernel
private theorem leaf1260 : binChunk w2 1260 4 = 103539205957 := by decide +kernel
private theorem leaf1264 : binChunk w2 1264 4 = 106311161039 := by decide +kernel
private theorem leaf1268 : binChunk w2 1268 4 = 109133253805 := by decide +kernel
private theorem leaf1272 : binChunk w2 1272 4 = 112002960769 := by decide +kernel
private theorem leaf1276 : binChunk w2 1276 4 = 114917330661 := by decide +kernel
private theorem leaf1280 : binChunk w2 1280 4 = 117873841227 := by decide +kernel
private theorem leaf1284 : binChunk w2 1284 4 = 120869546005 := by decide +kernel
private theorem leaf1288 : binChunk w2 1288 4 = 123901066243 := by decide +kernel
private theorem batch2_1228_1236 : binChunk w2 1228 8 = 169123689063 :=
  binChunk_join (w := w2) (start := 1228) (left := 4) (right := 4) (x := 83409033426) (y := 85714655637) leaf1228 leaf1232
private theorem batch2_1236_1244 : binChunk w2 1236 8 = 178588498861 :=
  binChunk_join (w := w2) (start := 1236) (left := 4) (right := 4) (x := 88080618453) (y := 90507880408) leaf1236 leaf1240
private theorem batch2_1228_1244 : binChunk w2 1228 16 = 347712187924 :=
  binChunk_join (w := w2) (start := 1228) (left := 8) (right := 8) (x := 169123689063) (y := 178588498861) batch2_1228_1236 batch2_1236_1244
private theorem batch2_1244_1252 : binChunk w2 1244 8 = 188543325163 :=
  binChunk_join (w := w2) (start := 1244) (left := 4) (right := 4) (x := 92996880168) (y := 95546444995) leaf1244 leaf1248
private theorem batch2_1252_1260 : binChunk w2 1252 8 = 198974034716 :=
  binChunk_join (w := w2) (start := 1252) (left := 4) (right := 4) (x := 98154542085) (y := 100819492631) leaf1252 leaf1256
private theorem batch2_1244_1260 : binChunk w2 1244 16 = 387517359879 :=
  binChunk_join (w := w2) (start := 1244) (left := 8) (right := 8) (x := 188543325163) (y := 198974034716) batch2_1244_1252 batch2_1252_1260
private theorem batch2_1228_1260 : binChunk w2 1228 32 = 735229547803 :=
  binChunk_join (w := w2) (start := 1228) (left := 16) (right := 16) (x := 347712187924) (y := 387517359879) batch2_1228_1244 batch2_1244_1260
private theorem batch2_1260_1268 : binChunk w2 1260 8 = 209850366996 :=
  binChunk_join (w := w2) (start := 1260) (left := 4) (right := 4) (x := 103539205957) (y := 106311161039) leaf1260 leaf1264
private theorem batch2_1268_1276 : binChunk w2 1268 8 = 221136214574 :=
  binChunk_join (w := w2) (start := 1268) (left := 4) (right := 4) (x := 109133253805) (y := 112002960769) leaf1268 leaf1272
private theorem batch2_1260_1276 : binChunk w2 1260 16 = 430986581570 :=
  binChunk_join (w := w2) (start := 1260) (left := 8) (right := 8) (x := 209850366996) (y := 221136214574) batch2_1260_1268 batch2_1268_1276
private theorem batch2_1276_1284 : binChunk w2 1276 8 = 232791171888 :=
  binChunk_join (w := w2) (start := 1276) (left := 4) (right := 4) (x := 114917330661) (y := 117873841227) leaf1276 leaf1280
private theorem batch2_1284_1292 : binChunk w2 1284 8 = 244770612248 :=
  binChunk_join (w := w2) (start := 1284) (left := 4) (right := 4) (x := 120869546005) (y := 123901066243) leaf1284 leaf1288
private theorem batch2_1276_1292 : binChunk w2 1276 16 = 477561784136 :=
  binChunk_join (w := w2) (start := 1276) (left := 8) (right := 8) (x := 232791171888) (y := 244770612248) batch2_1276_1284 batch2_1284_1292
private theorem batch2_1260_1292 : binChunk w2 1260 32 = 908548365706 :=
  binChunk_join (w := w2) (start := 1260) (left := 16) (right := 16) (x := 430986581570) (y := 477561784136) batch2_1260_1276 batch2_1276_1292
theorem batch2_1228_1292 : binChunk w2 1228 64 = 1643777913509 :=
  binChunk_join (w := w2) (start := 1228) (left := 32) (right := 32) (x := 735229547803) (y := 908548365706) batch2_1228_1260 batch2_1260_1292

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part1228

section Pack_Low48PrimaryPivotBins2Part1292

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1292 : binChunk w2 1292 4 = 126965461361 := by decide +kernel
private theorem leaf1296 : binChunk w2 1296 4 = 130059361921 := by decide +kernel
private theorem leaf1300 : binChunk w2 1300 4 = 133178961833 := by decide +kernel
private theorem leaf1304 : binChunk w2 1304 4 = 136320902047 := by decide +kernel
private theorem leaf1308 : binChunk w2 1308 4 = 139481390149 := by decide +kernel
private theorem leaf1312 : binChunk w2 1312 4 = 142656192855 := by decide +kernel
private theorem leaf1316 : binChunk w2 1316 4 = 145841532501 := by decide +kernel
private theorem leaf1320 : binChunk w2 1320 4 = 149033193697 := by decide +kernel
private theorem leaf1324 : binChunk w2 1324 4 = 152226516611 := by decide +kernel
private theorem leaf1328 : binChunk w2 1328 4 = 155131440614 := by decide +kernel
private theorem leaf1332 : binChunk w2 1332 4 = 157548047920 := by decide +kernel
private theorem leaf1336 : binChunk w2 1336 4 = 159945914769 := by decide +kernel
private theorem leaf1340 : binChunk w2 1340 4 = 162322815841 := by decide +kernel
private theorem leaf1344 : binChunk w2 1344 4 = 164676253751 := by decide +kernel
private theorem leaf1348 : binChunk w2 1348 4 = 167003459772 := by decide +kernel
private theorem leaf1352 : binChunk w2 1352 4 = 169302307360 := by decide +kernel
private theorem batch2_1292_1300 : binChunk w2 1292 8 = 257024823282 :=
  binChunk_join (w := w2) (start := 1292) (left := 4) (right := 4) (x := 126965461361) (y := 130059361921) leaf1292 leaf1296
private theorem batch2_1300_1308 : binChunk w2 1300 8 = 269499863880 :=
  binChunk_join (w := w2) (start := 1300) (left := 4) (right := 4) (x := 133178961833) (y := 136320902047) leaf1300 leaf1304
private theorem batch2_1292_1308 : binChunk w2 1292 16 = 526524687162 :=
  binChunk_join (w := w2) (start := 1292) (left := 8) (right := 8) (x := 257024823282) (y := 269499863880) batch2_1292_1300 batch2_1300_1308
private theorem batch2_1308_1316 : binChunk w2 1308 8 = 282137583004 :=
  binChunk_join (w := w2) (start := 1308) (left := 4) (right := 4) (x := 139481390149) (y := 142656192855) leaf1308 leaf1312
private theorem batch2_1316_1324 : binChunk w2 1316 8 = 294874726198 :=
  binChunk_join (w := w2) (start := 1316) (left := 4) (right := 4) (x := 145841532501) (y := 149033193697) leaf1316 leaf1320
private theorem batch2_1308_1324 : binChunk w2 1308 16 = 577012309202 :=
  binChunk_join (w := w2) (start := 1308) (left := 8) (right := 8) (x := 282137583004) (y := 294874726198) batch2_1308_1316 batch2_1316_1324
private theorem batch2_1292_1324 : binChunk w2 1292 32 = 1103536996364 :=
  binChunk_join (w := w2) (start := 1292) (left := 16) (right := 16) (x := 526524687162) (y := 577012309202) batch2_1292_1308 batch2_1308_1324
private theorem batch2_1324_1332 : binChunk w2 1324 8 = 307357957225 :=
  binChunk_join (w := w2) (start := 1324) (left := 4) (right := 4) (x := 152226516611) (y := 155131440614) leaf1324 leaf1328
private theorem batch2_1332_1340 : binChunk w2 1332 8 = 317493962689 :=
  binChunk_join (w := w2) (start := 1332) (left := 4) (right := 4) (x := 157548047920) (y := 159945914769) leaf1332 leaf1336
private theorem batch2_1324_1340 : binChunk w2 1324 16 = 624851919914 :=
  binChunk_join (w := w2) (start := 1324) (left := 8) (right := 8) (x := 307357957225) (y := 317493962689) batch2_1324_1332 batch2_1332_1340
private theorem batch2_1340_1348 : binChunk w2 1340 8 = 326999069592 :=
  binChunk_join (w := w2) (start := 1340) (left := 4) (right := 4) (x := 162322815841) (y := 164676253751) leaf1340 leaf1344
private theorem batch2_1348_1356 : binChunk w2 1348 8 = 336305767132 :=
  binChunk_join (w := w2) (start := 1348) (left := 4) (right := 4) (x := 167003459772) (y := 169302307360) leaf1348 leaf1352
private theorem batch2_1340_1356 : binChunk w2 1340 16 = 663304836724 :=
  binChunk_join (w := w2) (start := 1340) (left := 8) (right := 8) (x := 326999069592) (y := 336305767132) batch2_1340_1348 batch2_1348_1356
private theorem batch2_1324_1356 : binChunk w2 1324 32 = 1288156756638 :=
  binChunk_join (w := w2) (start := 1324) (left := 16) (right := 16) (x := 624851919914) (y := 663304836724) batch2_1324_1340 batch2_1340_1356
theorem batch2_1292_1356 : binChunk w2 1292 64 = 2391693753002 :=
  binChunk_join (w := w2) (start := 1292) (left := 32) (right := 32) (x := 1103536996364) (y := 1288156756638) batch2_1292_1324 batch2_1324_1356

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part1292

section Pack_Low48PrimaryPivotBins2Part1356

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1356 : binChunk w2 1356 4 = 171570397906 := by decide +kernel
private theorem leaf1360 : binChunk w2 1360 4 = 173805061451 := by decide +kernel
private theorem leaf1364 : binChunk w2 1364 4 = 176004270227 := by decide +kernel
private theorem leaf1368 : binChunk w2 1368 4 = 178165724401 := by decide +kernel
private theorem leaf1372 : binChunk w2 1372 4 = 180286852782 := by decide +kernel
private theorem leaf1376 : binChunk w2 1376 4 = 182365726378 := by decide +kernel
private theorem leaf1380 : binChunk w2 1380 4 = 184400258463 := by decide +kernel
private theorem leaf1384 : binChunk w2 1384 4 = 186389570911 := by decide +kernel
private theorem leaf1388 : binChunk w2 1388 4 = 188335035962 := by decide +kernel
private theorem leaf1392 : binChunk w2 1392 4 = 190237883351 := by decide +kernel
private theorem leaf1396 : binChunk w2 1396 4 = 192099040335 := by decide +kernel
private theorem leaf1400 : binChunk w2 1400 4 = 193920045282 := by decide +kernel
private theorem leaf1404 : binChunk w2 1404 4 = 195702133391 := by decide +kernel
private theorem leaf1408 : binChunk w2 1408 4 = 197446237375 := by decide +kernel
private theorem leaf1412 : binChunk w2 1412 4 = 199153901066 := by decide +kernel
private theorem leaf1416 : binChunk w2 1416 4 = 200826365127 := by decide +kernel
private theorem batch2_1356_1364 : binChunk w2 1356 8 = 345375459357 :=
  binChunk_join (w := w2) (start := 1356) (left := 4) (right := 4) (x := 171570397906) (y := 173805061451) leaf1356 leaf1360
private theorem batch2_1364_1372 : binChunk w2 1364 8 = 354169994628 :=
  binChunk_join (w := w2) (start := 1364) (left := 4) (right := 4) (x := 176004270227) (y := 178165724401) leaf1364 leaf1368
private theorem batch2_1356_1372 : binChunk w2 1356 16 = 699545453985 :=
  binChunk_join (w := w2) (start := 1356) (left := 8) (right := 8) (x := 345375459357) (y := 354169994628) batch2_1356_1364 batch2_1364_1372
private theorem batch2_1372_1380 : binChunk w2 1372 8 = 362652579160 :=
  binChunk_join (w := w2) (start := 1372) (left := 4) (right := 4) (x := 180286852782) (y := 182365726378) leaf1372 leaf1376
private theorem batch2_1380_1388 : binChunk w2 1380 8 = 370789829374 :=
  binChunk_join (w := w2) (start := 1380) (left := 4) (right := 4) (x := 184400258463) (y := 186389570911) leaf1380 leaf1384
private theorem batch2_1372_1388 : binChunk w2 1372 16 = 733442408534 :=
  binChunk_join (w := w2) (start := 1372) (left := 8) (right := 8) (x := 362652579160) (y := 370789829374) batch2_1372_1380 batch2_1380_1388
private theorem batch2_1356_1388 : binChunk w2 1356 32 = 1432987862519 :=
  binChunk_join (w := w2) (start := 1356) (left := 16) (right := 16) (x := 699545453985) (y := 733442408534) batch2_1356_1372 batch2_1372_1388
private theorem batch2_1388_1396 : binChunk w2 1388 8 = 378572919313 :=
  binChunk_join (w := w2) (start := 1388) (left := 4) (right := 4) (x := 188335035962) (y := 190237883351) leaf1388 leaf1392
private theorem batch2_1396_1404 : binChunk w2 1396 8 = 386019085617 :=
  binChunk_join (w := w2) (start := 1396) (left := 4) (right := 4) (x := 192099040335) (y := 193920045282) leaf1396 leaf1400
private theorem batch2_1388_1404 : binChunk w2 1388 16 = 764592004930 :=
  binChunk_join (w := w2) (start := 1388) (left := 8) (right := 8) (x := 378572919313) (y := 386019085617) batch2_1388_1396 batch2_1396_1404
private theorem batch2_1404_1412 : binChunk w2 1404 8 = 393148370766 :=
  binChunk_join (w := w2) (start := 1404) (left := 4) (right := 4) (x := 195702133391) (y := 197446237375) leaf1404 leaf1408
private theorem batch2_1412_1420 : binChunk w2 1412 8 = 399980266193 :=
  binChunk_join (w := w2) (start := 1412) (left := 4) (right := 4) (x := 199153901066) (y := 200826365127) leaf1412 leaf1416
private theorem batch2_1404_1420 : binChunk w2 1404 16 = 793128636959 :=
  binChunk_join (w := w2) (start := 1404) (left := 8) (right := 8) (x := 393148370766) (y := 399980266193) batch2_1404_1412 batch2_1412_1420
private theorem batch2_1388_1420 : binChunk w2 1388 32 = 1557720641889 :=
  binChunk_join (w := w2) (start := 1388) (left := 16) (right := 16) (x := 764592004930) (y := 793128636959) batch2_1388_1404 batch2_1404_1420
theorem batch2_1356_1420 : binChunk w2 1356 64 = 2990708504408 :=
  binChunk_join (w := w2) (start := 1356) (left := 32) (right := 32) (x := 1432987862519) (y := 1557720641889) batch2_1356_1388 batch2_1388_1420

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part1356

section Pack_Low48PrimaryPivotBins2Part1420

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1420 : binChunk w2 1420 4 = 202464567727 := by decide +kernel
private theorem leaf1424 : binChunk w2 1424 4 = 204070058162 := by decide +kernel
private theorem leaf1428 : binChunk w2 1428 4 = 205644082559 := by decide +kernel
private theorem leaf1432 : binChunk w2 1432 4 = 207187584541 := by decide +kernel
private theorem leaf1436 : binChunk w2 1436 4 = 208702118243 := by decide +kernel
private theorem leaf1440 : binChunk w2 1440 4 = 210188929788 := by decide +kernel
private theorem leaf1444 : binChunk w2 1444 4 = 211648954048 := by decide +kernel
private theorem leaf1448 : binChunk w2 1448 4 = 213083727823 := by decide +kernel
private theorem leaf1452 : binChunk w2 1452 4 = 214494475528 := by decide +kernel
private theorem leaf1456 : binChunk w2 1456 4 = 215882151685 := by decide +kernel
private theorem leaf1460 : binChunk w2 1460 4 = 217248568017 := by decide +kernel
private theorem leaf1464 : binChunk w2 1464 4 = 218595366915 := by decide +kernel
private theorem leaf1468 : binChunk w2 1468 4 = 219923881145 := by decide +kernel
private theorem leaf1472 : binChunk w2 1472 4 = 221236044245 := by decide +kernel
private theorem leaf1476 : binChunk w2 1476 4 = 222533475543 := by decide +kernel
private theorem leaf1480 : binChunk w2 1480 4 = 223817480157 := by decide +kernel
private theorem batch2_1420_1428 : binChunk w2 1420 8 = 406534625889 :=
  binChunk_join (w := w2) (start := 1420) (left := 4) (right := 4) (x := 202464567727) (y := 204070058162) leaf1420 leaf1424
private theorem batch2_1428_1436 : binChunk w2 1428 8 = 412831667100 :=
  binChunk_join (w := w2) (start := 1428) (left := 4) (right := 4) (x := 205644082559) (y := 207187584541) leaf1428 leaf1432
private theorem batch2_1420_1436 : binChunk w2 1420 16 = 819366292989 :=
  binChunk_join (w := w2) (start := 1420) (left := 8) (right := 8) (x := 406534625889) (y := 412831667100) batch2_1420_1428 batch2_1428_1436
private theorem batch2_1436_1444 : binChunk w2 1436 8 = 418891048031 :=
  binChunk_join (w := w2) (start := 1436) (left := 4) (right := 4) (x := 208702118243) (y := 210188929788) leaf1436 leaf1440
private theorem batch2_1444_1452 : binChunk w2 1444 8 = 424732681871 :=
  binChunk_join (w := w2) (start := 1444) (left := 4) (right := 4) (x := 211648954048) (y := 213083727823) leaf1444 leaf1448
private theorem batch2_1436_1452 : binChunk w2 1436 16 = 843623729902 :=
  binChunk_join (w := w2) (start := 1436) (left := 8) (right := 8) (x := 418891048031) (y := 424732681871) batch2_1436_1444 batch2_1444_1452
private theorem batch2_1420_1452 : binChunk w2 1420 32 = 1662990022891 :=
  binChunk_join (w := w2) (start := 1420) (left := 16) (right := 16) (x := 819366292989) (y := 843623729902) batch2_1420_1436 batch2_1436_1452
private theorem batch2_1452_1460 : binChunk w2 1452 8 = 430376627213 :=
  binChunk_join (w := w2) (start := 1452) (left := 4) (right := 4) (x := 214494475528) (y := 215882151685) leaf1452 leaf1456
private theorem batch2_1460_1468 : binChunk w2 1460 8 = 435843934932 :=
  binChunk_join (w := w2) (start := 1460) (left := 4) (right := 4) (x := 217248568017) (y := 218595366915) leaf1460 leaf1464
private theorem batch2_1452_1468 : binChunk w2 1452 16 = 866220562145 :=
  binChunk_join (w := w2) (start := 1452) (left := 8) (right := 8) (x := 430376627213) (y := 435843934932) batch2_1452_1460 batch2_1460_1468
private theorem batch2_1468_1476 : binChunk w2 1468 8 = 441159925390 :=
  binChunk_join (w := w2) (start := 1468) (left := 4) (right := 4) (x := 219923881145) (y := 221236044245) leaf1468 leaf1472
private theorem batch2_1476_1484 : binChunk w2 1476 8 = 446350955700 :=
  binChunk_join (w := w2) (start := 1476) (left := 4) (right := 4) (x := 222533475543) (y := 223817480157) leaf1476 leaf1480
private theorem batch2_1468_1484 : binChunk w2 1468 16 = 887510881090 :=
  binChunk_join (w := w2) (start := 1468) (left := 8) (right := 8) (x := 441159925390) (y := 446350955700) batch2_1468_1476 batch2_1476_1484
private theorem batch2_1452_1484 : binChunk w2 1452 32 = 1753731443235 :=
  binChunk_join (w := w2) (start := 1452) (left := 16) (right := 16) (x := 866220562145) (y := 887510881090) batch2_1452_1468 batch2_1468_1484
theorem batch2_1420_1484 : binChunk w2 1420 64 = 3416721466126 :=
  binChunk_join (w := w2) (start := 1420) (left := 32) (right := 32) (x := 1662990022891) (y := 1753731443235) batch2_1420_1452 batch2_1452_1484

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part1420

section Pack_Low48PrimaryPivotBins2Part1484

set_option Elab.async false
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
end Pack_Low48PrimaryPivotBins2Part1484

section Pack_Low48PrimaryPivotBins2Part1548

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
end Pack_Low48PrimaryPivotBins2Part1548

section Pack_Low48PrimaryPivotBins2Part652

set_option Elab.async false
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
end Pack_Low48PrimaryPivotBins2Part652

section Pack_Low48PrimaryPivotBins2Part716

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf716 : binChunk w2 716 4 = 1446172140 := by decide +kernel
private theorem leaf720 : binChunk w2 720 4 = 1528012881 := by decide +kernel
private theorem leaf724 : binChunk w2 724 4 = 1612011529 := by decide +kernel
private theorem leaf728 : binChunk w2 728 4 = 1698230736 := by decide +kernel
private theorem leaf732 : binChunk w2 732 4 = 1786705069 := by decide +kernel
private theorem leaf736 : binChunk w2 736 4 = 1877434297 := by decide +kernel
private theorem leaf740 : binChunk w2 740 4 = 1970485228 := by decide +kernel
private theorem leaf744 : binChunk w2 744 4 = 2065893153 := by decide +kernel
private theorem leaf748 : binChunk w2 748 4 = 2163654945 := by decide +kernel
private theorem leaf752 : binChunk w2 752 4 = 2263841664 := by decide +kernel
private theorem leaf756 : binChunk w2 756 4 = 2366489325 := by decide +kernel
private theorem leaf760 : binChunk w2 760 4 = 2471591809 := by decide +kernel
private theorem leaf764 : binChunk w2 764 4 = 2579224524 := by decide +kernel
private theorem leaf768 : binChunk w2 768 4 = 2689424209 := by decide +kernel
private theorem leaf772 : binChunk w2 772 4 = 2802181657 := by decide +kernel
private theorem leaf776 : binChunk w2 776 4 = 2917576720 := by decide +kernel
private theorem batch2_716_724 : binChunk w2 716 8 = 2974185021 :=
  binChunk_join (w := w2) (start := 716) (left := 4) (right := 4) (x := 1446172140) (y := 1528012881) leaf716 leaf720
private theorem batch2_724_732 : binChunk w2 724 8 = 3310242265 :=
  binChunk_join (w := w2) (start := 724) (left := 4) (right := 4) (x := 1612011529) (y := 1698230736) leaf724 leaf728
private theorem batch2_716_732 : binChunk w2 716 16 = 6284427286 :=
  binChunk_join (w := w2) (start := 716) (left := 8) (right := 8) (x := 2974185021) (y := 3310242265) batch2_716_724 batch2_724_732
private theorem batch2_732_740 : binChunk w2 732 8 = 3664139366 :=
  binChunk_join (w := w2) (start := 732) (left := 4) (right := 4) (x := 1786705069) (y := 1877434297) leaf732 leaf736
private theorem batch2_740_748 : binChunk w2 740 8 = 4036378381 :=
  binChunk_join (w := w2) (start := 740) (left := 4) (right := 4) (x := 1970485228) (y := 2065893153) leaf740 leaf744
private theorem batch2_732_748 : binChunk w2 732 16 = 7700517747 :=
  binChunk_join (w := w2) (start := 732) (left := 8) (right := 8) (x := 3664139366) (y := 4036378381) batch2_732_740 batch2_740_748
private theorem batch2_716_748 : binChunk w2 716 32 = 13984945033 :=
  binChunk_join (w := w2) (start := 716) (left := 16) (right := 16) (x := 6284427286) (y := 7700517747) batch2_716_732 batch2_732_748
private theorem batch2_748_756 : binChunk w2 748 8 = 4427496609 :=
  binChunk_join (w := w2) (start := 748) (left := 4) (right := 4) (x := 2163654945) (y := 2263841664) leaf748 leaf752
private theorem batch2_756_764 : binChunk w2 756 8 = 4838081134 :=
  binChunk_join (w := w2) (start := 756) (left := 4) (right := 4) (x := 2366489325) (y := 2471591809) leaf756 leaf760
private theorem batch2_748_764 : binChunk w2 748 16 = 9265577743 :=
  binChunk_join (w := w2) (start := 748) (left := 8) (right := 8) (x := 4427496609) (y := 4838081134) batch2_748_756 batch2_756_764
private theorem batch2_764_772 : binChunk w2 764 8 = 5268648733 :=
  binChunk_join (w := w2) (start := 764) (left := 4) (right := 4) (x := 2579224524) (y := 2689424209) leaf764 leaf768
private theorem batch2_772_780 : binChunk w2 772 8 = 5719758377 :=
  binChunk_join (w := w2) (start := 772) (left := 4) (right := 4) (x := 2802181657) (y := 2917576720) leaf772 leaf776
private theorem batch2_764_780 : binChunk w2 764 16 = 10988407110 :=
  binChunk_join (w := w2) (start := 764) (left := 8) (right := 8) (x := 5268648733) (y := 5719758377) batch2_764_772 batch2_772_780
private theorem batch2_748_780 : binChunk w2 748 32 = 20253984853 :=
  binChunk_join (w := w2) (start := 748) (left := 16) (right := 16) (x := 9265577743) (y := 10988407110) batch2_748_764 batch2_764_780
theorem batch2_716_780 : binChunk w2 716 64 = 34238929886 :=
  binChunk_join (w := w2) (start := 716) (left := 32) (right := 32) (x := 13984945033) (y := 20253984853) batch2_716_748 batch2_748_780

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part716

section Pack_Low48PrimaryPivotBins2Part780

set_option Elab.async false
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
end Pack_Low48PrimaryPivotBins2Part780

section Pack_Low48PrimaryPivotBins2Part844

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf844 : binChunk w2 844 4 = 5318025555 := by decide +kernel
private theorem leaf848 : binChunk w2 848 4 = 5488256899 := by decide +kernel
private theorem leaf852 : binChunk w2 852 4 = 5662381016 := by decide +kernel
private theorem leaf856 : binChunk w2 856 4 = 5840474787 := by decide +kernel
private theorem leaf860 : binChunk w2 860 4 = 6022769779 := by decide +kernel
private theorem leaf864 : binChunk w2 864 4 = 6209434168 := by decide +kernel
private theorem leaf868 : binChunk w2 868 4 = 6400564203 := by decide +kernel
private theorem leaf872 : binChunk w2 872 4 = 6596419867 := by decide +kernel
private theorem leaf876 : binChunk w2 876 4 = 6797193264 := by decide +kernel
private theorem leaf880 : binChunk w2 880 4 = 7002999915 := by decide +kernel
private theorem leaf884 : binChunk w2 884 4 = 7214128315 := by decide +kernel
private theorem leaf888 : binChunk w2 888 4 = 7430794496 := by decide +kernel
private theorem leaf892 : binChunk w2 892 4 = 7653133155 := by decide +kernel
private theorem leaf896 : binChunk w2 896 4 = 7881461326 := by decide +kernel
private theorem leaf900 : binChunk w2 900 4 = 8116017607 := by decide +kernel
private theorem leaf904 : binChunk w2 904 4 = 8356950902 := by decide +kernel
private theorem batch2_844_852 : binChunk w2 844 8 = 10806282454 :=
  binChunk_join (w := w2) (start := 844) (left := 4) (right := 4) (x := 5318025555) (y := 5488256899) leaf844 leaf848
private theorem batch2_852_860 : binChunk w2 852 8 = 11502855803 :=
  binChunk_join (w := w2) (start := 852) (left := 4) (right := 4) (x := 5662381016) (y := 5840474787) leaf852 leaf856
private theorem batch2_844_860 : binChunk w2 844 16 = 22309138257 :=
  binChunk_join (w := w2) (start := 844) (left := 8) (right := 8) (x := 10806282454) (y := 11502855803) batch2_844_852 batch2_852_860
private theorem batch2_860_868 : binChunk w2 860 8 = 12232203947 :=
  binChunk_join (w := w2) (start := 860) (left := 4) (right := 4) (x := 6022769779) (y := 6209434168) leaf860 leaf864
private theorem batch2_868_876 : binChunk w2 868 8 = 12996984070 :=
  binChunk_join (w := w2) (start := 868) (left := 4) (right := 4) (x := 6400564203) (y := 6596419867) leaf868 leaf872
private theorem batch2_860_876 : binChunk w2 860 16 = 25229188017 :=
  binChunk_join (w := w2) (start := 860) (left := 8) (right := 8) (x := 12232203947) (y := 12996984070) batch2_860_868 batch2_868_876
private theorem batch2_844_876 : binChunk w2 844 32 = 47538326274 :=
  binChunk_join (w := w2) (start := 844) (left := 16) (right := 16) (x := 22309138257) (y := 25229188017) batch2_844_860 batch2_860_876
private theorem batch2_876_884 : binChunk w2 876 8 = 13800193179 :=
  binChunk_join (w := w2) (start := 876) (left := 4) (right := 4) (x := 6797193264) (y := 7002999915) leaf876 leaf880
private theorem batch2_884_892 : binChunk w2 884 8 = 14644922811 :=
  binChunk_join (w := w2) (start := 884) (left := 4) (right := 4) (x := 7214128315) (y := 7430794496) leaf884 leaf888
private theorem batch2_876_892 : binChunk w2 876 16 = 28445115990 :=
  binChunk_join (w := w2) (start := 876) (left := 8) (right := 8) (x := 13800193179) (y := 14644922811) batch2_876_884 batch2_884_892
private theorem batch2_892_900 : binChunk w2 892 8 = 15534594481 :=
  binChunk_join (w := w2) (start := 892) (left := 4) (right := 4) (x := 7653133155) (y := 7881461326) leaf892 leaf896
private theorem batch2_900_908 : binChunk w2 900 8 = 16472968509 :=
  binChunk_join (w := w2) (start := 900) (left := 4) (right := 4) (x := 8116017607) (y := 8356950902) leaf900 leaf904
private theorem batch2_892_908 : binChunk w2 892 16 = 32007562990 :=
  binChunk_join (w := w2) (start := 892) (left := 8) (right := 8) (x := 15534594481) (y := 16472968509) batch2_892_900 batch2_900_908
private theorem batch2_876_908 : binChunk w2 876 32 = 60452678980 :=
  binChunk_join (w := w2) (start := 876) (left := 16) (right := 16) (x := 28445115990) (y := 32007562990) batch2_876_892 batch2_892_908
theorem batch2_844_908 : binChunk w2 844 64 = 107991005254 :=
  binChunk_join (w := w2) (start := 844) (left := 32) (right := 32) (x := 47538326274) (y := 60452678980) batch2_844_876 batch2_876_908

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part844

section Pack_Low48PrimaryPivotBins2Part908

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf908 : binChunk w2 908 4 = 8604598058 := by decide +kernel
private theorem leaf912 : binChunk w2 912 4 = 8859209907 := by decide +kernel
private theorem leaf916 : binChunk w2 916 4 = 9120942058 := by decide +kernel
private theorem leaf920 : binChunk w2 920 4 = 9390147870 := by decide +kernel
private theorem leaf924 : binChunk w2 924 4 = 9667089815 := by decide +kernel
private theorem leaf928 : binChunk w2 928 4 = 9951930102 := by decide +kernel
private theorem leaf932 : binChunk w2 932 4 = 10245038746 := by decide +kernel
private theorem leaf936 : binChunk w2 936 4 = 10546690610 := by decide +kernel
private theorem leaf940 : binChunk w2 940 4 = 10857056795 := by decide +kernel
private theorem leaf944 : binChunk w2 944 4 = 11176528182 := by decide +kernel
private theorem leaf948 : binChunk w2 948 4 = 11505396558 := by decide +kernel
private theorem leaf952 : binChunk w2 952 4 = 11843844887 := by decide +kernel
private theorem leaf956 : binChunk w2 956 4 = 12192286314 := by decide +kernel
private theorem leaf960 : binChunk w2 960 4 = 12551029730 := by decide +kernel
private theorem leaf964 : binChunk w2 964 4 = 12920269867 := by decide +kernel
private theorem leaf968 : binChunk w2 968 4 = 13300442230 := by decide +kernel
private theorem batch2_908_916 : binChunk w2 908 8 = 17463807965 :=
  binChunk_join (w := w2) (start := 908) (left := 4) (right := 4) (x := 8604598058) (y := 8859209907) leaf908 leaf912
private theorem batch2_916_924 : binChunk w2 916 8 = 18511089928 :=
  binChunk_join (w := w2) (start := 916) (left := 4) (right := 4) (x := 9120942058) (y := 9390147870) leaf916 leaf920
private theorem batch2_908_924 : binChunk w2 908 16 = 35974897893 :=
  binChunk_join (w := w2) (start := 908) (left := 8) (right := 8) (x := 17463807965) (y := 18511089928) batch2_908_916 batch2_916_924
private theorem batch2_924_932 : binChunk w2 924 8 = 19619019917 :=
  binChunk_join (w := w2) (start := 924) (left := 4) (right := 4) (x := 9667089815) (y := 9951930102) leaf924 leaf928
private theorem batch2_932_940 : binChunk w2 932 8 = 20791729356 :=
  binChunk_join (w := w2) (start := 932) (left := 4) (right := 4) (x := 10245038746) (y := 10546690610) leaf932 leaf936
private theorem batch2_924_940 : binChunk w2 924 16 = 40410749273 :=
  binChunk_join (w := w2) (start := 924) (left := 8) (right := 8) (x := 19619019917) (y := 20791729356) batch2_924_932 batch2_932_940
private theorem batch2_908_940 : binChunk w2 908 32 = 76385647166 :=
  binChunk_join (w := w2) (start := 908) (left := 16) (right := 16) (x := 35974897893) (y := 40410749273) batch2_908_924 batch2_924_940
private theorem batch2_940_948 : binChunk w2 940 8 = 22033584977 :=
  binChunk_join (w := w2) (start := 940) (left := 4) (right := 4) (x := 10857056795) (y := 11176528182) leaf940 leaf944
private theorem batch2_948_956 : binChunk w2 948 8 = 23349241445 :=
  binChunk_join (w := w2) (start := 948) (left := 4) (right := 4) (x := 11505396558) (y := 11843844887) leaf948 leaf952
private theorem batch2_940_956 : binChunk w2 940 16 = 45382826422 :=
  binChunk_join (w := w2) (start := 940) (left := 8) (right := 8) (x := 22033584977) (y := 23349241445) batch2_940_948 batch2_948_956
private theorem batch2_956_964 : binChunk w2 956 8 = 24743316044 :=
  binChunk_join (w := w2) (start := 956) (left := 4) (right := 4) (x := 12192286314) (y := 12551029730) leaf956 leaf960
private theorem batch2_964_972 : binChunk w2 964 8 = 26220712097 :=
  binChunk_join (w := w2) (start := 964) (left := 4) (right := 4) (x := 12920269867) (y := 13300442230) leaf964 leaf968
private theorem batch2_956_972 : binChunk w2 956 16 = 50964028141 :=
  binChunk_join (w := w2) (start := 956) (left := 8) (right := 8) (x := 24743316044) (y := 26220712097) batch2_956_964 batch2_964_972
private theorem batch2_940_972 : binChunk w2 940 32 = 96346854563 :=
  binChunk_join (w := w2) (start := 940) (left := 16) (right := 16) (x := 45382826422) (y := 50964028141) batch2_940_956 batch2_956_972
theorem batch2_908_972 : binChunk w2 908 64 = 172732501729 :=
  binChunk_join (w := w2) (start := 908) (left := 32) (right := 32) (x := 76385647166) (y := 96346854563) batch2_908_940 batch2_940_972

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins2Part908

section Pack_Low48PrimaryPivotBins2Part972

set_option Elab.async false
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
end Pack_Low48PrimaryPivotBins2Part972

section Pack_Low48PrimaryPivotBins3Part1306

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1306 : binChunk w3 1306 4 = 487947106 := by decide +kernel
private theorem leaf1310 : binChunk w3 1310 4 = 616811471 := by decide +kernel
private theorem leaf1314 : binChunk w3 1314 4 = 769677322 := by decide +kernel
private theorem leaf1318 : binChunk w3 1318 4 = 949352080 := by decide +kernel
private theorem leaf1322 : binChunk w3 1322 4 = 1158807340 := by decide +kernel
private theorem leaf1326 : binChunk w3 1326 4 = 1401160580 := by decide +kernel
private theorem leaf1330 : binChunk w3 1330 4 = 1677499764 := by decide +kernel
private theorem leaf1334 : binChunk w3 1334 4 = 1986243250 := by decide +kernel
private theorem leaf1338 : binChunk w3 1338 4 = 2328927758 := by decide +kernel
private theorem leaf1342 : binChunk w3 1342 4 = 2707408533 := by decide +kernel
private theorem leaf1346 : binChunk w3 1346 4 = 3123500719 := by decide +kernel
private theorem leaf1350 : binChunk w3 1350 4 = 3578958011 := by decide +kernel
private theorem leaf1354 : binChunk w3 1354 4 = 4075469202 := by decide +kernel
private theorem leaf1358 : binChunk w3 1358 4 = 4614686584 := by decide +kernel
private theorem leaf1362 : binChunk w3 1362 4 = 5198199236 := by decide +kernel
private theorem leaf1366 : binChunk w3 1366 4 = 5827505156 := by decide +kernel
private theorem batch3_1306_1314 : binChunk w3 1306 8 = 1104758577 :=
  binChunk_join (w := w3) (start := 1306) (left := 4) (right := 4) (x := 487947106) (y := 616811471) leaf1306 leaf1310
private theorem batch3_1314_1322 : binChunk w3 1314 8 = 1719029402 :=
  binChunk_join (w := w3) (start := 1314) (left := 4) (right := 4) (x := 769677322) (y := 949352080) leaf1314 leaf1318
private theorem batch3_1306_1322 : binChunk w3 1306 16 = 2823787979 :=
  binChunk_join (w := w3) (start := 1306) (left := 8) (right := 8) (x := 1104758577) (y := 1719029402) batch3_1306_1314 batch3_1314_1322
private theorem batch3_1322_1330 : binChunk w3 1322 8 = 2559967920 :=
  binChunk_join (w := w3) (start := 1322) (left := 4) (right := 4) (x := 1158807340) (y := 1401160580) leaf1322 leaf1326
private theorem batch3_1330_1338 : binChunk w3 1330 8 = 3663743014 :=
  binChunk_join (w := w3) (start := 1330) (left := 4) (right := 4) (x := 1677499764) (y := 1986243250) leaf1330 leaf1334
private theorem batch3_1322_1338 : binChunk w3 1322 16 = 6223710934 :=
  binChunk_join (w := w3) (start := 1322) (left := 8) (right := 8) (x := 2559967920) (y := 3663743014) batch3_1322_1330 batch3_1330_1338
private theorem batch3_1306_1338 : binChunk w3 1306 32 = 9047498913 :=
  binChunk_join (w := w3) (start := 1306) (left := 16) (right := 16) (x := 2823787979) (y := 6223710934) batch3_1306_1322 batch3_1322_1338
private theorem batch3_1338_1346 : binChunk w3 1338 8 = 5036336291 :=
  binChunk_join (w := w3) (start := 1338) (left := 4) (right := 4) (x := 2328927758) (y := 2707408533) leaf1338 leaf1342
private theorem batch3_1346_1354 : binChunk w3 1346 8 = 6702458730 :=
  binChunk_join (w := w3) (start := 1346) (left := 4) (right := 4) (x := 3123500719) (y := 3578958011) leaf1346 leaf1350
private theorem batch3_1338_1354 : binChunk w3 1338 16 = 11738795021 :=
  binChunk_join (w := w3) (start := 1338) (left := 8) (right := 8) (x := 5036336291) (y := 6702458730) batch3_1338_1346 batch3_1346_1354
private theorem batch3_1354_1362 : binChunk w3 1354 8 = 8690155786 :=
  binChunk_join (w := w3) (start := 1354) (left := 4) (right := 4) (x := 4075469202) (y := 4614686584) leaf1354 leaf1358
private theorem batch3_1362_1370 : binChunk w3 1362 8 = 11025704392 :=
  binChunk_join (w := w3) (start := 1362) (left := 4) (right := 4) (x := 5198199236) (y := 5827505156) leaf1362 leaf1366
private theorem batch3_1354_1370 : binChunk w3 1354 16 = 19715860178 :=
  binChunk_join (w := w3) (start := 1354) (left := 8) (right := 8) (x := 8690155786) (y := 11025704392) batch3_1354_1362 batch3_1362_1370
private theorem batch3_1338_1370 : binChunk w3 1338 32 = 31454655199 :=
  binChunk_join (w := w3) (start := 1338) (left := 16) (right := 16) (x := 11738795021) (y := 19715860178) batch3_1338_1354 batch3_1354_1370
theorem batch3_1306_1370 : binChunk w3 1306 64 = 40502154112 :=
  binChunk_join (w := w3) (start := 1306) (left := 32) (right := 32) (x := 9047498913) (y := 31454655199) batch3_1306_1338 batch3_1338_1370

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins3Part1306

section Pack_Low48PrimaryPivotBins3Part1370

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1370 : binChunk w3 1370 4 = 6503833818 := by decide +kernel
private theorem leaf1374 : binChunk w3 1374 4 = 7228100930 := by decide +kernel
private theorem leaf1378 : binChunk w3 1378 4 = 8001052622 := by decide +kernel
private theorem leaf1382 : binChunk w3 1382 4 = 8823317912 := by decide +kernel
private theorem leaf1386 : binChunk w3 1386 4 = 9695382401 := by decide +kernel
private theorem leaf1390 : binChunk w3 1390 4 = 10617599465 := by decide +kernel
private theorem leaf1394 : binChunk w3 1394 4 = 11590239416 := by decide +kernel
private theorem leaf1398 : binChunk w3 1398 4 = 12613444989 := by decide +kernel
private theorem leaf1402 : binChunk w3 1402 4 = 13687227217 := by decide +kernel
private theorem leaf1406 : binChunk w3 1406 4 = 14811518456 := by decide +kernel
private theorem leaf1410 : binChunk w3 1410 4 = 15986121337 := by decide +kernel
private theorem leaf1414 : binChunk w3 1414 4 = 17210704473 := by decide +kernel
private theorem leaf1418 : binChunk w3 1418 4 = 18484862360 := by decide +kernel
private theorem leaf1422 : binChunk w3 1422 4 = 19808057525 := by decide +kernel
private theorem leaf1426 : binChunk w3 1426 4 = 21179616065 := by decide +kernel
private theorem leaf1430 : binChunk w3 1430 4 = 22598794712 := by decide +kernel
private theorem batch3_1370_1378 : binChunk w3 1370 8 = 13731934748 :=
  binChunk_join (w := w3) (start := 1370) (left := 4) (right := 4) (x := 6503833818) (y := 7228100930) leaf1370 leaf1374
private theorem batch3_1378_1386 : binChunk w3 1378 8 = 16824370534 :=
  binChunk_join (w := w3) (start := 1378) (left := 4) (right := 4) (x := 8001052622) (y := 8823317912) leaf1378 leaf1382
private theorem batch3_1370_1386 : binChunk w3 1370 16 = 30556305282 :=
  binChunk_join (w := w3) (start := 1370) (left := 8) (right := 8) (x := 13731934748) (y := 16824370534) batch3_1370_1378 batch3_1378_1386
private theorem batch3_1386_1394 : binChunk w3 1386 8 = 20312981866 :=
  binChunk_join (w := w3) (start := 1386) (left := 4) (right := 4) (x := 9695382401) (y := 10617599465) leaf1386 leaf1390
private theorem batch3_1394_1402 : binChunk w3 1394 8 = 24203684405 :=
  binChunk_join (w := w3) (start := 1394) (left := 4) (right := 4) (x := 11590239416) (y := 12613444989) leaf1394 leaf1398
private theorem batch3_1386_1402 : binChunk w3 1386 16 = 44516666271 :=
  binChunk_join (w := w3) (start := 1386) (left := 8) (right := 8) (x := 20312981866) (y := 24203684405) batch3_1386_1394 batch3_1394_1402
private theorem batch3_1370_1402 : binChunk w3 1370 32 = 75072971553 :=
  binChunk_join (w := w3) (start := 1370) (left := 16) (right := 16) (x := 30556305282) (y := 44516666271) batch3_1370_1386 batch3_1386_1402
private theorem batch3_1402_1410 : binChunk w3 1402 8 = 28498745673 :=
  binChunk_join (w := w3) (start := 1402) (left := 4) (right := 4) (x := 13687227217) (y := 14811518456) leaf1402 leaf1406
private theorem batch3_1410_1418 : binChunk w3 1410 8 = 33196825810 :=
  binChunk_join (w := w3) (start := 1410) (left := 4) (right := 4) (x := 15986121337) (y := 17210704473) leaf1410 leaf1414
private theorem batch3_1402_1418 : binChunk w3 1402 16 = 61695571483 :=
  binChunk_join (w := w3) (start := 1402) (left := 8) (right := 8) (x := 28498745673) (y := 33196825810) batch3_1402_1410 batch3_1410_1418
private theorem batch3_1418_1426 : binChunk w3 1418 8 = 38292919885 :=
  binChunk_join (w := w3) (start := 1418) (left := 4) (right := 4) (x := 18484862360) (y := 19808057525) leaf1418 leaf1422
private theorem batch3_1426_1434 : binChunk w3 1426 8 = 43778410777 :=
  binChunk_join (w := w3) (start := 1426) (left := 4) (right := 4) (x := 21179616065) (y := 22598794712) leaf1426 leaf1430
private theorem batch3_1418_1434 : binChunk w3 1418 16 = 82071330662 :=
  binChunk_join (w := w3) (start := 1418) (left := 8) (right := 8) (x := 38292919885) (y := 43778410777) batch3_1418_1426 batch3_1426_1434
private theorem batch3_1402_1434 : binChunk w3 1402 32 = 143766902145 :=
  binChunk_join (w := w3) (start := 1402) (left := 16) (right := 16) (x := 61695571483) (y := 82071330662) batch3_1402_1418 batch3_1418_1434
theorem batch3_1370_1434 : binChunk w3 1370 64 = 218839873698 :=
  binChunk_join (w := w3) (start := 1370) (left := 32) (right := 32) (x := 75072971553) (y := 143766902145) batch3_1370_1402 batch3_1402_1434

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins3Part1370

section Pack_Low48PrimaryPivotBins3Part1434

set_option Elab.async false
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
end Pack_Low48PrimaryPivotBins3Part1434

section Pack_Low48PrimaryPivotBins3Part1498

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1498 : binChunk w3 1498 4 = 53053967138 := by decide +kernel
private theorem leaf1502 : binChunk w3 1502 4 = 55144817602 := by decide +kernel
private theorem leaf1506 : binChunk w3 1506 4 = 57258592550 := by decide +kernel
private theorem leaf1510 : binChunk w3 1510 4 = 59393127666 := by decide +kernel
private theorem leaf1514 : binChunk w3 1514 4 = 61546210306 := by decide +kernel
private theorem leaf1518 : binChunk w3 1518 4 = 63715456818 := by decide +kernel
private theorem leaf1522 : binChunk w3 1522 4 = 65898306435 := by decide +kernel
private theorem leaf1526 : binChunk w3 1526 4 = 68092155611 := by decide +kernel
private theorem leaf1530 : binChunk w3 1530 4 = 70294280704 := by decide +kernel
private theorem leaf1534 : binChunk w3 1534 4 = 72501963041 := by decide +kernel
private theorem leaf1538 : binChunk w3 1538 4 = 74712677938 := by decide +kernel
private theorem leaf1542 : binChunk w3 1542 4 = 76923954175 := by decide +kernel
private theorem leaf1546 : binChunk w3 1546 4 = 79133367792 := by decide +kernel
private theorem leaf1550 : binChunk w3 1550 4 = 81338696749 := by decide +kernel
private theorem leaf1554 : binChunk w3 1554 4 = 83537769170 := by decide +kernel
private theorem leaf1558 : binChunk w3 1558 4 = 85728456963 := by decide +kernel
private theorem batch3_1498_1506 : binChunk w3 1498 8 = 108198784740 :=
  binChunk_join (w := w3) (start := 1498) (left := 4) (right := 4) (x := 53053967138) (y := 55144817602) leaf1498 leaf1502
private theorem batch3_1506_1514 : binChunk w3 1506 8 = 116651720216 :=
  binChunk_join (w := w3) (start := 1506) (left := 4) (right := 4) (x := 57258592550) (y := 59393127666) leaf1506 leaf1510
private theorem batch3_1498_1514 : binChunk w3 1498 16 = 224850504956 :=
  binChunk_join (w := w3) (start := 1498) (left := 8) (right := 8) (x := 108198784740) (y := 116651720216) batch3_1498_1506 batch3_1506_1514
private theorem batch3_1514_1522 : binChunk w3 1514 8 = 125261667124 :=
  binChunk_join (w := w3) (start := 1514) (left := 4) (right := 4) (x := 61546210306) (y := 63715456818) leaf1514 leaf1518
private theorem batch3_1522_1530 : binChunk w3 1522 8 = 133990462046 :=
  binChunk_join (w := w3) (start := 1522) (left := 4) (right := 4) (x := 65898306435) (y := 68092155611) leaf1522 leaf1526
private theorem batch3_1514_1530 : binChunk w3 1514 16 = 259252129170 :=
  binChunk_join (w := w3) (start := 1514) (left := 8) (right := 8) (x := 125261667124) (y := 133990462046) batch3_1514_1522 batch3_1522_1530
private theorem batch3_1498_1530 : binChunk w3 1498 32 = 484102634126 :=
  binChunk_join (w := w3) (start := 1498) (left := 16) (right := 16) (x := 224850504956) (y := 259252129170) batch3_1498_1514 batch3_1514_1530
private theorem batch3_1530_1538 : binChunk w3 1530 8 = 142796243745 :=
  binChunk_join (w := w3) (start := 1530) (left := 4) (right := 4) (x := 70294280704) (y := 72501963041) leaf1530 leaf1534
private theorem batch3_1538_1546 : binChunk w3 1538 8 = 151636632113 :=
  binChunk_join (w := w3) (start := 1538) (left := 4) (right := 4) (x := 74712677938) (y := 76923954175) leaf1538 leaf1542
private theorem batch3_1530_1546 : binChunk w3 1530 16 = 294432875858 :=
  binChunk_join (w := w3) (start := 1530) (left := 8) (right := 8) (x := 142796243745) (y := 151636632113) batch3_1530_1538 batch3_1538_1546
private theorem batch3_1546_1554 : binChunk w3 1546 8 = 160472064541 :=
  binChunk_join (w := w3) (start := 1546) (left := 4) (right := 4) (x := 79133367792) (y := 81338696749) leaf1546 leaf1550
private theorem batch3_1554_1562 : binChunk w3 1554 8 = 169266226133 :=
  binChunk_join (w := w3) (start := 1554) (left := 4) (right := 4) (x := 83537769170) (y := 85728456963) leaf1554 leaf1558
private theorem batch3_1546_1562 : binChunk w3 1546 16 = 329738290674 :=
  binChunk_join (w := w3) (start := 1546) (left := 8) (right := 8) (x := 160472064541) (y := 169266226133) batch3_1546_1554 batch3_1554_1562
private theorem batch3_1530_1562 : binChunk w3 1530 32 = 624171166532 :=
  binChunk_join (w := w3) (start := 1530) (left := 16) (right := 16) (x := 294432875858) (y := 329738290674) batch3_1530_1546 batch3_1546_1562
theorem batch3_1498_1562 : binChunk w3 1498 64 = 1108273800658 :=
  binChunk_join (w := w3) (start := 1498) (left := 32) (right := 32) (x := 484102634126) (y := 624171166532) batch3_1498_1530 batch3_1530_1562

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins3Part1498

section Pack_Low48PrimaryPivotBins3Part1562

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1562 : binChunk w3 1562 4 = 87908840828 := by decide +kernel
private theorem leaf1566 : binChunk w3 1566 4 = 90077048233 := by decide +kernel
private theorem leaf1570 : binChunk w3 1570 4 = 92231246858 := by decide +kernel
private theorem leaf1574 : binChunk w3 1574 4 = 94369820239 := by decide +kernel
private theorem leaf1578 : binChunk w3 1578 4 = 96491195188 := by decide +kernel
private theorem leaf1582 : binChunk w3 1582 4 = 98593835061 := by decide +kernel
private theorem leaf1586 : binChunk w3 1586 4 = 100676426326 := by decide +kernel
private theorem leaf1590 : binChunk w3 1590 4 = 102737695139 := by decide +kernel
private theorem leaf1594 : binChunk w3 1594 4 = 104776400436 := by decide +kernel
private theorem leaf1598 : binChunk w3 1598 4 = 106791531713 := by decide +kernel
private theorem leaf1602 : binChunk w3 1602 4 = 108782114470 := by decide +kernel
private theorem leaf1606 : binChunk w3 1606 4 = 110747203127 := by decide +kernel
private theorem leaf1610 : binChunk w3 1610 4 = 112686090304 := by decide +kernel
private theorem leaf1614 : binChunk w3 1614 4 = 114598100845 := by decide +kernel
private theorem leaf1618 : binChunk w3 1618 4 = 116482584558 := by decide +kernel
private theorem leaf1622 : binChunk w3 1622 4 = 118339131042 := by decide +kernel
private theorem batch3_1562_1570 : binChunk w3 1562 8 = 177985889061 :=
  binChunk_join (w := w3) (start := 1562) (left := 4) (right := 4) (x := 87908840828) (y := 90077048233) leaf1562 leaf1566
private theorem batch3_1570_1578 : binChunk w3 1570 8 = 186601067097 :=
  binChunk_join (w := w3) (start := 1570) (left := 4) (right := 4) (x := 92231246858) (y := 94369820239) leaf1570 leaf1574
private theorem batch3_1562_1578 : binChunk w3 1562 16 = 364586956158 :=
  binChunk_join (w := w3) (start := 1562) (left := 8) (right := 8) (x := 177985889061) (y := 186601067097) batch3_1562_1570 batch3_1570_1578
private theorem batch3_1578_1586 : binChunk w3 1578 8 = 195085030249 :=
  binChunk_join (w := w3) (start := 1578) (left := 4) (right := 4) (x := 96491195188) (y := 98593835061) leaf1578 leaf1582
private theorem batch3_1586_1594 : binChunk w3 1586 8 = 203414121465 :=
  binChunk_join (w := w3) (start := 1586) (left := 4) (right := 4) (x := 100676426326) (y := 102737695139) leaf1586 leaf1590
private theorem batch3_1578_1594 : binChunk w3 1578 16 = 398499151714 :=
  binChunk_join (w := w3) (start := 1578) (left := 8) (right := 8) (x := 195085030249) (y := 203414121465) batch3_1578_1586 batch3_1586_1594
private theorem batch3_1562_1594 : binChunk w3 1562 32 = 763086107872 :=
  binChunk_join (w := w3) (start := 1562) (left := 16) (right := 16) (x := 364586956158) (y := 398499151714) batch3_1562_1578 batch3_1578_1594
private theorem batch3_1594_1602 : binChunk w3 1594 8 = 211567932149 :=
  binChunk_join (w := w3) (start := 1594) (left := 4) (right := 4) (x := 104776400436) (y := 106791531713) leaf1594 leaf1598
private theorem batch3_1602_1610 : binChunk w3 1602 8 = 219529317597 :=
  binChunk_join (w := w3) (start := 1602) (left := 4) (right := 4) (x := 108782114470) (y := 110747203127) leaf1602 leaf1606
private theorem batch3_1594_1610 : binChunk w3 1594 16 = 431097249746 :=
  binChunk_join (w := w3) (start := 1594) (left := 8) (right := 8) (x := 211567932149) (y := 219529317597) batch3_1594_1602 batch3_1602_1610
private theorem batch3_1610_1618 : binChunk w3 1610 8 = 227284191149 :=
  binChunk_join (w := w3) (start := 1610) (left := 4) (right := 4) (x := 112686090304) (y := 114598100845) leaf1610 leaf1614
private theorem batch3_1618_1626 : binChunk w3 1618 8 = 234821715600 :=
  binChunk_join (w := w3) (start := 1618) (left := 4) (right := 4) (x := 116482584558) (y := 118339131042) leaf1618 leaf1622
private theorem batch3_1610_1626 : binChunk w3 1610 16 = 462105906749 :=
  binChunk_join (w := w3) (start := 1610) (left := 8) (right := 8) (x := 227284191149) (y := 234821715600) batch3_1610_1618 batch3_1618_1626
private theorem batch3_1594_1626 : binChunk w3 1594 32 = 893203156495 :=
  binChunk_join (w := w3) (start := 1594) (left := 16) (right := 16) (x := 431097249746) (y := 462105906749) batch3_1594_1610 batch3_1610_1626
theorem batch3_1562_1626 : binChunk w3 1562 64 = 1656289264367 :=
  binChunk_join (w := w3) (start := 1562) (left := 32) (right := 32) (x := 763086107872) (y := 893203156495) batch3_1562_1594 batch3_1594_1626

end Low48PrimaryPivot
end Pack_Low48PrimaryPivotBins3Part1562

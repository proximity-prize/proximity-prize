import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option linter.defProp false

namespace Low48PrimaryPivot
open K1_13_2_3

private def leaf1164:=checkedBin w2 1164 4 53699082124
private def leaf1168:=checkedBin w2 1168 4 55207118657
private def leaf1172:=checkedBin w2 1172 4 56756487777
private def leaf1176:=checkedBin w2 1176 4 58348266593
private def leaf1180:=checkedBin w2 1180 4 59983315826
private def leaf1184:=checkedBin w2 1184 4 61662969685
private def leaf1188:=checkedBin w2 1188 4 63388351061
private def leaf1192:=checkedBin w2 1192 4 65160358278
private def leaf1196:=checkedBin w2 1196 4 66980377377
private def leaf1200:=checkedBin w2 1200 4 68849576001
private def leaf1204:=checkedBin w2 1204 4 70768889970
private def leaf1208:=checkedBin w2 1208 4 72739757253
private def leaf1212:=checkedBin w2 1212 4 74763390245
private def leaf1216:=checkedBin w2 1216 4 76840762166
private def leaf1220:=checkedBin w2 1220 4 78973363009
private def leaf1224:=checkedBin w2 1224 4 81162449921
private theorem batch2_1164_1172 : binChunk w2 1164 8 = 108906200781 :=
  binChunk_join (w:=w2) (start:=1164) (left:=4) (right:=4) (x:=53699082124) (y:=55207118657) leaf1164 leaf1168
private theorem batch2_1172_1180 : binChunk w2 1172 8 = 115104754370 :=
  binChunk_join (w:=w2) (start:=1172) (left:=4) (right:=4) (x:=56756487777) (y:=58348266593) leaf1172 leaf1176
private theorem batch2_1164_1180 : binChunk w2 1164 16 = 224010955151 :=
  binChunk_join (w:=w2) (start:=1164) (left:=8) (right:=8) (x:=108906200781) (y:=115104754370) batch2_1164_1172 batch2_1172_1180
private theorem batch2_1180_1188 : binChunk w2 1180 8 = 121646285511 :=
  binChunk_join (w:=w2) (start:=1180) (left:=4) (right:=4) (x:=59983315826) (y:=61662969685) leaf1180 leaf1184
private theorem batch2_1188_1196 : binChunk w2 1188 8 = 128548709339 :=
  binChunk_join (w:=w2) (start:=1188) (left:=4) (right:=4) (x:=63388351061) (y:=65160358278) leaf1188 leaf1192
private theorem batch2_1180_1196 : binChunk w2 1180 16 = 250194994850 :=
  binChunk_join (w:=w2) (start:=1180) (left:=8) (right:=8) (x:=121646285511) (y:=128548709339) batch2_1180_1188 batch2_1188_1196
private theorem batch2_1164_1196 : binChunk w2 1164 32 = 474205950001 :=
  binChunk_join (w:=w2) (start:=1164) (left:=16) (right:=16) (x:=224010955151) (y:=250194994850) batch2_1164_1180 batch2_1180_1196
private theorem batch2_1196_1204 : binChunk w2 1196 8 = 135829953378 :=
  binChunk_join (w:=w2) (start:=1196) (left:=4) (right:=4) (x:=66980377377) (y:=68849576001) leaf1196 leaf1200
private theorem batch2_1204_1212 : binChunk w2 1204 8 = 143508647223 :=
  binChunk_join (w:=w2) (start:=1204) (left:=4) (right:=4) (x:=70768889970) (y:=72739757253) leaf1204 leaf1208
private theorem batch2_1196_1212 : binChunk w2 1196 16 = 279338600601 :=
  binChunk_join (w:=w2) (start:=1196) (left:=8) (right:=8) (x:=135829953378) (y:=143508647223) batch2_1196_1204 batch2_1204_1212
private theorem batch2_1212_1220 : binChunk w2 1212 8 = 151604152411 :=
  binChunk_join (w:=w2) (start:=1212) (left:=4) (right:=4) (x:=74763390245) (y:=76840762166) leaf1212 leaf1216
private theorem batch2_1220_1228 : binChunk w2 1220 8 = 160135812930 :=
  binChunk_join (w:=w2) (start:=1220) (left:=4) (right:=4) (x:=78973363009) (y:=81162449921) leaf1220 leaf1224
private theorem batch2_1212_1228 : binChunk w2 1212 16 = 311739965341 :=
  binChunk_join (w:=w2) (start:=1212) (left:=8) (right:=8) (x:=151604152411) (y:=160135812930) batch2_1212_1220 batch2_1220_1228
private theorem batch2_1196_1228 : binChunk w2 1196 32 = 591078565942 :=
  binChunk_join (w:=w2) (start:=1196) (left:=16) (right:=16) (x:=279338600601) (y:=311739965341) batch2_1196_1212 batch2_1212_1228
theorem batch2_1164_1228 : binChunk w2 1164 64 = 1065284515943 :=
  binChunk_join (w:=w2) (start:=1164) (left:=32) (right:=32) (x:=474205950001) (y:=591078565942) batch2_1164_1196 batch2_1196_1228

end Low48PrimaryPivot

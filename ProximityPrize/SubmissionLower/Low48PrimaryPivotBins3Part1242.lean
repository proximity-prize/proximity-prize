import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option linter.defProp false

namespace Low48PrimaryPivot
open K1_13_2_3

private def leaf1242:=checkedBin w3 1242 4 3026
private def leaf1246:=checkedBin w3 1246 4 54386
private def leaf1250:=checkedBin w3 1250 4 318775
private def leaf1254:=checkedBin w3 1254 4 1113843
private def leaf1258:=checkedBin w3 1258 4 2912970
private def leaf1262:=checkedBin w3 1262 4 6345591
private def leaf1266:=checkedBin w3 1266 4 12197098
private def leaf1270:=checkedBin w3 1270 4 21408184
private def leaf1274:=checkedBin w3 1274 4 35076245
private def leaf1278:=checkedBin w3 1278 4 54454402
private def leaf1282:=checkedBin w3 1282 4 80950390
private def leaf1286:=checkedBin w3 1286 4 116129795
private def leaf1290:=checkedBin w3 1290 4 161713466
private def leaf1294:=checkedBin w3 1294 4 219575940
private def leaf1298:=checkedBin w3 1298 4 291751233
private def leaf1302:=checkedBin w3 1302 4 380427922
private theorem batch3_1242_1250 : binChunk w3 1242 8 = 57412 :=
  binChunk_join (w:=w3) (start:=1242) (left:=4) (right:=4) (x:=3026) (y:=54386) leaf1242 leaf1246
private theorem batch3_1250_1258 : binChunk w3 1250 8 = 1432618 :=
  binChunk_join (w:=w3) (start:=1250) (left:=4) (right:=4) (x:=318775) (y:=1113843) leaf1250 leaf1254
private theorem batch3_1242_1258 : binChunk w3 1242 16 = 1490030 :=
  binChunk_join (w:=w3) (start:=1242) (left:=8) (right:=8) (x:=57412) (y:=1432618) batch3_1242_1250 batch3_1250_1258
private theorem batch3_1258_1266 : binChunk w3 1258 8 = 9258561 :=
  binChunk_join (w:=w3) (start:=1258) (left:=4) (right:=4) (x:=2912970) (y:=6345591) leaf1258 leaf1262
private theorem batch3_1266_1274 : binChunk w3 1266 8 = 33605282 :=
  binChunk_join (w:=w3) (start:=1266) (left:=4) (right:=4) (x:=12197098) (y:=21408184) leaf1266 leaf1270
private theorem batch3_1258_1274 : binChunk w3 1258 16 = 42863843 :=
  binChunk_join (w:=w3) (start:=1258) (left:=8) (right:=8) (x:=9258561) (y:=33605282) batch3_1258_1266 batch3_1266_1274
private theorem batch3_1242_1274 : binChunk w3 1242 32 = 44353873 :=
  binChunk_join (w:=w3) (start:=1242) (left:=16) (right:=16) (x:=1490030) (y:=42863843) batch3_1242_1258 batch3_1258_1274
private theorem batch3_1274_1282 : binChunk w3 1274 8 = 89530647 :=
  binChunk_join (w:=w3) (start:=1274) (left:=4) (right:=4) (x:=35076245) (y:=54454402) leaf1274 leaf1278
private theorem batch3_1282_1290 : binChunk w3 1282 8 = 197080185 :=
  binChunk_join (w:=w3) (start:=1282) (left:=4) (right:=4) (x:=80950390) (y:=116129795) leaf1282 leaf1286
private theorem batch3_1274_1290 : binChunk w3 1274 16 = 286610832 :=
  binChunk_join (w:=w3) (start:=1274) (left:=8) (right:=8) (x:=89530647) (y:=197080185) batch3_1274_1282 batch3_1282_1290
private theorem batch3_1290_1298 : binChunk w3 1290 8 = 381289406 :=
  binChunk_join (w:=w3) (start:=1290) (left:=4) (right:=4) (x:=161713466) (y:=219575940) leaf1290 leaf1294
private theorem batch3_1298_1306 : binChunk w3 1298 8 = 672179155 :=
  binChunk_join (w:=w3) (start:=1298) (left:=4) (right:=4) (x:=291751233) (y:=380427922) leaf1298 leaf1302
private theorem batch3_1290_1306 : binChunk w3 1290 16 = 1053468561 :=
  binChunk_join (w:=w3) (start:=1290) (left:=8) (right:=8) (x:=381289406) (y:=672179155) batch3_1290_1298 batch3_1298_1306
private theorem batch3_1274_1306 : binChunk w3 1274 32 = 1340079393 :=
  binChunk_join (w:=w3) (start:=1274) (left:=16) (right:=16) (x:=286610832) (y:=1053468561) batch3_1274_1290 batch3_1290_1306
theorem batch3_1242_1306 : binChunk w3 1242 64 = 1384433266 :=
  binChunk_join (w:=w3) (start:=1242) (left:=32) (right:=32) (x:=44353873) (y:=1340079393) batch3_1242_1274 batch3_1274_1306

end Low48PrimaryPivot

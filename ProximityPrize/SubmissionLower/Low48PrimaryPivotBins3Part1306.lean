import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option linter.defProp false

namespace Low48PrimaryPivot
open K1_13_2_3

private def leaf1306:=checkedBin w3 1306 4 487947106
private def leaf1310:=checkedBin w3 1310 4 616811471
private def leaf1314:=checkedBin w3 1314 4 769677322
private def leaf1318:=checkedBin w3 1318 4 949352080
private def leaf1322:=checkedBin w3 1322 4 1158807340
private def leaf1326:=checkedBin w3 1326 4 1401160580
private def leaf1330:=checkedBin w3 1330 4 1677499764
private def leaf1334:=checkedBin w3 1334 4 1986243250
private def leaf1338:=checkedBin w3 1338 4 2328927758
private def leaf1342:=checkedBin w3 1342 4 2707408533
private def leaf1346:=checkedBin w3 1346 4 3123500719
private def leaf1350:=checkedBin w3 1350 4 3578958011
private def leaf1354:=checkedBin w3 1354 4 4075469202
private def leaf1358:=checkedBin w3 1358 4 4614686584
private def leaf1362:=checkedBin w3 1362 4 5198199236
private def leaf1366:=checkedBin w3 1366 4 5827505156
private theorem batch3_1306_1314 : binChunk w3 1306 8 = 1104758577 :=
  binChunk_join (w:=w3) (start:=1306) (left:=4) (right:=4) (x:=487947106) (y:=616811471) leaf1306 leaf1310
private theorem batch3_1314_1322 : binChunk w3 1314 8 = 1719029402 :=
  binChunk_join (w:=w3) (start:=1314) (left:=4) (right:=4) (x:=769677322) (y:=949352080) leaf1314 leaf1318
private theorem batch3_1306_1322 : binChunk w3 1306 16 = 2823787979 :=
  binChunk_join (w:=w3) (start:=1306) (left:=8) (right:=8) (x:=1104758577) (y:=1719029402) batch3_1306_1314 batch3_1314_1322
private theorem batch3_1322_1330 : binChunk w3 1322 8 = 2559967920 :=
  binChunk_join (w:=w3) (start:=1322) (left:=4) (right:=4) (x:=1158807340) (y:=1401160580) leaf1322 leaf1326
private theorem batch3_1330_1338 : binChunk w3 1330 8 = 3663743014 :=
  binChunk_join (w:=w3) (start:=1330) (left:=4) (right:=4) (x:=1677499764) (y:=1986243250) leaf1330 leaf1334
private theorem batch3_1322_1338 : binChunk w3 1322 16 = 6223710934 :=
  binChunk_join (w:=w3) (start:=1322) (left:=8) (right:=8) (x:=2559967920) (y:=3663743014) batch3_1322_1330 batch3_1330_1338
private theorem batch3_1306_1338 : binChunk w3 1306 32 = 9047498913 :=
  binChunk_join (w:=w3) (start:=1306) (left:=16) (right:=16) (x:=2823787979) (y:=6223710934) batch3_1306_1322 batch3_1322_1338
private theorem batch3_1338_1346 : binChunk w3 1338 8 = 5036336291 :=
  binChunk_join (w:=w3) (start:=1338) (left:=4) (right:=4) (x:=2328927758) (y:=2707408533) leaf1338 leaf1342
private theorem batch3_1346_1354 : binChunk w3 1346 8 = 6702458730 :=
  binChunk_join (w:=w3) (start:=1346) (left:=4) (right:=4) (x:=3123500719) (y:=3578958011) leaf1346 leaf1350
private theorem batch3_1338_1354 : binChunk w3 1338 16 = 11738795021 :=
  binChunk_join (w:=w3) (start:=1338) (left:=8) (right:=8) (x:=5036336291) (y:=6702458730) batch3_1338_1346 batch3_1346_1354
private theorem batch3_1354_1362 : binChunk w3 1354 8 = 8690155786 :=
  binChunk_join (w:=w3) (start:=1354) (left:=4) (right:=4) (x:=4075469202) (y:=4614686584) leaf1354 leaf1358
private theorem batch3_1362_1370 : binChunk w3 1362 8 = 11025704392 :=
  binChunk_join (w:=w3) (start:=1362) (left:=4) (right:=4) (x:=5198199236) (y:=5827505156) leaf1362 leaf1366
private theorem batch3_1354_1370 : binChunk w3 1354 16 = 19715860178 :=
  binChunk_join (w:=w3) (start:=1354) (left:=8) (right:=8) (x:=8690155786) (y:=11025704392) batch3_1354_1362 batch3_1362_1370
private theorem batch3_1338_1370 : binChunk w3 1338 32 = 31454655199 :=
  binChunk_join (w:=w3) (start:=1338) (left:=16) (right:=16) (x:=11738795021) (y:=19715860178) batch3_1338_1354 batch3_1354_1370
theorem batch3_1306_1370 : binChunk w3 1306 64 = 40502154112 :=
  binChunk_join (w:=w3) (start:=1306) (left:=32) (right:=32) (x:=9047498913) (y:=31454655199) batch3_1306_1338 batch3_1338_1370

end Low48PrimaryPivot

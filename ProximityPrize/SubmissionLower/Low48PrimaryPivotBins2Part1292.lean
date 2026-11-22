import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1228

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

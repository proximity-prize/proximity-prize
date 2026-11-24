import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part588

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

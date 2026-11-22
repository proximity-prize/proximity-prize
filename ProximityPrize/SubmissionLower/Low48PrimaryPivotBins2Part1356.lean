import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

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

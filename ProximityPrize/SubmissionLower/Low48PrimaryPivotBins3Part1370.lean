import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

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

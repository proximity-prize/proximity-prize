import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

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

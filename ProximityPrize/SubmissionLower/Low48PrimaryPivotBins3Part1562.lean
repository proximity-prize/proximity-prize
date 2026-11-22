import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

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

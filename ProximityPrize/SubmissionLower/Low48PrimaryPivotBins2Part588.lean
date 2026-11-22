import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf588 : binChunk w2 588 4 = 5264644 := by decide +kernel
private theorem leaf592 : binChunk w2 592 4 = 14705414 := by decide +kernel
private theorem leaf596 : binChunk w2 596 4 = 25599511 := by decide +kernel
private theorem leaf600 : binChunk w2 600 4 = 38070508 := by decide +kernel
private theorem leaf604 : binChunk w2 604 4 = 52244044 := by decide +kernel
private theorem leaf608 : binChunk w2 608 4 = 68254581 := by decide +kernel
private theorem leaf612 : binChunk w2 612 4 = 86240300 := by decide +kernel
private theorem leaf616 : binChunk w2 616 4 = 106339418 := by decide +kernel
private theorem leaf620 : binChunk w2 620 4 = 128702811 := by decide +kernel
private theorem leaf624 : binChunk w2 624 4 = 153483268 := by decide +kernel
private theorem leaf628 : binChunk w2 628 4 = 180831344 := by decide +kernel
private theorem leaf632 : binChunk w2 632 4 = 210914569 := by decide +kernel
private theorem leaf636 : binChunk w2 636 4 = 243900340 := by decide +kernel
private theorem leaf640 : binChunk w2 640 4 = 279951310 := by decide +kernel
private theorem leaf644 : binChunk w2 644 4 = 319251903 := by decide +kernel
private theorem leaf648 : binChunk w2 648 4 = 361984124 := by decide +kernel
private theorem batch2_588_596 : binChunk w2 588 8 = 19970058 :=
  binChunk_join (w := w2) (start := 588) (left := 4) (right := 4) (x := 5264644) (y := 14705414) leaf588 leaf592
private theorem batch2_596_604 : binChunk w2 596 8 = 63670019 :=
  binChunk_join (w := w2) (start := 596) (left := 4) (right := 4) (x := 25599511) (y := 38070508) leaf596 leaf600
private theorem batch2_588_604 : binChunk w2 588 16 = 83640077 :=
  binChunk_join (w := w2) (start := 588) (left := 8) (right := 8) (x := 19970058) (y := 63670019) batch2_588_596 batch2_596_604
private theorem batch2_604_612 : binChunk w2 604 8 = 120498625 :=
  binChunk_join (w := w2) (start := 604) (left := 4) (right := 4) (x := 52244044) (y := 68254581) leaf604 leaf608
private theorem batch2_612_620 : binChunk w2 612 8 = 192579718 :=
  binChunk_join (w := w2) (start := 612) (left := 4) (right := 4) (x := 86240300) (y := 106339418) leaf612 leaf616
private theorem batch2_604_620 : binChunk w2 604 16 = 313078343 :=
  binChunk_join (w := w2) (start := 604) (left := 8) (right := 8) (x := 120498625) (y := 192579718) batch2_604_612 batch2_612_620
private theorem batch2_588_620 : binChunk w2 588 32 = 396718420 :=
  binChunk_join (w := w2) (start := 588) (left := 16) (right := 16) (x := 83640077) (y := 313078343) batch2_588_604 batch2_604_620
private theorem batch2_620_628 : binChunk w2 620 8 = 282186079 :=
  binChunk_join (w := w2) (start := 620) (left := 4) (right := 4) (x := 128702811) (y := 153483268) leaf620 leaf624
private theorem batch2_628_636 : binChunk w2 628 8 = 391745913 :=
  binChunk_join (w := w2) (start := 628) (left := 4) (right := 4) (x := 180831344) (y := 210914569) leaf628 leaf632
private theorem batch2_620_636 : binChunk w2 620 16 = 673931992 :=
  binChunk_join (w := w2) (start := 620) (left := 8) (right := 8) (x := 282186079) (y := 391745913) batch2_620_628 batch2_628_636
private theorem batch2_636_644 : binChunk w2 636 8 = 523851650 :=
  binChunk_join (w := w2) (start := 636) (left := 4) (right := 4) (x := 243900340) (y := 279951310) leaf636 leaf640
private theorem batch2_644_652 : binChunk w2 644 8 = 681236027 :=
  binChunk_join (w := w2) (start := 644) (left := 4) (right := 4) (x := 319251903) (y := 361984124) leaf644 leaf648
private theorem batch2_636_652 : binChunk w2 636 16 = 1205087677 :=
  binChunk_join (w := w2) (start := 636) (left := 8) (right := 8) (x := 523851650) (y := 681236027) batch2_636_644 batch2_644_652
private theorem batch2_620_652 : binChunk w2 620 32 = 1879019669 :=
  binChunk_join (w := w2) (start := 620) (left := 16) (right := 16) (x := 673931992) (y := 1205087677) batch2_620_636 batch2_636_652
theorem batch2_588_652 : binChunk w2 588 64 = 2275738089 :=
  binChunk_join (w := w2) (start := 588) (left := 32) (right := 32) (x := 396718420) (y := 1879019669) batch2_588_620 batch2_620_652

end Low48PrimaryPivot

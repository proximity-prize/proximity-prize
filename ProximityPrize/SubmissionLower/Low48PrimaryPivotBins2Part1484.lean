import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option linter.defProp false

namespace Low48PrimaryPivot
open K1_13_2_3

private def leaf1484:=checkedBin w2 1484 4 225089963977
private def leaf1488:=checkedBin w2 1488 4 226352518683
private def leaf1492:=checkedBin w2 1492 4 227606421745
private def leaf1496:=checkedBin w2 1496 4 228853551405
private def leaf1500:=checkedBin w2 1500 4 230095471695
private def leaf1504:=checkedBin w2 1504 4 231333432437
private def leaf1508:=checkedBin w2 1508 4 232569284225
private def leaf1512:=checkedBin w2 1512 4 233804563443
private def leaf1516:=checkedBin w2 1516 4 235040492265
private def leaf1520:=checkedBin w2 1520 4 236278851800
private def leaf1524:=checkedBin w2 1524 4 237520482374
private def leaf1528:=checkedBin w2 1528 4 238765162888
private def leaf1532:=checkedBin w2 1532 4 240013198336
private def leaf1536:=checkedBin w2 1536 4 241264588718
private def leaf1540:=checkedBin w2 1540 4 242519029040
private def leaf1544:=checkedBin w2 1544 4 243776824296
private theorem batch2_1484_1492 : binChunk w2 1484 8 = 451442482660 :=
  binChunk_join (w:=w2) (start:=1484) (left:=4) (right:=4) (x:=225089963977) (y:=226352518683) leaf1484 leaf1488
private theorem batch2_1492_1500 : binChunk w2 1492 8 = 456459973150 :=
  binChunk_join (w:=w2) (start:=1492) (left:=4) (right:=4) (x:=227606421745) (y:=228853551405) leaf1492 leaf1496
private theorem batch2_1484_1500 : binChunk w2 1484 16 = 907902455810 :=
  binChunk_join (w:=w2) (start:=1484) (left:=8) (right:=8) (x:=451442482660) (y:=456459973150) batch2_1484_1492 batch2_1492_1500
private theorem batch2_1500_1508 : binChunk w2 1500 8 = 461428904132 :=
  binChunk_join (w:=w2) (start:=1500) (left:=4) (right:=4) (x:=230095471695) (y:=231333432437) leaf1500 leaf1504
private theorem batch2_1508_1516 : binChunk w2 1508 8 = 466373847668 :=
  binChunk_join (w:=w2) (start:=1508) (left:=4) (right:=4) (x:=232569284225) (y:=233804563443) leaf1508 leaf1512
private theorem batch2_1500_1516 : binChunk w2 1500 16 = 927802751800 :=
  binChunk_join (w:=w2) (start:=1500) (left:=8) (right:=8) (x:=461428904132) (y:=466373847668) batch2_1500_1508 batch2_1508_1516
private theorem batch2_1484_1516 : binChunk w2 1484 32 = 1835705207610 :=
  binChunk_join (w:=w2) (start:=1484) (left:=16) (right:=16) (x:=907902455810) (y:=927802751800) batch2_1484_1500 batch2_1500_1516
private theorem batch2_1516_1524 : binChunk w2 1516 8 = 471319344065 :=
  binChunk_join (w:=w2) (start:=1516) (left:=4) (right:=4) (x:=235040492265) (y:=236278851800) leaf1516 leaf1520
private theorem batch2_1524_1532 : binChunk w2 1524 8 = 476285645262 :=
  binChunk_join (w:=w2) (start:=1524) (left:=4) (right:=4) (x:=237520482374) (y:=238765162888) leaf1524 leaf1528
private theorem batch2_1516_1532 : binChunk w2 1516 16 = 947604989327 :=
  binChunk_join (w:=w2) (start:=1516) (left:=8) (right:=8) (x:=471319344065) (y:=476285645262) batch2_1516_1524 batch2_1524_1532
private theorem batch2_1532_1540 : binChunk w2 1532 8 = 481277787054 :=
  binChunk_join (w:=w2) (start:=1532) (left:=4) (right:=4) (x:=240013198336) (y:=241264588718) leaf1532 leaf1536
private theorem batch2_1540_1548 : binChunk w2 1540 8 = 486295853336 :=
  binChunk_join (w:=w2) (start:=1540) (left:=4) (right:=4) (x:=242519029040) (y:=243776824296) leaf1540 leaf1544
private theorem batch2_1532_1548 : binChunk w2 1532 16 = 967573640390 :=
  binChunk_join (w:=w2) (start:=1532) (left:=8) (right:=8) (x:=481277787054) (y:=486295853336) batch2_1532_1540 batch2_1540_1548
private theorem batch2_1516_1548 : binChunk w2 1516 32 = 1915178629717 :=
  binChunk_join (w:=w2) (start:=1516) (left:=16) (right:=16) (x:=947604989327) (y:=967573640390) batch2_1516_1532 batch2_1532_1548
theorem batch2_1484_1548 : binChunk w2 1484 64 = 3750883837327 :=
  binChunk_join (w:=w2) (start:=1484) (left:=32) (right:=32) (x:=1835705207610) (y:=1915178629717) batch2_1484_1516 batch2_1516_1548

end Low48PrimaryPivot

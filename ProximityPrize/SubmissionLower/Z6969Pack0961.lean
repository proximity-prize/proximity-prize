import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.PairReceipts277
section Z6969Source2874
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5540:PairCell.Row:=⟨53,53,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5540:ThreeRule.check cell5540 (2:Fin 18)=true:=by decide +kernel
def cell5541:PairCell.Row:=⟨53,53,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5541:ThreeRule.check cell5541 (2:Fin 18)=true:=by decide +kernel
def cell5542:PairCell.Row:=⟨53,53,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5542:ThreeRule.check cell5542 (2:Fin 18)=true:=by decide +kernel
def cell5543:PairCell.Row:=⟨53,53,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5543:ThreeRule.check cell5543 (2:Fin 18)=true:=by decide +kernel
def cell5544:PairCell.Row:=⟨53,53,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5544:ThreeRule.check cell5544 (2:Fin 18)=true:=by decide +kernel
def cell5545:PairCell.Row:=⟨53,53,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5545:ThreeRule.check cell5545 (2:Fin 18)=true:=by decide +kernel
def cell5546:PairCell.Row:=⟨53,53,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5546:ThreeRule.check cell5546 (2:Fin 18)=true:=by decide +kernel
def cell5547:PairCell.Row:=⟨53,53,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5547:ThreeRule.check cell5547 (2:Fin 18)=true:=by decide +kernel
def cell5548:PairCell.Row:=⟨53,53,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5548:ThreeRule.check cell5548 (2:Fin 18)=true:=by decide +kernel
def cell5549:PairCell.Row:=⟨53,53,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5549:ThreeRule.check cell5549 (2:Fin 18)=true:=by decide +kernel
def cell5550:PairCell.Row:=⟨53,53,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5550:ThreeRule.check cell5550 (2:Fin 18)=true:=by decide +kernel
def cell5551:PairCell.Row:=⟨53,53,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5551:ThreeRule.check cell5551 (2:Fin 18)=true:=by decide +kernel
def cell5552:PairCell.Row:=⟨53,53,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5552:ThreeRule.check cell5552 (2:Fin 18)=true:=by decide +kernel
def cell5553:PairCell.Row:=⟨53,53,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5553:ThreeRule.check cell5553 (2:Fin 18)=true:=by decide +kernel
def cell5554:PairCell.Row:=⟨53,53,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5554:ThreeRule.check cell5554 (2:Fin 18)=true:=by decide +kernel
def cell5555:PairCell.Row:=⟨53,53,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5555:ThreeRule.check cell5555 (2:Fin 18)=true:=by decide +kernel
private def rows5556 : List StockPairs.Receipt := [
  ⟨⟨54,54,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩]
private theorem paid5556 : StockPairs.checked rows5556 = true := by decide +kernel
theorem route5556 (i : Fin 4) : (rows5556.get i).Done :=
  StockPairs.doneAt paid5556 i

end Research6969.PairReceipts
end Z6969Source2874

-- Source: Research6969.PairReceipts278
section Z6969Source2875
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5560 : List StockPairs.Receipt := [
  ⟨⟨54,54,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩,
  ⟨⟨54,54,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid5560 : StockPairs.checked rows5560 = true := by decide +kernel
theorem route5560 (i : Fin 7) : (rows5560.get i).Done :=
  StockPairs.doneAt paid5560 i

def cell5567:PairCell.Row:=⟨54,54,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩
theorem check5567:ThreeRule.check cell5567 (2:Fin 18)=true:=by decide +kernel
def cell5568:PairCell.Row:=⟨54,54,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5568:ThreeRule.check cell5568 (2:Fin 18)=true:=by decide +kernel
def cell5569:PairCell.Row:=⟨54,54,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5569:ThreeRule.check cell5569 (2:Fin 18)=true:=by decide +kernel
def cell5570:PairCell.Row:=⟨54,54,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5570:ThreeRule.check cell5570 (2:Fin 18)=true:=by decide +kernel
def cell5571:PairCell.Row:=⟨54,54,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5571:ThreeRule.check cell5571 (2:Fin 18)=true:=by decide +kernel
def cell5572:PairCell.Row:=⟨54,54,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5572:ThreeRule.check cell5572 (2:Fin 18)=true:=by decide +kernel
def cell5573:PairCell.Row:=⟨54,54,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5573:ThreeRule.check cell5573 (2:Fin 18)=true:=by decide +kernel
def cell5574:PairCell.Row:=⟨54,54,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5574:ThreeRule.check cell5574 (2:Fin 18)=true:=by decide +kernel
def cell5575:PairCell.Row:=⟨54,54,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5575:ThreeRule.check cell5575 (2:Fin 18)=true:=by decide +kernel
def cell5576:PairCell.Row:=⟨54,54,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5576:ThreeRule.check cell5576 (2:Fin 18)=true:=by decide +kernel
def cell5577:PairCell.Row:=⟨54,54,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5577:ThreeRule.check cell5577 (2:Fin 18)=true:=by decide +kernel
def cell5578:PairCell.Row:=⟨54,54,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5578:ThreeRule.check cell5578 (2:Fin 18)=true:=by decide +kernel
def cell5579:PairCell.Row:=⟨54,54,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5579:ThreeRule.check cell5579 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2875

-- Source: Research6969.PairReceipts279
section Z6969Source2876
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5580:PairCell.Row:=⟨54,54,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5580:ThreeRule.check cell5580 (2:Fin 18)=true:=by decide +kernel
def cell5581:PairCell.Row:=⟨54,54,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5581:ThreeRule.check cell5581 (2:Fin 18)=true:=by decide +kernel
def cell5582:PairCell.Row:=⟨54,54,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5582:ThreeRule.check cell5582 (2:Fin 18)=true:=by decide +kernel
def cell5583:PairCell.Row:=⟨54,54,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5583:ThreeRule.check cell5583 (2:Fin 18)=true:=by decide +kernel
def cell5584:PairCell.Row:=⟨54,54,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5584:ThreeRule.check cell5584 (2:Fin 18)=true:=by decide +kernel
def cell5585:PairCell.Row:=⟨54,54,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5585:ThreeRule.check cell5585 (2:Fin 18)=true:=by decide +kernel
def cell5586:PairCell.Row:=⟨54,54,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5586:ThreeRule.check cell5586 (2:Fin 18)=true:=by decide +kernel
def cell5587:PairCell.Row:=⟨54,54,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5587:ThreeRule.check cell5587 (2:Fin 18)=true:=by decide +kernel
def cell5588:PairCell.Row:=⟨54,54,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5588:ThreeRule.check cell5588 (2:Fin 18)=true:=by decide +kernel
def cell5589:PairCell.Row:=⟨54,54,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5589:ThreeRule.check cell5589 (2:Fin 18)=true:=by decide +kernel
def cell5590:PairCell.Row:=⟨54,54,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5590:ThreeRule.check cell5590 (2:Fin 18)=true:=by decide +kernel
def cell5591:PairCell.Row:=⟨54,54,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5591:ThreeRule.check cell5591 (2:Fin 18)=true:=by decide +kernel
def cell5592:PairCell.Row:=⟨54,54,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5592:ThreeRule.check cell5592 (2:Fin 18)=true:=by decide +kernel
def cell5593:PairCell.Row:=⟨54,54,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5593:ThreeRule.check cell5593 (2:Fin 18)=true:=by decide +kernel
private def rows5594 : List StockPairs.Receipt := [
  ⟨⟨55,55,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩]
private theorem paid5594 : StockPairs.checked rows5594 = true := by decide +kernel
theorem route5594 (i : Fin 6) : (rows5594.get i).Done :=
  StockPairs.doneAt paid5594 i

end Research6969.PairReceipts
end Z6969Source2876

-- Source: Research6969.PairReceipts280
section Z6969Source2877
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5600 : List StockPairs.Receipt := [
  ⟨⟨55,55,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩,
  ⟨⟨55,55,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid5600 : StockPairs.checked rows5600 = true := by decide +kernel
theorem route5600 (i : Fin 5) : (rows5600.get i).Done :=
  StockPairs.doneAt paid5600 i

def cell5605:PairCell.Row:=⟨55,55,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩
theorem check5605:ThreeRule.check cell5605 (2:Fin 18)=true:=by decide +kernel
def cell5606:PairCell.Row:=⟨55,55,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5606:ThreeRule.check cell5606 (2:Fin 18)=true:=by decide +kernel
def cell5607:PairCell.Row:=⟨55,55,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5607:ThreeRule.check cell5607 (2:Fin 18)=true:=by decide +kernel
def cell5608:PairCell.Row:=⟨55,55,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5608:ThreeRule.check cell5608 (2:Fin 18)=true:=by decide +kernel
def cell5609:PairCell.Row:=⟨55,55,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5609:ThreeRule.check cell5609 (2:Fin 18)=true:=by decide +kernel
def cell5610:PairCell.Row:=⟨55,55,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5610:ThreeRule.check cell5610 (2:Fin 18)=true:=by decide +kernel
def cell5611:PairCell.Row:=⟨55,55,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5611:ThreeRule.check cell5611 (2:Fin 18)=true:=by decide +kernel
def cell5612:PairCell.Row:=⟨55,55,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5612:ThreeRule.check cell5612 (2:Fin 18)=true:=by decide +kernel
def cell5613:PairCell.Row:=⟨55,55,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5613:ThreeRule.check cell5613 (2:Fin 18)=true:=by decide +kernel
def cell5614:PairCell.Row:=⟨55,55,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5614:ThreeRule.check cell5614 (2:Fin 18)=true:=by decide +kernel
def cell5615:PairCell.Row:=⟨55,55,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5615:ThreeRule.check cell5615 (2:Fin 18)=true:=by decide +kernel
def cell5616:PairCell.Row:=⟨55,55,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5616:ThreeRule.check cell5616 (2:Fin 18)=true:=by decide +kernel
def cell5617:PairCell.Row:=⟨55,55,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5617:ThreeRule.check cell5617 (2:Fin 18)=true:=by decide +kernel
def cell5618:PairCell.Row:=⟨55,55,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5618:ThreeRule.check cell5618 (2:Fin 18)=true:=by decide +kernel
def cell5619:PairCell.Row:=⟨55,55,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5619:ThreeRule.check cell5619 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2877

-- Source: Research6969.PairReceipts281
section Z6969Source2878
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5620:PairCell.Row:=⟨55,55,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5620:ThreeRule.check cell5620 (2:Fin 18)=true:=by decide +kernel
def cell5621:PairCell.Row:=⟨55,55,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5621:ThreeRule.check cell5621 (2:Fin 18)=true:=by decide +kernel
def cell5622:PairCell.Row:=⟨55,55,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5622:ThreeRule.check cell5622 (2:Fin 18)=true:=by decide +kernel
def cell5623:PairCell.Row:=⟨55,55,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5623:ThreeRule.check cell5623 (2:Fin 18)=true:=by decide +kernel
def cell5624:PairCell.Row:=⟨55,55,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5624:ThreeRule.check cell5624 (2:Fin 18)=true:=by decide +kernel
def cell5625:PairCell.Row:=⟨55,55,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5625:ThreeRule.check cell5625 (2:Fin 18)=true:=by decide +kernel
def cell5626:PairCell.Row:=⟨55,55,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5626:ThreeRule.check cell5626 (2:Fin 18)=true:=by decide +kernel
def cell5627:PairCell.Row:=⟨55,55,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5627:ThreeRule.check cell5627 (2:Fin 18)=true:=by decide +kernel
def cell5628:PairCell.Row:=⟨55,55,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5628:ThreeRule.check cell5628 (2:Fin 18)=true:=by decide +kernel
def cell5629:PairCell.Row:=⟨55,55,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5629:ThreeRule.check cell5629 (2:Fin 18)=true:=by decide +kernel
def cell5630:PairCell.Row:=⟨55,55,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5630:ThreeRule.check cell5630 (2:Fin 18)=true:=by decide +kernel
def cell5631:PairCell.Row:=⟨55,55,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5631:ThreeRule.check cell5631 (2:Fin 18)=true:=by decide +kernel
private def rows5632 : List StockPairs.Receipt := [
  ⟨⟨56,56,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩]
private theorem paid5632 : StockPairs.checked rows5632 = true := by decide +kernel
theorem route5632 (i : Fin 8) : (rows5632.get i).Done :=
  StockPairs.doneAt paid5632 i

end Research6969.PairReceipts
end Z6969Source2878

-- Source: Research6969.PairReceipts282
section Z6969Source2879
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5640 : List StockPairs.Receipt := [
  ⟨⟨56,56,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid5640 : StockPairs.checked rows5640 = true := by decide +kernel
theorem route5640 (i : Fin 4) : (rows5640.get i).Done :=
  StockPairs.doneAt paid5640 i

def cell5644:PairCell.Row:=⟨56,56,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5644:ThreeRule.check cell5644 (2:Fin 18)=true:=by decide +kernel
def cell5645:PairCell.Row:=⟨56,56,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5645:ThreeRule.check cell5645 (2:Fin 18)=true:=by decide +kernel
def cell5646:PairCell.Row:=⟨56,56,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5646:ThreeRule.check cell5646 (2:Fin 18)=true:=by decide +kernel
def cell5647:PairCell.Row:=⟨56,56,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5647:ThreeRule.check cell5647 (2:Fin 18)=true:=by decide +kernel
def cell5648:PairCell.Row:=⟨56,56,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5648:ThreeRule.check cell5648 (2:Fin 18)=true:=by decide +kernel
def cell5649:PairCell.Row:=⟨56,56,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5649:ThreeRule.check cell5649 (2:Fin 18)=true:=by decide +kernel
def cell5650:PairCell.Row:=⟨56,56,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5650:ThreeRule.check cell5650 (2:Fin 18)=true:=by decide +kernel
def cell5651:PairCell.Row:=⟨56,56,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5651:ThreeRule.check cell5651 (2:Fin 18)=true:=by decide +kernel
def cell5652:PairCell.Row:=⟨56,56,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5652:ThreeRule.check cell5652 (2:Fin 18)=true:=by decide +kernel
def cell5653:PairCell.Row:=⟨56,56,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5653:ThreeRule.check cell5653 (2:Fin 18)=true:=by decide +kernel
def cell5654:PairCell.Row:=⟨56,56,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5654:ThreeRule.check cell5654 (2:Fin 18)=true:=by decide +kernel
def cell5655:PairCell.Row:=⟨56,56,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5655:ThreeRule.check cell5655 (2:Fin 18)=true:=by decide +kernel
def cell5656:PairCell.Row:=⟨56,56,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5656:ThreeRule.check cell5656 (2:Fin 18)=true:=by decide +kernel
def cell5657:PairCell.Row:=⟨56,56,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5657:ThreeRule.check cell5657 (2:Fin 18)=true:=by decide +kernel
def cell5658:PairCell.Row:=⟨56,56,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5658:ThreeRule.check cell5658 (2:Fin 18)=true:=by decide +kernel
def cell5659:PairCell.Row:=⟨56,56,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5659:ThreeRule.check cell5659 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2879

-- Source: Research6969.PairReceipts283
section Z6969Source2880
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5660:PairCell.Row:=⟨56,56,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5660:ThreeRule.check cell5660 (2:Fin 18)=true:=by decide +kernel
def cell5661:PairCell.Row:=⟨56,56,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5661:ThreeRule.check cell5661 (2:Fin 18)=true:=by decide +kernel
def cell5662:PairCell.Row:=⟨56,56,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5662:ThreeRule.check cell5662 (2:Fin 18)=true:=by decide +kernel
def cell5663:PairCell.Row:=⟨56,56,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5663:ThreeRule.check cell5663 (2:Fin 18)=true:=by decide +kernel
def cell5664:PairCell.Row:=⟨56,56,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5664:ThreeRule.check cell5664 (2:Fin 18)=true:=by decide +kernel
def cell5665:PairCell.Row:=⟨56,56,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5665:ThreeRule.check cell5665 (2:Fin 18)=true:=by decide +kernel
def cell5666:PairCell.Row:=⟨56,56,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5666:ThreeRule.check cell5666 (2:Fin 18)=true:=by decide +kernel
def cell5667:PairCell.Row:=⟨56,56,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5667:ThreeRule.check cell5667 (2:Fin 18)=true:=by decide +kernel
def cell5668:PairCell.Row:=⟨56,56,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5668:ThreeRule.check cell5668 (2:Fin 18)=true:=by decide +kernel
def cell5669:PairCell.Row:=⟨56,56,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5669:ThreeRule.check cell5669 (2:Fin 18)=true:=by decide +kernel
private def rows5670 : List StockPairs.Receipt := [
  ⟨⟨57,57,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩]
private theorem paid5670 : StockPairs.checked rows5670 = true := by decide +kernel
theorem route5670 (i : Fin 10) : (rows5670.get i).Done :=
  StockPairs.doneAt paid5670 i

end Research6969.PairReceipts
end Z6969Source2880

-- Source: Research6969.PairReceipts284
section Z6969Source2881
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5680 : List StockPairs.Receipt := [
  ⟨⟨57,57,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid5680 : StockPairs.checked rows5680 = true := by decide +kernel
theorem route5680 (i : Fin 2) : (rows5680.get i).Done :=
  StockPairs.doneAt paid5680 i

def cell5682:PairCell.Row:=⟨57,57,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5682:ThreeRule.check cell5682 (2:Fin 18)=true:=by decide +kernel
def cell5683:PairCell.Row:=⟨57,57,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5683:ThreeRule.check cell5683 (2:Fin 18)=true:=by decide +kernel
def cell5684:PairCell.Row:=⟨57,57,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5684:ThreeRule.check cell5684 (2:Fin 18)=true:=by decide +kernel
def cell5685:PairCell.Row:=⟨57,57,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5685:ThreeRule.check cell5685 (2:Fin 18)=true:=by decide +kernel
def cell5686:PairCell.Row:=⟨57,57,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5686:ThreeRule.check cell5686 (2:Fin 18)=true:=by decide +kernel
def cell5687:PairCell.Row:=⟨57,57,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5687:ThreeRule.check cell5687 (2:Fin 18)=true:=by decide +kernel
def cell5688:PairCell.Row:=⟨57,57,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5688:ThreeRule.check cell5688 (2:Fin 18)=true:=by decide +kernel
def cell5689:PairCell.Row:=⟨57,57,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5689:ThreeRule.check cell5689 (2:Fin 18)=true:=by decide +kernel
def cell5690:PairCell.Row:=⟨57,57,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5690:ThreeRule.check cell5690 (2:Fin 18)=true:=by decide +kernel
def cell5691:PairCell.Row:=⟨57,57,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5691:ThreeRule.check cell5691 (2:Fin 18)=true:=by decide +kernel
def cell5692:PairCell.Row:=⟨57,57,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5692:ThreeRule.check cell5692 (2:Fin 18)=true:=by decide +kernel
def cell5693:PairCell.Row:=⟨57,57,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5693:ThreeRule.check cell5693 (2:Fin 18)=true:=by decide +kernel
def cell5694:PairCell.Row:=⟨57,57,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5694:ThreeRule.check cell5694 (2:Fin 18)=true:=by decide +kernel
def cell5695:PairCell.Row:=⟨57,57,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5695:ThreeRule.check cell5695 (2:Fin 18)=true:=by decide +kernel
def cell5696:PairCell.Row:=⟨57,57,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5696:ThreeRule.check cell5696 (2:Fin 18)=true:=by decide +kernel
def cell5697:PairCell.Row:=⟨57,57,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5697:ThreeRule.check cell5697 (2:Fin 18)=true:=by decide +kernel
def cell5698:PairCell.Row:=⟨57,57,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5698:ThreeRule.check cell5698 (2:Fin 18)=true:=by decide +kernel
def cell5699:PairCell.Row:=⟨57,57,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5699:ThreeRule.check cell5699 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2881

-- Source: Research6969.PairReceipts285
section Z6969Source2882
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5700:PairCell.Row:=⟨57,57,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5700:ThreeRule.check cell5700 (2:Fin 18)=true:=by decide +kernel
def cell5701:PairCell.Row:=⟨57,57,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5701:ThreeRule.check cell5701 (2:Fin 18)=true:=by decide +kernel
def cell5702:PairCell.Row:=⟨57,57,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5702:ThreeRule.check cell5702 (2:Fin 18)=true:=by decide +kernel
def cell5703:PairCell.Row:=⟨57,57,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5703:ThreeRule.check cell5703 (2:Fin 18)=true:=by decide +kernel
def cell5704:PairCell.Row:=⟨57,57,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5704:ThreeRule.check cell5704 (2:Fin 18)=true:=by decide +kernel
def cell5705:PairCell.Row:=⟨57,57,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5705:ThreeRule.check cell5705 (2:Fin 18)=true:=by decide +kernel
def cell5706:PairCell.Row:=⟨57,57,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5706:ThreeRule.check cell5706 (2:Fin 18)=true:=by decide +kernel
def cell5707:PairCell.Row:=⟨57,57,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5707:ThreeRule.check cell5707 (2:Fin 18)=true:=by decide +kernel
private def rows5708 : List StockPairs.Receipt := [
  ⟨⟨58,58,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid5708 : StockPairs.checked rows5708 = true := by decide +kernel
theorem route5708 (i : Fin 12) : (rows5708.get i).Done :=
  StockPairs.doneAt paid5708 i

end Research6969.PairReceipts
end Z6969Source2882

-- Source: Research6969.PairReceipts286
section Z6969Source2883
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5720:PairCell.Row:=⟨58,58,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5720:ThreeRule.check cell5720 (2:Fin 18)=true:=by decide +kernel
def cell5721:PairCell.Row:=⟨58,58,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5721:ThreeRule.check cell5721 (2:Fin 18)=true:=by decide +kernel
def cell5722:PairCell.Row:=⟨58,58,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5722:ThreeRule.check cell5722 (2:Fin 18)=true:=by decide +kernel
def cell5723:PairCell.Row:=⟨58,58,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5723:ThreeRule.check cell5723 (2:Fin 18)=true:=by decide +kernel
def cell5724:PairCell.Row:=⟨58,58,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5724:ThreeRule.check cell5724 (2:Fin 18)=true:=by decide +kernel
def cell5725:PairCell.Row:=⟨58,58,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5725:ThreeRule.check cell5725 (2:Fin 18)=true:=by decide +kernel
def cell5726:PairCell.Row:=⟨58,58,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5726:ThreeRule.check cell5726 (2:Fin 18)=true:=by decide +kernel
def cell5727:PairCell.Row:=⟨58,58,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5727:ThreeRule.check cell5727 (2:Fin 18)=true:=by decide +kernel
def cell5728:PairCell.Row:=⟨58,58,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5728:ThreeRule.check cell5728 (2:Fin 18)=true:=by decide +kernel
def cell5729:PairCell.Row:=⟨58,58,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5729:ThreeRule.check cell5729 (2:Fin 18)=true:=by decide +kernel
def cell5730:PairCell.Row:=⟨58,58,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5730:ThreeRule.check cell5730 (2:Fin 18)=true:=by decide +kernel
def cell5731:PairCell.Row:=⟨58,58,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5731:ThreeRule.check cell5731 (2:Fin 18)=true:=by decide +kernel
def cell5732:PairCell.Row:=⟨58,58,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5732:ThreeRule.check cell5732 (2:Fin 18)=true:=by decide +kernel
def cell5733:PairCell.Row:=⟨58,58,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5733:ThreeRule.check cell5733 (2:Fin 18)=true:=by decide +kernel
def cell5734:PairCell.Row:=⟨58,58,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5734:ThreeRule.check cell5734 (2:Fin 18)=true:=by decide +kernel
def cell5735:PairCell.Row:=⟨58,58,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5735:ThreeRule.check cell5735 (2:Fin 18)=true:=by decide +kernel
def cell5736:PairCell.Row:=⟨58,58,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5736:ThreeRule.check cell5736 (2:Fin 18)=true:=by decide +kernel
def cell5737:PairCell.Row:=⟨58,58,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5737:ThreeRule.check cell5737 (2:Fin 18)=true:=by decide +kernel
def cell5738:PairCell.Row:=⟨58,58,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5738:ThreeRule.check cell5738 (2:Fin 18)=true:=by decide +kernel
def cell5739:PairCell.Row:=⟨58,58,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5739:ThreeRule.check cell5739 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2883

-- Source: Research6969.PairReceipts287
section Z6969Source2884
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5740:PairCell.Row:=⟨58,58,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5740:ThreeRule.check cell5740 (2:Fin 18)=true:=by decide +kernel
def cell5741:PairCell.Row:=⟨58,58,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5741:ThreeRule.check cell5741 (2:Fin 18)=true:=by decide +kernel
def cell5742:PairCell.Row:=⟨58,58,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5742:ThreeRule.check cell5742 (2:Fin 18)=true:=by decide +kernel
def cell5743:PairCell.Row:=⟨58,58,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5743:ThreeRule.check cell5743 (2:Fin 18)=true:=by decide +kernel
def cell5744:PairCell.Row:=⟨58,58,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5744:ThreeRule.check cell5744 (2:Fin 18)=true:=by decide +kernel
def cell5745:PairCell.Row:=⟨58,58,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5745:ThreeRule.check cell5745 (2:Fin 18)=true:=by decide +kernel
private def rows5746 : List StockPairs.Receipt := [
  ⟨⟨59,59,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid5746 : StockPairs.checked rows5746 = true := by decide +kernel
theorem route5746 (i : Fin 12) : (rows5746.get i).Done :=
  StockPairs.doneAt paid5746 i

def cell5758:PairCell.Row:=⟨59,59,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5758:ThreeRule.check cell5758 (2:Fin 18)=true:=by decide +kernel
def cell5759:PairCell.Row:=⟨59,59,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5759:ThreeRule.check cell5759 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2884

-- Source: Research6969.PairReceipts288
section Z6969Source2885
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5760:PairCell.Row:=⟨59,59,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5760:ThreeRule.check cell5760 (2:Fin 18)=true:=by decide +kernel
def cell5761:PairCell.Row:=⟨59,59,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5761:ThreeRule.check cell5761 (2:Fin 18)=true:=by decide +kernel
def cell5762:PairCell.Row:=⟨59,59,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5762:ThreeRule.check cell5762 (2:Fin 18)=true:=by decide +kernel
def cell5763:PairCell.Row:=⟨59,59,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5763:ThreeRule.check cell5763 (2:Fin 18)=true:=by decide +kernel
def cell5764:PairCell.Row:=⟨59,59,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5764:ThreeRule.check cell5764 (2:Fin 18)=true:=by decide +kernel
def cell5765:PairCell.Row:=⟨59,59,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5765:ThreeRule.check cell5765 (2:Fin 18)=true:=by decide +kernel
def cell5766:PairCell.Row:=⟨59,59,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5766:ThreeRule.check cell5766 (2:Fin 18)=true:=by decide +kernel
def cell5767:PairCell.Row:=⟨59,59,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5767:ThreeRule.check cell5767 (2:Fin 18)=true:=by decide +kernel
def cell5768:PairCell.Row:=⟨59,59,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5768:ThreeRule.check cell5768 (2:Fin 18)=true:=by decide +kernel
def cell5769:PairCell.Row:=⟨59,59,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5769:ThreeRule.check cell5769 (2:Fin 18)=true:=by decide +kernel
def cell5770:PairCell.Row:=⟨59,59,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5770:ThreeRule.check cell5770 (2:Fin 18)=true:=by decide +kernel
def cell5771:PairCell.Row:=⟨59,59,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5771:ThreeRule.check cell5771 (2:Fin 18)=true:=by decide +kernel
def cell5772:PairCell.Row:=⟨59,59,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5772:ThreeRule.check cell5772 (2:Fin 18)=true:=by decide +kernel
def cell5773:PairCell.Row:=⟨59,59,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5773:ThreeRule.check cell5773 (2:Fin 18)=true:=by decide +kernel
def cell5774:PairCell.Row:=⟨59,59,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5774:ThreeRule.check cell5774 (2:Fin 18)=true:=by decide +kernel
def cell5775:PairCell.Row:=⟨59,59,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5775:ThreeRule.check cell5775 (2:Fin 18)=true:=by decide +kernel
def cell5776:PairCell.Row:=⟨59,59,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5776:ThreeRule.check cell5776 (2:Fin 18)=true:=by decide +kernel
def cell5777:PairCell.Row:=⟨59,59,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5777:ThreeRule.check cell5777 (2:Fin 18)=true:=by decide +kernel
def cell5778:PairCell.Row:=⟨59,59,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5778:ThreeRule.check cell5778 (2:Fin 18)=true:=by decide +kernel
def cell5779:PairCell.Row:=⟨59,59,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5779:ThreeRule.check cell5779 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2885

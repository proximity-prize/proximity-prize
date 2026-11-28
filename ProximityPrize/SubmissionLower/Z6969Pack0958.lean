import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666

set_option Elab.async false

-- Source: Research6969.PairReceipts326
section Z6969Source2855
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6520:PairCell.Row:=⟨55,55,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6520:ThreeRule.check cell6520 (2:Fin 18)=true:=by decide +kernel
def cell6521:PairCell.Row:=⟨55,55,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6521:ThreeRule.check cell6521 (2:Fin 18)=true:=by decide +kernel
private def rows6522 : List StockPairs.Receipt := [
  ⟨⟨56,56,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid6522 : StockPairs.checked rows6522 = true := by decide +kernel
theorem route6522 (i : Fin 14) : (rows6522.get i).Done :=
  StockPairs.doneAt paid6522 i

def cell6534:PairCell.Row:=⟨56,56,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6534:ThreeRule.check cell6534 (2:Fin 18)=true:=by decide +kernel
def cell6535:PairCell.Row:=⟨56,56,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6535:ThreeRule.check cell6535 (2:Fin 18)=true:=by decide +kernel
def cell6536:PairCell.Row:=⟨56,56,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6536:ThreeRule.check cell6536 (2:Fin 18)=true:=by decide +kernel
def cell6537:PairCell.Row:=⟨56,56,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6537:ThreeRule.check cell6537 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2855

-- Source: Research6969.PairReceipts327
section Z6969Source2856
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6540 : List StockPairs.Receipt := [
  ⟨⟨57,57,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩]
private theorem paid6540 : StockPairs.checked rows6540 = true := by decide +kernel
theorem route6540 (i : Fin 16) : (rows6540.get i).Done :=
  StockPairs.doneAt paid6540 i

def cell6550:PairCell.Row:=⟨57,57,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6550:ThreeRule.check cell6550 (2:Fin 18)=true:=by decide +kernel
def cell6551:PairCell.Row:=⟨57,57,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6551:ThreeRule.check cell6551 (2:Fin 18)=true:=by decide +kernel
def cell6552:PairCell.Row:=⟨57,57,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6552:ThreeRule.check cell6552 (2:Fin 18)=true:=by decide +kernel
def cell6553:PairCell.Row:=⟨57,57,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6553:ThreeRule.check cell6553 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2856

-- Source: Research6969.PairReceipts328
section Z6969Source2857
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6560 : List StockPairs.Receipt := [
  ⟨⟨58,58,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6560 : StockPairs.checked rows6560 = true := by decide +kernel
theorem route6560 (i : Fin 16) : (rows6560.get i).Done :=
  StockPairs.doneAt paid6560 i

def cell6566:PairCell.Row:=⟨58,58,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6566:ThreeRule.check cell6566 (2:Fin 18)=true:=by decide +kernel
def cell6567:PairCell.Row:=⟨58,58,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6567:ThreeRule.check cell6567 (2:Fin 18)=true:=by decide +kernel
def cell6568:PairCell.Row:=⟨58,58,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6568:ThreeRule.check cell6568 (2:Fin 18)=true:=by decide +kernel
def cell6569:PairCell.Row:=⟨58,58,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6569:ThreeRule.check cell6569 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2857

-- Source: Research6969.PairReceipts329
section Z6969Source2858
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6580 : List StockPairs.Receipt := [
  ⟨⟨59,59,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid6580 : StockPairs.checked rows6580 = true := by decide +kernel
theorem route6580 (i : Fin 14) : (rows6580.get i).Done :=
  StockPairs.doneAt paid6580 i

def cell6582:PairCell.Row:=⟨59,59,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6582:ThreeRule.check cell6582 (2:Fin 18)=true:=by decide +kernel
def cell6583:PairCell.Row:=⟨59,59,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6583:ThreeRule.check cell6583 (2:Fin 18)=true:=by decide +kernel
def cell6584:PairCell.Row:=⟨59,59,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6584:ThreeRule.check cell6584 (2:Fin 18)=true:=by decide +kernel
def cell6585:PairCell.Row:=⟨59,59,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6585:ThreeRule.check cell6585 (2:Fin 18)=true:=by decide +kernel

def cell6598:PairCell.Row:=⟨60,60,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6598:ThreeRule.check cell6598 (2:Fin 18)=true:=by decide +kernel
def cell6599:PairCell.Row:=⟨60,60,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6599:ThreeRule.check cell6599 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2858

-- Source: Research6969.PairReceipts330
section Z6969Source2859
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6600:PairCell.Row:=⟨60,60,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6600:ThreeRule.check cell6600 (2:Fin 18)=true:=by decide +kernel
def cell6601:PairCell.Row:=⟨60,60,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6601:ThreeRule.check cell6601 (2:Fin 18)=true:=by decide +kernel
private def rows6602 : List StockPairs.Receipt := [
  ⟨⟨61,61,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid6602 : StockPairs.checked rows6602 = true := by decide +kernel
theorem route6602 (i : Fin 14) : (rows6602.get i).Done :=
  StockPairs.doneAt paid6602 i

def cell6614:PairCell.Row:=⟨61,61,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6614:ThreeRule.check cell6614 (2:Fin 18)=true:=by decide +kernel
def cell6615:PairCell.Row:=⟨61,61,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6615:ThreeRule.check cell6615 (2:Fin 18)=true:=by decide +kernel
def cell6616:PairCell.Row:=⟨61,61,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6616:ThreeRule.check cell6616 (2:Fin 18)=true:=by decide +kernel
def cell6617:PairCell.Row:=⟨61,61,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6617:ThreeRule.check cell6617 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2859

-- Source: Research6969.PairReceipts331
section Z6969Source2860
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6620 : List StockPairs.Receipt := [
  ⟨⟨62,62,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩]
private theorem paid6620 : StockPairs.checked rows6620 = true := by decide +kernel
theorem route6620 (i : Fin 16) : (rows6620.get i).Done :=
  StockPairs.doneAt paid6620 i

def cell6630:PairCell.Row:=⟨62,62,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6630:ThreeRule.check cell6630 (2:Fin 18)=true:=by decide +kernel
def cell6631:PairCell.Row:=⟨62,62,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6631:ThreeRule.check cell6631 (2:Fin 18)=true:=by decide +kernel
def cell6632:PairCell.Row:=⟨62,62,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6632:ThreeRule.check cell6632 (2:Fin 18)=true:=by decide +kernel
def cell6633:PairCell.Row:=⟨62,62,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6633:ThreeRule.check cell6633 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2860

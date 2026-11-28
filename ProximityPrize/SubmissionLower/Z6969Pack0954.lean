import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0951
import ProximityPrize.SubmissionLower.Z6969Pack0953
import ProximityPrize.SubmissionLower.Z6969Pack0952
import ProximityPrize.SubmissionLower.Z6969Pack0939

set_option Elab.async false

-- Source: Research6969.PairReceipts333
section Z6969Source2807
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6660:PairCell.Row:=⟨50,50,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩
theorem check6660:ThreeRule.check cell6660 (2:Fin 18)=true:=by decide +kernel
def cell6661:PairCell.Row:=⟨50,50,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩
theorem check6661:ThreeRule.check cell6661 (2:Fin 18)=true:=by decide +kernel
def cell6662:PairCell.Row:=⟨50,50,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6662:ThreeRule.check cell6662 (2:Fin 18)=true:=by decide +kernel
def cell6663:PairCell.Row:=⟨50,50,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6663:ThreeRule.check cell6663 (2:Fin 18)=true:=by decide +kernel
def cell6664:PairCell.Row:=⟨50,50,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6664:ThreeRule.check cell6664 (2:Fin 18)=true:=by decide +kernel
private def rows6665 : List StockPairs.Receipt := [
  ⟨⟨51,51,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid6665 : StockPairs.checked rows6665 = true := by decide +kernel
theorem route6665 (i : Fin 11) : (rows6665.get i).Done :=
  StockPairs.doneAt paid6665 i

def cell6676:PairCell.Row:=⟨51,51,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩
theorem check6676:ThreeRule.check cell6676 (2:Fin 18)=true:=by decide +kernel
def cell6677:PairCell.Row:=⟨51,51,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6677:ThreeRule.check cell6677 (2:Fin 18)=true:=by decide +kernel
def cell6678:PairCell.Row:=⟨51,51,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6678:ThreeRule.check cell6678 (2:Fin 18)=true:=by decide +kernel
def cell6679:PairCell.Row:=⟨51,51,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6679:ThreeRule.check cell6679 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2807

-- Source: Research6969.PairReceipts334
section Z6969Source2808
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6680 : List StockPairs.Receipt := [
  ⟨⟨52,52,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩]
private theorem paid6680 : StockPairs.checked rows6680 = true := by decide +kernel
theorem route6680 (i : Fin 16) : (rows6680.get i).Done :=
  StockPairs.doneAt paid6680 i

def cell6691:PairCell.Row:=⟨52,52,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩
theorem check6691:ThreeRule.check cell6691 (2:Fin 18)=true:=by decide +kernel
def cell6692:PairCell.Row:=⟨52,52,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6692:ThreeRule.check cell6692 (2:Fin 18)=true:=by decide +kernel
def cell6693:PairCell.Row:=⟨52,52,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6693:ThreeRule.check cell6693 (2:Fin 18)=true:=by decide +kernel
def cell6694:PairCell.Row:=⟨52,52,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6694:ThreeRule.check cell6694 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2808

-- Source: Research6969.PairReceipts335
section Z6969Source2809
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6700 : List StockPairs.Receipt := [
  ⟨⟨53,53,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6700 : StockPairs.checked rows6700 = true := by decide +kernel
theorem route6700 (i : Fin 16) : (rows6700.get i).Done :=
  StockPairs.doneAt paid6700 i

def cell6706:PairCell.Row:=⟨53,53,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩
theorem check6706:ThreeRule.check cell6706 (2:Fin 18)=true:=by decide +kernel
def cell6707:PairCell.Row:=⟨53,53,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6707:ThreeRule.check cell6707 (2:Fin 18)=true:=by decide +kernel
def cell6708:PairCell.Row:=⟨53,53,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6708:ThreeRule.check cell6708 (2:Fin 18)=true:=by decide +kernel
def cell6709:PairCell.Row:=⟨53,53,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6709:ThreeRule.check cell6709 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2809

-- Source: Research6969.PairReceipts336
section Z6969Source2810
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6720 : List StockPairs.Receipt := [
  ⟨⟨54,54,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid6720 : StockPairs.checked rows6720 = true := by decide +kernel
theorem route6720 (i : Fin 12) : (rows6720.get i).Done :=
  StockPairs.doneAt paid6720 i
def cell6721:PairCell.Row:=⟨54,54,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩
theorem check6721:ThreeRule.check cell6721 (2:Fin 18)=true:=by decide +kernel
def cell6722:PairCell.Row:=⟨54,54,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6722:ThreeRule.check cell6722 (2:Fin 18)=true:=by decide +kernel
def cell6723:PairCell.Row:=⟨54,54,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6723:ThreeRule.check cell6723 (2:Fin 18)=true:=by decide +kernel
def cell6724:PairCell.Row:=⟨54,54,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6724:ThreeRule.check cell6724 (2:Fin 18)=true:=by decide +kernel

def cell6736:PairCell.Row:=⟨55,55,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩
theorem check6736:ThreeRule.check cell6736 (2:Fin 18)=true:=by decide +kernel
def cell6737:PairCell.Row:=⟨55,55,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6737:ThreeRule.check cell6737 (2:Fin 18)=true:=by decide +kernel
def cell6738:PairCell.Row:=⟨55,55,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6738:ThreeRule.check cell6738 (2:Fin 18)=true:=by decide +kernel
def cell6739:PairCell.Row:=⟨55,55,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6739:ThreeRule.check cell6739 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2810

-- Source: Research6969.PairReceipts337
section Z6969Source2811
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6740 : List StockPairs.Receipt := [
  ⟨⟨56,56,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩]
private theorem paid6740 : StockPairs.checked rows6740 = true := by decide +kernel
theorem route6740 (i : Fin 17) : (rows6740.get i).Done :=
  StockPairs.doneAt paid6740 i

def cell6752:PairCell.Row:=⟨56,56,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6752:ThreeRule.check cell6752 (2:Fin 18)=true:=by decide +kernel
def cell6753:PairCell.Row:=⟨56,56,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6753:ThreeRule.check cell6753 (2:Fin 18)=true:=by decide +kernel
def cell6754:PairCell.Row:=⟨56,56,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6754:ThreeRule.check cell6754 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2811

-- Source: Research6969.PairReceipts338
section Z6969Source2812
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6760 : List StockPairs.Receipt := [
  ⟨⟨57,57,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6760 : StockPairs.checked rows6760 = true := by decide +kernel
theorem route6760 (i : Fin 17) : (rows6760.get i).Done :=
  StockPairs.doneAt paid6760 i

def cell6767:PairCell.Row:=⟨57,57,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6767:ThreeRule.check cell6767 (2:Fin 18)=true:=by decide +kernel
def cell6768:PairCell.Row:=⟨57,57,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6768:ThreeRule.check cell6768 (2:Fin 18)=true:=by decide +kernel
def cell6769:PairCell.Row:=⟨57,57,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6769:ThreeRule.check cell6769 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2812

-- Source: Research6969.PairReceipts339
section Z6969Source2813
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6780 : List StockPairs.Receipt := [
  ⟨⟨58,58,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid6780 : StockPairs.checked rows6780 = true := by decide +kernel
theorem route6780 (i : Fin 14) : (rows6780.get i).Done :=
  StockPairs.doneAt paid6780 i

def cell6782:PairCell.Row:=⟨58,58,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6782:ThreeRule.check cell6782 (2:Fin 18)=true:=by decide +kernel
def cell6783:PairCell.Row:=⟨58,58,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6783:ThreeRule.check cell6783 (2:Fin 18)=true:=by decide +kernel
def cell6784:PairCell.Row:=⟨58,58,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6784:ThreeRule.check cell6784 (2:Fin 18)=true:=by decide +kernel

def cell6797:PairCell.Row:=⟨59,59,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6797:ThreeRule.check cell6797 (2:Fin 18)=true:=by decide +kernel
def cell6798:PairCell.Row:=⟨59,59,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6798:ThreeRule.check cell6798 (2:Fin 18)=true:=by decide +kernel
def cell6799:PairCell.Row:=⟨59,59,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6799:ThreeRule.check cell6799 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2813

-- Source: Research6969.PairReceipts340
section Z6969Source2814
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6800 : List StockPairs.Receipt := [
  ⟨⟨60,60,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩]
private theorem paid6800 : StockPairs.checked rows6800 = true := by decide +kernel
theorem route6800 (i : Fin 17) : (rows6800.get i).Done :=
  StockPairs.doneAt paid6800 i

def cell6812:PairCell.Row:=⟨60,60,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6812:ThreeRule.check cell6812 (2:Fin 18)=true:=by decide +kernel
def cell6813:PairCell.Row:=⟨60,60,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6813:ThreeRule.check cell6813 (2:Fin 18)=true:=by decide +kernel
def cell6814:PairCell.Row:=⟨60,60,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6814:ThreeRule.check cell6814 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2814

-- Source: Research6969.PairReceipts341
section Z6969Source2815
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6820 : List StockPairs.Receipt := [
  ⟨⟨61,61,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6820 : StockPairs.checked rows6820 = true := by decide +kernel
theorem route6820 (i : Fin 17) : (rows6820.get i).Done :=
  StockPairs.doneAt paid6820 i

def cell6827:PairCell.Row:=⟨61,61,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6827:ThreeRule.check cell6827 (2:Fin 18)=true:=by decide +kernel
def cell6828:PairCell.Row:=⟨61,61,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6828:ThreeRule.check cell6828 (2:Fin 18)=true:=by decide +kernel
def cell6829:PairCell.Row:=⟨61,61,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6829:ThreeRule.check cell6829 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2815

-- Source: Research6969.PairReceipts342
section Z6969Source2816
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6840 : List StockPairs.Receipt := [
  ⟨⟨62,62,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid6840 : StockPairs.checked rows6840 = true := by decide +kernel
theorem route6840 (i : Fin 14) : (rows6840.get i).Done :=
  StockPairs.doneAt paid6840 i

def cell6842:PairCell.Row:=⟨62,62,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6842:ThreeRule.check cell6842 (2:Fin 18)=true:=by decide +kernel
def cell6843:PairCell.Row:=⟨62,62,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6843:ThreeRule.check cell6843 (2:Fin 18)=true:=by decide +kernel
def cell6844:PairCell.Row:=⟨62,62,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6844:ThreeRule.check cell6844 (2:Fin 18)=true:=by decide +kernel

def cell6857:PairCell.Row:=⟨63,63,10,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩
theorem check6857:ThreeRule.check cell6857 (2:Fin 18)=true:=by decide +kernel
def cell6858:PairCell.Row:=⟨63,63,10,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩
theorem check6858:ThreeRule.check cell6858 (2:Fin 18)=true:=by decide +kernel
def cell6859:PairCell.Row:=⟨63,63,10,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩
theorem check6859:ThreeRule.check cell6859 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2816

-- Source: Research6969.HardFit3At130
section Z6969Source2817
set_option autoImplicit true
namespace Research6969.HardFit3At130
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes111:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,55,some 55⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 55 ⟨
    (PairReceipts.route3010 0),
    (PairReceipts.route3010 1),
    (PairReceipts.route3010 2),
    (PairReceipts.route3010 3),
    (PairReceipts.route3010 4),
    (PairReceipts.route3010 5),
    (PairReceipts.route3010 6),
    (PairReceipts.route3010 7),
    (PairReceipts.route3010 8),
    (PairReceipts.route3010 9),
    (PairReceipts.route3020 0),
    (PairReceipts.route3020 1),
    (PairReceipts.route3020 2),
    (PairReceipts.route3020 3),
    (PairReceipts.route3020 4),
    (PairReceipts.route3020 5),
    (PairReceipts.route3020 6),
    (PairReceipts.route3020 7),
    (PairReceipts.route3020 8),
    (PairReceipts.route3020 9),
    (PairReceipts.route3020 10),
    (PairReceipts.route3020 11),
    (PairReceipts.route3020 12),
    (PairReceipts.route3020 13),
    (PairReceipts.route3020 14),
    PairLeaves.excluded PairReceipts.cell3035 PairReceipts.check3035 (none),
    PairLeaves.excluded PairReceipts.cell3036 PairReceipts.check3036 (none),
    PairLeaves.excluded PairReceipts.cell3037 PairReceipts.check3037 (none),
    PairLeaves.excluded PairReceipts.cell3038 PairReceipts.check3038 (none),
    PairLeaves.excluded PairReceipts.cell3039 PairReceipts.check3039 (none),
    PairLeaves.excluded PairReceipts.cell3040 PairReceipts.check3040 (none),
    PairLeaves.excluded PairReceipts.cell3041 PairReceipts.check3041 (none),
    PairLeaves.excluded PairReceipts.cell3042 PairReceipts.check3042 (none),
    PairLeaves.excluded PairReceipts.cell3043 PairReceipts.check3043 (none),
    PairLeaves.excluded PairReceipts.cell3044 PairReceipts.check3044 (none),
    PairLeaves.excluded PairReceipts.cell3045 PairReceipts.check3045 (none),
    PairLeaves.excluded PairReceipts.cell3046 PairReceipts.check3046 (none),
    PairLeaves.excluded PairReceipts.cell3047 PairReceipts.check3047 (none),
    PairLeaves.excluded PairReceipts.cell3048 PairReceipts.check3048 (none),
    PairLeaves.excluded PairReceipts.cell3049 PairReceipts.check3049 (none),
    PairLeaves.excluded PairReceipts.cell3050 PairReceipts.check3050 (none),
    PairLeaves.excluded PairReceipts.cell3051 PairReceipts.check3051 (none),
    PairLeaves.excluded PairReceipts.cell3052 PairReceipts.check3052 (none),
    PairLeaves.excluded PairReceipts.cell3053 PairReceipts.check3053 (none),
    PairLeaves.excluded PairReceipts.cell3054 PairReceipts.check3054 (none),
    PairLeaves.excluded PairReceipts.cell3055 PairReceipts.check3055 (none),
    PairLeaves.excluded PairReceipts.cell3056 PairReceipts.check3056 (none),
    PairLeaves.excluded PairReceipts.cell3057 PairReceipts.check3057 (none),
    PairLeaves.excluded PairReceipts.cell3058 PairReceipts.check3058 (none),
    PairLeaves.excluded PairReceipts.cell3059 PairReceipts.check3059 (none),
    PairLeaves.excluded PairReceipts.cell3060 PairReceipts.check3060 (none),
    PairLeaves.excluded PairReceipts.cell3061 PairReceipts.check3061 (none),
    PairLeaves.excluded PairReceipts.cell3062 PairReceipts.check3062 (none),
    PairLeaves.excluded PairReceipts.cell3063 PairReceipts.check3063 (none),
    PairLeaves.excluded PairReceipts.cell3064 PairReceipts.check3064 (none),
    PairLeaves.excluded PairReceipts.cell3065 PairReceipts.check3065 (none),
    trivial⟩)
theorem case130: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,55,some 55⟩:=PairRoute.start _ allAxes111
private theorem allAxes225:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,56,some 56⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 56 ⟨
    (PairReceipts.route2953 0),
    (PairReceipts.route2953 1),
    (PairReceipts.route2953 2),
    (PairReceipts.route2953 3),
    (PairReceipts.route2953 4),
    (PairReceipts.route2953 5),
    (PairReceipts.route2953 6),
    (PairReceipts.route2960 0),
    (PairReceipts.route2960 1),
    (PairReceipts.route2960 2),
    (PairReceipts.route2960 3),
    (PairReceipts.route2960 4),
    (PairReceipts.route2960 5),
    (PairReceipts.route2960 6),
    (PairReceipts.route2960 7),
    (PairReceipts.route2960 8),
    (PairReceipts.route2960 9),
    (PairReceipts.route2960 10),
    (PairReceipts.route2960 11),
    (PairReceipts.route2960 12),
    (PairReceipts.route2960 13),
    (PairReceipts.route2960 14),
    (PairReceipts.route2960 15),
    (PairReceipts.route2960 16),
    (PairReceipts.route2960 17),
    PairLeaves.excluded PairReceipts.cell2978 PairReceipts.check2978 (none),
    PairLeaves.excluded PairReceipts.cell2979 PairReceipts.check2979 (none),
    PairLeaves.excluded PairReceipts.cell2980 PairReceipts.check2980 (none),
    PairLeaves.excluded PairReceipts.cell2981 PairReceipts.check2981 (none),
    PairLeaves.excluded PairReceipts.cell2982 PairReceipts.check2982 (none),
    PairLeaves.excluded PairReceipts.cell2983 PairReceipts.check2983 (none),
    PairLeaves.excluded PairReceipts.cell2984 PairReceipts.check2984 (none),
    PairLeaves.excluded PairReceipts.cell2985 PairReceipts.check2985 (none),
    PairLeaves.excluded PairReceipts.cell2986 PairReceipts.check2986 (none),
    PairLeaves.excluded PairReceipts.cell2987 PairReceipts.check2987 (none),
    PairLeaves.excluded PairReceipts.cell2988 PairReceipts.check2988 (none),
    PairLeaves.excluded PairReceipts.cell2989 PairReceipts.check2989 (none),
    PairLeaves.excluded PairReceipts.cell2990 PairReceipts.check2990 (none),
    PairLeaves.excluded PairReceipts.cell2991 PairReceipts.check2991 (none),
    PairLeaves.excluded PairReceipts.cell2992 PairReceipts.check2992 (none),
    PairLeaves.excluded PairReceipts.cell2993 PairReceipts.check2993 (none),
    PairLeaves.excluded PairReceipts.cell2994 PairReceipts.check2994 (none),
    PairLeaves.excluded PairReceipts.cell2995 PairReceipts.check2995 (none),
    PairLeaves.excluded PairReceipts.cell2996 PairReceipts.check2996 (none),
    PairLeaves.excluded PairReceipts.cell2997 PairReceipts.check2997 (none),
    PairLeaves.excluded PairReceipts.cell2998 PairReceipts.check2998 (none),
    PairLeaves.excluded PairReceipts.cell2999 PairReceipts.check2999 (none),
    PairLeaves.excluded PairReceipts.cell3000 PairReceipts.check3000 (none),
    PairLeaves.excluded PairReceipts.cell3001 PairReceipts.check3001 (none),
    PairLeaves.excluded PairReceipts.cell3002 PairReceipts.check3002 (none),
    PairLeaves.excluded PairReceipts.cell3003 PairReceipts.check3003 (none),
    PairLeaves.excluded PairReceipts.cell3004 PairReceipts.check3004 (none),
    PairLeaves.excluded PairReceipts.cell3005 PairReceipts.check3005 (none),
    PairLeaves.excluded PairReceipts.cell3006 PairReceipts.check3006 (none),
    PairLeaves.excluded PairReceipts.cell3007 PairReceipts.check3007 (none),
    PairLeaves.excluded PairReceipts.cell3008 PairReceipts.check3008 (none),
    PairLeaves.excluded PairReceipts.cell3009 PairReceipts.check3009 (none),
    trivial⟩)
theorem case131: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,56,some 56⟩:=PairRoute.start _ allAxes225
private theorem allAxes341:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,2,57,some 57⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 57 ⟨
    (PairReceipts.route2880 15),
    (PairReceipts.route2880 16),
    (PairReceipts.route2880 17),
    (PairReceipts.route2880 18),
    (PairReceipts.route2880 19),
    (PairReceipts.route2900 0),
    (PairReceipts.route2900 1),
    (PairReceipts.route2900 2),
    (PairReceipts.route2900 3),
    (PairReceipts.route2900 4),
    (PairReceipts.route2900 5),
    (PairReceipts.route2900 6),
    (PairReceipts.route2900 7),
    (PairReceipts.route2900 8),
    (PairReceipts.route2900 9),
    (PairReceipts.route2900 10),
    (PairReceipts.route2900 11),
    (PairReceipts.route2900 12),
    (PairReceipts.route2900 13),
    (PairReceipts.route2900 14),
    (PairReceipts.route2900 15),
    (PairReceipts.route2900 16),
    (PairReceipts.route2900 17),
    (PairReceipts.route2900 18),
    (PairReceipts.route2900 19),
    PairLeaves.excluded PairReceipts.cell2920 PairReceipts.check2920 (none),
    PairLeaves.excluded PairReceipts.cell2921 PairReceipts.check2921 (none),
    PairLeaves.excluded PairReceipts.cell2922 PairReceipts.check2922 (none),
    PairLeaves.excluded PairReceipts.cell2923 PairReceipts.check2923 (none),
    PairLeaves.excluded PairReceipts.cell2924 PairReceipts.check2924 (none),
    PairLeaves.excluded PairReceipts.cell2925 PairReceipts.check2925 (none),
    PairLeaves.excluded PairReceipts.cell2926 PairReceipts.check2926 (none),
    PairLeaves.excluded PairReceipts.cell2927 PairReceipts.check2927 (none),
    PairLeaves.excluded PairReceipts.cell2928 PairReceipts.check2928 (none),
    PairLeaves.excluded PairReceipts.cell2929 PairReceipts.check2929 (none),
    PairLeaves.excluded PairReceipts.cell2930 PairReceipts.check2930 (none),
    PairLeaves.excluded PairReceipts.cell2931 PairReceipts.check2931 (none),
    PairLeaves.excluded PairReceipts.cell2932 PairReceipts.check2932 (none),
    PairLeaves.excluded PairReceipts.cell2933 PairReceipts.check2933 (none),
    PairLeaves.excluded PairReceipts.cell2934 PairReceipts.check2934 (none),
    PairLeaves.excluded PairReceipts.cell2935 PairReceipts.check2935 (none),
    PairLeaves.excluded PairReceipts.cell2936 PairReceipts.check2936 (none),
    PairLeaves.excluded PairReceipts.cell2937 PairReceipts.check2937 (none),
    PairLeaves.excluded PairReceipts.cell2938 PairReceipts.check2938 (none),
    PairLeaves.excluded PairReceipts.cell2939 PairReceipts.check2939 (none),
    PairLeaves.excluded PairReceipts.cell2940 PairReceipts.check2940 (none),
    PairLeaves.excluded PairReceipts.cell2941 PairReceipts.check2941 (none),
    PairLeaves.excluded PairReceipts.cell2942 PairReceipts.check2942 (none),
    PairLeaves.excluded PairReceipts.cell2943 PairReceipts.check2943 (none),
    PairLeaves.excluded PairReceipts.cell2944 PairReceipts.check2944 (none),
    PairLeaves.excluded PairReceipts.cell2945 PairReceipts.check2945 (none),
    PairLeaves.excluded PairReceipts.cell2946 PairReceipts.check2946 (none),
    PairLeaves.excluded PairReceipts.cell2947 PairReceipts.check2947 (none),
    PairLeaves.excluded PairReceipts.cell2948 PairReceipts.check2948 (none),
    PairLeaves.excluded PairReceipts.cell2949 PairReceipts.check2949 (none),
    PairLeaves.excluded PairReceipts.cell2950 PairReceipts.check2950 (none),
    PairLeaves.excluded PairReceipts.cell2951 PairReceipts.check2951 (none),
    PairLeaves.excluded PairReceipts.cell2952 PairReceipts.check2952 (none),
    trivial⟩)
theorem case132: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,57,some 57⟩:=PairRoute.start _ allAxes341
private def leaf342 := (PairReceipts.route2880 13)
private def leaf343 := (PairReceipts.route2880 14)
private def weight344 := PairRoute.weight 283522 leaf342 leaf343
theorem case133: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,58,some 58⟩:=PairRoute.start _ weight344
private def leaf345 := (PairReceipts.route2880 12)
theorem case134: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,59,some 60⟩:=PairRoute.start _ leaf345
private def leaf346 := (PairReceipts.route2880 11)
theorem case135: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,61,some 64⟩:=PairRoute.start _ leaf346
private def leaf347 := (PairReceipts.route3380 8)
theorem case136: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,4,some 8⟩:=PairRoute.start _ leaf347
private def leaf348 := (PairReceipts.route3380 7)
theorem case137: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,9,some 12⟩:=PairRoute.start _ leaf348
private def leaf349 := (PairReceipts.route3380 6)
theorem case138: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,13,some 13⟩:=PairRoute.start _ leaf349
private theorem allAxes379:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6640 6),
    (PairReceipts.route6640 7),
    (PairReceipts.route6640 8),
    (PairReceipts.route6640 9),
    (PairReceipts.route6640 10),
    (PairReceipts.route6640 11),
    (PairReceipts.route6640 12),
    (PairReceipts.route6640 13),
    (PairReceipts.route6640 14),
    (PairReceipts.route6640 15),
    PairLeaves.three PairReceipts.cell6660 PairReceipts.check6660 (by decide) (none),
    PairLeaves.three PairReceipts.cell6661 PairReceipts.check6661 (by decide) (none),
    PairLeaves.three PairReceipts.cell6662 PairReceipts.check6662 (by decide) (none),
    PairLeaves.three PairReceipts.cell6663 PairReceipts.check6663 (by decide) (none),
    PairLeaves.three PairReceipts.cell6664 PairReceipts.check6664 (by decide) (none),
    trivial⟩)
private theorem allAxes409:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6665 0),
    (PairReceipts.route6665 1),
    (PairReceipts.route6665 2),
    (PairReceipts.route6665 3),
    (PairReceipts.route6665 4),
    (PairReceipts.route6665 5),
    (PairReceipts.route6665 6),
    (PairReceipts.route6665 7),
    (PairReceipts.route6665 8),
    (PairReceipts.route6665 9),
    (PairReceipts.route6665 10),
    PairLeaves.three PairReceipts.cell6676 PairReceipts.check6676 (by decide) (none),
    PairLeaves.three PairReceipts.cell6677 PairReceipts.check6677 (by decide) (none),
    PairLeaves.three PairReceipts.cell6678 PairReceipts.check6678 (by decide) (none),
    PairLeaves.three PairReceipts.cell6679 PairReceipts.check6679 (by decide) (none),
    trivial⟩)
private theorem allAxes439:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6680 0),
    (PairReceipts.route6680 1),
    (PairReceipts.route6680 2),
    (PairReceipts.route6680 3),
    (PairReceipts.route6680 4),
    (PairReceipts.route6680 5),
    (PairReceipts.route6680 6),
    (PairReceipts.route6680 7),
    (PairReceipts.route6680 8),
    (PairReceipts.route6680 9),
    (PairReceipts.route6680 10),
    PairLeaves.three PairReceipts.cell6691 PairReceipts.check6691 (by decide) (none),
    PairLeaves.three PairReceipts.cell6692 PairReceipts.check6692 (by decide) (none),
    PairLeaves.three PairReceipts.cell6693 PairReceipts.check6693 (by decide) (none),
    PairLeaves.three PairReceipts.cell6694 PairReceipts.check6694 (by decide) (none),
    trivial⟩)
private theorem allAxes469:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6680 11),
    (PairReceipts.route6680 12),
    (PairReceipts.route6680 13),
    (PairReceipts.route6680 14),
    (PairReceipts.route6680 15),
    (PairReceipts.route6700 0),
    (PairReceipts.route6700 1),
    (PairReceipts.route6700 2),
    (PairReceipts.route6700 3),
    (PairReceipts.route6700 4),
    (PairReceipts.route6700 5),
    PairLeaves.three PairReceipts.cell6706 PairReceipts.check6706 (by decide) (none),
    PairLeaves.three PairReceipts.cell6707 PairReceipts.check6707 (by decide) (none),
    PairLeaves.three PairReceipts.cell6708 PairReceipts.check6708 (by decide) (none),
    PairLeaves.three PairReceipts.cell6709 PairReceipts.check6709 (by decide) (none),
    trivial⟩)
private theorem allAxes499:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6700 6),
    (PairReceipts.route6700 7),
    (PairReceipts.route6700 8),
    (PairReceipts.route6700 9),
    (PairReceipts.route6700 10),
    (PairReceipts.route6700 11),
    (PairReceipts.route6700 12),
    (PairReceipts.route6700 13),
    (PairReceipts.route6700 14),
    (PairReceipts.route6700 15),
    (PairReceipts.route6720 0),
    PairLeaves.three PairReceipts.cell6721 PairReceipts.check6721 (by decide) (none),
    PairLeaves.three PairReceipts.cell6722 PairReceipts.check6722 (by decide) (none),
    PairLeaves.three PairReceipts.cell6723 PairReceipts.check6723 (by decide) (none),
    PairLeaves.three PairReceipts.cell6724 PairReceipts.check6724 (by decide) (none),
    trivial⟩)
private theorem allAxes529:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6720 1),
    (PairReceipts.route6720 2),
    (PairReceipts.route6720 3),
    (PairReceipts.route6720 4),
    (PairReceipts.route6720 5),
    (PairReceipts.route6720 6),
    (PairReceipts.route6720 7),
    (PairReceipts.route6720 8),
    (PairReceipts.route6720 9),
    (PairReceipts.route6720 10),
    (PairReceipts.route6720 11),
    PairLeaves.three PairReceipts.cell6736 PairReceipts.check6736 (by decide) (none),
    PairLeaves.three PairReceipts.cell6737 PairReceipts.check6737 (by decide) (none),
    PairLeaves.three PairReceipts.cell6738 PairReceipts.check6738 (by decide) (none),
    PairLeaves.three PairReceipts.cell6739 PairReceipts.check6739 (by decide) (none),
    trivial⟩)
private theorem allAxes559:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6740 0),
    (PairReceipts.route6740 1),
    (PairReceipts.route6740 2),
    (PairReceipts.route6740 3),
    (PairReceipts.route6740 4),
    (PairReceipts.route6740 5),
    (PairReceipts.route6740 6),
    (PairReceipts.route6740 7),
    (PairReceipts.route6740 8),
    (PairReceipts.route6740 9),
    (PairReceipts.route6740 10),
    (PairReceipts.route6740 11),
    PairLeaves.three PairReceipts.cell6752 PairReceipts.check6752 (by decide) (none),
    PairLeaves.three PairReceipts.cell6753 PairReceipts.check6753 (by decide) (none),
    PairLeaves.three PairReceipts.cell6754 PairReceipts.check6754 (by decide) (none),
    trivial⟩)
private theorem allAxes589:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6740 12),
    (PairReceipts.route6740 13),
    (PairReceipts.route6740 14),
    (PairReceipts.route6740 15),
    (PairReceipts.route6740 16),
    (PairReceipts.route6760 0),
    (PairReceipts.route6760 1),
    (PairReceipts.route6760 2),
    (PairReceipts.route6760 3),
    (PairReceipts.route6760 4),
    (PairReceipts.route6760 5),
    (PairReceipts.route6760 6),
    PairLeaves.three PairReceipts.cell6767 PairReceipts.check6767 (by decide) (none),
    PairLeaves.three PairReceipts.cell6768 PairReceipts.check6768 (by decide) (none),
    PairLeaves.three PairReceipts.cell6769 PairReceipts.check6769 (by decide) (none),
    trivial⟩)
private theorem allAxes619:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6760 7),
    (PairReceipts.route6760 8),
    (PairReceipts.route6760 9),
    (PairReceipts.route6760 10),
    (PairReceipts.route6760 11),
    (PairReceipts.route6760 12),
    (PairReceipts.route6760 13),
    (PairReceipts.route6760 14),
    (PairReceipts.route6760 15),
    (PairReceipts.route6760 16),
    (PairReceipts.route6780 0),
    (PairReceipts.route6780 1),
    PairLeaves.three PairReceipts.cell6782 PairReceipts.check6782 (by decide) (none),
    PairLeaves.three PairReceipts.cell6783 PairReceipts.check6783 (by decide) (none),
    PairLeaves.three PairReceipts.cell6784 PairReceipts.check6784 (by decide) (none),
    trivial⟩)
private theorem allAxes649:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6780 2),
    (PairReceipts.route6780 3),
    (PairReceipts.route6780 4),
    (PairReceipts.route6780 5),
    (PairReceipts.route6780 6),
    (PairReceipts.route6780 7),
    (PairReceipts.route6780 8),
    (PairReceipts.route6780 9),
    (PairReceipts.route6780 10),
    (PairReceipts.route6780 11),
    (PairReceipts.route6780 12),
    (PairReceipts.route6780 13),
    PairLeaves.three PairReceipts.cell6797 PairReceipts.check6797 (by decide) (none),
    PairLeaves.three PairReceipts.cell6798 PairReceipts.check6798 (by decide) (none),
    PairLeaves.three PairReceipts.cell6799 PairReceipts.check6799 (by decide) (none),
    trivial⟩)
private theorem allAxes679:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6800 0),
    (PairReceipts.route6800 1),
    (PairReceipts.route6800 2),
    (PairReceipts.route6800 3),
    (PairReceipts.route6800 4),
    (PairReceipts.route6800 5),
    (PairReceipts.route6800 6),
    (PairReceipts.route6800 7),
    (PairReceipts.route6800 8),
    (PairReceipts.route6800 9),
    (PairReceipts.route6800 10),
    (PairReceipts.route6800 11),
    PairLeaves.three PairReceipts.cell6812 PairReceipts.check6812 (by decide) (none),
    PairLeaves.three PairReceipts.cell6813 PairReceipts.check6813 (by decide) (none),
    PairLeaves.three PairReceipts.cell6814 PairReceipts.check6814 (by decide) (none),
    trivial⟩)
private theorem allAxes709:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6800 12),
    (PairReceipts.route6800 13),
    (PairReceipts.route6800 14),
    (PairReceipts.route6800 15),
    (PairReceipts.route6800 16),
    (PairReceipts.route6820 0),
    (PairReceipts.route6820 1),
    (PairReceipts.route6820 2),
    (PairReceipts.route6820 3),
    (PairReceipts.route6820 4),
    (PairReceipts.route6820 5),
    (PairReceipts.route6820 6),
    PairLeaves.three PairReceipts.cell6827 PairReceipts.check6827 (by decide) (none),
    PairLeaves.three PairReceipts.cell6828 PairReceipts.check6828 (by decide) (none),
    PairLeaves.three PairReceipts.cell6829 PairReceipts.check6829 (by decide) (none),
    trivial⟩)
private theorem allAxes739:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6820 7),
    (PairReceipts.route6820 8),
    (PairReceipts.route6820 9),
    (PairReceipts.route6820 10),
    (PairReceipts.route6820 11),
    (PairReceipts.route6820 12),
    (PairReceipts.route6820 13),
    (PairReceipts.route6820 14),
    (PairReceipts.route6820 15),
    (PairReceipts.route6820 16),
    (PairReceipts.route6840 0),
    (PairReceipts.route6840 1),
    PairLeaves.three PairReceipts.cell6842 PairReceipts.check6842 (by decide) (none),
    PairLeaves.three PairReceipts.cell6843 PairReceipts.check6843 (by decide) (none),
    PairLeaves.three PairReceipts.cell6844 PairReceipts.check6844 (by decide) (none),
    trivial⟩)
private theorem allAxes769:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route6840 2),
    (PairReceipts.route6840 3),
    (PairReceipts.route6840 4),
    (PairReceipts.route6840 5),
    (PairReceipts.route6840 6),
    (PairReceipts.route6840 7),
    (PairReceipts.route6840 8),
    (PairReceipts.route6840 9),
    (PairReceipts.route6840 10),
    (PairReceipts.route6840 11),
    (PairReceipts.route6840 12),
    (PairReceipts.route6840 13),
    PairLeaves.three PairReceipts.cell6857 PairReceipts.check6857 (by decide) (none),
    PairLeaves.three PairReceipts.cell6858 PairReceipts.check6858 (by decide) (none),
    PairLeaves.three PairReceipts.cell6859 PairReceipts.check6859 (by decide) (none),
    trivial⟩)
private def grade770 := PairRoute.grade 62 allAxes739 allAxes769
private def grade771 := PairRoute.grade 61 allAxes709 grade770
private def grade772 := PairRoute.grade 60 allAxes679 grade771
private def grade773 := PairRoute.grade 59 allAxes649 grade772
private def grade774 := PairRoute.grade 58 allAxes619 grade773
private def grade775 := PairRoute.grade 57 allAxes589 grade774
private def grade776 := PairRoute.grade 56 allAxes559 grade775
private def grade777 := PairRoute.grade 55 allAxes529 grade776
private def grade778 := PairRoute.grade 54 allAxes499 grade777
private def grade779 := PairRoute.grade 53 allAxes469 grade778
private def grade780 := PairRoute.grade 52 allAxes439 grade779
private def grade781 := PairRoute.grade 51 allAxes409 grade780
private def grade782 := PairRoute.grade 50 allAxes379 grade781
theorem case139: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,14,some 14⟩:=PairRoute.start _ grade782
end Research6969.HardFit3At130
end Z6969Source2817

-- Source: Research6969.PairReceipts162
section Z6969Source2818
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3240 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,25,some 25,10,some 10,385979,[MeasuredChoices.test924],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,11,some 11,385979,[MeasuredChoices.test924],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,12,some 12,385979,[MeasuredChoices.test924],[AxisChoices.test1833]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,13,some 13,385979,[MeasuredChoices.test924],[AxisChoices.test1834]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,14,some 14,385979,[MeasuredChoices.test924],[AxisChoices.test1835]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,15,some 15,385979,[MeasuredChoices.test924],[AxisChoices.test1836]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,16,some 16,385979,[MeasuredChoices.test924],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,17,some 17,385979,[MeasuredChoices.test924],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,18,some 18,385979,[MeasuredChoices.test924],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,19,some 19,385979,[MeasuredChoices.test924],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,20,some 20,385979,[MeasuredChoices.test924],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,21,some 21,385979,[MeasuredChoices.test924],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,22,some 22,385979,[MeasuredChoices.test924],[AxisChoices.test1843]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,23,some 23,385979,[MeasuredChoices.test924],[AxisChoices.test1844]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,24,some 24,385979,[MeasuredChoices.test924],[AxisChoices.test1845]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,25,some 25,385979,[MeasuredChoices.test924],[AxisChoices.test1845,AxisChoices.test1846]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,24,some 24,0,none,385979,[MeasuredChoices.test910],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,0,some 0,385979,[MeasuredChoices.test896],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,1,some 1,385979,[MeasuredChoices.test896],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,2,some 2,385979,[MeasuredChoices.test896],[AxisChoices.test1823]⟩,2,separateIntersection⟩]
private theorem paid3240 : StockPairs.checked rows3240 = true := by decide +kernel
theorem route3240 (i : Fin 20) : (rows3240.get i).Done :=
  StockPairs.doneAt paid3240 i

end Research6969.PairReceipts
end Z6969Source2818

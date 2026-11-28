import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0675
import ProximityPrize.SubmissionLower.Z6969Pack0970
import ProximityPrize.SubmissionLower.Z6969Pack0971
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0676

set_option Elab.async false

-- Source: Research6969.PairReceipts241
section Z6969Source3004
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4820:PairCell.Row:=⟨64,654,12,2,49,some 49,46,some 46,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4820:(cell4820.cap (5:Fin 18)).grade<cell4820.lowerGrade-cell4820.off:=by decide +kernel
def cell4821:PairCell.Row:=⟨64,654,12,2,49,some 49,47,some 47,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4821:(cell4821.cap (5:Fin 18)).grade<cell4821.lowerGrade-cell4821.off:=by decide +kernel
def cell4822:PairCell.Row:=⟨64,654,12,2,49,some 49,48,some 48,257319,[MeasuredChoices.test62],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4822:(cell4822.cap (5:Fin 18)).grade<cell4822.lowerGrade-cell4822.off:=by decide +kernel
def cell4823:PairCell.Row:=⟨64,654,12,2,49,some 49,49,some 49,257319,[MeasuredChoices.test62],[AxisChoices.test1812]⟩
theorem check4823:(cell4823.cap (5:Fin 18)).grade<cell4823.lowerGrade-cell4823.off:=by decide +kernel
private def rows4824 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,48,some 48,0,some 0,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,1,some 1,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,2,some 2,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,3,some 3,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,4,some 4,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,5,some 5,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,6,some 6,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,7,some 7,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,8,some 8,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,9,some 9,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,10,some 10,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,11,some 11,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[AxisChoices.test1774]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,12,some 12,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[AxisChoices.test1775]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,13,some 13,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[AxisChoices.test1776]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,14,some 14,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[AxisChoices.test1777]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,15,some 15,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[AxisChoices.test1778]⟩,5,separateWhole⟩]
private theorem paid4824 : StockPairs.checked rows4824 = true := by decide +kernel
theorem route4824 (i : Fin 16) : (rows4824.get i).Done :=
  StockPairs.doneAt paid4824 i

end Research6969.PairReceipts
end Z6969Source3004

-- Source: Research6969.PairReceipts242
section Z6969Source3005
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4840 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,48,some 48,16,some 16,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[AxisChoices.test1779]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,17,some 17,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[AxisChoices.test1780]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,18,some 18,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[AxisChoices.test1781]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,19,some 19,257319,[MeasuredChoices.test61],[AxisChoices.test1782]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,20,some 20,257319,[MeasuredChoices.test61],[AxisChoices.test1783]⟩,5,markedAxisWhole⟩]
private theorem paid4840 : StockPairs.checked rows4840 = true := by decide +kernel
theorem route4840 (i : Fin 5) : (rows4840.get i).Done :=
  StockPairs.doneAt paid4840 i

def cell4845:PairCell.Row:=⟨64,654,12,2,48,some 48,21,some 21,257319,[MeasuredChoices.test61],[AxisChoices.test1784]⟩
theorem check4845:(cell4845.cap (5:Fin 18)).grade<cell4845.lowerGrade-cell4845.off:=by decide +kernel
def cell4846:PairCell.Row:=⟨64,654,12,2,48,some 48,22,some 22,257319,[MeasuredChoices.test61],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4846:(cell4846.cap (5:Fin 18)).grade<cell4846.lowerGrade-cell4846.off:=by decide +kernel
def cell4847:PairCell.Row:=⟨64,654,12,2,48,some 48,23,some 23,257319,[MeasuredChoices.test61],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4847:(cell4847.cap (5:Fin 18)).grade<cell4847.lowerGrade-cell4847.off:=by decide +kernel
def cell4848:PairCell.Row:=⟨64,654,12,2,48,some 48,24,some 24,257319,[MeasuredChoices.test61],[AxisChoices.test1787]⟩
theorem check4848:(cell4848.cap (5:Fin 18)).grade<cell4848.lowerGrade-cell4848.off:=by decide +kernel
def cell4849:PairCell.Row:=⟨64,654,12,2,48,some 48,25,some 25,257319,[MeasuredChoices.test61],[AxisChoices.test1788]⟩
theorem check4849:(cell4849.cap (5:Fin 18)).grade<cell4849.lowerGrade-cell4849.off:=by decide +kernel
def cell4850:PairCell.Row:=⟨64,654,12,2,48,some 48,26,some 26,257319,[MeasuredChoices.test61],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4850:(cell4850.cap (5:Fin 18)).grade<cell4850.lowerGrade-cell4850.off:=by decide +kernel
def cell4851:PairCell.Row:=⟨64,654,12,2,48,some 48,27,some 27,257319,[MeasuredChoices.test61],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4851:(cell4851.cap (5:Fin 18)).grade<cell4851.lowerGrade-cell4851.off:=by decide +kernel
def cell4852:PairCell.Row:=⟨64,654,12,2,48,some 48,28,some 28,257319,[MeasuredChoices.test61],[AxisChoices.test1791]⟩
theorem check4852:(cell4852.cap (5:Fin 18)).grade<cell4852.lowerGrade-cell4852.off:=by decide +kernel
def cell4853:PairCell.Row:=⟨64,654,12,2,48,some 48,29,some 29,257319,[MeasuredChoices.test61],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4853:(cell4853.cap (5:Fin 18)).grade<cell4853.lowerGrade-cell4853.off:=by decide +kernel
def cell4854:PairCell.Row:=⟨64,654,12,2,48,some 48,30,some 30,257319,[MeasuredChoices.test61],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4854:(cell4854.cap (5:Fin 18)).grade<cell4854.lowerGrade-cell4854.off:=by decide +kernel
def cell4855:PairCell.Row:=⟨64,654,12,2,48,some 48,31,some 31,257319,[MeasuredChoices.test61],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4855:(cell4855.cap (5:Fin 18)).grade<cell4855.lowerGrade-cell4855.off:=by decide +kernel
def cell4856:PairCell.Row:=⟨64,654,12,2,48,some 48,32,some 32,257319,[MeasuredChoices.test61],[AxisChoices.test1795]⟩
theorem check4856:(cell4856.cap (5:Fin 18)).grade<cell4856.lowerGrade-cell4856.off:=by decide +kernel
def cell4857:PairCell.Row:=⟨64,654,12,2,48,some 48,33,some 33,257319,[MeasuredChoices.test61],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4857:(cell4857.cap (5:Fin 18)).grade<cell4857.lowerGrade-cell4857.off:=by decide +kernel
def cell4858:PairCell.Row:=⟨64,654,12,2,48,some 48,34,some 34,257319,[MeasuredChoices.test61],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4858:(cell4858.cap (5:Fin 18)).grade<cell4858.lowerGrade-cell4858.off:=by decide +kernel
def cell4859:PairCell.Row:=⟨64,654,12,2,48,some 48,35,some 35,257319,[MeasuredChoices.test61],[AxisChoices.test1798]⟩
theorem check4859:(cell4859.cap (5:Fin 18)).grade<cell4859.lowerGrade-cell4859.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source3005

-- Source: Research6969.HardFit6At070
section Z6969Source3006
set_option autoImplicit true
namespace Research6969.HardFit6At070
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4873 5)
private def leaf1 := (PairReceipts.route4873 6)
private def weight2 := PairRoute.weight 294092 leaf0 leaf1
theorem case70: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,43,some 44⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route4873 4)
theorem case71: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,45,some 46⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4873 0)
private def terminalLeaf7020 := (PairReceipts.route4873 1)
private def terminalLeaf7021 := (PairReceipts.route4873 2)
private def terminalLeaf7022 := (PairReceipts.route4873 3)
private theorem leaf5:PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,47,some 47⟩,0,none,300246,none⟩:=(PairRoute.axes_of_total (PairRoute.axis 17 terminalLeaf7020 (PairRoute.axis 27 terminalLeaf7021 terminalLeaf7022)))
private def weight6 := PairRoute.weight 300246 leaf4 leaf5
theorem case72: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,47,some 47⟩:=PairRoute.start _ weight6
private theorem allAxes104:PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,48,some 48⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 48 ⟨
    (PairReceipts.route4824 0),
    (PairReceipts.route4824 1),
    (PairReceipts.route4824 2),
    (PairReceipts.route4824 3),
    (PairReceipts.route4824 4),
    (PairReceipts.route4824 5),
    (PairReceipts.route4824 6),
    (PairReceipts.route4824 7),
    (PairReceipts.route4824 8),
    (PairReceipts.route4824 9),
    (PairReceipts.route4824 10),
    (PairReceipts.route4824 11),
    (PairReceipts.route4824 12),
    (PairReceipts.route4824 13),
    (PairReceipts.route4824 14),
    (PairReceipts.route4824 15),
    (PairReceipts.route4840 0),
    (PairReceipts.route4840 1),
    (PairReceipts.route4840 2),
    (PairReceipts.route4840 3),
    (PairReceipts.route4840 4),
    PairLeaves.excluded PairReceipts.cell4845 PairReceipts.check4845 (none),
    PairLeaves.excluded PairReceipts.cell4846 PairReceipts.check4846 (none),
    PairLeaves.excluded PairReceipts.cell4847 PairReceipts.check4847 (none),
    PairLeaves.excluded PairReceipts.cell4848 PairReceipts.check4848 (none),
    PairLeaves.excluded PairReceipts.cell4849 PairReceipts.check4849 (none),
    PairLeaves.excluded PairReceipts.cell4850 PairReceipts.check4850 (none),
    PairLeaves.excluded PairReceipts.cell4851 PairReceipts.check4851 (none),
    PairLeaves.excluded PairReceipts.cell4852 PairReceipts.check4852 (none),
    PairLeaves.excluded PairReceipts.cell4853 PairReceipts.check4853 (none),
    PairLeaves.excluded PairReceipts.cell4854 PairReceipts.check4854 (none),
    PairLeaves.excluded PairReceipts.cell4855 PairReceipts.check4855 (none),
    PairLeaves.excluded PairReceipts.cell4856 PairReceipts.check4856 (none),
    PairLeaves.excluded PairReceipts.cell4857 PairReceipts.check4857 (none),
    PairLeaves.excluded PairReceipts.cell4858 PairReceipts.check4858 (none),
    PairLeaves.excluded PairReceipts.cell4859 PairReceipts.check4859 (none),
    PairLeaves.excluded PairReceipts.cell4860 PairReceipts.check4860 (none),
    PairLeaves.excluded PairReceipts.cell4861 PairReceipts.check4861 (none),
    PairLeaves.excluded PairReceipts.cell4862 PairReceipts.check4862 (none),
    PairLeaves.excluded PairReceipts.cell4863 PairReceipts.check4863 (none),
    PairLeaves.excluded PairReceipts.cell4864 PairReceipts.check4864 (none),
    PairLeaves.excluded PairReceipts.cell4865 PairReceipts.check4865 (none),
    PairLeaves.excluded PairReceipts.cell4866 PairReceipts.check4866 (none),
    PairLeaves.excluded PairReceipts.cell4867 PairReceipts.check4867 (none),
    PairLeaves.excluded PairReceipts.cell4868 PairReceipts.check4868 (none),
    PairLeaves.excluded PairReceipts.cell4869 PairReceipts.check4869 (none),
    PairLeaves.excluded PairReceipts.cell4870 PairReceipts.check4870 (none),
    PairLeaves.excluded PairReceipts.cell4871 PairReceipts.check4871 (none),
    PairLeaves.excluded PairReceipts.cell4872 PairReceipts.check4872 (none),
    trivial⟩)
theorem case73: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,48,some 48⟩:=PairRoute.start _ allAxes104
private theorem allAxes204:PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,49,some 49⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 49 ⟨
    (PairReceipts.route4774 0),
    (PairReceipts.route4774 1),
    (PairReceipts.route4774 2),
    (PairReceipts.route4774 3),
    (PairReceipts.route4774 4),
    (PairReceipts.route4774 5),
    (PairReceipts.route4780 0),
    (PairReceipts.route4780 1),
    (PairReceipts.route4780 2),
    (PairReceipts.route4780 3),
    (PairReceipts.route4780 4),
    (PairReceipts.route4780 5),
    (PairReceipts.route4780 6),
    (PairReceipts.route4780 7),
    (PairReceipts.route4780 8),
    (PairReceipts.route4780 9),
    (PairReceipts.route4780 10),
    (PairReceipts.route4780 11),
    (PairReceipts.route4780 12),
    (PairReceipts.route4780 13),
    (PairReceipts.route4780 14),
    PairLeaves.excluded PairReceipts.cell4795 PairReceipts.check4795 (none),
    PairLeaves.excluded PairReceipts.cell4796 PairReceipts.check4796 (none),
    PairLeaves.excluded PairReceipts.cell4797 PairReceipts.check4797 (none),
    PairLeaves.excluded PairReceipts.cell4798 PairReceipts.check4798 (none),
    PairLeaves.excluded PairReceipts.cell4799 PairReceipts.check4799 (none),
    PairLeaves.excluded PairReceipts.cell4800 PairReceipts.check4800 (none),
    PairLeaves.excluded PairReceipts.cell4801 PairReceipts.check4801 (none),
    PairLeaves.excluded PairReceipts.cell4802 PairReceipts.check4802 (none),
    PairLeaves.excluded PairReceipts.cell4803 PairReceipts.check4803 (none),
    PairLeaves.excluded PairReceipts.cell4804 PairReceipts.check4804 (none),
    PairLeaves.excluded PairReceipts.cell4805 PairReceipts.check4805 (none),
    PairLeaves.excluded PairReceipts.cell4806 PairReceipts.check4806 (none),
    PairLeaves.excluded PairReceipts.cell4807 PairReceipts.check4807 (none),
    PairLeaves.excluded PairReceipts.cell4808 PairReceipts.check4808 (none),
    PairLeaves.excluded PairReceipts.cell4809 PairReceipts.check4809 (none),
    PairLeaves.excluded PairReceipts.cell4810 PairReceipts.check4810 (none),
    PairLeaves.excluded PairReceipts.cell4811 PairReceipts.check4811 (none),
    PairLeaves.excluded PairReceipts.cell4812 PairReceipts.check4812 (none),
    PairLeaves.excluded PairReceipts.cell4813 PairReceipts.check4813 (none),
    PairLeaves.excluded PairReceipts.cell4814 PairReceipts.check4814 (none),
    PairLeaves.excluded PairReceipts.cell4815 PairReceipts.check4815 (none),
    PairLeaves.excluded PairReceipts.cell4816 PairReceipts.check4816 (none),
    PairLeaves.excluded PairReceipts.cell4817 PairReceipts.check4817 (none),
    PairLeaves.excluded PairReceipts.cell4818 PairReceipts.check4818 (none),
    PairLeaves.excluded PairReceipts.cell4819 PairReceipts.check4819 (none),
    PairLeaves.excluded PairReceipts.cell4820 PairReceipts.check4820 (none),
    PairLeaves.excluded PairReceipts.cell4821 PairReceipts.check4821 (none),
    PairLeaves.excluded PairReceipts.cell4822 PairReceipts.check4822 (none),
    PairLeaves.excluded PairReceipts.cell4823 PairReceipts.check4823 (none),
    trivial⟩)
theorem case74: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,49,some 49⟩:=PairRoute.start _ allAxes204
private theorem allAxes306:PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,50,some 50⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 50 ⟨
    (PairReceipts.route4723 0),
    (PairReceipts.route4723 1),
    (PairReceipts.route4723 2),
    (PairReceipts.route4723 3),
    (PairReceipts.route4723 4),
    (PairReceipts.route4723 5),
    (PairReceipts.route4723 6),
    (PairReceipts.route4723 7),
    (PairReceipts.route4723 8),
    (PairReceipts.route4723 9),
    (PairReceipts.route4723 10),
    (PairReceipts.route4723 11),
    (PairReceipts.route4723 12),
    (PairReceipts.route4723 13),
    (PairReceipts.route4723 14),
    (PairReceipts.route4723 15),
    (PairReceipts.route4723 16),
    (PairReceipts.route4740 0),
    (PairReceipts.route4740 1),
    (PairReceipts.route4740 2),
    (PairReceipts.route4740 3),
    PairLeaves.excluded PairReceipts.cell4744 PairReceipts.check4744 (none),
    PairLeaves.excluded PairReceipts.cell4745 PairReceipts.check4745 (none),
    PairLeaves.excluded PairReceipts.cell4746 PairReceipts.check4746 (none),
    PairLeaves.excluded PairReceipts.cell4747 PairReceipts.check4747 (none),
    PairLeaves.excluded PairReceipts.cell4748 PairReceipts.check4748 (none),
    PairLeaves.excluded PairReceipts.cell4749 PairReceipts.check4749 (none),
    PairLeaves.excluded PairReceipts.cell4750 PairReceipts.check4750 (none),
    PairLeaves.excluded PairReceipts.cell4751 PairReceipts.check4751 (none),
    PairLeaves.excluded PairReceipts.cell4752 PairReceipts.check4752 (none),
    PairLeaves.excluded PairReceipts.cell4753 PairReceipts.check4753 (none),
    PairLeaves.excluded PairReceipts.cell4754 PairReceipts.check4754 (none),
    PairLeaves.excluded PairReceipts.cell4755 PairReceipts.check4755 (none),
    PairLeaves.excluded PairReceipts.cell4756 PairReceipts.check4756 (none),
    PairLeaves.excluded PairReceipts.cell4757 PairReceipts.check4757 (none),
    PairLeaves.excluded PairReceipts.cell4758 PairReceipts.check4758 (none),
    PairLeaves.excluded PairReceipts.cell4759 PairReceipts.check4759 (none),
    PairLeaves.excluded PairReceipts.cell4760 PairReceipts.check4760 (none),
    PairLeaves.excluded PairReceipts.cell4761 PairReceipts.check4761 (none),
    PairLeaves.excluded PairReceipts.cell4762 PairReceipts.check4762 (none),
    PairLeaves.excluded PairReceipts.cell4763 PairReceipts.check4763 (none),
    PairLeaves.excluded PairReceipts.cell4764 PairReceipts.check4764 (none),
    PairLeaves.excluded PairReceipts.cell4765 PairReceipts.check4765 (none),
    PairLeaves.excluded PairReceipts.cell4766 PairReceipts.check4766 (none),
    PairLeaves.excluded PairReceipts.cell4767 PairReceipts.check4767 (none),
    PairLeaves.excluded PairReceipts.cell4768 PairReceipts.check4768 (none),
    PairLeaves.excluded PairReceipts.cell4769 PairReceipts.check4769 (none),
    PairLeaves.excluded PairReceipts.cell4770 PairReceipts.check4770 (none),
    PairLeaves.excluded PairReceipts.cell4771 PairReceipts.check4771 (none),
    PairLeaves.excluded PairReceipts.cell4772 PairReceipts.check4772 (none),
    PairLeaves.excluded PairReceipts.cell4773 PairReceipts.check4773 (none),
    trivial⟩)
theorem case75: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,50,some 50⟩:=PairRoute.start _ allAxes306
private theorem allAxes410:PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,51,some 51⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 51 ⟨
    (PairReceipts.route4660 10),
    (PairReceipts.route4660 11),
    (PairReceipts.route4660 12),
    (PairReceipts.route4660 13),
    (PairReceipts.route4660 14),
    (PairReceipts.route4660 15),
    (PairReceipts.route4660 16),
    (PairReceipts.route4660 17),
    (PairReceipts.route4660 18),
    (PairReceipts.route4680 0),
    (PairReceipts.route4680 1),
    (PairReceipts.route4680 2),
    (PairReceipts.route4680 3),
    (PairReceipts.route4680 4),
    (PairReceipts.route4680 5),
    (PairReceipts.route4680 6),
    (PairReceipts.route4680 7),
    (PairReceipts.route4680 8),
    (PairReceipts.route4680 9),
    (PairReceipts.route4680 10),
    (PairReceipts.route4680 11),
    PairLeaves.excluded PairReceipts.cell4692 PairReceipts.check4692 (none),
    PairLeaves.excluded PairReceipts.cell4693 PairReceipts.check4693 (none),
    PairLeaves.excluded PairReceipts.cell4694 PairReceipts.check4694 (none),
    PairLeaves.excluded PairReceipts.cell4695 PairReceipts.check4695 (none),
    PairLeaves.excluded PairReceipts.cell4696 PairReceipts.check4696 (none),
    PairLeaves.excluded PairReceipts.cell4697 PairReceipts.check4697 (none),
    PairLeaves.excluded PairReceipts.cell4698 PairReceipts.check4698 (none),
    PairLeaves.excluded PairReceipts.cell4699 PairReceipts.check4699 (none),
    PairLeaves.excluded PairReceipts.cell4700 PairReceipts.check4700 (none),
    PairLeaves.excluded PairReceipts.cell4701 PairReceipts.check4701 (none),
    PairLeaves.excluded PairReceipts.cell4702 PairReceipts.check4702 (none),
    PairLeaves.excluded PairReceipts.cell4703 PairReceipts.check4703 (none),
    PairLeaves.excluded PairReceipts.cell4704 PairReceipts.check4704 (none),
    PairLeaves.excluded PairReceipts.cell4705 PairReceipts.check4705 (none),
    PairLeaves.excluded PairReceipts.cell4706 PairReceipts.check4706 (none),
    PairLeaves.excluded PairReceipts.cell4707 PairReceipts.check4707 (none),
    PairLeaves.excluded PairReceipts.cell4708 PairReceipts.check4708 (none),
    PairLeaves.excluded PairReceipts.cell4709 PairReceipts.check4709 (none),
    PairLeaves.excluded PairReceipts.cell4710 PairReceipts.check4710 (none),
    PairLeaves.excluded PairReceipts.cell4711 PairReceipts.check4711 (none),
    PairLeaves.excluded PairReceipts.cell4712 PairReceipts.check4712 (none),
    PairLeaves.excluded PairReceipts.cell4713 PairReceipts.check4713 (none),
    PairLeaves.excluded PairReceipts.cell4714 PairReceipts.check4714 (none),
    PairLeaves.excluded PairReceipts.cell4715 PairReceipts.check4715 (none),
    PairLeaves.excluded PairReceipts.cell4716 PairReceipts.check4716 (none),
    PairLeaves.excluded PairReceipts.cell4717 PairReceipts.check4717 (none),
    PairLeaves.excluded PairReceipts.cell4718 PairReceipts.check4718 (none),
    PairLeaves.excluded PairReceipts.cell4719 PairReceipts.check4719 (none),
    PairLeaves.excluded PairReceipts.cell4720 PairReceipts.check4720 (none),
    PairLeaves.excluded PairReceipts.cell4721 PairReceipts.check4721 (none),
    PairLeaves.excluded PairReceipts.cell4722 PairReceipts.check4722 (none),
    trivial⟩)
theorem case76: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,51,some 51⟩:=PairRoute.start _ allAxes410
private def leaf411 := (PairReceipts.route4660 9)
private theorem leaf412:PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,52,some 52⟩,0,none,288407,none⟩:=PairLeaves.excluded PairReceipts.cell4670 PairReceipts.check4670 (none)
private def weight413 := PairRoute.weight 288407 leaf411 leaf412
theorem case77: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,52,some 52⟩:=PairRoute.start _ weight413
end Research6969.HardFit6At070
end Z6969Source3006

-- Source: Research6969.HardComplete6
section Z6969Source3007
set_option autoImplicit true
namespace Research6969.HardComplete6
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_4 (j:Fin HighPendingSeed6.regions.size) (l:0≤j.val) (h:j.val<4):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At000.case0
  · exact HardFit6At000.case1
  · exact HardFit6At000.case2
  · exact HardFit6At000.case3
private theorem covered4_9 (j:Fin HighPendingSeed6.regions.size) (l:4≤j.val) (h:j.val<9):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At000.case4
  · exact HardFit6At000.case5
  · exact HardFit6At000.case6
  · exact HardFit6At000.case7
  · exact HardFit6At000.case8
private theorem covered0_9 (j:Fin HighPendingSeed6.regions.size) (l:0≤j.val) (h:j.val<9):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<4
  · exact covered0_4 j l low
  · exact covered4_9 j (by omega) h
private theorem covered9_14 (j:Fin HighPendingSeed6.regions.size) (l:9≤j.val) (h:j.val<14):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At000.case9
  · exact HardFit6At010.case10
  · exact HardFit6At010.case11
  · exact HardFit6At010.case12
  · exact HardFit6At010.case13
private theorem covered14_19 (j:Fin HighPendingSeed6.regions.size) (l:14≤j.val) (h:j.val<19):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At010.case14
  · exact HardFit6At010.case15
  · exact HardFit6At010.case16
  · exact HardFit6At010.case17
  · exact HardFit6At010.case18
private theorem covered9_19 (j:Fin HighPendingSeed6.regions.size) (l:9≤j.val) (h:j.val<19):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<14
  · exact covered9_14 j l low
  · exact covered14_19 j (by omega) h
private theorem covered0_19 (j:Fin HighPendingSeed6.regions.size) (l:0≤j.val) (h:j.val<19):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<9
  · exact covered0_9 j l low
  · exact covered9_19 j (by omega) h
private theorem covered19_24 (j:Fin HighPendingSeed6.regions.size) (l:19≤j.val) (h:j.val<24):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At010.case19
  · exact HardFit6At020.case20
  · exact HardFit6At020.case21
  · exact HardFit6At020.case22
  · exact HardFit6At020.case23
private theorem covered24_29 (j:Fin HighPendingSeed6.regions.size) (l:24≤j.val) (h:j.val<29):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At020.case24
  · exact HardFit6At020.case25
  · exact HardFit6At020.case26
  · exact HardFit6At020.case27
  · exact HardFit6At020.case28
private theorem covered19_29 (j:Fin HighPendingSeed6.regions.size) (l:19≤j.val) (h:j.val<29):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<24
  · exact covered19_24 j l low
  · exact covered24_29 j (by omega) h
private theorem covered29_34 (j:Fin HighPendingSeed6.regions.size) (l:29≤j.val) (h:j.val<34):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At020.case29
  · exact HardFit6At030.case30
  · exact HardFit6At030.case31
  · exact HardFit6At030.case32
  · exact HardFit6At030.case33
private theorem covered34_39 (j:Fin HighPendingSeed6.regions.size) (l:34≤j.val) (h:j.val<39):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At030.case34
  · exact HardFit6At030.case35
  · exact HardFit6At030.case36
  · exact HardFit6At030.case37
  · exact HardFit6At030.case38
private theorem covered29_39 (j:Fin HighPendingSeed6.regions.size) (l:29≤j.val) (h:j.val<39):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<34
  · exact covered29_34 j l low
  · exact covered34_39 j (by omega) h
private theorem covered19_39 (j:Fin HighPendingSeed6.regions.size) (l:19≤j.val) (h:j.val<39):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<29
  · exact covered19_29 j l low
  · exact covered29_39 j (by omega) h
private theorem covered0_39 (j:Fin HighPendingSeed6.regions.size) (l:0≤j.val) (h:j.val<39):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<19
  · exact covered0_19 j l low
  · exact covered19_39 j (by omega) h
private theorem covered39_43 (j:Fin HighPendingSeed6.regions.size) (l:39≤j.val) (h:j.val<43):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At030.case39
  · exact HardFit6At040.case40
  · exact HardFit6At040.case41
  · exact HardFit6At040.case42
private theorem covered43_48 (j:Fin HighPendingSeed6.regions.size) (l:43≤j.val) (h:j.val<48):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At040.case43
  · exact HardFit6At040.case44
  · exact HardFit6At040.case45
  · exact HardFit6At040.case46
  · exact HardFit6At040.case47
private theorem covered39_48 (j:Fin HighPendingSeed6.regions.size) (l:39≤j.val) (h:j.val<48):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<43
  · exact covered39_43 j l low
  · exact covered43_48 j (by omega) h
private theorem covered48_53 (j:Fin HighPendingSeed6.regions.size) (l:48≤j.val) (h:j.val<53):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At040.case48
  · exact HardFit6At040.case49
  · exact HardFit6At050.case50
  · exact HardFit6At050.case51
  · exact HardFit6At050.case52
private theorem covered53_58 (j:Fin HighPendingSeed6.regions.size) (l:53≤j.val) (h:j.val<58):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At050.case53
  · exact HardFit6At050.case54
  · exact HardFit6At050.case55
  · exact HardFit6At050.case56
  · exact HardFit6At050.case57
private theorem covered48_58 (j:Fin HighPendingSeed6.regions.size) (l:48≤j.val) (h:j.val<58):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<53
  · exact covered48_53 j l low
  · exact covered53_58 j (by omega) h
private theorem covered39_58 (j:Fin HighPendingSeed6.regions.size) (l:39≤j.val) (h:j.val<58):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<48
  · exact covered39_48 j l low
  · exact covered48_58 j (by omega) h
private theorem covered58_63 (j:Fin HighPendingSeed6.regions.size) (l:58≤j.val) (h:j.val<63):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At050.case58
  · exact HardFit6At050.case59
  · exact HardFit6At060.case60
  · exact HardFit6At060.case61
  · exact HardFit6At060.case62
private theorem covered63_68 (j:Fin HighPendingSeed6.regions.size) (l:63≤j.val) (h:j.val<68):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At060.case63
  · exact HardFit6At060.case64
  · exact HardFit6At060.case65
  · exact HardFit6At060.case66
  · exact HardFit6At060.case67
private theorem covered58_68 (j:Fin HighPendingSeed6.regions.size) (l:58≤j.val) (h:j.val<68):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<63
  · exact covered58_63 j l low
  · exact covered63_68 j (by omega) h
private theorem covered68_73 (j:Fin HighPendingSeed6.regions.size) (l:68≤j.val) (h:j.val<73):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At060.case68
  · exact HardFit6At060.case69
  · exact HardFit6At070.case70
  · exact HardFit6At070.case71
  · exact HardFit6At070.case72
private theorem covered73_78 (j:Fin HighPendingSeed6.regions.size) (l:73≤j.val) (h:j.val<78):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit6At070.case73
  · exact HardFit6At070.case74
  · exact HardFit6At070.case75
  · exact HardFit6At070.case76
  · exact HardFit6At070.case77
private theorem covered68_78 (j:Fin HighPendingSeed6.regions.size) (l:68≤j.val) (h:j.val<78):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<73
  · exact covered68_73 j l low
  · exact covered73_78 j (by omega) h
private theorem covered58_78 (j:Fin HighPendingSeed6.regions.size) (l:58≤j.val) (h:j.val<78):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<68
  · exact covered58_68 j l low
  · exact covered68_78 j (by omega) h
private theorem covered39_78 (j:Fin HighPendingSeed6.regions.size) (l:39≤j.val) (h:j.val<78):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<58
  · exact covered39_58 j l low
  · exact covered58_78 j (by omega) h
private theorem covered0_78 (j:Fin HighPendingSeed6.regions.size) (l:0≤j.val) (h:j.val<78):Done (5:Fin 18) (HighPendingSeed6.atIndex j):=by
  by_cases low:j.val<39
  · exact covered0_39 j l low
  · exact covered39_78 j (by omega) h
theorem required:HighPendingSeed6.Required:=fun j=>covered0_78 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete6
end Z6969Source3007

-- Source: Research6969.PairReceipts245
section Z6969Source3008
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4900 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,6,surfaceIntersection⟩]
private theorem paid4900 : StockPairs.checked rows4900 = true := by decide +kernel
theorem route4900 (i : Fin 20) : (rows4900.get i).Done :=
  StockPairs.doneAt paid4900 i

end Research6969.PairReceipts
end Z6969Source3008

-- Source: Research6969.HardFit7At000
section Z6969Source3009
set_option autoImplicit true
namespace Research6969.HardFit7At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4900 2)
theorem case0: NormalRoute.Done (6:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4900 1)
theorem case1: NormalRoute.Done (6:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4900 0)
theorem case2: NormalRoute.Done (6:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4880 19)
theorem case3: NormalRoute.Done (6:Fin 18) ⟨25,27,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4880 18)
theorem case4: NormalRoute.Done (6:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4900 4)
theorem case5: NormalRoute.Done (6:Fin 18) ⟨25,27,9,3,13,some 16⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4900 3)
theorem case6: NormalRoute.Done (6:Fin 18) ⟨25,27,9,3,17,some 20⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4900 9)
theorem case7: NormalRoute.Done (6:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4900 8)
theorem case8: NormalRoute.Done (6:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4900 7)
theorem case9: NormalRoute.Done (6:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit7At000
end Z6969Source3009

-- Source: Research6969.HardFit7At010
section Z6969Source3010
set_option autoImplicit true
namespace Research6969.HardFit7At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4900 6)
theorem case10: NormalRoute.Done (6:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4900 5)
theorem case11: NormalRoute.Done (6:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4900 13)
theorem case12: NormalRoute.Done (6:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4900 12)
theorem case13: NormalRoute.Done (6:Fin 18) ⟨28,32,9,3,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4900 11)
theorem case14: NormalRoute.Done (6:Fin 18) ⟨28,32,9,3,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4900 10)
theorem case15: NormalRoute.Done (6:Fin 18) ⟨28,32,9,3,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4900 18)
theorem case16: NormalRoute.Done (6:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4900 17)
theorem case17: NormalRoute.Done (6:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4900 16)
theorem case18: NormalRoute.Done (6:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4900 15)
theorem case19: NormalRoute.Done (6:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf9
end Research6969.HardFit7At010
end Z6969Source3010

-- Source: Research6969.PairReceipts246
section Z6969Source3011
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4920 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,6,⟨(.node 16064838841308028),.intersection,.impossible,293263⟩⟩,
  ⟨⟨41,49,9,2,49,some 64,0,none,293263,[MeasuredChoices.test126],[]⟩,6,markedIntersection⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,57,some 60,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,49,some 52,0,none,257319,[MeasuredChoices.test63],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,53,some 56,0,none,257319,[MeasuredChoices.test69],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,surfaceIntersection⟩]
private theorem paid4920 : StockPairs.checked rows4920 = true := by decide +kernel
theorem route4920 (i : Fin 21) : (rows4920.get i).Done :=
  StockPairs.doneAt paid4920 i

end Research6969.PairReceipts
end Z6969Source3011

-- Source: Research6969.HardFit7At020
section Z6969Source3012
set_option autoImplicit true
namespace Research6969.HardFit7At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4900 14)
theorem case20: NormalRoute.Done (6:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4920 2)
theorem case21: NormalRoute.Done (6:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4920 1)
theorem case22: NormalRoute.Done (6:Fin 18) ⟨33,40,9,3,13,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4920 0)
theorem case23: NormalRoute.Done (6:Fin 18) ⟨33,40,9,3,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4900 19)
theorem case24: NormalRoute.Done (6:Fin 18) ⟨33,40,9,3,21,some 24⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4920 9)
theorem case25: NormalRoute.Done (6:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4920 8)
theorem case26: NormalRoute.Done (6:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4920 7)
theorem case27: NormalRoute.Done (6:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4920 6)
theorem case28: NormalRoute.Done (6:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4920 5)
theorem case29: NormalRoute.Done (6:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ leaf9
end Research6969.HardFit7At020
end Z6969Source3012

-- Source: Research6969.PairReceipts247
section Z6969Source3013
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4940 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,6,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,706,12,2,51,some 51,0,some 0,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,1,some 1,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,2,some 2,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,3,some 3,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,4,some 4,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,5,some 5,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,6,some 6,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩]
private theorem paid4940 : StockPairs.checked rows4940 = true := by decide +kernel
theorem route4940 (i : Fin 19) : (rows4940.get i).Done :=
  StockPairs.doneAt paid4940 i

def cell4952:PairCell.Row:=⟨64,706,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩
theorem check4952:(cell4952.cap (6:Fin 18)).grade<cell4952.lowerGrade-cell4952.off:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source3013

-- Source: Research6969.HardFit7At030
section Z6969Source3014
set_option autoImplicit true
namespace Research6969.HardFit7At030
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4920 3)
private def leaf1 := (PairReceipts.route4920 4)
private def weight2 := PairRoute.weight 293263 leaf0 leaf1
theorem case30: NormalRoute.Done (6:Fin 18) ⟨41,49,9,2,49,some 64⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route4920 15)
theorem case31: NormalRoute.Done (6:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4920 14)
theorem case32: NormalRoute.Done (6:Fin 18) ⟨41,49,9,3,13,some 16⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4920 13)
theorem case33: NormalRoute.Done (6:Fin 18) ⟨41,49,9,3,17,some 20⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4920 12)
theorem case34: NormalRoute.Done (6:Fin 18) ⟨41,49,9,3,21,some 24⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4920 11)
theorem case35: NormalRoute.Done (6:Fin 18) ⟨41,49,9,3,33,some 40⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4920 10)
theorem case36: NormalRoute.Done (6:Fin 18) ⟨41,49,9,3,41,some 48⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4940 3)
theorem case37: NormalRoute.Done (6:Fin 18) ⟨50,63,10,2,9,some 12⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route4940 2)
theorem case38: NormalRoute.Done (6:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route4940 1)
theorem case39: NormalRoute.Done (6:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf11
end Research6969.HardFit7At030
end Z6969Source3014

-- Source: Research6969.HardFit7At040
section Z6969Source3015
set_option autoImplicit true
namespace Research6969.HardFit7At040
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4940 0)
theorem case40: NormalRoute.Done (6:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4920 20)
theorem case41: NormalRoute.Done (6:Fin 18) ⟨50,63,10,2,25,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4920 19)
theorem case42: NormalRoute.Done (6:Fin 18) ⟨50,63,10,2,41,some 48⟩:=PairRoute.start _ leaf2
private def terminalLeaf7070 := (PairReceipts.route4920 17)
private def terminalLeaf7071 := (PairReceipts.route4920 18)
private def leaf3 := PairRoute.splitSeed 52 terminalLeaf7070 terminalLeaf7071
theorem case43: NormalRoute.Done (6:Fin 18) ⟨50,63,10,2,49,some 56⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4920 16)
theorem case44: NormalRoute.Done (6:Fin 18) ⟨50,63,10,2,57,some 60⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4940 10)
theorem case45: NormalRoute.Done (6:Fin 18) ⟨50,63,10,3,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4940 9)
theorem case46: NormalRoute.Done (6:Fin 18) ⟨50,63,10,3,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4940 8)
theorem case47: NormalRoute.Done (6:Fin 18) ⟨50,63,10,3,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4940 7)
theorem case48: NormalRoute.Done (6:Fin 18) ⟨50,63,10,3,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4940 6)
theorem case49: NormalRoute.Done (6:Fin 18) ⟨50,63,10,3,25,some 28⟩:=PairRoute.start _ leaf9
end Research6969.HardFit7At040
end Z6969Source3015

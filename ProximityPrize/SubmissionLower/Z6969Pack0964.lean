import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0672
import ProximityPrize.SubmissionLower.Z6969Pack0963
import ProximityPrize.SubmissionLower.Z6969Pack0939

set_option Elab.async false

-- Source: Research6969.PairReceipts179
section Z6969Source2908
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3580:PairCell.Row:=⟨41,49,9,2,49,some 64,62,some 62,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check3580:(cell3580.cap (3:Fin 18)).grade<cell3580.lowerGrade-cell3580.off:=by decide +kernel
def cell3581:PairCell.Row:=⟨41,49,9,2,49,some 64,63,some 63,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check3581:(cell3581.cap (3:Fin 18)).grade<cell3581.lowerGrade-cell3581.off:=by decide +kernel
def cell3582:PairCell.Row:=⟨41,49,9,2,49,some 64,64,some 64,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check3582:(cell3582.cap (3:Fin 18)).grade<cell3582.lowerGrade-cell3582.off:=by decide +kernel
private def rows3583 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,4,some 8,0,none,257319,[],[]⟩,3,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨41,49,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩,3,markedIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,0,none,385979,[MeasuredChoices.test1139],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,0,none,385979,[MeasuredChoices.test1133],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,37,some 40,0,none,385979,[MeasuredChoices.test1079],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,3,surfaceIntersection⟩]
private theorem paid3583 : StockPairs.checked rows3583 = true := by decide +kernel
theorem route3583 (i : Fin 17) : (rows3583.get i).Done :=
  StockPairs.doneAt paid3583 i

end Research6969.PairReceipts
end Z6969Source2908

-- Source: Research6969.HardFit4At050
section Z6969Source2909
set_option autoImplicit true
namespace Research6969.HardFit4At050
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3500 13)
theorem case50: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,21,some 22⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3500 12)
theorem case51: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,23,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3500 11)
theorem case52: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,25,some 28⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route3500 10)
theorem case53: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,29,some 32⟩:=PairRoute.start _ leaf3
private def terminalLeaf7000 := (PairReceipts.route3500 8)
private def terminalLeaf7001 := (PairReceipts.route3500 9)
private def leaf4 := PairRoute.splitSeed 39 terminalLeaf7000 terminalLeaf7001
theorem case54: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,33,some 40⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route3583 9)
theorem case55: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,4,some 8⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route3583 8)
theorem case56: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route3583 7)
theorem case57: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route3583 6)
theorem case58: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route3583 5)
theorem case59: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf9
end Research6969.HardFit4At050
end Z6969Source2909

-- Source: Research6969.PairReceipts176
section Z6969Source2910
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3520 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,2,some 2,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,3,some 3,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,4,some 4,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,5,some 5,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,6,some 6,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,7,some 7,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,8,some 8,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,9,some 9,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,10,some 10,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,11,some 11,257319,[MeasuredChoices.test62],[AxisChoices.test1774]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,12,some 12,257319,[MeasuredChoices.test62],[AxisChoices.test1775]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,13,some 13,257319,[MeasuredChoices.test62],[AxisChoices.test1776]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,14,some 14,257319,[MeasuredChoices.test62],[AxisChoices.test1777]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,15,some 15,257319,[MeasuredChoices.test62],[AxisChoices.test1778]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,16,some 16,257319,[MeasuredChoices.test62],[AxisChoices.test1779]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,17,some 17,257319,[MeasuredChoices.test62],[AxisChoices.test1780]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,18,some 18,257319,[MeasuredChoices.test62],[AxisChoices.test1781]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,19,some 19,257319,[MeasuredChoices.test62],[AxisChoices.test1782]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,20,some 20,257319,[MeasuredChoices.test62],[AxisChoices.test1783]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,21,some 21,257319,[MeasuredChoices.test62],[AxisChoices.test1784]⟩,3,markedAxisIntersection⟩]
private theorem paid3520 : StockPairs.checked rows3520 = true := by decide +kernel
theorem route3520 (i : Fin 20) : (rows3520.get i).Done :=
  StockPairs.doneAt paid3520 i

end Research6969.PairReceipts
end Z6969Source2910

-- Source: Research6969.PairReceipts177
section Z6969Source2911
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3540 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,22,some 22,257319,[MeasuredChoices.test62],[AxisChoices.test1785]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,23,some 23,257319,[MeasuredChoices.test62],[AxisChoices.test1786]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,24,some 24,257319,[MeasuredChoices.test62],[AxisChoices.test1787]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,25,some 25,257319,[MeasuredChoices.test62],[AxisChoices.test1788]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,26,some 26,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1789]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,27,some 27,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1790]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,28,some 28,257319,[MeasuredChoices.test62],[AxisChoices.test1791]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,29,some 29,257319,[MeasuredChoices.test62],[AxisChoices.test1791,AxisChoices.test1792]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,30,some 30,257319,[MeasuredChoices.test62],[AxisChoices.test1792,AxisChoices.test1793]⟩,3,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,31,some 31,257319,[MeasuredChoices.test62],[AxisChoices.test1793,AxisChoices.test1794]⟩,3,markedAxisIntersection⟩]
private theorem paid3540 : StockPairs.checked rows3540 = true := by decide +kernel
theorem route3540 (i : Fin 10) : (rows3540.get i).Done :=
  StockPairs.doneAt paid3540 i

def cell3550:PairCell.Row:=⟨41,49,9,2,49,some 64,32,some 32,257319,[MeasuredChoices.test62],[AxisChoices.test1795]⟩
theorem check3550:(cell3550.cap (3:Fin 18)).grade<cell3550.lowerGrade-cell3550.off:=by decide +kernel
def cell3551:PairCell.Row:=⟨41,49,9,2,49,some 64,33,some 33,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check3551:(cell3551.cap (3:Fin 18)).grade<cell3551.lowerGrade-cell3551.off:=by decide +kernel
def cell3552:PairCell.Row:=⟨41,49,9,2,49,some 64,34,some 34,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check3552:(cell3552.cap (3:Fin 18)).grade<cell3552.lowerGrade-cell3552.off:=by decide +kernel
def cell3553:PairCell.Row:=⟨41,49,9,2,49,some 64,35,some 35,257319,[MeasuredChoices.test62],[AxisChoices.test1798]⟩
theorem check3553:(cell3553.cap (3:Fin 18)).grade<cell3553.lowerGrade-cell3553.off:=by decide +kernel
def cell3554:PairCell.Row:=⟨41,49,9,2,49,some 64,36,some 36,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check3554:(cell3554.cap (3:Fin 18)).grade<cell3554.lowerGrade-cell3554.off:=by decide +kernel
def cell3555:PairCell.Row:=⟨41,49,9,2,49,some 64,37,some 37,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check3555:(cell3555.cap (3:Fin 18)).grade<cell3555.lowerGrade-cell3555.off:=by decide +kernel
def cell3556:PairCell.Row:=⟨41,49,9,2,49,some 64,38,some 38,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check3556:(cell3556.cap (3:Fin 18)).grade<cell3556.lowerGrade-cell3556.off:=by decide +kernel
def cell3557:PairCell.Row:=⟨41,49,9,2,49,some 64,39,some 39,257319,[MeasuredChoices.test62],[AxisChoices.test1802]⟩
theorem check3557:(cell3557.cap (3:Fin 18)).grade<cell3557.lowerGrade-cell3557.off:=by decide +kernel
def cell3558:PairCell.Row:=⟨41,49,9,2,49,some 64,40,some 40,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check3558:(cell3558.cap (3:Fin 18)).grade<cell3558.lowerGrade-cell3558.off:=by decide +kernel
def cell3559:PairCell.Row:=⟨41,49,9,2,49,some 64,41,some 41,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check3559:(cell3559.cap (3:Fin 18)).grade<cell3559.lowerGrade-cell3559.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2911

-- Source: Research6969.PairReceipts178
section Z6969Source2912
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3560:PairCell.Row:=⟨41,49,9,2,49,some 64,42,some 42,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check3560:(cell3560.cap (3:Fin 18)).grade<cell3560.lowerGrade-cell3560.off:=by decide +kernel
def cell3561:PairCell.Row:=⟨41,49,9,2,49,some 64,43,some 43,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check3561:(cell3561.cap (3:Fin 18)).grade<cell3561.lowerGrade-cell3561.off:=by decide +kernel
def cell3562:PairCell.Row:=⟨41,49,9,2,49,some 64,44,some 44,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check3562:(cell3562.cap (3:Fin 18)).grade<cell3562.lowerGrade-cell3562.off:=by decide +kernel
def cell3563:PairCell.Row:=⟨41,49,9,2,49,some 64,45,some 45,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check3563:(cell3563.cap (3:Fin 18)).grade<cell3563.lowerGrade-cell3563.off:=by decide +kernel
def cell3564:PairCell.Row:=⟨41,49,9,2,49,some 64,46,some 46,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check3564:(cell3564.cap (3:Fin 18)).grade<cell3564.lowerGrade-cell3564.off:=by decide +kernel
def cell3565:PairCell.Row:=⟨41,49,9,2,49,some 64,47,some 47,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check3565:(cell3565.cap (3:Fin 18)).grade<cell3565.lowerGrade-cell3565.off:=by decide +kernel
def cell3566:PairCell.Row:=⟨41,49,9,2,49,some 64,48,some 48,257319,[MeasuredChoices.test62],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check3566:(cell3566.cap (3:Fin 18)).grade<cell3566.lowerGrade-cell3566.off:=by decide +kernel
def cell3567:PairCell.Row:=⟨41,49,9,2,49,some 64,49,some 49,257319,[MeasuredChoices.test62],[AxisChoices.test1812]⟩
theorem check3567:(cell3567.cap (3:Fin 18)).grade<cell3567.lowerGrade-cell3567.off:=by decide +kernel
def cell3568:PairCell.Row:=⟨41,49,9,2,49,some 64,50,some 50,257319,[MeasuredChoices.test62],[AxisChoices.test1813]⟩
theorem check3568:(cell3568.cap (3:Fin 18)).grade<cell3568.lowerGrade-cell3568.off:=by decide +kernel
def cell3569:PairCell.Row:=⟨41,49,9,2,49,some 64,51,some 51,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3569:(cell3569.cap (3:Fin 18)).grade<cell3569.lowerGrade-cell3569.off:=by decide +kernel
def cell3570:PairCell.Row:=⟨41,49,9,2,49,some 64,52,some 52,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3570:(cell3570.cap (3:Fin 18)).grade<cell3570.lowerGrade-cell3570.off:=by decide +kernel
def cell3571:PairCell.Row:=⟨41,49,9,2,49,some 64,53,some 53,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check3571:(cell3571.cap (3:Fin 18)).grade<cell3571.lowerGrade-cell3571.off:=by decide +kernel
def cell3572:PairCell.Row:=⟨41,49,9,2,49,some 64,54,some 54,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check3572:(cell3572.cap (3:Fin 18)).grade<cell3572.lowerGrade-cell3572.off:=by decide +kernel
def cell3573:PairCell.Row:=⟨41,49,9,2,49,some 64,55,some 55,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check3573:(cell3573.cap (3:Fin 18)).grade<cell3573.lowerGrade-cell3573.off:=by decide +kernel
def cell3574:PairCell.Row:=⟨41,49,9,2,49,some 64,56,some 56,257319,[MeasuredChoices.test62],[AxisChoices.test1819]⟩
theorem check3574:(cell3574.cap (3:Fin 18)).grade<cell3574.lowerGrade-cell3574.off:=by decide +kernel
def cell3575:PairCell.Row:=⟨41,49,9,2,49,some 64,57,some 57,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check3575:(cell3575.cap (3:Fin 18)).grade<cell3575.lowerGrade-cell3575.off:=by decide +kernel
def cell3576:PairCell.Row:=⟨41,49,9,2,49,some 64,58,some 58,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check3576:(cell3576.cap (3:Fin 18)).grade<cell3576.lowerGrade-cell3576.off:=by decide +kernel
def cell3577:PairCell.Row:=⟨41,49,9,2,49,some 64,59,some 59,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check3577:(cell3577.cap (3:Fin 18)).grade<cell3577.lowerGrade-cell3577.off:=by decide +kernel
def cell3578:PairCell.Row:=⟨41,49,9,2,49,some 64,60,some 60,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check3578:(cell3578.cap (3:Fin 18)).grade<cell3578.lowerGrade-cell3578.off:=by decide +kernel
def cell3579:PairCell.Row:=⟨41,49,9,2,49,some 64,61,some 61,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check3579:(cell3579.cap (3:Fin 18)).grade<cell3579.lowerGrade-cell3579.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2912

-- Source: Research6969.PairReceipts180
section Z6969Source2913
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3600 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,21,some 22,0,none,385979,[MeasuredChoices.test869],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,17,some 18,0,none,385979,[MeasuredChoices.test821],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,15,some 16,0,none,385979,[MeasuredChoices.test797],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,61,some 64,0,none,257319,[MeasuredChoices.test82,MeasuredChoices.test85],[]⟩,3,markedIntersection⟩,
  ⟨⟨50,63,10,2,59,some 60,0,none,257319,[MeasuredChoices.test82],[]⟩,3,markedIntersection⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,3,⟨(.node 8025893007439878),.intersection,.impossible,283522⟩⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩,3,markedIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,0,some 0,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,1,some 1,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,2,some 2,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,3,some 3,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,4,some 4,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,5,some 5,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,6,some 6,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,7,some 7,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,8,some 8,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩]
private theorem paid3600 : StockPairs.checked rows3600 = true := by decide +kernel
theorem route3600 (i : Fin 20) : (rows3600.get i).Done :=
  StockPairs.doneAt paid3600 i

end Research6969.PairReceipts
end Z6969Source2913

-- Source: Research6969.HardFit4At060
section Z6969Source2914
set_option autoImplicit true
namespace Research6969.HardFit4At060
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3583 3)
private def leaf1 := (PairReceipts.route3583 4)
private def weight2 := PairRoute.weight 302619 leaf0 leaf1
theorem case60: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route3583 2)
theorem case61: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,29,some 32⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route3583 1)
theorem case62: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,33,some 40⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route3583 0)
theorem case63: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,41,some 48⟩:=PairRoute.start _ leaf5
private theorem allAxes135:PairRoute.Done (3:Fin 18) ⟨⟨41,49,9,2,49,some 64⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 64 ⟨
    (PairReceipts.route3500 19),
    (PairReceipts.route3500 20),
    (PairReceipts.route3520 0),
    (PairReceipts.route3520 1),
    (PairReceipts.route3520 2),
    (PairReceipts.route3520 3),
    (PairReceipts.route3520 4),
    (PairReceipts.route3520 5),
    (PairReceipts.route3520 6),
    (PairReceipts.route3520 7),
    (PairReceipts.route3520 8),
    (PairReceipts.route3520 9),
    (PairReceipts.route3520 10),
    (PairReceipts.route3520 11),
    (PairReceipts.route3520 12),
    (PairReceipts.route3520 13),
    (PairReceipts.route3520 14),
    (PairReceipts.route3520 15),
    (PairReceipts.route3520 16),
    (PairReceipts.route3520 17),
    (PairReceipts.route3520 18),
    (PairReceipts.route3520 19),
    (PairReceipts.route3540 0),
    (PairReceipts.route3540 1),
    (PairReceipts.route3540 2),
    (PairReceipts.route3540 3),
    (PairReceipts.route3540 4),
    (PairReceipts.route3540 5),
    (PairReceipts.route3540 6),
    (PairReceipts.route3540 7),
    (PairReceipts.route3540 8),
    (PairReceipts.route3540 9),
    PairLeaves.excluded PairReceipts.cell3550 PairReceipts.check3550 (none),
    PairLeaves.excluded PairReceipts.cell3551 PairReceipts.check3551 (none),
    PairLeaves.excluded PairReceipts.cell3552 PairReceipts.check3552 (none),
    PairLeaves.excluded PairReceipts.cell3553 PairReceipts.check3553 (none),
    PairLeaves.excluded PairReceipts.cell3554 PairReceipts.check3554 (none),
    PairLeaves.excluded PairReceipts.cell3555 PairReceipts.check3555 (none),
    PairLeaves.excluded PairReceipts.cell3556 PairReceipts.check3556 (none),
    PairLeaves.excluded PairReceipts.cell3557 PairReceipts.check3557 (none),
    PairLeaves.excluded PairReceipts.cell3558 PairReceipts.check3558 (none),
    PairLeaves.excluded PairReceipts.cell3559 PairReceipts.check3559 (none),
    PairLeaves.excluded PairReceipts.cell3560 PairReceipts.check3560 (none),
    PairLeaves.excluded PairReceipts.cell3561 PairReceipts.check3561 (none),
    PairLeaves.excluded PairReceipts.cell3562 PairReceipts.check3562 (none),
    PairLeaves.excluded PairReceipts.cell3563 PairReceipts.check3563 (none),
    PairLeaves.excluded PairReceipts.cell3564 PairReceipts.check3564 (none),
    PairLeaves.excluded PairReceipts.cell3565 PairReceipts.check3565 (none),
    PairLeaves.excluded PairReceipts.cell3566 PairReceipts.check3566 (none),
    PairLeaves.excluded PairReceipts.cell3567 PairReceipts.check3567 (none),
    PairLeaves.excluded PairReceipts.cell3568 PairReceipts.check3568 (none),
    PairLeaves.excluded PairReceipts.cell3569 PairReceipts.check3569 (none),
    PairLeaves.excluded PairReceipts.cell3570 PairReceipts.check3570 (none),
    PairLeaves.excluded PairReceipts.cell3571 PairReceipts.check3571 (none),
    PairLeaves.excluded PairReceipts.cell3572 PairReceipts.check3572 (none),
    PairLeaves.excluded PairReceipts.cell3573 PairReceipts.check3573 (none),
    PairLeaves.excluded PairReceipts.cell3574 PairReceipts.check3574 (none),
    PairLeaves.excluded PairReceipts.cell3575 PairReceipts.check3575 (none),
    PairLeaves.excluded PairReceipts.cell3576 PairReceipts.check3576 (none),
    PairLeaves.excluded PairReceipts.cell3577 PairReceipts.check3577 (none),
    PairLeaves.excluded PairReceipts.cell3578 PairReceipts.check3578 (none),
    PairLeaves.excluded PairReceipts.cell3579 PairReceipts.check3579 (none),
    PairLeaves.excluded PairReceipts.cell3580 PairReceipts.check3580 (none),
    PairLeaves.excluded PairReceipts.cell3581 PairReceipts.check3581 (none),
    PairLeaves.excluded PairReceipts.cell3582 PairReceipts.check3582 (none),
    trivial⟩)
theorem case64: NormalRoute.Done (3:Fin 18) ⟨41,49,9,2,49,some 64⟩:=PairRoute.start _ allAxes135
private def leaf136 := (PairReceipts.route3600 6)
theorem case65: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf136
private def leaf137 := (PairReceipts.route3600 5)
theorem case66: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,13,some 14⟩:=PairRoute.start _ leaf137
private def leaf138 := (PairReceipts.route3600 4)
theorem case67: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,15,some 16⟩:=PairRoute.start _ leaf138
private def leaf139 := (PairReceipts.route3600 3)
theorem case68: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,17,some 18⟩:=PairRoute.start _ leaf139
private def leaf140 := (PairReceipts.route3600 2)
theorem case69: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,19,some 20⟩:=PairRoute.start _ leaf140
end Research6969.HardFit4At060
end Z6969Source2914

-- Source: Research6969.PairReceipts343
section Z6969Source2915
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6860:PairCell.Row:=⟨41,49,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩
theorem check6860:ThreeRule.check cell6860 (3:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2915

-- Source: Research6969.HardFit4At070
section Z6969Source2916
set_option autoImplicit true
namespace Research6969.HardFit4At070
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3600 1)
theorem case70: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,21,some 22⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3600 0)
theorem case71: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,23,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3583 16)
theorem case72: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,25,some 28⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route3583 15)
theorem case73: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,29,some 32⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route3583 14)
theorem case74: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,33,some 36⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route3583 13)
theorem case75: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,37,some 40⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route3583 12)
theorem case76: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,41,some 44⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route3583 11)
theorem case77: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,45,some 48⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (3:Fin 18) ⟨⟨41,49,9,3,49,some 64⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell6860 PairReceipts.check6860 (by decide) (none)
theorem case78: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,49,some 64⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route3583 10)
theorem case79: NormalRoute.Done (3:Fin 18) ⟨41,49,9,3,65,some 96⟩:=PairRoute.start _ leaf9
end Research6969.HardFit4At070
end Z6969Source2916

-- Source: Research6969.PairReceipts200
section Z6969Source2917
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4000 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,41,some 44,0,none,257319,[MeasuredChoices.test50],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,3,⟨(.node 8037210057961988),.intersection,.impossible,296579⟩⟩,
  ⟨⟨50,63,10,2,33,some 40,0,none,296579,[MeasuredChoices.test157],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,3,⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,300842,[MeasuredChoices.test165],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,27,some 28,0,none,257319,[MeasuredChoices.test37],[]⟩,3,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨50,63,10,2,27,some 28,0,none,302619,[MeasuredChoices.test169],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,25,some 26,0,none,257319,[MeasuredChoices.test36],[]⟩,3,⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨⟨50,63,10,2,25,some 26,0,none,303418,[MeasuredChoices.test172],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,3,⟨(.node 30786469546942771),.intersection,.impossible,307280⟩⟩,
  ⟨⟨50,63,10,2,23,some 24,0,none,307280,[MeasuredChoices.test425],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,4,some 8,0,none,257319,[],[]⟩,3,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨50,63,10,3,39,some 40,0,none,385979,[MeasuredChoices.test1105],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,37,some 38,0,none,385979,[MeasuredChoices.test1079],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,3,surfaceIntersection⟩]
private theorem paid4000 : StockPairs.checked rows4000 = true := by decide +kernel
theorem route4000 (i : Fin 20) : (rows4000.get i).Done :=
  StockPairs.doneAt paid4000 i

end Research6969.PairReceipts
end Z6969Source2917

-- Source: Research6969.HardFit4At080
section Z6969Source2918
set_option autoImplicit true
namespace Research6969.HardFit4At080
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4000 15)
theorem case80: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,4,some 8⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4000 14)
theorem case81: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,9,some 12⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4000 13)
theorem case82: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4000 12)
theorem case83: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4000 11)
theorem case84: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,21,some 22⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4000 9)
private def leaf6 := (PairReceipts.route4000 10)
private def weight7 := PairRoute.weight 307280 leaf5 leaf6
theorem case85: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,23,some 24⟩:=PairRoute.start _ weight7
private def leaf8 := (PairReceipts.route4000 7)
private def leaf9 := (PairReceipts.route4000 8)
private def weight10 := PairRoute.weight 303418 leaf8 leaf9
theorem case86: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,25,some 26⟩:=PairRoute.start _ weight10
private def leaf11 := (PairReceipts.route4000 5)
private def leaf12 := (PairReceipts.route4000 6)
private def weight13 := PairRoute.weight 302619 leaf11 leaf12
theorem case87: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,27,some 28⟩:=PairRoute.start _ weight13
private def leaf14 := (PairReceipts.route4000 3)
private def leaf15 := (PairReceipts.route4000 4)
private def weight16 := PairRoute.weight 300842 leaf14 leaf15
theorem case88: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,29,some 32⟩:=PairRoute.start _ weight16
private def leaf17 := (PairReceipts.route4000 1)
private def leaf18 := (PairReceipts.route4000 2)
private def weight19 := PairRoute.weight 296579 leaf17 leaf18
theorem case89: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,33,some 40⟩:=PairRoute.start _ weight19
end Research6969.HardFit4At080
end Z6969Source2918

-- Source: Research6969.PairReceipts181
section Z6969Source2919
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3620 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,57,some 57,9,some 9,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,10,some 10,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,11,some 11,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1774]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,12,some 12,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1775]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,13,some 13,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1776]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,14,some 14,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1777]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,15,some 15,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1778]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,16,some 16,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1779]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,17,some 17,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1780]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,18,some 18,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1781]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,19,some 19,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1782]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,20,some 20,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1783]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,21,some 21,257319,[MeasuredChoices.test79],[AxisChoices.test1784]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,22,some 22,257319,[MeasuredChoices.test79],[AxisChoices.test1784,AxisChoices.test1785]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,23,some 23,257319,[MeasuredChoices.test79],[AxisChoices.test1784,AxisChoices.test1786]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,24,some 24,257319,[MeasuredChoices.test79],[AxisChoices.test1787]⟩,3,markedAxisIntersection⟩]
private theorem paid3620 : StockPairs.checked rows3620 = true := by decide +kernel
theorem route3620 (i : Fin 16) : (rows3620.get i).Done :=
  StockPairs.doneAt paid3620 i

def cell3636:PairCell.Row:=⟨50,63,10,2,57,some 57,25,some 25,257319,[MeasuredChoices.test79],[AxisChoices.test1788]⟩
theorem check3636:(cell3636.cap (3:Fin 18)).grade<cell3636.lowerGrade-cell3636.off:=by decide +kernel
def cell3637:PairCell.Row:=⟨50,63,10,2,57,some 57,26,some 26,257319,[MeasuredChoices.test79],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check3637:(cell3637.cap (3:Fin 18)).grade<cell3637.lowerGrade-cell3637.off:=by decide +kernel
def cell3638:PairCell.Row:=⟨50,63,10,2,57,some 57,27,some 27,257319,[MeasuredChoices.test79],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check3638:(cell3638.cap (3:Fin 18)).grade<cell3638.lowerGrade-cell3638.off:=by decide +kernel
def cell3639:PairCell.Row:=⟨50,63,10,2,57,some 57,28,some 28,257319,[MeasuredChoices.test79],[AxisChoices.test1791]⟩
theorem check3639:(cell3639.cap (3:Fin 18)).grade<cell3639.lowerGrade-cell3639.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2919

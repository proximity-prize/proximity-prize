import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0676
import ProximityPrize.SubmissionLower.Z6969Pack0972
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0677

set_option Elab.async false

-- Source: Research6969.PairReceipts253
section Z6969Source3016
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5060 : List StockPairs.Receipt := [
  ⟨⟨64,706,12,2,45,some 46,0,none,257319,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,41,some 44,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,6,⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨⟨64,706,12,2,41,some 44,0,none,294092,[MeasuredChoices.test124,MeasuredChoices.test140],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,37,some 40,0,none,257319,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩,6,⟨(.node 8037210057961988),.intersection,.impossible,296579⟩⟩,
  ⟨⟨64,706,12,2,37,some 40,0,none,296579,[MeasuredChoices.test158],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,33,some 36,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,6,⟨(.node 8042152515659111),.intersection,.impossible,298829⟩⟩,
  ⟨⟨64,706,12,2,33,some 36,0,none,298829,[MeasuredChoices.test156,MeasuredChoices.test161],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,6,⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨64,706,12,2,29,some 32,0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,27,some 28,0,none,257319,[MeasuredChoices.test37],[]⟩,6,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨64,706,12,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,25,some 26,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,6,⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨⟨64,706,12,2,25,some 26,0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,23,some 24,0,none,257319,[MeasuredChoices.test29,MeasuredChoices.test32],[]⟩,6,⟨(.node 30786469546942771),.intersection,.impossible,307280⟩⟩,
  ⟨⟨64,706,12,2,23,some 24,0,none,307280,[MeasuredChoices.test425],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,21,some 22,0,none,257319,[MeasuredChoices.test26],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,17,some 20,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,13,some 16,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,9,some 12,0,none,257319,[],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,surfaceIntersection⟩]
private theorem paid5060 : StockPairs.checked rows5060 = true := by decide +kernel
theorem route5060 (i : Fin 20) : (rows5060.get i).Done :=
  StockPairs.doneAt paid5060 i

end Research6969.PairReceipts
end Z6969Source3016

-- Source: Research6969.HardFit7At050
section Z6969Source3017
set_option autoImplicit true
namespace Research6969.HardFit7At050
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4940 5)
theorem case50: NormalRoute.Done (6:Fin 18) ⟨50,63,10,3,29,some 32⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4940 4)
theorem case51: NormalRoute.Done (6:Fin 18) ⟨50,63,10,3,33,some 40⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route5060 18)
theorem case52: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route5060 17)
theorem case53: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route5060 16)
theorem case54: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route5060 15)
theorem case55: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,21,some 22⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route5060 13)
private def leaf7 := (PairReceipts.route5060 14)
private def weight8 := PairRoute.weight 307280 leaf6 leaf7
theorem case56: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,23,some 24⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route5060 11)
private def leaf10 := (PairReceipts.route5060 12)
private def weight11 := PairRoute.weight 303418 leaf9 leaf10
theorem case57: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,25,some 26⟩:=PairRoute.start _ weight11
private def leaf12 := (PairReceipts.route5060 9)
private def leaf13 := (PairReceipts.route5060 10)
private def weight14 := PairRoute.weight 302619 leaf12 leaf13
theorem case58: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,27,some 28⟩:=PairRoute.start _ weight14
private def leaf15 := (PairReceipts.route5060 7)
private def leaf16 := (PairReceipts.route5060 8)
private def weight17 := PairRoute.weight 300842 leaf15 leaf16
theorem case59: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,29,some 32⟩:=PairRoute.start _ weight17
end Research6969.HardFit7At050
end Z6969Source3017

-- Source: Research6969.PairReceipts248
section Z6969Source3018
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4960 : List StockPairs.Receipt := [
  ⟨⟨64,706,12,2,51,some 51,7,some 7,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,8,some 8,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,9,some 9,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,10,some 10,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,11,some 11,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1774]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,12,some 12,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1775]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,13,some 13,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1776]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,14,some 14,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1777]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,15,some 15,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1778]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,16,some 16,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1779]⟩,6,markedAxisIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,17,some 17,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1780]⟩,6,markedAxisIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,18,some 18,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1781]⟩,6,markedAxisIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,19,some 19,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1782]⟩,6,markedAxisIntersection⟩,
  ⟨⟨64,706,12,2,51,some 51,20,some 20,257319,[MeasuredChoices.test66],[AxisChoices.test1783]⟩,6,markedAxisIntersection⟩]
private theorem paid4960 : StockPairs.checked rows4960 = true := by decide +kernel
theorem route4960 (i : Fin 14) : (rows4960.get i).Done :=
  StockPairs.doneAt paid4960 i

def cell4974:PairCell.Row:=⟨64,706,12,2,51,some 51,21,some 21,257319,[MeasuredChoices.test66],[AxisChoices.test1784]⟩
theorem check4974:(cell4974.cap (6:Fin 18)).grade<cell4974.lowerGrade-cell4974.off:=by decide +kernel
def cell4975:PairCell.Row:=⟨64,706,12,2,51,some 51,22,some 22,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4975:(cell4975.cap (6:Fin 18)).grade<cell4975.lowerGrade-cell4975.off:=by decide +kernel
def cell4976:PairCell.Row:=⟨64,706,12,2,51,some 51,23,some 23,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4976:(cell4976.cap (6:Fin 18)).grade<cell4976.lowerGrade-cell4976.off:=by decide +kernel
def cell4977:PairCell.Row:=⟨64,706,12,2,51,some 51,24,some 24,257319,[MeasuredChoices.test66],[AxisChoices.test1787]⟩
theorem check4977:(cell4977.cap (6:Fin 18)).grade<cell4977.lowerGrade-cell4977.off:=by decide +kernel
def cell4978:PairCell.Row:=⟨64,706,12,2,51,some 51,25,some 25,257319,[MeasuredChoices.test66],[AxisChoices.test1788]⟩
theorem check4978:(cell4978.cap (6:Fin 18)).grade<cell4978.lowerGrade-cell4978.off:=by decide +kernel
def cell4979:PairCell.Row:=⟨64,706,12,2,51,some 51,26,some 26,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4979:(cell4979.cap (6:Fin 18)).grade<cell4979.lowerGrade-cell4979.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source3018

-- Source: Research6969.PairReceipts249
section Z6969Source3019
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4980:PairCell.Row:=⟨64,706,12,2,51,some 51,27,some 27,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4980:(cell4980.cap (6:Fin 18)).grade<cell4980.lowerGrade-cell4980.off:=by decide +kernel
def cell4981:PairCell.Row:=⟨64,706,12,2,51,some 51,28,some 28,257319,[MeasuredChoices.test66],[AxisChoices.test1791]⟩
theorem check4981:(cell4981.cap (6:Fin 18)).grade<cell4981.lowerGrade-cell4981.off:=by decide +kernel
def cell4982:PairCell.Row:=⟨64,706,12,2,51,some 51,29,some 29,257319,[MeasuredChoices.test66],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4982:(cell4982.cap (6:Fin 18)).grade<cell4982.lowerGrade-cell4982.off:=by decide +kernel
def cell4983:PairCell.Row:=⟨64,706,12,2,51,some 51,30,some 30,257319,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4983:(cell4983.cap (6:Fin 18)).grade<cell4983.lowerGrade-cell4983.off:=by decide +kernel
def cell4984:PairCell.Row:=⟨64,706,12,2,51,some 51,31,some 31,257319,[MeasuredChoices.test66],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4984:(cell4984.cap (6:Fin 18)).grade<cell4984.lowerGrade-cell4984.off:=by decide +kernel
def cell4985:PairCell.Row:=⟨64,706,12,2,51,some 51,32,some 32,257319,[MeasuredChoices.test66],[AxisChoices.test1795]⟩
theorem check4985:(cell4985.cap (6:Fin 18)).grade<cell4985.lowerGrade-cell4985.off:=by decide +kernel
def cell4986:PairCell.Row:=⟨64,706,12,2,51,some 51,33,some 33,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4986:(cell4986.cap (6:Fin 18)).grade<cell4986.lowerGrade-cell4986.off:=by decide +kernel
def cell4987:PairCell.Row:=⟨64,706,12,2,51,some 51,34,some 34,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4987:(cell4987.cap (6:Fin 18)).grade<cell4987.lowerGrade-cell4987.off:=by decide +kernel
def cell4988:PairCell.Row:=⟨64,706,12,2,51,some 51,35,some 35,257319,[MeasuredChoices.test66],[AxisChoices.test1798]⟩
theorem check4988:(cell4988.cap (6:Fin 18)).grade<cell4988.lowerGrade-cell4988.off:=by decide +kernel
def cell4989:PairCell.Row:=⟨64,706,12,2,51,some 51,36,some 36,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4989:(cell4989.cap (6:Fin 18)).grade<cell4989.lowerGrade-cell4989.off:=by decide +kernel
def cell4990:PairCell.Row:=⟨64,706,12,2,51,some 51,37,some 37,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4990:(cell4990.cap (6:Fin 18)).grade<cell4990.lowerGrade-cell4990.off:=by decide +kernel
def cell4991:PairCell.Row:=⟨64,706,12,2,51,some 51,38,some 38,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4991:(cell4991.cap (6:Fin 18)).grade<cell4991.lowerGrade-cell4991.off:=by decide +kernel
def cell4992:PairCell.Row:=⟨64,706,12,2,51,some 51,39,some 39,257319,[MeasuredChoices.test66],[AxisChoices.test1802]⟩
theorem check4992:(cell4992.cap (6:Fin 18)).grade<cell4992.lowerGrade-cell4992.off:=by decide +kernel
def cell4993:PairCell.Row:=⟨64,706,12,2,51,some 51,40,some 40,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4993:(cell4993.cap (6:Fin 18)).grade<cell4993.lowerGrade-cell4993.off:=by decide +kernel
def cell4994:PairCell.Row:=⟨64,706,12,2,51,some 51,41,some 41,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4994:(cell4994.cap (6:Fin 18)).grade<cell4994.lowerGrade-cell4994.off:=by decide +kernel
def cell4995:PairCell.Row:=⟨64,706,12,2,51,some 51,42,some 42,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4995:(cell4995.cap (6:Fin 18)).grade<cell4995.lowerGrade-cell4995.off:=by decide +kernel
def cell4996:PairCell.Row:=⟨64,706,12,2,51,some 51,43,some 43,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4996:(cell4996.cap (6:Fin 18)).grade<cell4996.lowerGrade-cell4996.off:=by decide +kernel
def cell4997:PairCell.Row:=⟨64,706,12,2,51,some 51,44,some 44,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4997:(cell4997.cap (6:Fin 18)).grade<cell4997.lowerGrade-cell4997.off:=by decide +kernel
def cell4998:PairCell.Row:=⟨64,706,12,2,51,some 51,45,some 45,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4998:(cell4998.cap (6:Fin 18)).grade<cell4998.lowerGrade-cell4998.off:=by decide +kernel
def cell4999:PairCell.Row:=⟨64,706,12,2,51,some 51,46,some 46,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4999:(cell4999.cap (6:Fin 18)).grade<cell4999.lowerGrade-cell4999.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source3019

-- Source: Research6969.PairReceipts250
section Z6969Source3020
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5000:PairCell.Row:=⟨64,706,12,2,51,some 51,47,some 47,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check5000:(cell5000.cap (6:Fin 18)).grade<cell5000.lowerGrade-cell5000.off:=by decide +kernel
def cell5001:PairCell.Row:=⟨64,706,12,2,51,some 51,48,some 48,257319,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check5001:(cell5001.cap (6:Fin 18)).grade<cell5001.lowerGrade-cell5001.off:=by decide +kernel
def cell5002:PairCell.Row:=⟨64,706,12,2,51,some 51,49,some 49,257319,[MeasuredChoices.test66],[AxisChoices.test1812]⟩
theorem check5002:(cell5002.cap (6:Fin 18)).grade<cell5002.lowerGrade-cell5002.off:=by decide +kernel
def cell5003:PairCell.Row:=⟨64,706,12,2,51,some 51,50,some 50,257319,[MeasuredChoices.test66],[AxisChoices.test1813]⟩
theorem check5003:(cell5003.cap (6:Fin 18)).grade<cell5003.lowerGrade-cell5003.off:=by decide +kernel
def cell5004:PairCell.Row:=⟨64,706,12,2,51,some 51,51,some 51,257319,[MeasuredChoices.test66],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check5004:(cell5004.cap (6:Fin 18)).grade<cell5004.lowerGrade-cell5004.off:=by decide +kernel
private def rows5005 : List StockPairs.Receipt := [
  ⟨⟨64,706,12,2,50,some 50,0,some 0,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,1,some 1,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,2,some 2,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,3,some 3,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,4,some 4,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,5,some 5,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,6,some 6,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,7,some 7,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,8,some 8,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,9,some 9,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,10,some 10,257319,[MeasuredChoices.test64],[]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,11,some 11,257319,[MeasuredChoices.test64],[AxisChoices.test1774]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,12,some 12,257319,[MeasuredChoices.test64],[AxisChoices.test1775]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,13,some 13,257319,[MeasuredChoices.test64],[AxisChoices.test1776]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,14,some 14,257319,[MeasuredChoices.test64],[AxisChoices.test1777]⟩,6,separateIntersection⟩]
private theorem paid5005 : StockPairs.checked rows5005 = true := by decide +kernel
theorem route5005 (i : Fin 15) : (rows5005.get i).Done :=
  StockPairs.doneAt paid5005 i

end Research6969.PairReceipts
end Z6969Source3020

-- Source: Research6969.PairReceipts251
section Z6969Source3021
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5020 : List StockPairs.Receipt := [
  ⟨⟨64,706,12,2,50,some 50,15,some 15,257319,[MeasuredChoices.test64],[AxisChoices.test1778]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,16,some 16,257319,[MeasuredChoices.test64],[AxisChoices.test1779]⟩,6,separateIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,17,some 17,257319,[MeasuredChoices.test64],[AxisChoices.test1780]⟩,6,markedAxisIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,18,some 18,257319,[MeasuredChoices.test64],[AxisChoices.test1781]⟩,6,markedAxisIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,19,some 19,257319,[MeasuredChoices.test64],[AxisChoices.test1782]⟩,6,markedAxisIntersection⟩,
  ⟨⟨64,706,12,2,50,some 50,20,some 20,257319,[MeasuredChoices.test64],[AxisChoices.test1783]⟩,6,markedAxisIntersection⟩]
private theorem paid5020 : StockPairs.checked rows5020 = true := by decide +kernel
theorem route5020 (i : Fin 6) : (rows5020.get i).Done :=
  StockPairs.doneAt paid5020 i

def cell5026:PairCell.Row:=⟨64,706,12,2,50,some 50,21,some 21,257319,[MeasuredChoices.test64],[AxisChoices.test1784]⟩
theorem check5026:(cell5026.cap (6:Fin 18)).grade<cell5026.lowerGrade-cell5026.off:=by decide +kernel
def cell5027:PairCell.Row:=⟨64,706,12,2,50,some 50,22,some 22,257319,[MeasuredChoices.test64],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check5027:(cell5027.cap (6:Fin 18)).grade<cell5027.lowerGrade-cell5027.off:=by decide +kernel
def cell5028:PairCell.Row:=⟨64,706,12,2,50,some 50,23,some 23,257319,[MeasuredChoices.test64],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check5028:(cell5028.cap (6:Fin 18)).grade<cell5028.lowerGrade-cell5028.off:=by decide +kernel
def cell5029:PairCell.Row:=⟨64,706,12,2,50,some 50,24,some 24,257319,[MeasuredChoices.test64],[AxisChoices.test1787]⟩
theorem check5029:(cell5029.cap (6:Fin 18)).grade<cell5029.lowerGrade-cell5029.off:=by decide +kernel
def cell5030:PairCell.Row:=⟨64,706,12,2,50,some 50,25,some 25,257319,[MeasuredChoices.test64],[AxisChoices.test1788]⟩
theorem check5030:(cell5030.cap (6:Fin 18)).grade<cell5030.lowerGrade-cell5030.off:=by decide +kernel
def cell5031:PairCell.Row:=⟨64,706,12,2,50,some 50,26,some 26,257319,[MeasuredChoices.test64],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check5031:(cell5031.cap (6:Fin 18)).grade<cell5031.lowerGrade-cell5031.off:=by decide +kernel
def cell5032:PairCell.Row:=⟨64,706,12,2,50,some 50,27,some 27,257319,[MeasuredChoices.test64],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check5032:(cell5032.cap (6:Fin 18)).grade<cell5032.lowerGrade-cell5032.off:=by decide +kernel
def cell5033:PairCell.Row:=⟨64,706,12,2,50,some 50,28,some 28,257319,[MeasuredChoices.test64],[AxisChoices.test1791]⟩
theorem check5033:(cell5033.cap (6:Fin 18)).grade<cell5033.lowerGrade-cell5033.off:=by decide +kernel
def cell5034:PairCell.Row:=⟨64,706,12,2,50,some 50,29,some 29,257319,[MeasuredChoices.test64],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check5034:(cell5034.cap (6:Fin 18)).grade<cell5034.lowerGrade-cell5034.off:=by decide +kernel
def cell5035:PairCell.Row:=⟨64,706,12,2,50,some 50,30,some 30,257319,[MeasuredChoices.test64],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check5035:(cell5035.cap (6:Fin 18)).grade<cell5035.lowerGrade-cell5035.off:=by decide +kernel
def cell5036:PairCell.Row:=⟨64,706,12,2,50,some 50,31,some 31,257319,[MeasuredChoices.test64],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check5036:(cell5036.cap (6:Fin 18)).grade<cell5036.lowerGrade-cell5036.off:=by decide +kernel
def cell5037:PairCell.Row:=⟨64,706,12,2,50,some 50,32,some 32,257319,[MeasuredChoices.test64],[AxisChoices.test1795]⟩
theorem check5037:(cell5037.cap (6:Fin 18)).grade<cell5037.lowerGrade-cell5037.off:=by decide +kernel
def cell5038:PairCell.Row:=⟨64,706,12,2,50,some 50,33,some 33,257319,[MeasuredChoices.test64],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check5038:(cell5038.cap (6:Fin 18)).grade<cell5038.lowerGrade-cell5038.off:=by decide +kernel
def cell5039:PairCell.Row:=⟨64,706,12,2,50,some 50,34,some 34,257319,[MeasuredChoices.test64],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check5039:(cell5039.cap (6:Fin 18)).grade<cell5039.lowerGrade-cell5039.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source3021

-- Source: Research6969.PairReceipts252
section Z6969Source3022
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5040:PairCell.Row:=⟨64,706,12,2,50,some 50,35,some 35,257319,[MeasuredChoices.test64],[AxisChoices.test1798]⟩
theorem check5040:(cell5040.cap (6:Fin 18)).grade<cell5040.lowerGrade-cell5040.off:=by decide +kernel
def cell5041:PairCell.Row:=⟨64,706,12,2,50,some 50,36,some 36,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check5041:(cell5041.cap (6:Fin 18)).grade<cell5041.lowerGrade-cell5041.off:=by decide +kernel
def cell5042:PairCell.Row:=⟨64,706,12,2,50,some 50,37,some 37,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check5042:(cell5042.cap (6:Fin 18)).grade<cell5042.lowerGrade-cell5042.off:=by decide +kernel
def cell5043:PairCell.Row:=⟨64,706,12,2,50,some 50,38,some 38,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check5043:(cell5043.cap (6:Fin 18)).grade<cell5043.lowerGrade-cell5043.off:=by decide +kernel
def cell5044:PairCell.Row:=⟨64,706,12,2,50,some 50,39,some 39,257319,[MeasuredChoices.test64],[AxisChoices.test1802]⟩
theorem check5044:(cell5044.cap (6:Fin 18)).grade<cell5044.lowerGrade-cell5044.off:=by decide +kernel
def cell5045:PairCell.Row:=⟨64,706,12,2,50,some 50,40,some 40,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check5045:(cell5045.cap (6:Fin 18)).grade<cell5045.lowerGrade-cell5045.off:=by decide +kernel
def cell5046:PairCell.Row:=⟨64,706,12,2,50,some 50,41,some 41,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check5046:(cell5046.cap (6:Fin 18)).grade<cell5046.lowerGrade-cell5046.off:=by decide +kernel
def cell5047:PairCell.Row:=⟨64,706,12,2,50,some 50,42,some 42,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check5047:(cell5047.cap (6:Fin 18)).grade<cell5047.lowerGrade-cell5047.off:=by decide +kernel
def cell5048:PairCell.Row:=⟨64,706,12,2,50,some 50,43,some 43,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check5048:(cell5048.cap (6:Fin 18)).grade<cell5048.lowerGrade-cell5048.off:=by decide +kernel
def cell5049:PairCell.Row:=⟨64,706,12,2,50,some 50,44,some 44,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check5049:(cell5049.cap (6:Fin 18)).grade<cell5049.lowerGrade-cell5049.off:=by decide +kernel
def cell5050:PairCell.Row:=⟨64,706,12,2,50,some 50,45,some 45,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check5050:(cell5050.cap (6:Fin 18)).grade<cell5050.lowerGrade-cell5050.off:=by decide +kernel
def cell5051:PairCell.Row:=⟨64,706,12,2,50,some 50,46,some 46,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check5051:(cell5051.cap (6:Fin 18)).grade<cell5051.lowerGrade-cell5051.off:=by decide +kernel
def cell5052:PairCell.Row:=⟨64,706,12,2,50,some 50,47,some 47,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check5052:(cell5052.cap (6:Fin 18)).grade<cell5052.lowerGrade-cell5052.off:=by decide +kernel
def cell5053:PairCell.Row:=⟨64,706,12,2,50,some 50,48,some 48,257319,[MeasuredChoices.test64],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check5053:(cell5053.cap (6:Fin 18)).grade<cell5053.lowerGrade-cell5053.off:=by decide +kernel
def cell5054:PairCell.Row:=⟨64,706,12,2,50,some 50,49,some 49,257319,[MeasuredChoices.test64],[AxisChoices.test1812]⟩
theorem check5054:(cell5054.cap (6:Fin 18)).grade<cell5054.lowerGrade-cell5054.off:=by decide +kernel
def cell5055:PairCell.Row:=⟨64,706,12,2,50,some 50,50,some 50,257319,[MeasuredChoices.test64],[AxisChoices.test1813]⟩
theorem check5055:(cell5055.cap (6:Fin 18)).grade<cell5055.lowerGrade-cell5055.off:=by decide +kernel
private def rows5056 : List StockPairs.Receipt := [
  ⟨⟨64,706,12,2,49,some 49,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,6,⟨(.node 8029965254169422),.intersection,.impossible,290650⟩⟩,
  ⟨⟨64,706,12,2,49,some 49,0,none,290650,[MeasuredChoices.test104,MeasuredChoices.test120],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨64,706,12,2,47,some 48,0,none,257319,[MeasuredChoices.test57,MeasuredChoices.test58],[]⟩,6,⟨(.node 30268515783660603),.intersection,.impossible,303874⟩⟩,
  ⟨⟨64,706,12,2,47,some 48,0,none,303874,[MeasuredChoices.test170,MeasuredChoices.test171],[]⟩,6,surfaceIntersection⟩]
private theorem paid5056 : StockPairs.checked rows5056 = true := by decide +kernel
theorem route5056 (i : Fin 4) : (rows5056.get i).Done :=
  StockPairs.doneAt paid5056 i

end Research6969.PairReceipts
end Z6969Source3022

-- Source: Research6969.HardFit7At060
section Z6969Source3023
set_option autoImplicit true
namespace Research6969.HardFit7At060
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route5060 5)
private def leaf1 := (PairReceipts.route5060 6)
private def weight2 := PairRoute.weight 298829 leaf0 leaf1
theorem case60: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,33,some 36⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route5060 3)
private def leaf4 := (PairReceipts.route5060 4)
private def weight5 := PairRoute.weight 296579 leaf3 leaf4
theorem case61: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,37,some 40⟩:=PairRoute.start _ weight5
private def leaf6 := (PairReceipts.route5060 1)
private def leaf7 := (PairReceipts.route5060 2)
private def weight8 := PairRoute.weight 294092 leaf6 leaf7
theorem case62: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,41,some 44⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route5060 0)
theorem case63: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,45,some 46⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route5056 2)
private def leaf11 := (PairReceipts.route5056 3)
private def weight12 := PairRoute.weight 303874 leaf10 leaf11
theorem case64: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,47,some 48⟩:=PairRoute.start _ weight12
private def leaf13 := (PairReceipts.route5056 0)
private def leaf14 := (PairReceipts.route5056 1)
private def weight15 := PairRoute.weight 290650 leaf13 leaf14
theorem case65: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,49,some 49⟩:=PairRoute.start _ weight15
private theorem allAxes117:PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,50,some 50⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 50 ⟨
    (PairReceipts.route5005 0),
    (PairReceipts.route5005 1),
    (PairReceipts.route5005 2),
    (PairReceipts.route5005 3),
    (PairReceipts.route5005 4),
    (PairReceipts.route5005 5),
    (PairReceipts.route5005 6),
    (PairReceipts.route5005 7),
    (PairReceipts.route5005 8),
    (PairReceipts.route5005 9),
    (PairReceipts.route5005 10),
    (PairReceipts.route5005 11),
    (PairReceipts.route5005 12),
    (PairReceipts.route5005 13),
    (PairReceipts.route5005 14),
    (PairReceipts.route5020 0),
    (PairReceipts.route5020 1),
    (PairReceipts.route5020 2),
    (PairReceipts.route5020 3),
    (PairReceipts.route5020 4),
    (PairReceipts.route5020 5),
    PairLeaves.excluded PairReceipts.cell5026 PairReceipts.check5026 (none),
    PairLeaves.excluded PairReceipts.cell5027 PairReceipts.check5027 (none),
    PairLeaves.excluded PairReceipts.cell5028 PairReceipts.check5028 (none),
    PairLeaves.excluded PairReceipts.cell5029 PairReceipts.check5029 (none),
    PairLeaves.excluded PairReceipts.cell5030 PairReceipts.check5030 (none),
    PairLeaves.excluded PairReceipts.cell5031 PairReceipts.check5031 (none),
    PairLeaves.excluded PairReceipts.cell5032 PairReceipts.check5032 (none),
    PairLeaves.excluded PairReceipts.cell5033 PairReceipts.check5033 (none),
    PairLeaves.excluded PairReceipts.cell5034 PairReceipts.check5034 (none),
    PairLeaves.excluded PairReceipts.cell5035 PairReceipts.check5035 (none),
    PairLeaves.excluded PairReceipts.cell5036 PairReceipts.check5036 (none),
    PairLeaves.excluded PairReceipts.cell5037 PairReceipts.check5037 (none),
    PairLeaves.excluded PairReceipts.cell5038 PairReceipts.check5038 (none),
    PairLeaves.excluded PairReceipts.cell5039 PairReceipts.check5039 (none),
    PairLeaves.excluded PairReceipts.cell5040 PairReceipts.check5040 (none),
    PairLeaves.excluded PairReceipts.cell5041 PairReceipts.check5041 (none),
    PairLeaves.excluded PairReceipts.cell5042 PairReceipts.check5042 (none),
    PairLeaves.excluded PairReceipts.cell5043 PairReceipts.check5043 (none),
    PairLeaves.excluded PairReceipts.cell5044 PairReceipts.check5044 (none),
    PairLeaves.excluded PairReceipts.cell5045 PairReceipts.check5045 (none),
    PairLeaves.excluded PairReceipts.cell5046 PairReceipts.check5046 (none),
    PairLeaves.excluded PairReceipts.cell5047 PairReceipts.check5047 (none),
    PairLeaves.excluded PairReceipts.cell5048 PairReceipts.check5048 (none),
    PairLeaves.excluded PairReceipts.cell5049 PairReceipts.check5049 (none),
    PairLeaves.excluded PairReceipts.cell5050 PairReceipts.check5050 (none),
    PairLeaves.excluded PairReceipts.cell5051 PairReceipts.check5051 (none),
    PairLeaves.excluded PairReceipts.cell5052 PairReceipts.check5052 (none),
    PairLeaves.excluded PairReceipts.cell5053 PairReceipts.check5053 (none),
    PairLeaves.excluded PairReceipts.cell5054 PairReceipts.check5054 (none),
    PairLeaves.excluded PairReceipts.cell5055 PairReceipts.check5055 (none),
    trivial⟩)
theorem case66: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,50,some 50⟩:=PairRoute.start _ allAxes117
private theorem allAxes221:PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,51,some 51⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 51 ⟨
    (PairReceipts.route4940 12),
    (PairReceipts.route4940 13),
    (PairReceipts.route4940 14),
    (PairReceipts.route4940 15),
    (PairReceipts.route4940 16),
    (PairReceipts.route4940 17),
    (PairReceipts.route4940 18),
    (PairReceipts.route4960 0),
    (PairReceipts.route4960 1),
    (PairReceipts.route4960 2),
    (PairReceipts.route4960 3),
    (PairReceipts.route4960 4),
    (PairReceipts.route4960 5),
    (PairReceipts.route4960 6),
    (PairReceipts.route4960 7),
    (PairReceipts.route4960 8),
    (PairReceipts.route4960 9),
    (PairReceipts.route4960 10),
    (PairReceipts.route4960 11),
    (PairReceipts.route4960 12),
    (PairReceipts.route4960 13),
    PairLeaves.excluded PairReceipts.cell4974 PairReceipts.check4974 (none),
    PairLeaves.excluded PairReceipts.cell4975 PairReceipts.check4975 (none),
    PairLeaves.excluded PairReceipts.cell4976 PairReceipts.check4976 (none),
    PairLeaves.excluded PairReceipts.cell4977 PairReceipts.check4977 (none),
    PairLeaves.excluded PairReceipts.cell4978 PairReceipts.check4978 (none),
    PairLeaves.excluded PairReceipts.cell4979 PairReceipts.check4979 (none),
    PairLeaves.excluded PairReceipts.cell4980 PairReceipts.check4980 (none),
    PairLeaves.excluded PairReceipts.cell4981 PairReceipts.check4981 (none),
    PairLeaves.excluded PairReceipts.cell4982 PairReceipts.check4982 (none),
    PairLeaves.excluded PairReceipts.cell4983 PairReceipts.check4983 (none),
    PairLeaves.excluded PairReceipts.cell4984 PairReceipts.check4984 (none),
    PairLeaves.excluded PairReceipts.cell4985 PairReceipts.check4985 (none),
    PairLeaves.excluded PairReceipts.cell4986 PairReceipts.check4986 (none),
    PairLeaves.excluded PairReceipts.cell4987 PairReceipts.check4987 (none),
    PairLeaves.excluded PairReceipts.cell4988 PairReceipts.check4988 (none),
    PairLeaves.excluded PairReceipts.cell4989 PairReceipts.check4989 (none),
    PairLeaves.excluded PairReceipts.cell4990 PairReceipts.check4990 (none),
    PairLeaves.excluded PairReceipts.cell4991 PairReceipts.check4991 (none),
    PairLeaves.excluded PairReceipts.cell4992 PairReceipts.check4992 (none),
    PairLeaves.excluded PairReceipts.cell4993 PairReceipts.check4993 (none),
    PairLeaves.excluded PairReceipts.cell4994 PairReceipts.check4994 (none),
    PairLeaves.excluded PairReceipts.cell4995 PairReceipts.check4995 (none),
    PairLeaves.excluded PairReceipts.cell4996 PairReceipts.check4996 (none),
    PairLeaves.excluded PairReceipts.cell4997 PairReceipts.check4997 (none),
    PairLeaves.excluded PairReceipts.cell4998 PairReceipts.check4998 (none),
    PairLeaves.excluded PairReceipts.cell4999 PairReceipts.check4999 (none),
    PairLeaves.excluded PairReceipts.cell5000 PairReceipts.check5000 (none),
    PairLeaves.excluded PairReceipts.cell5001 PairReceipts.check5001 (none),
    PairLeaves.excluded PairReceipts.cell5002 PairReceipts.check5002 (none),
    PairLeaves.excluded PairReceipts.cell5003 PairReceipts.check5003 (none),
    PairLeaves.excluded PairReceipts.cell5004 PairReceipts.check5004 (none),
    trivial⟩)
theorem case67: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,51,some 51⟩:=PairRoute.start _ allAxes221
private def leaf222 := (PairReceipts.route4940 11)
private theorem leaf223:PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,52,some 52⟩,0,none,288407,none⟩:=PairLeaves.excluded PairReceipts.cell4952 PairReceipts.check4952 (none)
private def weight224 := PairRoute.weight 288407 leaf222 leaf223
theorem case68: NormalRoute.Done (6:Fin 18) ⟨64,706,12,2,52,some 52⟩:=PairRoute.start _ weight224
end Research6969.HardFit7At060
end Z6969Source3023

-- Source: Research6969.HardComplete7
section Z6969Source3024
set_option autoImplicit true
namespace Research6969.HardComplete7
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_8 (j:Fin HighPendingSeed7.regions.size) (l:0≤j.val) (h:j.val<8):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At000.case0
  · exact HardFit7At000.case1
  · exact HardFit7At000.case2
  · exact HardFit7At000.case3
  · exact HardFit7At000.case4
  · exact HardFit7At000.case5
  · exact HardFit7At000.case6
  · exact HardFit7At000.case7
private theorem covered8_12 (j:Fin HighPendingSeed7.regions.size) (l:8≤j.val) (h:j.val<12):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At000.case8
  · exact HardFit7At000.case9
  · exact HardFit7At010.case10
  · exact HardFit7At010.case11
private theorem covered12_17 (j:Fin HighPendingSeed7.regions.size) (l:12≤j.val) (h:j.val<17):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At010.case12
  · exact HardFit7At010.case13
  · exact HardFit7At010.case14
  · exact HardFit7At010.case15
  · exact HardFit7At010.case16
private theorem covered8_17 (j:Fin HighPendingSeed7.regions.size) (l:8≤j.val) (h:j.val<17):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<12
  · exact covered8_12 j l low
  · exact covered12_17 j (by omega) h
private theorem covered0_17 (j:Fin HighPendingSeed7.regions.size) (l:0≤j.val) (h:j.val<17):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<8
  · exact covered0_8 j l low
  · exact covered8_17 j (by omega) h
private theorem covered17_25 (j:Fin HighPendingSeed7.regions.size) (l:17≤j.val) (h:j.val<25):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At010.case17
  · exact HardFit7At010.case18
  · exact HardFit7At010.case19
  · exact HardFit7At020.case20
  · exact HardFit7At020.case21
  · exact HardFit7At020.case22
  · exact HardFit7At020.case23
  · exact HardFit7At020.case24
private theorem covered25_29 (j:Fin HighPendingSeed7.regions.size) (l:25≤j.val) (h:j.val<29):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At020.case25
  · exact HardFit7At020.case26
  · exact HardFit7At020.case27
  · exact HardFit7At020.case28
private theorem covered29_34 (j:Fin HighPendingSeed7.regions.size) (l:29≤j.val) (h:j.val<34):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At020.case29
  · exact HardFit7At030.case30
  · exact HardFit7At030.case31
  · exact HardFit7At030.case32
  · exact HardFit7At030.case33
private theorem covered25_34 (j:Fin HighPendingSeed7.regions.size) (l:25≤j.val) (h:j.val<34):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<29
  · exact covered25_29 j l low
  · exact covered29_34 j (by omega) h
private theorem covered17_34 (j:Fin HighPendingSeed7.regions.size) (l:17≤j.val) (h:j.val<34):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<25
  · exact covered17_25 j l low
  · exact covered25_34 j (by omega) h
private theorem covered0_34 (j:Fin HighPendingSeed7.regions.size) (l:0≤j.val) (h:j.val<34):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<17
  · exact covered0_17 j l low
  · exact covered17_34 j (by omega) h
private theorem covered34_42 (j:Fin HighPendingSeed7.regions.size) (l:34≤j.val) (h:j.val<42):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At030.case34
  · exact HardFit7At030.case35
  · exact HardFit7At030.case36
  · exact HardFit7At030.case37
  · exact HardFit7At030.case38
  · exact HardFit7At030.case39
  · exact HardFit7At040.case40
  · exact HardFit7At040.case41
private theorem covered42_46 (j:Fin HighPendingSeed7.regions.size) (l:42≤j.val) (h:j.val<46):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At040.case42
  · exact HardFit7At040.case43
  · exact HardFit7At040.case44
  · exact HardFit7At040.case45
private theorem covered46_51 (j:Fin HighPendingSeed7.regions.size) (l:46≤j.val) (h:j.val<51):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At040.case46
  · exact HardFit7At040.case47
  · exact HardFit7At040.case48
  · exact HardFit7At040.case49
  · exact HardFit7At050.case50
private theorem covered42_51 (j:Fin HighPendingSeed7.regions.size) (l:42≤j.val) (h:j.val<51):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<46
  · exact covered42_46 j l low
  · exact covered46_51 j (by omega) h
private theorem covered34_51 (j:Fin HighPendingSeed7.regions.size) (l:34≤j.val) (h:j.val<51):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<42
  · exact covered34_42 j l low
  · exact covered42_51 j (by omega) h
private theorem covered51_55 (j:Fin HighPendingSeed7.regions.size) (l:51≤j.val) (h:j.val<55):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At050.case51
  · exact HardFit7At050.case52
  · exact HardFit7At050.case53
  · exact HardFit7At050.case54
private theorem covered55_60 (j:Fin HighPendingSeed7.regions.size) (l:55≤j.val) (h:j.val<60):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At050.case55
  · exact HardFit7At050.case56
  · exact HardFit7At050.case57
  · exact HardFit7At050.case58
  · exact HardFit7At050.case59
private theorem covered51_60 (j:Fin HighPendingSeed7.regions.size) (l:51≤j.val) (h:j.val<60):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<55
  · exact covered51_55 j l low
  · exact covered55_60 j (by omega) h
private theorem covered60_64 (j:Fin HighPendingSeed7.regions.size) (l:60≤j.val) (h:j.val<64):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At060.case60
  · exact HardFit7At060.case61
  · exact HardFit7At060.case62
  · exact HardFit7At060.case63
private theorem covered64_69 (j:Fin HighPendingSeed7.regions.size) (l:64≤j.val) (h:j.val<69):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit7At060.case64
  · exact HardFit7At060.case65
  · exact HardFit7At060.case66
  · exact HardFit7At060.case67
  · exact HardFit7At060.case68
private theorem covered60_69 (j:Fin HighPendingSeed7.regions.size) (l:60≤j.val) (h:j.val<69):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<64
  · exact covered60_64 j l low
  · exact covered64_69 j (by omega) h
private theorem covered51_69 (j:Fin HighPendingSeed7.regions.size) (l:51≤j.val) (h:j.val<69):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<60
  · exact covered51_60 j l low
  · exact covered60_69 j (by omega) h
private theorem covered34_69 (j:Fin HighPendingSeed7.regions.size) (l:34≤j.val) (h:j.val<69):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<51
  · exact covered34_51 j l low
  · exact covered51_69 j (by omega) h
private theorem covered0_69 (j:Fin HighPendingSeed7.regions.size) (l:0≤j.val) (h:j.val<69):Done (6:Fin 18) (HighPendingSeed7.atIndex j):=by
  by_cases low:j.val<34
  · exact covered0_34 j l low
  · exact covered34_69 j (by omega) h
theorem required:HighPendingSeed7.Required:=fun j=>covered0_69 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete7
end Z6969Source3024

-- Source: Research6969.PairReceipts254
section Z6969Source3025
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5080 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,7,surfaceIntersection⟩]
private theorem paid5080 : StockPairs.checked rows5080 = true := by decide +kernel
theorem route5080 (i : Fin 20) : (rows5080.get i).Done :=
  StockPairs.doneAt paid5080 i

end Research6969.PairReceipts
end Z6969Source3025

-- Source: Research6969.HardFit8At000
section Z6969Source3026
set_option autoImplicit true
namespace Research6969.HardFit8At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route5080 3)
theorem case0: NormalRoute.Done (7:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route5080 2)
theorem case1: NormalRoute.Done (7:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route5080 1)
theorem case2: NormalRoute.Done (7:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route5080 0)
theorem case3: NormalRoute.Done (7:Fin 18) ⟨25,27,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route5060 19)
theorem case4: NormalRoute.Done (7:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route5080 8)
theorem case5: NormalRoute.Done (7:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route5080 7)
theorem case6: NormalRoute.Done (7:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route5080 6)
theorem case7: NormalRoute.Done (7:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route5080 5)
theorem case8: NormalRoute.Done (7:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route5080 4)
theorem case9: NormalRoute.Done (7:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ leaf9
end Research6969.HardFit8At000
end Z6969Source3026

-- Source: Research6969.PairReceipts255
section Z6969Source3027
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5100 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,57,some 64,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,7,markedIntersection⟩,
  ⟨⟨50,63,10,2,49,some 56,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨64,722,12,2,49,some 52,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,7,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,722,12,2,49,some 52,0,none,288407,[MeasuredChoices.test104,MeasuredChoices.test114],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨64,722,12,2,45,some 48,0,none,257319,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨64,722,12,2,41,some 44,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨64,722,12,2,37,some 40,0,none,257319,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩,7,surfaceIntersection⟩,
  ⟨⟨64,722,12,2,33,some 36,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,7,surfaceIntersection⟩]
private theorem paid5100 : StockPairs.checked rows5100 = true := by decide +kernel
theorem route5100 (i : Fin 20) : (rows5100.get i).Done :=
  StockPairs.doneAt paid5100 i

end Research6969.PairReceipts
end Z6969Source3027

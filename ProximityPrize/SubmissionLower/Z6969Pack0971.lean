import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0675
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0970
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0939

set_option Elab.async false

-- Source: Research6969.HardFit6At040
section Z6969Source2992
set_option autoImplicit true
namespace Research6969.HardFit6At040
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4640 19)
theorem case40: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4640 18)
theorem case41: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4640 17)
theorem case42: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,25,some 28⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4640 16)
theorem case43: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,29,some 32⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4640 15)
theorem case44: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,33,some 40⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4640 14)
theorem case45: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,41,some 48⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4640 12)
private def leaf7 := (PairReceipts.route4640 13)
private def weight8 := PairRoute.weight 285209 leaf6 leaf7
theorem case46: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,49,some 56⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route4640 9)
private def terminalLeaf7050 := (PairReceipts.route4640 10)
private def terminalLeaf7051 := (PairReceipts.route4640 11)
private def leaf10 := PairRoute.splitSeed 59 terminalLeaf7050 terminalLeaf7051
private def weight11 := PairRoute.weight 290657 leaf9 leaf10
theorem case47: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,57,some 60⟩:=PairRoute.start _ weight11
private def leaf12 := (PairReceipts.route4660 8)
theorem case48: NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,9,some 12⟩:=PairRoute.start _ leaf12
private def leaf13 := (PairReceipts.route4660 7)
theorem case49: NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,13,some 16⟩:=PairRoute.start _ leaf13
end Research6969.HardFit6At040
end Z6969Source2992

-- Source: Research6969.PairReceipts244
section Z6969Source2993
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4880 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,39,some 40,0,none,257319,[MeasuredChoices.test47,MeasuredChoices.test48],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,37,some 38,0,none,257319,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,33,some 36,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,5,⟨(.node 25309255810936571),.intersection,.impossible,305352⟩⟩,
  ⟨⟨64,654,12,2,33,some 36,0,none,305352,[MeasuredChoices.test276,MeasuredChoices.test277],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,31,some 32,0,none,257319,[MeasuredChoices.test41,MeasuredChoices.test42],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,29,some 30,0,none,257319,[MeasuredChoices.test39],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,27,some 28,0,none,257319,[MeasuredChoices.test37],[]⟩,5,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨64,654,12,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,25,some 26,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,5,⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨⟨64,654,12,2,25,some 26,0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,24,some 24,0,none,257319,[MeasuredChoices.test32,MeasuredChoices.test34],[]⟩,5,⟨(.node 8075014212150647),.intersection,.impossible,304158⟩⟩,
  ⟨⟨64,654,12,2,24,some 24,0,none,304158,[MeasuredChoices.test216,MeasuredChoices.test217],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,23,some 23,0,none,257319,[MeasuredChoices.test29,MeasuredChoices.test32],[]⟩,5,⟨(.node 12169361715993978),.intersection,.impossible,305811⟩⟩,
  ⟨⟨64,654,12,2,23,some 23,0,none,305811,[MeasuredChoices.test216,MeasuredChoices.test312],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,21,some 22,0,none,257319,[MeasuredChoices.test26],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,17,some 20,0,none,257319,[],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,13,some 16,0,none,257319,[],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,9,some 12,0,none,257319,[],[]⟩,5,surfaceWhole⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,6,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[],[]⟩,6,surfaceIntersection⟩]
private theorem paid4880 : StockPairs.checked rows4880 = true := by decide +kernel
theorem route4880 (i : Fin 20) : (rows4880.get i).Done :=
  StockPairs.doneAt paid4880 i

end Research6969.PairReceipts
end Z6969Source2993

-- Source: Research6969.HardFit6At050
section Z6969Source2994
set_option autoImplicit true
namespace Research6969.HardFit6At050
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4660 6)
theorem case50: NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,17,some 18⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4660 5)
theorem case51: NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,19,some 20⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4660 4)
theorem case52: NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4660 3)
theorem case53: NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,25,some 28⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4660 2)
theorem case54: NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,29,some 32⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4660 1)
theorem case55: NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,33,some 40⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4880 17)
theorem case56: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4880 16)
theorem case57: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,13,some 16⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4880 15)
theorem case58: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,17,some 20⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4880 14)
theorem case59: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,21,some 22⟩:=PairRoute.start _ leaf9
end Research6969.HardFit6At050
end Z6969Source2994

-- Source: Research6969.PairReceipts243
section Z6969Source2995
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4860:PairCell.Row:=⟨64,654,12,2,48,some 48,36,some 36,257319,[MeasuredChoices.test61],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4860:(cell4860.cap (5:Fin 18)).grade<cell4860.lowerGrade-cell4860.off:=by decide +kernel
def cell4861:PairCell.Row:=⟨64,654,12,2,48,some 48,37,some 37,257319,[MeasuredChoices.test61],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4861:(cell4861.cap (5:Fin 18)).grade<cell4861.lowerGrade-cell4861.off:=by decide +kernel
def cell4862:PairCell.Row:=⟨64,654,12,2,48,some 48,38,some 38,257319,[MeasuredChoices.test61],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4862:(cell4862.cap (5:Fin 18)).grade<cell4862.lowerGrade-cell4862.off:=by decide +kernel
def cell4863:PairCell.Row:=⟨64,654,12,2,48,some 48,39,some 39,257319,[MeasuredChoices.test61],[AxisChoices.test1802]⟩
theorem check4863:(cell4863.cap (5:Fin 18)).grade<cell4863.lowerGrade-cell4863.off:=by decide +kernel
def cell4864:PairCell.Row:=⟨64,654,12,2,48,some 48,40,some 40,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4864:(cell4864.cap (5:Fin 18)).grade<cell4864.lowerGrade-cell4864.off:=by decide +kernel
def cell4865:PairCell.Row:=⟨64,654,12,2,48,some 48,41,some 41,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4865:(cell4865.cap (5:Fin 18)).grade<cell4865.lowerGrade-cell4865.off:=by decide +kernel
def cell4866:PairCell.Row:=⟨64,654,12,2,48,some 48,42,some 42,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4866:(cell4866.cap (5:Fin 18)).grade<cell4866.lowerGrade-cell4866.off:=by decide +kernel
def cell4867:PairCell.Row:=⟨64,654,12,2,48,some 48,43,some 43,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4867:(cell4867.cap (5:Fin 18)).grade<cell4867.lowerGrade-cell4867.off:=by decide +kernel
def cell4868:PairCell.Row:=⟨64,654,12,2,48,some 48,44,some 44,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4868:(cell4868.cap (5:Fin 18)).grade<cell4868.lowerGrade-cell4868.off:=by decide +kernel
def cell4869:PairCell.Row:=⟨64,654,12,2,48,some 48,45,some 45,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4869:(cell4869.cap (5:Fin 18)).grade<cell4869.lowerGrade-cell4869.off:=by decide +kernel
def cell4870:PairCell.Row:=⟨64,654,12,2,48,some 48,46,some 46,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4870:(cell4870.cap (5:Fin 18)).grade<cell4870.lowerGrade-cell4870.off:=by decide +kernel
def cell4871:PairCell.Row:=⟨64,654,12,2,48,some 48,47,some 47,257319,[MeasuredChoices.test61],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4871:(cell4871.cap (5:Fin 18)).grade<cell4871.lowerGrade-cell4871.off:=by decide +kernel
def cell4872:PairCell.Row:=⟨64,654,12,2,48,some 48,48,some 48,257319,[MeasuredChoices.test61],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4872:(cell4872.cap (5:Fin 18)).grade<cell4872.lowerGrade-cell4872.off:=by decide +kernel
private def rows4873 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,47,some 47,0,none,257319,[MeasuredChoices.test57,MeasuredChoices.test58],[]⟩,5,⟨(.node 16092526819772228),.intersection,.impossible,300246⟩⟩,
  ⟨⟨64,654,12,2,47,some 47,0,some 17,300246,[MeasuredChoices.test163],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,47,some 47,18,some 27,300246,[MeasuredChoices.test163],[AxisChoices.test1781]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,47,some 47,28,some 47,300246,[],[AxisChoices.test1791]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,45,some 46,0,none,257319,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,43,some 44,0,none,257319,[MeasuredChoices.test51,MeasuredChoices.test52],[]⟩,5,⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨⟨64,654,12,2,43,some 44,0,none,294092,[MeasuredChoices.test141,MeasuredChoices.test142],[]⟩,5,surfaceWhole⟩,
  ⟨⟨64,654,12,2,41,some 42,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,5,⟨(.node 8035141832419182),.intersection,.impossible,295365⟩⟩,
  ⟨⟨64,654,12,2,41,some 42,0,none,295365,[MeasuredChoices.test124,MeasuredChoices.test144],[]⟩,5,surfaceWhole⟩]
private theorem paid4873 : StockPairs.checked rows4873 = true := by decide +kernel
theorem route4873 (i : Fin 9) : (rows4873.get i).Done :=
  StockPairs.doneAt paid4873 i

end Research6969.PairReceipts
end Z6969Source2995

-- Source: Research6969.HardFit6At060
section Z6969Source2996
set_option autoImplicit true
namespace Research6969.HardFit6At060
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4880 12)
private def leaf1 := (PairReceipts.route4880 13)
private def weight2 := PairRoute.weight 305811 leaf0 leaf1
theorem case60: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,23,some 23⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route4880 10)
private def leaf4 := (PairReceipts.route4880 11)
private def weight5 := PairRoute.weight 304158 leaf3 leaf4
theorem case61: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,24,some 24⟩:=PairRoute.start _ weight5
private def leaf6 := (PairReceipts.route4880 8)
private def leaf7 := (PairReceipts.route4880 9)
private def weight8 := PairRoute.weight 303418 leaf6 leaf7
theorem case62: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,25,some 26⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route4880 6)
private def leaf10 := (PairReceipts.route4880 7)
private def weight11 := PairRoute.weight 302619 leaf9 leaf10
theorem case63: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,27,some 28⟩:=PairRoute.start _ weight11
private def leaf12 := (PairReceipts.route4880 5)
theorem case64: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,29,some 30⟩:=PairRoute.start _ leaf12
private def leaf13 := (PairReceipts.route4880 4)
theorem case65: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,31,some 32⟩:=PairRoute.start _ leaf13
private def leaf14 := (PairReceipts.route4880 2)
private def leaf15 := (PairReceipts.route4880 3)
private def weight16 := PairRoute.weight 305352 leaf14 leaf15
theorem case66: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,33,some 36⟩:=PairRoute.start _ weight16
private def leaf17 := (PairReceipts.route4880 1)
theorem case67: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,37,some 38⟩:=PairRoute.start _ leaf17
private def leaf18 := (PairReceipts.route4880 0)
theorem case68: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,39,some 40⟩:=PairRoute.start _ leaf18
private def leaf19 := (PairReceipts.route4873 7)
private def leaf20 := (PairReceipts.route4873 8)
private def weight21 := PairRoute.weight 295365 leaf19 leaf20
theorem case69: NormalRoute.Done (5:Fin 18) ⟨64,654,12,2,41,some 42⟩:=PairRoute.start _ weight21
end Research6969.HardFit6At060
end Z6969Source2996

-- Source: Research6969.PairReceipts234
section Z6969Source2997
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4680 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,51,some 51,9,some 9,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,10,some 10,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,11,some 11,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1774]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,12,some 12,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1775]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,13,some 13,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1776]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,14,some 14,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1777]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,15,some 15,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1778]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,16,some 16,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1779]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,17,some 17,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1780]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,18,some 18,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1781]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,19,some 19,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1782]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,20,some 20,257319,[MeasuredChoices.test66],[AxisChoices.test1783]⟩,5,markedAxisWhole⟩]
private theorem paid4680 : StockPairs.checked rows4680 = true := by decide +kernel
theorem route4680 (i : Fin 12) : (rows4680.get i).Done :=
  StockPairs.doneAt paid4680 i

def cell4692:PairCell.Row:=⟨64,654,12,2,51,some 51,21,some 21,257319,[MeasuredChoices.test66],[AxisChoices.test1784]⟩
theorem check4692:(cell4692.cap (5:Fin 18)).grade<cell4692.lowerGrade-cell4692.off:=by decide +kernel
def cell4693:PairCell.Row:=⟨64,654,12,2,51,some 51,22,some 22,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4693:(cell4693.cap (5:Fin 18)).grade<cell4693.lowerGrade-cell4693.off:=by decide +kernel
def cell4694:PairCell.Row:=⟨64,654,12,2,51,some 51,23,some 23,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4694:(cell4694.cap (5:Fin 18)).grade<cell4694.lowerGrade-cell4694.off:=by decide +kernel
def cell4695:PairCell.Row:=⟨64,654,12,2,51,some 51,24,some 24,257319,[MeasuredChoices.test66],[AxisChoices.test1787]⟩
theorem check4695:(cell4695.cap (5:Fin 18)).grade<cell4695.lowerGrade-cell4695.off:=by decide +kernel
def cell4696:PairCell.Row:=⟨64,654,12,2,51,some 51,25,some 25,257319,[MeasuredChoices.test66],[AxisChoices.test1788]⟩
theorem check4696:(cell4696.cap (5:Fin 18)).grade<cell4696.lowerGrade-cell4696.off:=by decide +kernel
def cell4697:PairCell.Row:=⟨64,654,12,2,51,some 51,26,some 26,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4697:(cell4697.cap (5:Fin 18)).grade<cell4697.lowerGrade-cell4697.off:=by decide +kernel
def cell4698:PairCell.Row:=⟨64,654,12,2,51,some 51,27,some 27,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4698:(cell4698.cap (5:Fin 18)).grade<cell4698.lowerGrade-cell4698.off:=by decide +kernel
def cell4699:PairCell.Row:=⟨64,654,12,2,51,some 51,28,some 28,257319,[MeasuredChoices.test66],[AxisChoices.test1791]⟩
theorem check4699:(cell4699.cap (5:Fin 18)).grade<cell4699.lowerGrade-cell4699.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2997

-- Source: Research6969.PairReceipts235
section Z6969Source2998
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4700:PairCell.Row:=⟨64,654,12,2,51,some 51,29,some 29,257319,[MeasuredChoices.test66],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4700:(cell4700.cap (5:Fin 18)).grade<cell4700.lowerGrade-cell4700.off:=by decide +kernel
def cell4701:PairCell.Row:=⟨64,654,12,2,51,some 51,30,some 30,257319,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4701:(cell4701.cap (5:Fin 18)).grade<cell4701.lowerGrade-cell4701.off:=by decide +kernel
def cell4702:PairCell.Row:=⟨64,654,12,2,51,some 51,31,some 31,257319,[MeasuredChoices.test66],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4702:(cell4702.cap (5:Fin 18)).grade<cell4702.lowerGrade-cell4702.off:=by decide +kernel
def cell4703:PairCell.Row:=⟨64,654,12,2,51,some 51,32,some 32,257319,[MeasuredChoices.test66],[AxisChoices.test1795]⟩
theorem check4703:(cell4703.cap (5:Fin 18)).grade<cell4703.lowerGrade-cell4703.off:=by decide +kernel
def cell4704:PairCell.Row:=⟨64,654,12,2,51,some 51,33,some 33,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4704:(cell4704.cap (5:Fin 18)).grade<cell4704.lowerGrade-cell4704.off:=by decide +kernel
def cell4705:PairCell.Row:=⟨64,654,12,2,51,some 51,34,some 34,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4705:(cell4705.cap (5:Fin 18)).grade<cell4705.lowerGrade-cell4705.off:=by decide +kernel
def cell4706:PairCell.Row:=⟨64,654,12,2,51,some 51,35,some 35,257319,[MeasuredChoices.test66],[AxisChoices.test1798]⟩
theorem check4706:(cell4706.cap (5:Fin 18)).grade<cell4706.lowerGrade-cell4706.off:=by decide +kernel
def cell4707:PairCell.Row:=⟨64,654,12,2,51,some 51,36,some 36,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4707:(cell4707.cap (5:Fin 18)).grade<cell4707.lowerGrade-cell4707.off:=by decide +kernel
def cell4708:PairCell.Row:=⟨64,654,12,2,51,some 51,37,some 37,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4708:(cell4708.cap (5:Fin 18)).grade<cell4708.lowerGrade-cell4708.off:=by decide +kernel
def cell4709:PairCell.Row:=⟨64,654,12,2,51,some 51,38,some 38,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4709:(cell4709.cap (5:Fin 18)).grade<cell4709.lowerGrade-cell4709.off:=by decide +kernel
def cell4710:PairCell.Row:=⟨64,654,12,2,51,some 51,39,some 39,257319,[MeasuredChoices.test66],[AxisChoices.test1802]⟩
theorem check4710:(cell4710.cap (5:Fin 18)).grade<cell4710.lowerGrade-cell4710.off:=by decide +kernel
def cell4711:PairCell.Row:=⟨64,654,12,2,51,some 51,40,some 40,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4711:(cell4711.cap (5:Fin 18)).grade<cell4711.lowerGrade-cell4711.off:=by decide +kernel
def cell4712:PairCell.Row:=⟨64,654,12,2,51,some 51,41,some 41,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4712:(cell4712.cap (5:Fin 18)).grade<cell4712.lowerGrade-cell4712.off:=by decide +kernel
def cell4713:PairCell.Row:=⟨64,654,12,2,51,some 51,42,some 42,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4713:(cell4713.cap (5:Fin 18)).grade<cell4713.lowerGrade-cell4713.off:=by decide +kernel
def cell4714:PairCell.Row:=⟨64,654,12,2,51,some 51,43,some 43,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4714:(cell4714.cap (5:Fin 18)).grade<cell4714.lowerGrade-cell4714.off:=by decide +kernel
def cell4715:PairCell.Row:=⟨64,654,12,2,51,some 51,44,some 44,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4715:(cell4715.cap (5:Fin 18)).grade<cell4715.lowerGrade-cell4715.off:=by decide +kernel
def cell4716:PairCell.Row:=⟨64,654,12,2,51,some 51,45,some 45,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4716:(cell4716.cap (5:Fin 18)).grade<cell4716.lowerGrade-cell4716.off:=by decide +kernel
def cell4717:PairCell.Row:=⟨64,654,12,2,51,some 51,46,some 46,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4717:(cell4717.cap (5:Fin 18)).grade<cell4717.lowerGrade-cell4717.off:=by decide +kernel
def cell4718:PairCell.Row:=⟨64,654,12,2,51,some 51,47,some 47,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4718:(cell4718.cap (5:Fin 18)).grade<cell4718.lowerGrade-cell4718.off:=by decide +kernel
def cell4719:PairCell.Row:=⟨64,654,12,2,51,some 51,48,some 48,257319,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4719:(cell4719.cap (5:Fin 18)).grade<cell4719.lowerGrade-cell4719.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2998

-- Source: Research6969.PairReceipts236
section Z6969Source2999
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4720:PairCell.Row:=⟨64,654,12,2,51,some 51,49,some 49,257319,[MeasuredChoices.test66],[AxisChoices.test1812]⟩
theorem check4720:(cell4720.cap (5:Fin 18)).grade<cell4720.lowerGrade-cell4720.off:=by decide +kernel
def cell4721:PairCell.Row:=⟨64,654,12,2,51,some 51,50,some 50,257319,[MeasuredChoices.test66],[AxisChoices.test1813]⟩
theorem check4721:(cell4721.cap (5:Fin 18)).grade<cell4721.lowerGrade-cell4721.off:=by decide +kernel
def cell4722:PairCell.Row:=⟨64,654,12,2,51,some 51,51,some 51,257319,[MeasuredChoices.test66],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4722:(cell4722.cap (5:Fin 18)).grade<cell4722.lowerGrade-cell4722.off:=by decide +kernel
private def rows4723 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,50,some 50,0,some 0,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,1,some 1,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,2,some 2,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,3,some 3,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,4,some 4,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,5,some 5,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,6,some 6,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,7,some 7,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,8,some 8,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,9,some 9,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,10,some 10,257319,[MeasuredChoices.test64],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,11,some 11,257319,[MeasuredChoices.test64],[AxisChoices.test1774]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,12,some 12,257319,[MeasuredChoices.test64],[AxisChoices.test1775]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,13,some 13,257319,[MeasuredChoices.test64],[AxisChoices.test1776]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,14,some 14,257319,[MeasuredChoices.test64],[AxisChoices.test1777]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,15,some 15,257319,[MeasuredChoices.test64],[AxisChoices.test1778]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,16,some 16,257319,[MeasuredChoices.test64],[AxisChoices.test1779]⟩,5,separateWhole⟩]
private theorem paid4723 : StockPairs.checked rows4723 = true := by decide +kernel
theorem route4723 (i : Fin 17) : (rows4723.get i).Done :=
  StockPairs.doneAt paid4723 i

end Research6969.PairReceipts
end Z6969Source2999

-- Source: Research6969.PairReceipts237
section Z6969Source3000
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4740 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,50,some 50,17,some 17,257319,[MeasuredChoices.test64],[AxisChoices.test1780]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,18,some 18,257319,[MeasuredChoices.test64],[AxisChoices.test1781]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,19,some 19,257319,[MeasuredChoices.test64],[AxisChoices.test1782]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,20,some 20,257319,[MeasuredChoices.test64],[AxisChoices.test1783]⟩,5,markedAxisWhole⟩]
private theorem paid4740 : StockPairs.checked rows4740 = true := by decide +kernel
theorem route4740 (i : Fin 4) : (rows4740.get i).Done :=
  StockPairs.doneAt paid4740 i

def cell4744:PairCell.Row:=⟨64,654,12,2,50,some 50,21,some 21,257319,[MeasuredChoices.test64],[AxisChoices.test1784]⟩
theorem check4744:(cell4744.cap (5:Fin 18)).grade<cell4744.lowerGrade-cell4744.off:=by decide +kernel
def cell4745:PairCell.Row:=⟨64,654,12,2,50,some 50,22,some 22,257319,[MeasuredChoices.test64],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4745:(cell4745.cap (5:Fin 18)).grade<cell4745.lowerGrade-cell4745.off:=by decide +kernel
def cell4746:PairCell.Row:=⟨64,654,12,2,50,some 50,23,some 23,257319,[MeasuredChoices.test64],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4746:(cell4746.cap (5:Fin 18)).grade<cell4746.lowerGrade-cell4746.off:=by decide +kernel
def cell4747:PairCell.Row:=⟨64,654,12,2,50,some 50,24,some 24,257319,[MeasuredChoices.test64],[AxisChoices.test1787]⟩
theorem check4747:(cell4747.cap (5:Fin 18)).grade<cell4747.lowerGrade-cell4747.off:=by decide +kernel
def cell4748:PairCell.Row:=⟨64,654,12,2,50,some 50,25,some 25,257319,[MeasuredChoices.test64],[AxisChoices.test1788]⟩
theorem check4748:(cell4748.cap (5:Fin 18)).grade<cell4748.lowerGrade-cell4748.off:=by decide +kernel
def cell4749:PairCell.Row:=⟨64,654,12,2,50,some 50,26,some 26,257319,[MeasuredChoices.test64],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4749:(cell4749.cap (5:Fin 18)).grade<cell4749.lowerGrade-cell4749.off:=by decide +kernel
def cell4750:PairCell.Row:=⟨64,654,12,2,50,some 50,27,some 27,257319,[MeasuredChoices.test64],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4750:(cell4750.cap (5:Fin 18)).grade<cell4750.lowerGrade-cell4750.off:=by decide +kernel
def cell4751:PairCell.Row:=⟨64,654,12,2,50,some 50,28,some 28,257319,[MeasuredChoices.test64],[AxisChoices.test1791]⟩
theorem check4751:(cell4751.cap (5:Fin 18)).grade<cell4751.lowerGrade-cell4751.off:=by decide +kernel
def cell4752:PairCell.Row:=⟨64,654,12,2,50,some 50,29,some 29,257319,[MeasuredChoices.test64],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4752:(cell4752.cap (5:Fin 18)).grade<cell4752.lowerGrade-cell4752.off:=by decide +kernel
def cell4753:PairCell.Row:=⟨64,654,12,2,50,some 50,30,some 30,257319,[MeasuredChoices.test64],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4753:(cell4753.cap (5:Fin 18)).grade<cell4753.lowerGrade-cell4753.off:=by decide +kernel
def cell4754:PairCell.Row:=⟨64,654,12,2,50,some 50,31,some 31,257319,[MeasuredChoices.test64],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4754:(cell4754.cap (5:Fin 18)).grade<cell4754.lowerGrade-cell4754.off:=by decide +kernel
def cell4755:PairCell.Row:=⟨64,654,12,2,50,some 50,32,some 32,257319,[MeasuredChoices.test64],[AxisChoices.test1795]⟩
theorem check4755:(cell4755.cap (5:Fin 18)).grade<cell4755.lowerGrade-cell4755.off:=by decide +kernel
def cell4756:PairCell.Row:=⟨64,654,12,2,50,some 50,33,some 33,257319,[MeasuredChoices.test64],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4756:(cell4756.cap (5:Fin 18)).grade<cell4756.lowerGrade-cell4756.off:=by decide +kernel
def cell4757:PairCell.Row:=⟨64,654,12,2,50,some 50,34,some 34,257319,[MeasuredChoices.test64],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4757:(cell4757.cap (5:Fin 18)).grade<cell4757.lowerGrade-cell4757.off:=by decide +kernel
def cell4758:PairCell.Row:=⟨64,654,12,2,50,some 50,35,some 35,257319,[MeasuredChoices.test64],[AxisChoices.test1798]⟩
theorem check4758:(cell4758.cap (5:Fin 18)).grade<cell4758.lowerGrade-cell4758.off:=by decide +kernel
def cell4759:PairCell.Row:=⟨64,654,12,2,50,some 50,36,some 36,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4759:(cell4759.cap (5:Fin 18)).grade<cell4759.lowerGrade-cell4759.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source3000

-- Source: Research6969.PairReceipts238
section Z6969Source3001
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4760:PairCell.Row:=⟨64,654,12,2,50,some 50,37,some 37,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4760:(cell4760.cap (5:Fin 18)).grade<cell4760.lowerGrade-cell4760.off:=by decide +kernel
def cell4761:PairCell.Row:=⟨64,654,12,2,50,some 50,38,some 38,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4761:(cell4761.cap (5:Fin 18)).grade<cell4761.lowerGrade-cell4761.off:=by decide +kernel
def cell4762:PairCell.Row:=⟨64,654,12,2,50,some 50,39,some 39,257319,[MeasuredChoices.test64],[AxisChoices.test1802]⟩
theorem check4762:(cell4762.cap (5:Fin 18)).grade<cell4762.lowerGrade-cell4762.off:=by decide +kernel
def cell4763:PairCell.Row:=⟨64,654,12,2,50,some 50,40,some 40,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4763:(cell4763.cap (5:Fin 18)).grade<cell4763.lowerGrade-cell4763.off:=by decide +kernel
def cell4764:PairCell.Row:=⟨64,654,12,2,50,some 50,41,some 41,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4764:(cell4764.cap (5:Fin 18)).grade<cell4764.lowerGrade-cell4764.off:=by decide +kernel
def cell4765:PairCell.Row:=⟨64,654,12,2,50,some 50,42,some 42,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4765:(cell4765.cap (5:Fin 18)).grade<cell4765.lowerGrade-cell4765.off:=by decide +kernel
def cell4766:PairCell.Row:=⟨64,654,12,2,50,some 50,43,some 43,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4766:(cell4766.cap (5:Fin 18)).grade<cell4766.lowerGrade-cell4766.off:=by decide +kernel
def cell4767:PairCell.Row:=⟨64,654,12,2,50,some 50,44,some 44,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4767:(cell4767.cap (5:Fin 18)).grade<cell4767.lowerGrade-cell4767.off:=by decide +kernel
def cell4768:PairCell.Row:=⟨64,654,12,2,50,some 50,45,some 45,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4768:(cell4768.cap (5:Fin 18)).grade<cell4768.lowerGrade-cell4768.off:=by decide +kernel
def cell4769:PairCell.Row:=⟨64,654,12,2,50,some 50,46,some 46,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4769:(cell4769.cap (5:Fin 18)).grade<cell4769.lowerGrade-cell4769.off:=by decide +kernel
def cell4770:PairCell.Row:=⟨64,654,12,2,50,some 50,47,some 47,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4770:(cell4770.cap (5:Fin 18)).grade<cell4770.lowerGrade-cell4770.off:=by decide +kernel
def cell4771:PairCell.Row:=⟨64,654,12,2,50,some 50,48,some 48,257319,[MeasuredChoices.test64],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4771:(cell4771.cap (5:Fin 18)).grade<cell4771.lowerGrade-cell4771.off:=by decide +kernel
def cell4772:PairCell.Row:=⟨64,654,12,2,50,some 50,49,some 49,257319,[MeasuredChoices.test64],[AxisChoices.test1812]⟩
theorem check4772:(cell4772.cap (5:Fin 18)).grade<cell4772.lowerGrade-cell4772.off:=by decide +kernel
def cell4773:PairCell.Row:=⟨64,654,12,2,50,some 50,50,some 50,257319,[MeasuredChoices.test64],[AxisChoices.test1813]⟩
theorem check4773:(cell4773.cap (5:Fin 18)).grade<cell4773.lowerGrade-cell4773.off:=by decide +kernel
private def rows4774 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,49,some 49,0,some 0,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,1,some 1,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,2,some 2,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,3,some 3,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,4,some 4,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,5,some 5,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩]
private theorem paid4774 : StockPairs.checked rows4774 = true := by decide +kernel
theorem route4774 (i : Fin 6) : (rows4774.get i).Done :=
  StockPairs.doneAt paid4774 i

end Research6969.PairReceipts
end Z6969Source3001

-- Source: Research6969.PairReceipts239
section Z6969Source3002
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4780 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,49,some 49,6,some 6,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,7,some 7,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,8,some 8,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,9,some 9,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,10,some 10,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,11,some 11,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[AxisChoices.test1774]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,12,some 12,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[AxisChoices.test1775]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,13,some 13,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[AxisChoices.test1776]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,14,some 14,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[AxisChoices.test1777]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,15,some 15,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[AxisChoices.test1778]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,16,some 16,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[AxisChoices.test1779]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,17,some 17,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[AxisChoices.test1780]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,18,some 18,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[AxisChoices.test1781]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,19,some 19,257319,[MeasuredChoices.test62],[AxisChoices.test1782]⟩,5,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,49,some 49,20,some 20,257319,[MeasuredChoices.test62],[AxisChoices.test1783]⟩,5,markedAxisWhole⟩]
private theorem paid4780 : StockPairs.checked rows4780 = true := by decide +kernel
theorem route4780 (i : Fin 15) : (rows4780.get i).Done :=
  StockPairs.doneAt paid4780 i

def cell4795:PairCell.Row:=⟨64,654,12,2,49,some 49,21,some 21,257319,[MeasuredChoices.test62],[AxisChoices.test1784]⟩
theorem check4795:(cell4795.cap (5:Fin 18)).grade<cell4795.lowerGrade-cell4795.off:=by decide +kernel
def cell4796:PairCell.Row:=⟨64,654,12,2,49,some 49,22,some 22,257319,[MeasuredChoices.test62],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4796:(cell4796.cap (5:Fin 18)).grade<cell4796.lowerGrade-cell4796.off:=by decide +kernel
def cell4797:PairCell.Row:=⟨64,654,12,2,49,some 49,23,some 23,257319,[MeasuredChoices.test62],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4797:(cell4797.cap (5:Fin 18)).grade<cell4797.lowerGrade-cell4797.off:=by decide +kernel
def cell4798:PairCell.Row:=⟨64,654,12,2,49,some 49,24,some 24,257319,[MeasuredChoices.test62],[AxisChoices.test1787]⟩
theorem check4798:(cell4798.cap (5:Fin 18)).grade<cell4798.lowerGrade-cell4798.off:=by decide +kernel
def cell4799:PairCell.Row:=⟨64,654,12,2,49,some 49,25,some 25,257319,[MeasuredChoices.test62],[AxisChoices.test1788]⟩
theorem check4799:(cell4799.cap (5:Fin 18)).grade<cell4799.lowerGrade-cell4799.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source3002

-- Source: Research6969.PairReceipts240
section Z6969Source3003
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4800:PairCell.Row:=⟨64,654,12,2,49,some 49,26,some 26,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4800:(cell4800.cap (5:Fin 18)).grade<cell4800.lowerGrade-cell4800.off:=by decide +kernel
def cell4801:PairCell.Row:=⟨64,654,12,2,49,some 49,27,some 27,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4801:(cell4801.cap (5:Fin 18)).grade<cell4801.lowerGrade-cell4801.off:=by decide +kernel
def cell4802:PairCell.Row:=⟨64,654,12,2,49,some 49,28,some 28,257319,[MeasuredChoices.test62],[AxisChoices.test1791]⟩
theorem check4802:(cell4802.cap (5:Fin 18)).grade<cell4802.lowerGrade-cell4802.off:=by decide +kernel
def cell4803:PairCell.Row:=⟨64,654,12,2,49,some 49,29,some 29,257319,[MeasuredChoices.test62],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4803:(cell4803.cap (5:Fin 18)).grade<cell4803.lowerGrade-cell4803.off:=by decide +kernel
def cell4804:PairCell.Row:=⟨64,654,12,2,49,some 49,30,some 30,257319,[MeasuredChoices.test62],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4804:(cell4804.cap (5:Fin 18)).grade<cell4804.lowerGrade-cell4804.off:=by decide +kernel
def cell4805:PairCell.Row:=⟨64,654,12,2,49,some 49,31,some 31,257319,[MeasuredChoices.test62],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4805:(cell4805.cap (5:Fin 18)).grade<cell4805.lowerGrade-cell4805.off:=by decide +kernel
def cell4806:PairCell.Row:=⟨64,654,12,2,49,some 49,32,some 32,257319,[MeasuredChoices.test62],[AxisChoices.test1795]⟩
theorem check4806:(cell4806.cap (5:Fin 18)).grade<cell4806.lowerGrade-cell4806.off:=by decide +kernel
def cell4807:PairCell.Row:=⟨64,654,12,2,49,some 49,33,some 33,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4807:(cell4807.cap (5:Fin 18)).grade<cell4807.lowerGrade-cell4807.off:=by decide +kernel
def cell4808:PairCell.Row:=⟨64,654,12,2,49,some 49,34,some 34,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4808:(cell4808.cap (5:Fin 18)).grade<cell4808.lowerGrade-cell4808.off:=by decide +kernel
def cell4809:PairCell.Row:=⟨64,654,12,2,49,some 49,35,some 35,257319,[MeasuredChoices.test62],[AxisChoices.test1798]⟩
theorem check4809:(cell4809.cap (5:Fin 18)).grade<cell4809.lowerGrade-cell4809.off:=by decide +kernel
def cell4810:PairCell.Row:=⟨64,654,12,2,49,some 49,36,some 36,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4810:(cell4810.cap (5:Fin 18)).grade<cell4810.lowerGrade-cell4810.off:=by decide +kernel
def cell4811:PairCell.Row:=⟨64,654,12,2,49,some 49,37,some 37,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4811:(cell4811.cap (5:Fin 18)).grade<cell4811.lowerGrade-cell4811.off:=by decide +kernel
def cell4812:PairCell.Row:=⟨64,654,12,2,49,some 49,38,some 38,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4812:(cell4812.cap (5:Fin 18)).grade<cell4812.lowerGrade-cell4812.off:=by decide +kernel
def cell4813:PairCell.Row:=⟨64,654,12,2,49,some 49,39,some 39,257319,[MeasuredChoices.test62],[AxisChoices.test1802]⟩
theorem check4813:(cell4813.cap (5:Fin 18)).grade<cell4813.lowerGrade-cell4813.off:=by decide +kernel
def cell4814:PairCell.Row:=⟨64,654,12,2,49,some 49,40,some 40,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4814:(cell4814.cap (5:Fin 18)).grade<cell4814.lowerGrade-cell4814.off:=by decide +kernel
def cell4815:PairCell.Row:=⟨64,654,12,2,49,some 49,41,some 41,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4815:(cell4815.cap (5:Fin 18)).grade<cell4815.lowerGrade-cell4815.off:=by decide +kernel
def cell4816:PairCell.Row:=⟨64,654,12,2,49,some 49,42,some 42,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4816:(cell4816.cap (5:Fin 18)).grade<cell4816.lowerGrade-cell4816.off:=by decide +kernel
def cell4817:PairCell.Row:=⟨64,654,12,2,49,some 49,43,some 43,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4817:(cell4817.cap (5:Fin 18)).grade<cell4817.lowerGrade-cell4817.off:=by decide +kernel
def cell4818:PairCell.Row:=⟨64,654,12,2,49,some 49,44,some 44,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4818:(cell4818.cap (5:Fin 18)).grade<cell4818.lowerGrade-cell4818.off:=by decide +kernel
def cell4819:PairCell.Row:=⟨64,654,12,2,49,some 49,45,some 45,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4819:(cell4819.cap (5:Fin 18)).grade<cell4819.lowerGrade-cell4819.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source3003

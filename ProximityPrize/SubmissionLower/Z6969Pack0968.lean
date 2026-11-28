import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0673
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0967
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0939

set_option Elab.async false

-- Source: Research6969.HardFit5At000
section Z6969Source2956
set_option autoImplicit true
namespace Research6969.HardFit5At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4200 6)
theorem case0: NormalRoute.Done (4:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4200 5)
theorem case1: NormalRoute.Done (4:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4200 4)
theorem case2: NormalRoute.Done (4:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4200 3)
theorem case3: NormalRoute.Done (4:Fin 18) ⟨25,27,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4200 2)
theorem case4: NormalRoute.Done (4:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4220 10)
theorem case5: NormalRoute.Done (4:Fin 18) ⟨25,27,9,3,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4220 9)
theorem case6: NormalRoute.Done (4:Fin 18) ⟨25,27,9,3,13,some 16⟩:=PairRoute.start _ leaf6
private theorem allAxes48:PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,17,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route4200 8),
    (PairReceipts.route4200 9),
    (PairReceipts.route4200 10),
    (PairReceipts.route4200 11),
    (PairReceipts.route4200 12),
    (PairReceipts.route4200 13),
    (PairReceipts.route4200 14),
    (PairReceipts.route4200 15),
    (PairReceipts.route4200 16),
    (PairReceipts.route4200 17),
    (PairReceipts.route4200 18),
    (PairReceipts.route4200 19),
    (PairReceipts.route4220 0),
    (PairReceipts.route4220 1),
    (PairReceipts.route4220 2),
    (PairReceipts.route4220 3),
    (PairReceipts.route4220 4),
    (PairReceipts.route4220 5),
    (PairReceipts.route4220 6),
    (PairReceipts.route4220 7),
    (PairReceipts.route4220 8),
    trivial⟩)
theorem case7: NormalRoute.Done (4:Fin 18) ⟨25,27,9,3,17,some 20⟩:=PairRoute.start _ allAxes48
private def leaf49 := (PairReceipts.route4200 7)
theorem case8: NormalRoute.Done (4:Fin 18) ⟨25,27,9,3,21,some 24⟩:=PairRoute.start _ leaf49
private def leaf50 := (PairReceipts.route4220 15)
theorem case9: NormalRoute.Done (4:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf50
end Research6969.HardFit5At000
end Z6969Source2956

-- Source: Research6969.PairReceipts212
section Z6969Source2957
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4240 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,4,some 8,0,none,257319,[],[]⟩,4,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨33,40,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,17,some 18,0,none,385979,[MeasuredChoices.test821],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,0,some 0,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,1,some 1,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,2,some 2,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,3,some 3,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,4,some 4,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,5,some 5,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩]
private theorem paid4240 : StockPairs.checked rows4240 = true := by decide +kernel
theorem route4240 (i : Fin 20) : (rows4240.get i).Done :=
  StockPairs.doneAt paid4240 i

end Research6969.PairReceipts
end Z6969Source2957

-- Source: Research6969.HardFit5At010
section Z6969Source2958
set_option autoImplicit true
namespace Research6969.HardFit5At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4220 14)
theorem case10: NormalRoute.Done (4:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4220 13)
theorem case11: NormalRoute.Done (4:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4220 12)
theorem case12: NormalRoute.Done (4:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4220 11)
theorem case13: NormalRoute.Done (4:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4240 0)
theorem case14: NormalRoute.Done (4:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4220 19)
theorem case15: NormalRoute.Done (4:Fin 18) ⟨28,32,9,3,13,some 16⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4220 18)
theorem case16: NormalRoute.Done (4:Fin 18) ⟨28,32,9,3,17,some 18⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4220 17)
theorem case17: NormalRoute.Done (4:Fin 18) ⟨28,32,9,3,19,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4220 16)
theorem case18: NormalRoute.Done (4:Fin 18) ⟨28,32,9,3,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4240 6)
theorem case19: NormalRoute.Done (4:Fin 18) ⟨33,40,9,2,4,some 8⟩:=PairRoute.start _ leaf9
end Research6969.HardFit5At010
end Z6969Source2958

-- Source: Research6969.HardFit5At020
section Z6969Source2959
set_option autoImplicit true
namespace Research6969.HardFit5At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4240 5)
theorem case20: NormalRoute.Done (4:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4240 4)
theorem case21: NormalRoute.Done (4:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4240 3)
theorem case22: NormalRoute.Done (4:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4240 2)
theorem case23: NormalRoute.Done (4:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4240 1)
theorem case24: NormalRoute.Done (4:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4240 13)
theorem case25: NormalRoute.Done (4:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4240 12)
theorem case26: NormalRoute.Done (4:Fin 18) ⟨33,40,9,3,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4240 11)
theorem case27: NormalRoute.Done (4:Fin 18) ⟨33,40,9,3,17,some 18⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4240 10)
theorem case28: NormalRoute.Done (4:Fin 18) ⟨33,40,9,3,19,some 20⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4240 9)
theorem case29: NormalRoute.Done (4:Fin 18) ⟨33,40,9,3,21,some 24⟩:=PairRoute.start _ leaf9
end Research6969.HardFit5At020
end Z6969Source2959

-- Source: Research6969.PairReceipts213
section Z6969Source2960
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4260 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,6,some 6,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,7,some 7,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,8,some 8,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,9,some 9,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,10,some 10,257319,[MeasuredChoices.test62],[]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,11,some 11,257319,[MeasuredChoices.test62],[AxisChoices.test1774]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,12,some 12,257319,[MeasuredChoices.test62],[AxisChoices.test1775]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,13,some 13,257319,[MeasuredChoices.test62],[AxisChoices.test1776]⟩,4,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,14,some 14,257319,[MeasuredChoices.test62],[AxisChoices.test1777]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,15,some 15,257319,[MeasuredChoices.test62],[AxisChoices.test1778]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,16,some 16,257319,[MeasuredChoices.test62],[AxisChoices.test1779]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,17,some 17,257319,[MeasuredChoices.test62],[AxisChoices.test1780]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,18,some 18,257319,[MeasuredChoices.test62],[AxisChoices.test1781]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,19,some 19,257319,[MeasuredChoices.test62],[AxisChoices.test1782]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,20,some 20,257319,[MeasuredChoices.test62],[AxisChoices.test1783]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,21,some 21,257319,[MeasuredChoices.test62],[AxisChoices.test1784]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,22,some 22,257319,[MeasuredChoices.test62],[AxisChoices.test1785]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,23,some 23,257319,[MeasuredChoices.test62],[AxisChoices.test1786]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,24,some 24,257319,[MeasuredChoices.test62],[AxisChoices.test1787]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,25,some 25,257319,[MeasuredChoices.test62],[AxisChoices.test1788]⟩,4,markedAxisIntersection⟩]
private theorem paid4260 : StockPairs.checked rows4260 = true := by decide +kernel
theorem route4260 (i : Fin 20) : (rows4260.get i).Done :=
  StockPairs.doneAt paid4260 i

end Research6969.PairReceipts
end Z6969Source2960

-- Source: Research6969.PairReceipts214
section Z6969Source2961
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4280 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,26,some 26,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1789]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,27,some 27,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1790]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,28,some 28,257319,[MeasuredChoices.test62],[AxisChoices.test1791]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,29,some 29,257319,[MeasuredChoices.test62],[AxisChoices.test1791,AxisChoices.test1792]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,30,some 30,257319,[MeasuredChoices.test62],[AxisChoices.test1792,AxisChoices.test1793]⟩,4,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,31,some 31,257319,[MeasuredChoices.test62],[AxisChoices.test1793,AxisChoices.test1794]⟩,4,markedAxisIntersection⟩]
private theorem paid4280 : StockPairs.checked rows4280 = true := by decide +kernel
theorem route4280 (i : Fin 6) : (rows4280.get i).Done :=
  StockPairs.doneAt paid4280 i

def cell4286:PairCell.Row:=⟨41,49,9,2,49,some 64,32,some 32,257319,[MeasuredChoices.test62],[AxisChoices.test1795]⟩
theorem check4286:(cell4286.cap (4:Fin 18)).grade<cell4286.lowerGrade-cell4286.off:=by decide +kernel
def cell4287:PairCell.Row:=⟨41,49,9,2,49,some 64,33,some 33,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4287:(cell4287.cap (4:Fin 18)).grade<cell4287.lowerGrade-cell4287.off:=by decide +kernel
def cell4288:PairCell.Row:=⟨41,49,9,2,49,some 64,34,some 34,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4288:(cell4288.cap (4:Fin 18)).grade<cell4288.lowerGrade-cell4288.off:=by decide +kernel
def cell4289:PairCell.Row:=⟨41,49,9,2,49,some 64,35,some 35,257319,[MeasuredChoices.test62],[AxisChoices.test1798]⟩
theorem check4289:(cell4289.cap (4:Fin 18)).grade<cell4289.lowerGrade-cell4289.off:=by decide +kernel
def cell4290:PairCell.Row:=⟨41,49,9,2,49,some 64,36,some 36,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4290:(cell4290.cap (4:Fin 18)).grade<cell4290.lowerGrade-cell4290.off:=by decide +kernel
def cell4291:PairCell.Row:=⟨41,49,9,2,49,some 64,37,some 37,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4291:(cell4291.cap (4:Fin 18)).grade<cell4291.lowerGrade-cell4291.off:=by decide +kernel
def cell4292:PairCell.Row:=⟨41,49,9,2,49,some 64,38,some 38,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4292:(cell4292.cap (4:Fin 18)).grade<cell4292.lowerGrade-cell4292.off:=by decide +kernel
def cell4293:PairCell.Row:=⟨41,49,9,2,49,some 64,39,some 39,257319,[MeasuredChoices.test62],[AxisChoices.test1802]⟩
theorem check4293:(cell4293.cap (4:Fin 18)).grade<cell4293.lowerGrade-cell4293.off:=by decide +kernel
def cell4294:PairCell.Row:=⟨41,49,9,2,49,some 64,40,some 40,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4294:(cell4294.cap (4:Fin 18)).grade<cell4294.lowerGrade-cell4294.off:=by decide +kernel
def cell4295:PairCell.Row:=⟨41,49,9,2,49,some 64,41,some 41,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4295:(cell4295.cap (4:Fin 18)).grade<cell4295.lowerGrade-cell4295.off:=by decide +kernel
def cell4296:PairCell.Row:=⟨41,49,9,2,49,some 64,42,some 42,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4296:(cell4296.cap (4:Fin 18)).grade<cell4296.lowerGrade-cell4296.off:=by decide +kernel
def cell4297:PairCell.Row:=⟨41,49,9,2,49,some 64,43,some 43,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4297:(cell4297.cap (4:Fin 18)).grade<cell4297.lowerGrade-cell4297.off:=by decide +kernel
def cell4298:PairCell.Row:=⟨41,49,9,2,49,some 64,44,some 44,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4298:(cell4298.cap (4:Fin 18)).grade<cell4298.lowerGrade-cell4298.off:=by decide +kernel
def cell4299:PairCell.Row:=⟨41,49,9,2,49,some 64,45,some 45,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4299:(cell4299.cap (4:Fin 18)).grade<cell4299.lowerGrade-cell4299.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2961

-- Source: Research6969.PairReceipts215
section Z6969Source2962
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4300:PairCell.Row:=⟨41,49,9,2,49,some 64,46,some 46,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4300:(cell4300.cap (4:Fin 18)).grade<cell4300.lowerGrade-cell4300.off:=by decide +kernel
def cell4301:PairCell.Row:=⟨41,49,9,2,49,some 64,47,some 47,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4301:(cell4301.cap (4:Fin 18)).grade<cell4301.lowerGrade-cell4301.off:=by decide +kernel
def cell4302:PairCell.Row:=⟨41,49,9,2,49,some 64,48,some 48,257319,[MeasuredChoices.test62],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4302:(cell4302.cap (4:Fin 18)).grade<cell4302.lowerGrade-cell4302.off:=by decide +kernel
def cell4303:PairCell.Row:=⟨41,49,9,2,49,some 64,49,some 49,257319,[MeasuredChoices.test62],[AxisChoices.test1812]⟩
theorem check4303:(cell4303.cap (4:Fin 18)).grade<cell4303.lowerGrade-cell4303.off:=by decide +kernel
def cell4304:PairCell.Row:=⟨41,49,9,2,49,some 64,50,some 50,257319,[MeasuredChoices.test62],[AxisChoices.test1813]⟩
theorem check4304:(cell4304.cap (4:Fin 18)).grade<cell4304.lowerGrade-cell4304.off:=by decide +kernel
def cell4305:PairCell.Row:=⟨41,49,9,2,49,some 64,51,some 51,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4305:(cell4305.cap (4:Fin 18)).grade<cell4305.lowerGrade-cell4305.off:=by decide +kernel
def cell4306:PairCell.Row:=⟨41,49,9,2,49,some 64,52,some 52,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4306:(cell4306.cap (4:Fin 18)).grade<cell4306.lowerGrade-cell4306.off:=by decide +kernel
def cell4307:PairCell.Row:=⟨41,49,9,2,49,some 64,53,some 53,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check4307:(cell4307.cap (4:Fin 18)).grade<cell4307.lowerGrade-cell4307.off:=by decide +kernel
def cell4308:PairCell.Row:=⟨41,49,9,2,49,some 64,54,some 54,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check4308:(cell4308.cap (4:Fin 18)).grade<cell4308.lowerGrade-cell4308.off:=by decide +kernel
def cell4309:PairCell.Row:=⟨41,49,9,2,49,some 64,55,some 55,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check4309:(cell4309.cap (4:Fin 18)).grade<cell4309.lowerGrade-cell4309.off:=by decide +kernel
def cell4310:PairCell.Row:=⟨41,49,9,2,49,some 64,56,some 56,257319,[MeasuredChoices.test62],[AxisChoices.test1819]⟩
theorem check4310:(cell4310.cap (4:Fin 18)).grade<cell4310.lowerGrade-cell4310.off:=by decide +kernel
def cell4311:PairCell.Row:=⟨41,49,9,2,49,some 64,57,some 57,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4311:(cell4311.cap (4:Fin 18)).grade<cell4311.lowerGrade-cell4311.off:=by decide +kernel
def cell4312:PairCell.Row:=⟨41,49,9,2,49,some 64,58,some 58,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4312:(cell4312.cap (4:Fin 18)).grade<cell4312.lowerGrade-cell4312.off:=by decide +kernel
def cell4313:PairCell.Row:=⟨41,49,9,2,49,some 64,59,some 59,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4313:(cell4313.cap (4:Fin 18)).grade<cell4313.lowerGrade-cell4313.off:=by decide +kernel
def cell4314:PairCell.Row:=⟨41,49,9,2,49,some 64,60,some 60,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4314:(cell4314.cap (4:Fin 18)).grade<cell4314.lowerGrade-cell4314.off:=by decide +kernel
def cell4315:PairCell.Row:=⟨41,49,9,2,49,some 64,61,some 61,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4315:(cell4315.cap (4:Fin 18)).grade<cell4315.lowerGrade-cell4315.off:=by decide +kernel
def cell4316:PairCell.Row:=⟨41,49,9,2,49,some 64,62,some 62,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4316:(cell4316.cap (4:Fin 18)).grade<cell4316.lowerGrade-cell4316.off:=by decide +kernel
def cell4317:PairCell.Row:=⟨41,49,9,2,49,some 64,63,some 63,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4317:(cell4317.cap (4:Fin 18)).grade<cell4317.lowerGrade-cell4317.off:=by decide +kernel
def cell4318:PairCell.Row:=⟨41,49,9,2,49,some 64,64,some 64,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4318:(cell4318.cap (4:Fin 18)).grade<cell4318.lowerGrade-cell4318.off:=by decide +kernel
private def rows4319 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,4,surfaceIntersection⟩]
private theorem paid4319 : StockPairs.checked rows4319 = true := by decide +kernel
theorem route4319 (i : Fin 1) : (rows4319.get i).Done :=
  StockPairs.doneAt paid4319 i
end Research6969.PairReceipts
end Z6969Source2962

-- Source: Research6969.PairReceipts216
section Z6969Source2963
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4320 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,4,some 8,0,none,257319,[],[]⟩,4,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨41,49,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩,4,markedIntersection⟩,
  ⟨⟨41,49,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,17,some 18,0,none,385979,[MeasuredChoices.test821],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,4,⟨(.node 8025893007439878),.intersection,.impossible,283522⟩⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩,4,markedIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,0,some 0,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,1,some 1,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,2,some 2,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,3,some 3,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩]
private theorem paid4320 : StockPairs.checked rows4320 = true := by decide +kernel
theorem route4320 (i : Fin 20) : (rows4320.get i).Done :=
  StockPairs.doneAt paid4320 i

end Research6969.PairReceipts
end Z6969Source2963

-- Source: Research6969.HardFit5At030
section Z6969Source2964
set_option autoImplicit true
namespace Research6969.HardFit5At030
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4240 8)
theorem case30: NormalRoute.Done (4:Fin 18) ⟨33,40,9,3,25,some 28⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4240 7)
theorem case31: NormalRoute.Done (4:Fin 18) ⟨33,40,9,3,33,some 40⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4320 4)
theorem case32: NormalRoute.Done (4:Fin 18) ⟨41,49,9,2,4,some 8⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4320 3)
theorem case33: NormalRoute.Done (4:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4320 2)
theorem case34: NormalRoute.Done (4:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4320 1)
theorem case35: NormalRoute.Done (4:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4320 0)
theorem case36: NormalRoute.Done (4:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4319 0)
theorem case37: NormalRoute.Done (4:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ leaf7
private theorem allAxes137:PairRoute.Done (4:Fin 18) ⟨⟨41,49,9,2,49,some 64⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 64 ⟨
    (PairReceipts.route4240 14),
    (PairReceipts.route4240 15),
    (PairReceipts.route4240 16),
    (PairReceipts.route4240 17),
    (PairReceipts.route4240 18),
    (PairReceipts.route4240 19),
    (PairReceipts.route4260 0),
    (PairReceipts.route4260 1),
    (PairReceipts.route4260 2),
    (PairReceipts.route4260 3),
    (PairReceipts.route4260 4),
    (PairReceipts.route4260 5),
    (PairReceipts.route4260 6),
    (PairReceipts.route4260 7),
    (PairReceipts.route4260 8),
    (PairReceipts.route4260 9),
    (PairReceipts.route4260 10),
    (PairReceipts.route4260 11),
    (PairReceipts.route4260 12),
    (PairReceipts.route4260 13),
    (PairReceipts.route4260 14),
    (PairReceipts.route4260 15),
    (PairReceipts.route4260 16),
    (PairReceipts.route4260 17),
    (PairReceipts.route4260 18),
    (PairReceipts.route4260 19),
    (PairReceipts.route4280 0),
    (PairReceipts.route4280 1),
    (PairReceipts.route4280 2),
    (PairReceipts.route4280 3),
    (PairReceipts.route4280 4),
    (PairReceipts.route4280 5),
    PairLeaves.excluded PairReceipts.cell4286 PairReceipts.check4286 (none),
    PairLeaves.excluded PairReceipts.cell4287 PairReceipts.check4287 (none),
    PairLeaves.excluded PairReceipts.cell4288 PairReceipts.check4288 (none),
    PairLeaves.excluded PairReceipts.cell4289 PairReceipts.check4289 (none),
    PairLeaves.excluded PairReceipts.cell4290 PairReceipts.check4290 (none),
    PairLeaves.excluded PairReceipts.cell4291 PairReceipts.check4291 (none),
    PairLeaves.excluded PairReceipts.cell4292 PairReceipts.check4292 (none),
    PairLeaves.excluded PairReceipts.cell4293 PairReceipts.check4293 (none),
    PairLeaves.excluded PairReceipts.cell4294 PairReceipts.check4294 (none),
    PairLeaves.excluded PairReceipts.cell4295 PairReceipts.check4295 (none),
    PairLeaves.excluded PairReceipts.cell4296 PairReceipts.check4296 (none),
    PairLeaves.excluded PairReceipts.cell4297 PairReceipts.check4297 (none),
    PairLeaves.excluded PairReceipts.cell4298 PairReceipts.check4298 (none),
    PairLeaves.excluded PairReceipts.cell4299 PairReceipts.check4299 (none),
    PairLeaves.excluded PairReceipts.cell4300 PairReceipts.check4300 (none),
    PairLeaves.excluded PairReceipts.cell4301 PairReceipts.check4301 (none),
    PairLeaves.excluded PairReceipts.cell4302 PairReceipts.check4302 (none),
    PairLeaves.excluded PairReceipts.cell4303 PairReceipts.check4303 (none),
    PairLeaves.excluded PairReceipts.cell4304 PairReceipts.check4304 (none),
    PairLeaves.excluded PairReceipts.cell4305 PairReceipts.check4305 (none),
    PairLeaves.excluded PairReceipts.cell4306 PairReceipts.check4306 (none),
    PairLeaves.excluded PairReceipts.cell4307 PairReceipts.check4307 (none),
    PairLeaves.excluded PairReceipts.cell4308 PairReceipts.check4308 (none),
    PairLeaves.excluded PairReceipts.cell4309 PairReceipts.check4309 (none),
    PairLeaves.excluded PairReceipts.cell4310 PairReceipts.check4310 (none),
    PairLeaves.excluded PairReceipts.cell4311 PairReceipts.check4311 (none),
    PairLeaves.excluded PairReceipts.cell4312 PairReceipts.check4312 (none),
    PairLeaves.excluded PairReceipts.cell4313 PairReceipts.check4313 (none),
    PairLeaves.excluded PairReceipts.cell4314 PairReceipts.check4314 (none),
    PairLeaves.excluded PairReceipts.cell4315 PairReceipts.check4315 (none),
    PairLeaves.excluded PairReceipts.cell4316 PairReceipts.check4316 (none),
    PairLeaves.excluded PairReceipts.cell4317 PairReceipts.check4317 (none),
    PairLeaves.excluded PairReceipts.cell4318 PairReceipts.check4318 (none),
    trivial⟩)
theorem case38: NormalRoute.Done (4:Fin 18) ⟨41,49,9,2,49,some 64⟩:=PairRoute.start _ allAxes137
private def leaf138 := (PairReceipts.route4320 13)
theorem case39: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf138
end Research6969.HardFit5At030
end Z6969Source2964

-- Source: Research6969.PairReceipts220
section Z6969Source2965
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4400 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,4,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,37,some 40,0,none,385979,[MeasuredChoices.test1079],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,21,some 22,0,none,385979,[MeasuredChoices.test869],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,17,some 18,0,none,385979,[MeasuredChoices.test821],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,15,some 16,0,none,385979,[MeasuredChoices.test797],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,4,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,654,12,2,51,some 51,0,some 0,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩]
private theorem paid4400 : StockPairs.checked rows4400 = true := by decide +kernel
theorem route4400 (i : Fin 19) : (rows4400.get i).Done :=
  StockPairs.doneAt paid4400 i

def cell4418:PairCell.Row:=⟨64,654,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩
theorem check4418:(cell4418.cap (4:Fin 18)).grade<cell4418.lowerGrade-cell4418.off:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2965

-- Source: Research6969.HardFit5At040
section Z6969Source2966
set_option autoImplicit true
namespace Research6969.HardFit5At040
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4320 12)
theorem case40: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,13,some 16⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4320 11)
theorem case41: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,17,some 18⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4320 10)
theorem case42: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,19,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4320 9)
theorem case43: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4320 8)
theorem case44: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4320 7)
theorem case45: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,33,some 40⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4320 6)
theorem case46: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,41,some 48⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4320 5)
theorem case47: NormalRoute.Done (4:Fin 18) ⟨41,49,9,3,49,some 64⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4400 5)
theorem case48: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,9,some 12⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4400 4)
theorem case49: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6969.HardFit5At040
end Z6969Source2966

-- Source: Research6969.PairReceipts217
section Z6969Source2967
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4340 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,57,some 57,4,some 4,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,5,some 5,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,6,some 6,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,7,some 7,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,8,some 8,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,9,some 9,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,10,some 10,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,11,some 11,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1774]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,12,some 12,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1775]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,13,some 13,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1776]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,14,some 14,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1777]⟩,4,separateIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,15,some 15,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1778]⟩,4,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,16,some 16,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1779]⟩,4,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,17,some 17,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1780]⟩,4,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,18,some 18,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1781]⟩,4,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,19,some 19,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1782]⟩,4,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,20,some 20,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1783]⟩,4,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,21,some 21,257319,[MeasuredChoices.test79],[AxisChoices.test1784]⟩,4,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,22,some 22,257319,[MeasuredChoices.test79],[AxisChoices.test1784,AxisChoices.test1785]⟩,4,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,57,some 57,23,some 23,257319,[MeasuredChoices.test79],[AxisChoices.test1784,AxisChoices.test1786]⟩,4,markedAxisIntersection⟩]
private theorem paid4340 : StockPairs.checked rows4340 = true := by decide +kernel
theorem route4340 (i : Fin 20) : (rows4340.get i).Done :=
  StockPairs.doneAt paid4340 i

end Research6969.PairReceipts
end Z6969Source2967

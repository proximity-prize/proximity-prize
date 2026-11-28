import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0673
import ProximityPrize.SubmissionLower.Z6969Pack0968
import ProximityPrize.SubmissionLower.Z6969Pack0682

set_option Elab.async false

-- Source: Research6969.PairReceipts218
section Z6969Source2968
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4360 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,57,some 57,24,some 24,257319,[MeasuredChoices.test79],[AxisChoices.test1787]⟩,4,markedAxisIntersection⟩]
private theorem paid4360 : StockPairs.checked rows4360 = true := by decide +kernel
theorem route4360 (i : Fin 1) : (rows4360.get i).Done :=
  StockPairs.doneAt paid4360 i
def cell4361:PairCell.Row:=⟨50,63,10,2,57,some 57,25,some 25,257319,[MeasuredChoices.test79],[AxisChoices.test1788]⟩
theorem check4361:(cell4361.cap (4:Fin 18)).grade<cell4361.lowerGrade-cell4361.off:=by decide +kernel
def cell4362:PairCell.Row:=⟨50,63,10,2,57,some 57,26,some 26,257319,[MeasuredChoices.test79],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4362:(cell4362.cap (4:Fin 18)).grade<cell4362.lowerGrade-cell4362.off:=by decide +kernel
def cell4363:PairCell.Row:=⟨50,63,10,2,57,some 57,27,some 27,257319,[MeasuredChoices.test79],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4363:(cell4363.cap (4:Fin 18)).grade<cell4363.lowerGrade-cell4363.off:=by decide +kernel
def cell4364:PairCell.Row:=⟨50,63,10,2,57,some 57,28,some 28,257319,[MeasuredChoices.test79],[AxisChoices.test1791]⟩
theorem check4364:(cell4364.cap (4:Fin 18)).grade<cell4364.lowerGrade-cell4364.off:=by decide +kernel
def cell4365:PairCell.Row:=⟨50,63,10,2,57,some 57,29,some 29,257319,[MeasuredChoices.test79],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4365:(cell4365.cap (4:Fin 18)).grade<cell4365.lowerGrade-cell4365.off:=by decide +kernel
def cell4366:PairCell.Row:=⟨50,63,10,2,57,some 57,30,some 30,257319,[MeasuredChoices.test79],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4366:(cell4366.cap (4:Fin 18)).grade<cell4366.lowerGrade-cell4366.off:=by decide +kernel
def cell4367:PairCell.Row:=⟨50,63,10,2,57,some 57,31,some 31,257319,[MeasuredChoices.test79],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4367:(cell4367.cap (4:Fin 18)).grade<cell4367.lowerGrade-cell4367.off:=by decide +kernel
def cell4368:PairCell.Row:=⟨50,63,10,2,57,some 57,32,some 32,257319,[MeasuredChoices.test79],[AxisChoices.test1795]⟩
theorem check4368:(cell4368.cap (4:Fin 18)).grade<cell4368.lowerGrade-cell4368.off:=by decide +kernel
def cell4369:PairCell.Row:=⟨50,63,10,2,57,some 57,33,some 33,257319,[MeasuredChoices.test79],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4369:(cell4369.cap (4:Fin 18)).grade<cell4369.lowerGrade-cell4369.off:=by decide +kernel
def cell4370:PairCell.Row:=⟨50,63,10,2,57,some 57,34,some 34,257319,[MeasuredChoices.test79],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4370:(cell4370.cap (4:Fin 18)).grade<cell4370.lowerGrade-cell4370.off:=by decide +kernel
def cell4371:PairCell.Row:=⟨50,63,10,2,57,some 57,35,some 35,257319,[MeasuredChoices.test79],[AxisChoices.test1798]⟩
theorem check4371:(cell4371.cap (4:Fin 18)).grade<cell4371.lowerGrade-cell4371.off:=by decide +kernel
def cell4372:PairCell.Row:=⟨50,63,10,2,57,some 57,36,some 36,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4372:(cell4372.cap (4:Fin 18)).grade<cell4372.lowerGrade-cell4372.off:=by decide +kernel
def cell4373:PairCell.Row:=⟨50,63,10,2,57,some 57,37,some 37,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4373:(cell4373.cap (4:Fin 18)).grade<cell4373.lowerGrade-cell4373.off:=by decide +kernel
def cell4374:PairCell.Row:=⟨50,63,10,2,57,some 57,38,some 38,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4374:(cell4374.cap (4:Fin 18)).grade<cell4374.lowerGrade-cell4374.off:=by decide +kernel
def cell4375:PairCell.Row:=⟨50,63,10,2,57,some 57,39,some 39,257319,[MeasuredChoices.test79],[AxisChoices.test1802]⟩
theorem check4375:(cell4375.cap (4:Fin 18)).grade<cell4375.lowerGrade-cell4375.off:=by decide +kernel
def cell4376:PairCell.Row:=⟨50,63,10,2,57,some 57,40,some 40,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4376:(cell4376.cap (4:Fin 18)).grade<cell4376.lowerGrade-cell4376.off:=by decide +kernel
def cell4377:PairCell.Row:=⟨50,63,10,2,57,some 57,41,some 41,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4377:(cell4377.cap (4:Fin 18)).grade<cell4377.lowerGrade-cell4377.off:=by decide +kernel
def cell4378:PairCell.Row:=⟨50,63,10,2,57,some 57,42,some 42,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4378:(cell4378.cap (4:Fin 18)).grade<cell4378.lowerGrade-cell4378.off:=by decide +kernel
def cell4379:PairCell.Row:=⟨50,63,10,2,57,some 57,43,some 43,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4379:(cell4379.cap (4:Fin 18)).grade<cell4379.lowerGrade-cell4379.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2968

-- Source: Research6969.PairReceipts219
section Z6969Source2969
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4380:PairCell.Row:=⟨50,63,10,2,57,some 57,44,some 44,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4380:(cell4380.cap (4:Fin 18)).grade<cell4380.lowerGrade-cell4380.off:=by decide +kernel
def cell4381:PairCell.Row:=⟨50,63,10,2,57,some 57,45,some 45,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4381:(cell4381.cap (4:Fin 18)).grade<cell4381.lowerGrade-cell4381.off:=by decide +kernel
def cell4382:PairCell.Row:=⟨50,63,10,2,57,some 57,46,some 46,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4382:(cell4382.cap (4:Fin 18)).grade<cell4382.lowerGrade-cell4382.off:=by decide +kernel
def cell4383:PairCell.Row:=⟨50,63,10,2,57,some 57,47,some 47,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4383:(cell4383.cap (4:Fin 18)).grade<cell4383.lowerGrade-cell4383.off:=by decide +kernel
def cell4384:PairCell.Row:=⟨50,63,10,2,57,some 57,48,some 48,257319,[MeasuredChoices.test79],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4384:(cell4384.cap (4:Fin 18)).grade<cell4384.lowerGrade-cell4384.off:=by decide +kernel
def cell4385:PairCell.Row:=⟨50,63,10,2,57,some 57,49,some 49,257319,[MeasuredChoices.test79],[AxisChoices.test1812]⟩
theorem check4385:(cell4385.cap (4:Fin 18)).grade<cell4385.lowerGrade-cell4385.off:=by decide +kernel
def cell4386:PairCell.Row:=⟨50,63,10,2,57,some 57,50,some 50,257319,[MeasuredChoices.test79],[AxisChoices.test1813]⟩
theorem check4386:(cell4386.cap (4:Fin 18)).grade<cell4386.lowerGrade-cell4386.off:=by decide +kernel
def cell4387:PairCell.Row:=⟨50,63,10,2,57,some 57,51,some 51,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4387:(cell4387.cap (4:Fin 18)).grade<cell4387.lowerGrade-cell4387.off:=by decide +kernel
def cell4388:PairCell.Row:=⟨50,63,10,2,57,some 57,52,some 52,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4388:(cell4388.cap (4:Fin 18)).grade<cell4388.lowerGrade-cell4388.off:=by decide +kernel
def cell4389:PairCell.Row:=⟨50,63,10,2,57,some 57,53,some 53,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check4389:(cell4389.cap (4:Fin 18)).grade<cell4389.lowerGrade-cell4389.off:=by decide +kernel
def cell4390:PairCell.Row:=⟨50,63,10,2,57,some 57,54,some 54,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check4390:(cell4390.cap (4:Fin 18)).grade<cell4390.lowerGrade-cell4390.off:=by decide +kernel
def cell4391:PairCell.Row:=⟨50,63,10,2,57,some 57,55,some 55,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check4391:(cell4391.cap (4:Fin 18)).grade<cell4391.lowerGrade-cell4391.off:=by decide +kernel
def cell4392:PairCell.Row:=⟨50,63,10,2,57,some 57,56,some 56,257319,[MeasuredChoices.test79],[AxisChoices.test1819]⟩
theorem check4392:(cell4392.cap (4:Fin 18)).grade<cell4392.lowerGrade-cell4392.off:=by decide +kernel
def cell4393:PairCell.Row:=⟨50,63,10,2,57,some 57,57,some 57,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4393:(cell4393.cap (4:Fin 18)).grade<cell4393.lowerGrade-cell4393.off:=by decide +kernel
private def rows4394 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,53,some 56,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test71],[]⟩,4,⟨(.node 8026411704957730),.intersection,.impossible,285209⟩⟩,
  ⟨⟨50,63,10,2,53,some 56,0,none,285209,[MeasuredChoices.test70,MeasuredChoices.test111],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,49,some 52,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,4,surfaceIntersection⟩]
private theorem paid4394 : StockPairs.checked rows4394 = true := by decide +kernel
theorem route4394 (i : Fin 6) : (rows4394.get i).Done :=
  StockPairs.doneAt paid4394 i

end Research6969.PairReceipts
end Z6969Source2969

-- Source: Research6969.HardFit5At050
section Z6969Source2970
set_option autoImplicit true
namespace Research6969.HardFit5At050
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4400 3)
theorem case50: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4400 2)
theorem case51: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4400 0)
private def leaf3 := (PairReceipts.route4400 1)
private def weight4 := PairRoute.weight 302619 leaf2 leaf3
theorem case52: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,25,some 28⟩:=PairRoute.start _ weight4
private def leaf5 := (PairReceipts.route4394 5)
theorem case53: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,29,some 32⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4394 4)
theorem case54: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,33,some 40⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4394 3)
theorem case55: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,41,some 48⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4394 2)
theorem case56: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,49,some 52⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4394 0)
private def leaf10 := (PairReceipts.route4394 1)
private def weight11 := PairRoute.weight 285209 leaf9 leaf10
theorem case57: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,53,some 56⟩:=PairRoute.start _ weight11
private theorem allAxes127:PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,some 57⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 57 ⟨
    (PairReceipts.route4320 16),
    (PairReceipts.route4320 17),
    (PairReceipts.route4320 18),
    (PairReceipts.route4320 19),
    (PairReceipts.route4340 0),
    (PairReceipts.route4340 1),
    (PairReceipts.route4340 2),
    (PairReceipts.route4340 3),
    (PairReceipts.route4340 4),
    (PairReceipts.route4340 5),
    (PairReceipts.route4340 6),
    (PairReceipts.route4340 7),
    (PairReceipts.route4340 8),
    (PairReceipts.route4340 9),
    (PairReceipts.route4340 10),
    (PairReceipts.route4340 11),
    (PairReceipts.route4340 12),
    (PairReceipts.route4340 13),
    (PairReceipts.route4340 14),
    (PairReceipts.route4340 15),
    (PairReceipts.route4340 16),
    (PairReceipts.route4340 17),
    (PairReceipts.route4340 18),
    (PairReceipts.route4340 19),
    (PairReceipts.route4360 0),
    PairLeaves.excluded PairReceipts.cell4361 PairReceipts.check4361 (none),
    PairLeaves.excluded PairReceipts.cell4362 PairReceipts.check4362 (none),
    PairLeaves.excluded PairReceipts.cell4363 PairReceipts.check4363 (none),
    PairLeaves.excluded PairReceipts.cell4364 PairReceipts.check4364 (none),
    PairLeaves.excluded PairReceipts.cell4365 PairReceipts.check4365 (none),
    PairLeaves.excluded PairReceipts.cell4366 PairReceipts.check4366 (none),
    PairLeaves.excluded PairReceipts.cell4367 PairReceipts.check4367 (none),
    PairLeaves.excluded PairReceipts.cell4368 PairReceipts.check4368 (none),
    PairLeaves.excluded PairReceipts.cell4369 PairReceipts.check4369 (none),
    PairLeaves.excluded PairReceipts.cell4370 PairReceipts.check4370 (none),
    PairLeaves.excluded PairReceipts.cell4371 PairReceipts.check4371 (none),
    PairLeaves.excluded PairReceipts.cell4372 PairReceipts.check4372 (none),
    PairLeaves.excluded PairReceipts.cell4373 PairReceipts.check4373 (none),
    PairLeaves.excluded PairReceipts.cell4374 PairReceipts.check4374 (none),
    PairLeaves.excluded PairReceipts.cell4375 PairReceipts.check4375 (none),
    PairLeaves.excluded PairReceipts.cell4376 PairReceipts.check4376 (none),
    PairLeaves.excluded PairReceipts.cell4377 PairReceipts.check4377 (none),
    PairLeaves.excluded PairReceipts.cell4378 PairReceipts.check4378 (none),
    PairLeaves.excluded PairReceipts.cell4379 PairReceipts.check4379 (none),
    PairLeaves.excluded PairReceipts.cell4380 PairReceipts.check4380 (none),
    PairLeaves.excluded PairReceipts.cell4381 PairReceipts.check4381 (none),
    PairLeaves.excluded PairReceipts.cell4382 PairReceipts.check4382 (none),
    PairLeaves.excluded PairReceipts.cell4383 PairReceipts.check4383 (none),
    PairLeaves.excluded PairReceipts.cell4384 PairReceipts.check4384 (none),
    PairLeaves.excluded PairReceipts.cell4385 PairReceipts.check4385 (none),
    PairLeaves.excluded PairReceipts.cell4386 PairReceipts.check4386 (none),
    PairLeaves.excluded PairReceipts.cell4387 PairReceipts.check4387 (none),
    PairLeaves.excluded PairReceipts.cell4388 PairReceipts.check4388 (none),
    PairLeaves.excluded PairReceipts.cell4389 PairReceipts.check4389 (none),
    PairLeaves.excluded PairReceipts.cell4390 PairReceipts.check4390 (none),
    PairLeaves.excluded PairReceipts.cell4391 PairReceipts.check4391 (none),
    PairLeaves.excluded PairReceipts.cell4392 PairReceipts.check4392 (none),
    PairLeaves.excluded PairReceipts.cell4393 PairReceipts.check4393 (none),
    trivial⟩)
theorem case58: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,57,some 57⟩:=PairRoute.start _ allAxes127
private def leaf128 := (PairReceipts.route4320 14)
private def leaf129 := (PairReceipts.route4320 15)
private def weight130 := PairRoute.weight 283522 leaf128 leaf129
theorem case59: NormalRoute.Done (4:Fin 18) ⟨50,63,10,2,58,some 58⟩:=PairRoute.start _ weight130
end Research6969.HardFit5At050
end Z6969Source2970

-- Source: Research6969.HardFit5At060
section Z6969Source2971
set_option autoImplicit true
namespace Research6969.HardFit5At060
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4400 16)
theorem case60: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4400 15)
theorem case61: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,13,some 14⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4400 14)
theorem case62: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,15,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4400 13)
theorem case63: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,17,some 18⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4400 12)
theorem case64: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,19,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4400 11)
theorem case65: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,21,some 22⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4400 10)
theorem case66: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,23,some 24⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4400 9)
theorem case67: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,25,some 28⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4400 8)
theorem case68: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,29,some 32⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4400 7)
theorem case69: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,33,some 36⟩:=PairRoute.start _ leaf9
end Research6969.HardFit5At060
end Z6969Source2971

-- Source: Research6969.PairReceipts226
section Z6969Source2972
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4520:PairCell.Row:=⟨64,654,12,2,50,some 50,49,some 49,257319,[MeasuredChoices.test64],[AxisChoices.test1812]⟩
theorem check4520:(cell4520.cap (4:Fin 18)).grade<cell4520.lowerGrade-cell4520.off:=by decide +kernel
def cell4521:PairCell.Row:=⟨64,654,12,2,50,some 50,50,some 50,257319,[MeasuredChoices.test64],[AxisChoices.test1813]⟩
theorem check4521:(cell4521.cap (4:Fin 18)).grade<cell4521.lowerGrade-cell4521.off:=by decide +kernel
private def rows4522 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,49,some 49,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,4,⟨(.node 8029965254169422),.intersection,.impossible,290650⟩⟩,
  ⟨⟨64,654,12,2,49,some 49,0,none,290650,[MeasuredChoices.test104,MeasuredChoices.test120],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,48,some 48,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test61],[]⟩,4,⟨(.node 30268515783660603),.intersection,.impossible,303874⟩⟩,
  ⟨⟨64,654,12,2,48,some 48,0,none,303874,[MeasuredChoices.test170,MeasuredChoices.test191],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,47,some 47,0,none,257319,[MeasuredChoices.test57,MeasuredChoices.test58],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,45,some 46,0,none,257319,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,41,some 44,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,4,⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨⟨64,654,12,2,41,some 43,0,none,294092,[MeasuredChoices.test140],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,44,some 44,0,none,294092,[MeasuredChoices.test142],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,37,some 40,0,none,257319,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩,4,⟨(.node 8037210057961988),.intersection,.impossible,296579⟩⟩,
  ⟨⟨64,654,12,2,37,some 40,0,none,296579,[MeasuredChoices.test158],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,33,some 36,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,4,⟨(.node 8042152515659111),.intersection,.impossible,298829⟩⟩,
  ⟨⟨64,654,12,2,33,some 35,0,none,298829,[MeasuredChoices.test161],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,36,some 36,0,some 13,298829,[MeasuredChoices.test161],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,36,some 36,14,some 19,298829,[MeasuredChoices.test161],[AxisChoices.test1777]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,36,some 36,20,some 36,298829,[],[AxisChoices.test1783]⟩,4,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,4,⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨64,654,12,2,29,some 32,0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,27,some 28,0,none,257319,[MeasuredChoices.test37],[]⟩,4,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨64,654,12,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,25,some 26,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,4,⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨⟨64,654,12,2,25,some 26,0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩,4,surfaceWhole⟩]
private theorem paid4522 : StockPairs.checked rows4522 = true := by decide +kernel
theorem route4522 (i : Fin 22) : (rows4522.get i).Done :=
  StockPairs.doneAt paid4522 i

end Research6969.PairReceipts
end Z6969Source2972

-- Source: Research6969.PairReceipts227
section Z6969Source2973
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4540 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,23,some 24,0,none,257319,[MeasuredChoices.test29,MeasuredChoices.test32],[]⟩,4,⟨(.node 30786469546942771),.intersection,.impossible,307280⟩⟩,
  ⟨⟨64,654,12,2,23,some 24,0,none,307280,[MeasuredChoices.test425],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,21,some 22,0,none,257319,[MeasuredChoices.test26],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,17,some 20,0,none,257319,[],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,13,some 16,0,none,257319,[],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,9,some 12,0,none,257319,[],[]⟩,4,surfaceWhole⟩,
  ⟨⟨64,654,12,2,4,some 8,0,none,257319,[],[]⟩,4,⟨.surface,.whole,.surface,0⟩⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,5,surfaceIntersection⟩]
private theorem paid4540 : StockPairs.checked rows4540 = true := by decide +kernel
theorem route4540 (i : Fin 20) : (rows4540.get i).Done :=
  StockPairs.doneAt paid4540 i

end Research6969.PairReceipts
end Z6969Source2973

-- Source: Research6969.HardFit5At070
section Z6969Source2974
set_option autoImplicit true
namespace Research6969.HardFit5At070
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4400 6)
theorem case70: NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,37,some 40⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4540 6)
theorem case71: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,4,some 8⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4540 5)
theorem case72: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4540 4)
theorem case73: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4540 3)
theorem case74: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4540 2)
theorem case75: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,21,some 22⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4540 0)
private def leaf7 := (PairReceipts.route4540 1)
private def weight8 := PairRoute.weight 307280 leaf6 leaf7
theorem case76: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,23,some 24⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route4522 20)
private def leaf10 := (PairReceipts.route4522 21)
private def weight11 := PairRoute.weight 303418 leaf9 leaf10
theorem case77: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,25,some 26⟩:=PairRoute.start _ weight11
private def leaf12 := (PairReceipts.route4522 18)
private def leaf13 := (PairReceipts.route4522 19)
private def weight14 := PairRoute.weight 302619 leaf12 leaf13
theorem case78: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,27,some 28⟩:=PairRoute.start _ weight14
private def leaf15 := (PairReceipts.route4522 16)
private def leaf16 := (PairReceipts.route4522 17)
private def weight17 := PairRoute.weight 300842 leaf15 leaf16
theorem case79: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,29,some 32⟩:=PairRoute.start _ weight17
end Research6969.HardFit5At070
end Z6969Source2974

-- Source: Research6969.PairReceipts221
section Z6969Source2975
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4420 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,51,some 51,1,some 1,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,2,some 2,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,3,some 3,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,4,some 4,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,5,some 5,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,6,some 6,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,7,some 7,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,8,some 8,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,9,some 9,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,10,some 10,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,11,some 11,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1774]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,12,some 12,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1775]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,13,some 13,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1776]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,14,some 14,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1777]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,15,some 15,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1778]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,16,some 16,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1779]⟩,4,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,17,some 17,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1780]⟩,4,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,18,some 18,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1781]⟩,4,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,19,some 19,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1782]⟩,4,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,20,some 20,257319,[MeasuredChoices.test66],[AxisChoices.test1783]⟩,4,markedAxisWhole⟩]
private theorem paid4420 : StockPairs.checked rows4420 = true := by decide +kernel
theorem route4420 (i : Fin 20) : (rows4420.get i).Done :=
  StockPairs.doneAt paid4420 i

end Research6969.PairReceipts
end Z6969Source2975

-- Source: Research6969.PairReceipts222
section Z6969Source2976
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4440:PairCell.Row:=⟨64,654,12,2,51,some 51,21,some 21,257319,[MeasuredChoices.test66],[AxisChoices.test1784]⟩
theorem check4440:(cell4440.cap (4:Fin 18)).grade<cell4440.lowerGrade-cell4440.off:=by decide +kernel
def cell4441:PairCell.Row:=⟨64,654,12,2,51,some 51,22,some 22,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4441:(cell4441.cap (4:Fin 18)).grade<cell4441.lowerGrade-cell4441.off:=by decide +kernel
def cell4442:PairCell.Row:=⟨64,654,12,2,51,some 51,23,some 23,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4442:(cell4442.cap (4:Fin 18)).grade<cell4442.lowerGrade-cell4442.off:=by decide +kernel
def cell4443:PairCell.Row:=⟨64,654,12,2,51,some 51,24,some 24,257319,[MeasuredChoices.test66],[AxisChoices.test1787]⟩
theorem check4443:(cell4443.cap (4:Fin 18)).grade<cell4443.lowerGrade-cell4443.off:=by decide +kernel
def cell4444:PairCell.Row:=⟨64,654,12,2,51,some 51,25,some 25,257319,[MeasuredChoices.test66],[AxisChoices.test1788]⟩
theorem check4444:(cell4444.cap (4:Fin 18)).grade<cell4444.lowerGrade-cell4444.off:=by decide +kernel
def cell4445:PairCell.Row:=⟨64,654,12,2,51,some 51,26,some 26,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4445:(cell4445.cap (4:Fin 18)).grade<cell4445.lowerGrade-cell4445.off:=by decide +kernel
def cell4446:PairCell.Row:=⟨64,654,12,2,51,some 51,27,some 27,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4446:(cell4446.cap (4:Fin 18)).grade<cell4446.lowerGrade-cell4446.off:=by decide +kernel
def cell4447:PairCell.Row:=⟨64,654,12,2,51,some 51,28,some 28,257319,[MeasuredChoices.test66],[AxisChoices.test1791]⟩
theorem check4447:(cell4447.cap (4:Fin 18)).grade<cell4447.lowerGrade-cell4447.off:=by decide +kernel
def cell4448:PairCell.Row:=⟨64,654,12,2,51,some 51,29,some 29,257319,[MeasuredChoices.test66],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4448:(cell4448.cap (4:Fin 18)).grade<cell4448.lowerGrade-cell4448.off:=by decide +kernel
def cell4449:PairCell.Row:=⟨64,654,12,2,51,some 51,30,some 30,257319,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4449:(cell4449.cap (4:Fin 18)).grade<cell4449.lowerGrade-cell4449.off:=by decide +kernel
def cell4450:PairCell.Row:=⟨64,654,12,2,51,some 51,31,some 31,257319,[MeasuredChoices.test66],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4450:(cell4450.cap (4:Fin 18)).grade<cell4450.lowerGrade-cell4450.off:=by decide +kernel
def cell4451:PairCell.Row:=⟨64,654,12,2,51,some 51,32,some 32,257319,[MeasuredChoices.test66],[AxisChoices.test1795]⟩
theorem check4451:(cell4451.cap (4:Fin 18)).grade<cell4451.lowerGrade-cell4451.off:=by decide +kernel
def cell4452:PairCell.Row:=⟨64,654,12,2,51,some 51,33,some 33,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4452:(cell4452.cap (4:Fin 18)).grade<cell4452.lowerGrade-cell4452.off:=by decide +kernel
def cell4453:PairCell.Row:=⟨64,654,12,2,51,some 51,34,some 34,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4453:(cell4453.cap (4:Fin 18)).grade<cell4453.lowerGrade-cell4453.off:=by decide +kernel
def cell4454:PairCell.Row:=⟨64,654,12,2,51,some 51,35,some 35,257319,[MeasuredChoices.test66],[AxisChoices.test1798]⟩
theorem check4454:(cell4454.cap (4:Fin 18)).grade<cell4454.lowerGrade-cell4454.off:=by decide +kernel
def cell4455:PairCell.Row:=⟨64,654,12,2,51,some 51,36,some 36,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4455:(cell4455.cap (4:Fin 18)).grade<cell4455.lowerGrade-cell4455.off:=by decide +kernel
def cell4456:PairCell.Row:=⟨64,654,12,2,51,some 51,37,some 37,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4456:(cell4456.cap (4:Fin 18)).grade<cell4456.lowerGrade-cell4456.off:=by decide +kernel
def cell4457:PairCell.Row:=⟨64,654,12,2,51,some 51,38,some 38,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4457:(cell4457.cap (4:Fin 18)).grade<cell4457.lowerGrade-cell4457.off:=by decide +kernel
def cell4458:PairCell.Row:=⟨64,654,12,2,51,some 51,39,some 39,257319,[MeasuredChoices.test66],[AxisChoices.test1802]⟩
theorem check4458:(cell4458.cap (4:Fin 18)).grade<cell4458.lowerGrade-cell4458.off:=by decide +kernel
def cell4459:PairCell.Row:=⟨64,654,12,2,51,some 51,40,some 40,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4459:(cell4459.cap (4:Fin 18)).grade<cell4459.lowerGrade-cell4459.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2976

-- Source: Research6969.PairReceipts223
section Z6969Source2977
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4460:PairCell.Row:=⟨64,654,12,2,51,some 51,41,some 41,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4460:(cell4460.cap (4:Fin 18)).grade<cell4460.lowerGrade-cell4460.off:=by decide +kernel
def cell4461:PairCell.Row:=⟨64,654,12,2,51,some 51,42,some 42,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4461:(cell4461.cap (4:Fin 18)).grade<cell4461.lowerGrade-cell4461.off:=by decide +kernel
def cell4462:PairCell.Row:=⟨64,654,12,2,51,some 51,43,some 43,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4462:(cell4462.cap (4:Fin 18)).grade<cell4462.lowerGrade-cell4462.off:=by decide +kernel
def cell4463:PairCell.Row:=⟨64,654,12,2,51,some 51,44,some 44,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4463:(cell4463.cap (4:Fin 18)).grade<cell4463.lowerGrade-cell4463.off:=by decide +kernel
def cell4464:PairCell.Row:=⟨64,654,12,2,51,some 51,45,some 45,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4464:(cell4464.cap (4:Fin 18)).grade<cell4464.lowerGrade-cell4464.off:=by decide +kernel
def cell4465:PairCell.Row:=⟨64,654,12,2,51,some 51,46,some 46,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4465:(cell4465.cap (4:Fin 18)).grade<cell4465.lowerGrade-cell4465.off:=by decide +kernel
def cell4466:PairCell.Row:=⟨64,654,12,2,51,some 51,47,some 47,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4466:(cell4466.cap (4:Fin 18)).grade<cell4466.lowerGrade-cell4466.off:=by decide +kernel
def cell4467:PairCell.Row:=⟨64,654,12,2,51,some 51,48,some 48,257319,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4467:(cell4467.cap (4:Fin 18)).grade<cell4467.lowerGrade-cell4467.off:=by decide +kernel
def cell4468:PairCell.Row:=⟨64,654,12,2,51,some 51,49,some 49,257319,[MeasuredChoices.test66],[AxisChoices.test1812]⟩
theorem check4468:(cell4468.cap (4:Fin 18)).grade<cell4468.lowerGrade-cell4468.off:=by decide +kernel
def cell4469:PairCell.Row:=⟨64,654,12,2,51,some 51,50,some 50,257319,[MeasuredChoices.test66],[AxisChoices.test1813]⟩
theorem check4469:(cell4469.cap (4:Fin 18)).grade<cell4469.lowerGrade-cell4469.off:=by decide +kernel
def cell4470:PairCell.Row:=⟨64,654,12,2,51,some 51,51,some 51,257319,[MeasuredChoices.test66],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4470:(cell4470.cap (4:Fin 18)).grade<cell4470.lowerGrade-cell4470.off:=by decide +kernel
private def rows4471 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,50,some 50,0,some 0,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,1,some 1,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,2,some 2,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,3,some 3,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,4,some 4,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,5,some 5,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,6,some 6,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,7,some 7,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,8,some 8,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩]
private theorem paid4471 : StockPairs.checked rows4471 = true := by decide +kernel
theorem route4471 (i : Fin 9) : (rows4471.get i).Done :=
  StockPairs.doneAt paid4471 i

end Research6969.PairReceipts
end Z6969Source2977

-- Source: Research6969.PairReceipts224
section Z6969Source2978
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4480 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,50,some 50,9,some 9,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,10,some 10,257319,[MeasuredChoices.test64],[]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,11,some 11,257319,[MeasuredChoices.test64],[AxisChoices.test1774]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,12,some 12,257319,[MeasuredChoices.test64],[AxisChoices.test1775]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,13,some 13,257319,[MeasuredChoices.test64],[AxisChoices.test1776]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,14,some 14,257319,[MeasuredChoices.test64],[AxisChoices.test1777]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,15,some 15,257319,[MeasuredChoices.test64],[AxisChoices.test1778]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,16,some 16,257319,[MeasuredChoices.test64],[AxisChoices.test1779]⟩,4,separateWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,17,some 17,257319,[MeasuredChoices.test64],[AxisChoices.test1780]⟩,4,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,18,some 18,257319,[MeasuredChoices.test64],[AxisChoices.test1781]⟩,4,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,19,some 19,257319,[MeasuredChoices.test64],[AxisChoices.test1782]⟩,4,markedAxisWhole⟩,
  ⟨⟨64,654,12,2,50,some 50,20,some 20,257319,[MeasuredChoices.test64],[AxisChoices.test1783]⟩,4,markedAxisWhole⟩]
private theorem paid4480 : StockPairs.checked rows4480 = true := by decide +kernel
theorem route4480 (i : Fin 12) : (rows4480.get i).Done :=
  StockPairs.doneAt paid4480 i

def cell4492:PairCell.Row:=⟨64,654,12,2,50,some 50,21,some 21,257319,[MeasuredChoices.test64],[AxisChoices.test1784]⟩
theorem check4492:(cell4492.cap (4:Fin 18)).grade<cell4492.lowerGrade-cell4492.off:=by decide +kernel
def cell4493:PairCell.Row:=⟨64,654,12,2,50,some 50,22,some 22,257319,[MeasuredChoices.test64],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4493:(cell4493.cap (4:Fin 18)).grade<cell4493.lowerGrade-cell4493.off:=by decide +kernel
def cell4494:PairCell.Row:=⟨64,654,12,2,50,some 50,23,some 23,257319,[MeasuredChoices.test64],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4494:(cell4494.cap (4:Fin 18)).grade<cell4494.lowerGrade-cell4494.off:=by decide +kernel
def cell4495:PairCell.Row:=⟨64,654,12,2,50,some 50,24,some 24,257319,[MeasuredChoices.test64],[AxisChoices.test1787]⟩
theorem check4495:(cell4495.cap (4:Fin 18)).grade<cell4495.lowerGrade-cell4495.off:=by decide +kernel
def cell4496:PairCell.Row:=⟨64,654,12,2,50,some 50,25,some 25,257319,[MeasuredChoices.test64],[AxisChoices.test1788]⟩
theorem check4496:(cell4496.cap (4:Fin 18)).grade<cell4496.lowerGrade-cell4496.off:=by decide +kernel
def cell4497:PairCell.Row:=⟨64,654,12,2,50,some 50,26,some 26,257319,[MeasuredChoices.test64],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4497:(cell4497.cap (4:Fin 18)).grade<cell4497.lowerGrade-cell4497.off:=by decide +kernel
def cell4498:PairCell.Row:=⟨64,654,12,2,50,some 50,27,some 27,257319,[MeasuredChoices.test64],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4498:(cell4498.cap (4:Fin 18)).grade<cell4498.lowerGrade-cell4498.off:=by decide +kernel
def cell4499:PairCell.Row:=⟨64,654,12,2,50,some 50,28,some 28,257319,[MeasuredChoices.test64],[AxisChoices.test1791]⟩
theorem check4499:(cell4499.cap (4:Fin 18)).grade<cell4499.lowerGrade-cell4499.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2978

-- Source: Research6969.PairReceipts225
section Z6969Source2979
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4500:PairCell.Row:=⟨64,654,12,2,50,some 50,29,some 29,257319,[MeasuredChoices.test64],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4500:(cell4500.cap (4:Fin 18)).grade<cell4500.lowerGrade-cell4500.off:=by decide +kernel
def cell4501:PairCell.Row:=⟨64,654,12,2,50,some 50,30,some 30,257319,[MeasuredChoices.test64],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4501:(cell4501.cap (4:Fin 18)).grade<cell4501.lowerGrade-cell4501.off:=by decide +kernel
def cell4502:PairCell.Row:=⟨64,654,12,2,50,some 50,31,some 31,257319,[MeasuredChoices.test64],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4502:(cell4502.cap (4:Fin 18)).grade<cell4502.lowerGrade-cell4502.off:=by decide +kernel
def cell4503:PairCell.Row:=⟨64,654,12,2,50,some 50,32,some 32,257319,[MeasuredChoices.test64],[AxisChoices.test1795]⟩
theorem check4503:(cell4503.cap (4:Fin 18)).grade<cell4503.lowerGrade-cell4503.off:=by decide +kernel
def cell4504:PairCell.Row:=⟨64,654,12,2,50,some 50,33,some 33,257319,[MeasuredChoices.test64],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4504:(cell4504.cap (4:Fin 18)).grade<cell4504.lowerGrade-cell4504.off:=by decide +kernel
def cell4505:PairCell.Row:=⟨64,654,12,2,50,some 50,34,some 34,257319,[MeasuredChoices.test64],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4505:(cell4505.cap (4:Fin 18)).grade<cell4505.lowerGrade-cell4505.off:=by decide +kernel
def cell4506:PairCell.Row:=⟨64,654,12,2,50,some 50,35,some 35,257319,[MeasuredChoices.test64],[AxisChoices.test1798]⟩
theorem check4506:(cell4506.cap (4:Fin 18)).grade<cell4506.lowerGrade-cell4506.off:=by decide +kernel
def cell4507:PairCell.Row:=⟨64,654,12,2,50,some 50,36,some 36,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4507:(cell4507.cap (4:Fin 18)).grade<cell4507.lowerGrade-cell4507.off:=by decide +kernel
def cell4508:PairCell.Row:=⟨64,654,12,2,50,some 50,37,some 37,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4508:(cell4508.cap (4:Fin 18)).grade<cell4508.lowerGrade-cell4508.off:=by decide +kernel
def cell4509:PairCell.Row:=⟨64,654,12,2,50,some 50,38,some 38,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4509:(cell4509.cap (4:Fin 18)).grade<cell4509.lowerGrade-cell4509.off:=by decide +kernel
def cell4510:PairCell.Row:=⟨64,654,12,2,50,some 50,39,some 39,257319,[MeasuredChoices.test64],[AxisChoices.test1802]⟩
theorem check4510:(cell4510.cap (4:Fin 18)).grade<cell4510.lowerGrade-cell4510.off:=by decide +kernel
def cell4511:PairCell.Row:=⟨64,654,12,2,50,some 50,40,some 40,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4511:(cell4511.cap (4:Fin 18)).grade<cell4511.lowerGrade-cell4511.off:=by decide +kernel
def cell4512:PairCell.Row:=⟨64,654,12,2,50,some 50,41,some 41,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4512:(cell4512.cap (4:Fin 18)).grade<cell4512.lowerGrade-cell4512.off:=by decide +kernel
def cell4513:PairCell.Row:=⟨64,654,12,2,50,some 50,42,some 42,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4513:(cell4513.cap (4:Fin 18)).grade<cell4513.lowerGrade-cell4513.off:=by decide +kernel
def cell4514:PairCell.Row:=⟨64,654,12,2,50,some 50,43,some 43,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4514:(cell4514.cap (4:Fin 18)).grade<cell4514.lowerGrade-cell4514.off:=by decide +kernel
def cell4515:PairCell.Row:=⟨64,654,12,2,50,some 50,44,some 44,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4515:(cell4515.cap (4:Fin 18)).grade<cell4515.lowerGrade-cell4515.off:=by decide +kernel
def cell4516:PairCell.Row:=⟨64,654,12,2,50,some 50,45,some 45,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4516:(cell4516.cap (4:Fin 18)).grade<cell4516.lowerGrade-cell4516.off:=by decide +kernel
def cell4517:PairCell.Row:=⟨64,654,12,2,50,some 50,46,some 46,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4517:(cell4517.cap (4:Fin 18)).grade<cell4517.lowerGrade-cell4517.off:=by decide +kernel
def cell4518:PairCell.Row:=⟨64,654,12,2,50,some 50,47,some 47,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4518:(cell4518.cap (4:Fin 18)).grade<cell4518.lowerGrade-cell4518.off:=by decide +kernel
def cell4519:PairCell.Row:=⟨64,654,12,2,50,some 50,48,some 48,257319,[MeasuredChoices.test64],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4519:(cell4519.cap (4:Fin 18)).grade<cell4519.lowerGrade-cell4519.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2979

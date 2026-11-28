import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0949
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.PairReceipts124
section Z6969Source2759
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2480 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩]
private theorem paid2480 : StockPairs.checked rows2480 = true := by decide +kernel
theorem route2480 (i : Fin 20) : (rows2480.get i).Done :=
  StockPairs.doneAt paid2480 i

end Research6969.PairReceipts
end Z6969Source2759

-- Source: Research6969.PairReceipts125
section Z6969Source2760
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2500 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩]
private theorem paid2500 : StockPairs.checked rows2500 = true := by decide +kernel
theorem route2500 (i : Fin 20) : (rows2500.get i).Done :=
  StockPairs.doneAt paid2500 i

end Research6969.PairReceipts
end Z6969Source2760

-- Source: Research6969.PairReceipts126
section Z6969Source2761
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2520 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,2,⟨(.node 10087576824704342),.intersection,.impossible,303779⟩⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,303779,[MeasuredChoices.test172],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,2,⟨(.node 12156969814651320),.intersection,.impossible,305579⟩⟩,
  ⟨⟨28,32,9,2,23,some 24,0,none,305579,[MeasuredChoices.test299],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,4,some 8,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,21,some 21,0,none,385979,[MeasuredChoices.test869],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid2520 : StockPairs.checked rows2520 = true := by decide +kernel
theorem route2520 (i : Fin 20) : (rows2520.get i).Done :=
  StockPairs.doneAt paid2520 i

end Research6969.PairReceipts
end Z6969Source2761

-- Source: Research6969.HardFit3At020
section Z6969Source2762
set_option autoImplicit true
namespace Research6969.HardFit3At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2380 15)
theorem case20: NormalRoute.Done (2:Fin 18) ⟨25,27,9,2,29,some 32⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2520 3)
theorem case21: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,4,some 8⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2520 2)
theorem case22: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2520 1)
theorem case23: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,13,some 14⟩:=PairRoute.start _ leaf3
private theorem allAxes35:PairRoute.Done (2:Fin 18) ⟨⟨25,27,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route2500 5),
    (PairReceipts.route2500 6),
    (PairReceipts.route2500 7),
    (PairReceipts.route2500 8),
    (PairReceipts.route2500 9),
    (PairReceipts.route2500 10),
    (PairReceipts.route2500 11),
    (PairReceipts.route2500 12),
    (PairReceipts.route2500 13),
    (PairReceipts.route2500 14),
    (PairReceipts.route2500 15),
    (PairReceipts.route2500 16),
    (PairReceipts.route2500 17),
    (PairReceipts.route2500 18),
    (PairReceipts.route2500 19),
    (PairReceipts.route2520 0),
    trivial⟩)
theorem case24: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,15,some 15⟩:=PairRoute.start _ allAxes35
private theorem allAxes69:PairRoute.Done (2:Fin 18) ⟨⟨25,27,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route2480 8),
    (PairReceipts.route2480 9),
    (PairReceipts.route2480 10),
    (PairReceipts.route2480 11),
    (PairReceipts.route2480 12),
    (PairReceipts.route2480 13),
    (PairReceipts.route2480 14),
    (PairReceipts.route2480 15),
    (PairReceipts.route2480 16),
    (PairReceipts.route2480 17),
    (PairReceipts.route2480 18),
    (PairReceipts.route2480 19),
    (PairReceipts.route2500 0),
    (PairReceipts.route2500 1),
    (PairReceipts.route2500 2),
    (PairReceipts.route2500 3),
    (PairReceipts.route2500 4),
    trivial⟩)
theorem case25: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,16,some 16⟩:=PairRoute.start _ allAxes69
private theorem allAxes105:PairRoute.Done (2:Fin 18) ⟨⟨25,27,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route2460 10),
    (PairReceipts.route2460 11),
    (PairReceipts.route2460 12),
    (PairReceipts.route2460 13),
    (PairReceipts.route2460 14),
    (PairReceipts.route2460 15),
    (PairReceipts.route2460 16),
    (PairReceipts.route2460 17),
    (PairReceipts.route2460 18),
    (PairReceipts.route2460 19),
    (PairReceipts.route2480 0),
    (PairReceipts.route2480 1),
    (PairReceipts.route2480 2),
    (PairReceipts.route2480 3),
    (PairReceipts.route2480 4),
    (PairReceipts.route2480 5),
    (PairReceipts.route2480 6),
    (PairReceipts.route2480 7),
    trivial⟩)
theorem case26: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,17,some 17⟩:=PairRoute.start _ allAxes105
private theorem allAxes143:PairRoute.Done (2:Fin 18) ⟨⟨25,27,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route2440 11),
    (PairReceipts.route2440 12),
    (PairReceipts.route2440 13),
    (PairReceipts.route2440 14),
    (PairReceipts.route2440 15),
    (PairReceipts.route2440 16),
    (PairReceipts.route2440 17),
    (PairReceipts.route2440 18),
    (PairReceipts.route2440 19),
    (PairReceipts.route2460 0),
    (PairReceipts.route2460 1),
    (PairReceipts.route2460 2),
    (PairReceipts.route2460 3),
    (PairReceipts.route2460 4),
    (PairReceipts.route2460 5),
    (PairReceipts.route2460 6),
    (PairReceipts.route2460 7),
    (PairReceipts.route2460 8),
    (PairReceipts.route2460 9),
    trivial⟩)
theorem case27: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,18,some 18⟩:=PairRoute.start _ allAxes143
private theorem allAxes185:PairRoute.Done (2:Fin 18) ⟨⟨25,27,9,3,19,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route2420 10),
    (PairReceipts.route2420 11),
    (PairReceipts.route2420 12),
    (PairReceipts.route2420 13),
    (PairReceipts.route2420 14),
    (PairReceipts.route2420 15),
    (PairReceipts.route2420 16),
    (PairReceipts.route2420 17),
    (PairReceipts.route2420 18),
    (PairReceipts.route2420 19),
    (PairReceipts.route2440 0),
    (PairReceipts.route2440 1),
    (PairReceipts.route2440 2),
    (PairReceipts.route2440 3),
    (PairReceipts.route2440 4),
    (PairReceipts.route2440 5),
    (PairReceipts.route2440 6),
    (PairReceipts.route2440 7),
    (PairReceipts.route2440 8),
    (PairReceipts.route2440 9),
    (PairReceipts.route2440 10),
    trivial⟩)
theorem case28: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,19,some 20⟩:=PairRoute.start _ allAxes185
private theorem allAxes235:PairRoute.Done (2:Fin 18) ⟨⟨25,27,9,3,21,some 24⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 24 ⟨
    (PairReceipts.route2400 5),
    (PairReceipts.route2400 6),
    (PairReceipts.route2400 7),
    (PairReceipts.route2400 8),
    (PairReceipts.route2400 9),
    (PairReceipts.route2400 10),
    (PairReceipts.route2400 11),
    (PairReceipts.route2400 12),
    (PairReceipts.route2400 13),
    (PairReceipts.route2400 14),
    (PairReceipts.route2400 15),
    (PairReceipts.route2400 16),
    (PairReceipts.route2400 17),
    (PairReceipts.route2400 18),
    (PairReceipts.route2400 19),
    (PairReceipts.route2420 0),
    (PairReceipts.route2420 1),
    (PairReceipts.route2420 2),
    (PairReceipts.route2420 3),
    (PairReceipts.route2420 4),
    (PairReceipts.route2420 5),
    (PairReceipts.route2420 6),
    (PairReceipts.route2420 7),
    (PairReceipts.route2420 8),
    (PairReceipts.route2420 9),
    trivial⟩)
theorem case29: NormalRoute.Done (2:Fin 18) ⟨25,27,9,3,21,some 24⟩:=PairRoute.start _ allAxes235
end Research6969.HardFit3At020
end Z6969Source2762

-- Source: Research6969.PairReceipts130
section Z6969Source2763
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2600 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,15,some 15,0,none,385979,[MeasuredChoices.test797],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,65,some 96,0,none,257319,[MeasuredChoices.test87],[]⟩,2,markedIntersection⟩]
private theorem paid2600 : StockPairs.checked rows2600 = true := by decide +kernel
theorem route2600 (i : Fin 20) : (rows2600.get i).Done :=
  StockPairs.doneAt paid2600 i

end Research6969.PairReceipts
end Z6969Source2763

-- Source: Research6969.HardFit3At030
section Z6969Source2764
set_option autoImplicit true
namespace Research6969.HardFit3At030
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2520 14)
theorem case30: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,4,some 8⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2520 13)
theorem case31: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2520 12)
theorem case32: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2520 11)
theorem case33: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route2520 10)
theorem case34: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,21,some 22⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2520 8)
private def leaf6 := (PairReceipts.route2520 9)
private def weight7 := PairRoute.weight 305579 leaf5 leaf6
theorem case35: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,23,some 24⟩:=PairRoute.start _ weight7
private def leaf8 := (PairReceipts.route2520 6)
private def leaf9 := (PairReceipts.route2520 7)
private def weight10 := PairRoute.weight 303779 leaf8 leaf9
theorem case36: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ weight10
private def leaf11 := (PairReceipts.route2520 5)
theorem case37: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,29,some 32⟩:=PairRoute.start _ leaf11
private def leaf12 := (PairReceipts.route2520 4)
theorem case38: NormalRoute.Done (2:Fin 18) ⟨28,32,9,2,33,some 40⟩:=PairRoute.start _ leaf12
private def leaf13 := (PairReceipts.route2600 18)
theorem case39: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,4,some 8⟩:=PairRoute.start _ leaf13
end Research6969.HardFit3At030
end Z6969Source2764

-- Source: Research6969.PairReceipts127
section Z6969Source2765
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2540 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,2,separateIntersection⟩]
private theorem paid2540 : StockPairs.checked rows2540 = true := by decide +kernel
theorem route2540 (i : Fin 20) : (rows2540.get i).Done :=
  StockPairs.doneAt paid2540 i

end Research6969.PairReceipts
end Z6969Source2765

-- Source: Research6969.PairReceipts128
section Z6969Source2766
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2560 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,18,some 18,0,none,385979,[MeasuredChoices.test831],[]⟩,2,surfaceIntersection⟩]
private theorem paid2560 : StockPairs.checked rows2560 = true := by decide +kernel
theorem route2560 (i : Fin 20) : (rows2560.get i).Done :=
  StockPairs.doneAt paid2560 i

end Research6969.PairReceipts
end Z6969Source2766

-- Source: Research6969.PairReceipts129
section Z6969Source2767
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2580 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨28,32,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid2580 : StockPairs.checked rows2580 = true := by decide +kernel
theorem route2580 (i : Fin 20) : (rows2580.get i).Done :=
  StockPairs.doneAt paid2580 i

end Research6969.PairReceipts
end Z6969Source2767

-- Source: Research6969.HardFit3At040
section Z6969Source2768
set_option autoImplicit true
namespace Research6969.HardFit3At040
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2600 17)
theorem case40: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2600 16)
theorem case41: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,13,some 14⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2600 15)
theorem case42: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,15,some 15⟩:=PairRoute.start _ leaf2
private theorem allAxes36:PairRoute.Done (2:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route2580 18),
    (PairReceipts.route2580 19),
    (PairReceipts.route2600 0),
    (PairReceipts.route2600 1),
    (PairReceipts.route2600 2),
    (PairReceipts.route2600 3),
    (PairReceipts.route2600 4),
    (PairReceipts.route2600 5),
    (PairReceipts.route2600 6),
    (PairReceipts.route2600 7),
    (PairReceipts.route2600 8),
    (PairReceipts.route2600 9),
    (PairReceipts.route2600 10),
    (PairReceipts.route2600 11),
    (PairReceipts.route2600 12),
    (PairReceipts.route2600 13),
    (PairReceipts.route2600 14),
    trivial⟩)
theorem case43: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,16,some 16⟩:=PairRoute.start _ allAxes36
private theorem allAxes72:PairRoute.Done (2:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route2580 0),
    (PairReceipts.route2580 1),
    (PairReceipts.route2580 2),
    (PairReceipts.route2580 3),
    (PairReceipts.route2580 4),
    (PairReceipts.route2580 5),
    (PairReceipts.route2580 6),
    (PairReceipts.route2580 7),
    (PairReceipts.route2580 8),
    (PairReceipts.route2580 9),
    (PairReceipts.route2580 10),
    (PairReceipts.route2580 11),
    (PairReceipts.route2580 12),
    (PairReceipts.route2580 13),
    (PairReceipts.route2580 14),
    (PairReceipts.route2580 15),
    (PairReceipts.route2580 16),
    (PairReceipts.route2580 17),
    trivial⟩)
theorem case44: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,17,some 17⟩:=PairRoute.start _ allAxes72
private def leaf73 := (PairReceipts.route2560 19)
theorem case45: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,18,some 18⟩:=PairRoute.start _ leaf73
private theorem allAxes113:PairRoute.Done (2:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route2540 19),
    (PairReceipts.route2560 0),
    (PairReceipts.route2560 1),
    (PairReceipts.route2560 2),
    (PairReceipts.route2560 3),
    (PairReceipts.route2560 4),
    (PairReceipts.route2560 5),
    (PairReceipts.route2560 6),
    (PairReceipts.route2560 7),
    (PairReceipts.route2560 8),
    (PairReceipts.route2560 9),
    (PairReceipts.route2560 10),
    (PairReceipts.route2560 11),
    (PairReceipts.route2560 12),
    (PairReceipts.route2560 13),
    (PairReceipts.route2560 14),
    (PairReceipts.route2560 15),
    (PairReceipts.route2560 16),
    (PairReceipts.route2560 17),
    (PairReceipts.route2560 18),
    trivial⟩)
theorem case46: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,19,some 19⟩:=PairRoute.start _ allAxes113
private theorem allAxes155:PairRoute.Done (2:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route2520 18),
    (PairReceipts.route2520 19),
    (PairReceipts.route2540 0),
    (PairReceipts.route2540 1),
    (PairReceipts.route2540 2),
    (PairReceipts.route2540 3),
    (PairReceipts.route2540 4),
    (PairReceipts.route2540 5),
    (PairReceipts.route2540 6),
    (PairReceipts.route2540 7),
    (PairReceipts.route2540 8),
    (PairReceipts.route2540 9),
    (PairReceipts.route2540 10),
    (PairReceipts.route2540 11),
    (PairReceipts.route2540 12),
    (PairReceipts.route2540 13),
    (PairReceipts.route2540 14),
    (PairReceipts.route2540 15),
    (PairReceipts.route2540 16),
    (PairReceipts.route2540 17),
    (PairReceipts.route2540 18),
    trivial⟩)
theorem case47: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,20,some 20⟩:=PairRoute.start _ allAxes155
private def leaf156 := (PairReceipts.route2520 17)
theorem case48: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,21,some 21⟩:=PairRoute.start _ leaf156
private def leaf157 := (PairReceipts.route2520 16)
theorem case49: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,22,some 22⟩:=PairRoute.start _ leaf157
end Research6969.HardFit3At040
end Z6969Source2768

-- Source: Research6969.PairReceipts131
section Z6969Source2769
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2620 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,2,⟨(.node 8023872256819695),.intersection,.impossible,278103⟩⟩,
  ⟨⟨33,40,9,2,49,some 64,0,none,278103,[MeasuredChoices.test104],[]⟩,2,markedIntersection⟩,
  ⟨⟨33,40,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,2,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨33,40,9,2,25,some 26,0,none,302619,[MeasuredChoices.test166],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,27,some 28,0,none,302619,[MeasuredChoices.test169],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,2,⟨(.node 12156969814651320),.intersection,.impossible,305579⟩⟩,
  ⟨⟨33,40,9,2,23,some 24,0,none,305579,[MeasuredChoices.test299],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,4,some 8,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,21,some 21,0,none,385979,[MeasuredChoices.test869],[]⟩,2,surfaceIntersection⟩]
private theorem paid2620 : StockPairs.checked rows2620 = true := by decide +kernel
theorem route2620 (i : Fin 21) : (rows2620.get i).Done :=
  StockPairs.doneAt paid2620 i

end Research6969.PairReceipts
end Z6969Source2769

-- Source: Research6969.PairReceipts270
section Z6969Source2770
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5400:PairCell.Row:=⟨28,32,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩
theorem check5400:ThreeRule.check cell5400 (2:Fin 18)=true:=by decide +kernel
def cell5401:PairCell.Row:=⟨33,40,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩
theorem check5401:ThreeRule.check cell5401 (2:Fin 18)=true:=by decide +kernel
def cell5402:PairCell.Row:=⟨41,49,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩
theorem check5402:ThreeRule.check cell5402 (2:Fin 18)=true:=by decide +kernel
def cell5403:PairCell.Row:=⟨41,49,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩
theorem check5403:ThreeRule.check cell5403 (2:Fin 18)=true:=by decide +kernel
private def rows5404 : List StockPairs.Receipt := [
  ⟨⟨50,50,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩]
private theorem paid5404 : StockPairs.checked rows5404 = true := by decide +kernel
theorem route5404 (i : Fin 10) : (rows5404.get i).Done :=
  StockPairs.doneAt paid5404 i

def cell5414:PairCell.Row:=⟨50,50,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩
theorem check5414:ThreeRule.check cell5414 (2:Fin 18)=true:=by decide +kernel
def cell5415:PairCell.Row:=⟨50,50,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩
theorem check5415:ThreeRule.check cell5415 (2:Fin 18)=true:=by decide +kernel
def cell5416:PairCell.Row:=⟨50,50,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5416:ThreeRule.check cell5416 (2:Fin 18)=true:=by decide +kernel
def cell5417:PairCell.Row:=⟨50,50,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5417:ThreeRule.check cell5417 (2:Fin 18)=true:=by decide +kernel
def cell5418:PairCell.Row:=⟨50,50,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5418:ThreeRule.check cell5418 (2:Fin 18)=true:=by decide +kernel
def cell5419:PairCell.Row:=⟨50,50,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5419:ThreeRule.check cell5419 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2770

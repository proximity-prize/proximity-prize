import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0950
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0682

set_option Elab.async false

-- Source: Research6969.HardFit3At050
section Z6969Source2771
set_option autoImplicit true
namespace Research6969.HardFit3At050
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2520 15)
theorem case50: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,23,some 24⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (2:Fin 18) ⟨⟨28,32,9,3,25,some 28⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5400 PairReceipts.check5400 (by decide) (none)
theorem case51: NormalRoute.Done (2:Fin 18) ⟨28,32,9,3,25,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2620 14)
theorem case52: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,4,some 8⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2620 13)
theorem case53: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route2620 12)
theorem case54: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2620 11)
theorem case55: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route2620 10)
theorem case56: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,21,some 22⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route2620 8)
private def leaf8 := (PairReceipts.route2620 9)
private def weight9 := PairRoute.weight 305579 leaf7 leaf8
theorem case57: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,23,some 24⟩:=PairRoute.start _ weight9
private def leaf10 := (PairReceipts.route2620 5)
private def terminalLeaf7060 := (PairReceipts.route2620 6)
private def terminalLeaf7061 := (PairReceipts.route2620 7)
private def leaf11 := PairRoute.splitSeed 26 terminalLeaf7060 terminalLeaf7061
private def weight12 := PairRoute.weight 302619 leaf10 leaf11
theorem case58: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ weight12
private def leaf13 := (PairReceipts.route2620 4)
theorem case59: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,29,some 32⟩:=PairRoute.start _ leaf13
end Research6969.HardFit3At050
end Z6969Source2771

-- Source: Research6969.PairReceipts133
section Z6969Source2772
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2660 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,18,some 18,0,none,385979,[MeasuredChoices.test831],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩]
private theorem paid2660 : StockPairs.checked rows2660 = true := by decide +kernel
theorem route2660 (i : Fin 20) : (rows2660.get i).Done :=
  StockPairs.doneAt paid2660 i

end Research6969.PairReceipts
end Z6969Source2772

-- Source: Research6969.PairReceipts134
section Z6969Source2773
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2680 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,15,some 15,0,none,385979,[MeasuredChoices.test797],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,surfaceIntersection⟩]
private theorem paid2680 : StockPairs.checked rows2680 = true := by decide +kernel
theorem route2680 (i : Fin 20) : (rows2680.get i).Done :=
  StockPairs.doneAt paid2680 i

end Research6969.PairReceipts
end Z6969Source2773

-- Source: Research6969.PairReceipts135
section Z6969Source2774
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2700 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,4,25,some 28,0,none,514639,[MeasuredChoices.test1272],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,65,some 96,0,none,257319,[MeasuredChoices.test86,MeasuredChoices.test87],[]⟩,2,markedIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,0,some 0,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,1,some 1,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,2,some 2,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,3,some 3,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,4,some 4,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,5,some 5,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,6,some 6,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,7,some 7,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,8,some 8,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,9,some 9,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,10,some 10,257319,[MeasuredChoices.test62],[]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,11,some 11,257319,[MeasuredChoices.test62],[AxisChoices.test1774]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,12,some 12,257319,[MeasuredChoices.test62],[AxisChoices.test1775]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,13,some 13,257319,[MeasuredChoices.test62],[AxisChoices.test1776]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,14,some 14,257319,[MeasuredChoices.test62],[AxisChoices.test1777]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,15,some 15,257319,[MeasuredChoices.test62],[AxisChoices.test1778]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,16,some 16,257319,[MeasuredChoices.test62],[AxisChoices.test1779]⟩,2,markedAxisIntersection⟩]
private theorem paid2700 : StockPairs.checked rows2700 = true := by decide +kernel
theorem route2700 (i : Fin 20) : (rows2700.get i).Done :=
  StockPairs.doneAt paid2700 i

end Research6969.PairReceipts
end Z6969Source2774

-- Source: Research6969.HardFit3At060
section Z6969Source2775
set_option autoImplicit true
namespace Research6969.HardFit3At060
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2620 3)
theorem case60: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,33,some 40⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2620 2)
theorem case61: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,41,some 48⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2620 0)
private def leaf3 := (PairReceipts.route2620 1)
private def weight4 := PairRoute.weight 278103 leaf2 leaf3
theorem case62: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,49,some 64⟩:=PairRoute.start _ weight4
private def leaf5 := (PairReceipts.route2600 19)
theorem case63: NormalRoute.Done (2:Fin 18) ⟨33,40,9,2,65,some 96⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route2700 0)
theorem case64: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,4,some 8⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route2680 19)
theorem case65: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route2680 18)
theorem case66: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,13,some 14⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route2680 17)
theorem case67: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,15,some 15⟩:=PairRoute.start _ leaf9
private theorem allAxes43:PairRoute.Done (2:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route2680 0),
    (PairReceipts.route2680 1),
    (PairReceipts.route2680 2),
    (PairReceipts.route2680 3),
    (PairReceipts.route2680 4),
    (PairReceipts.route2680 5),
    (PairReceipts.route2680 6),
    (PairReceipts.route2680 7),
    (PairReceipts.route2680 8),
    (PairReceipts.route2680 9),
    (PairReceipts.route2680 10),
    (PairReceipts.route2680 11),
    (PairReceipts.route2680 12),
    (PairReceipts.route2680 13),
    (PairReceipts.route2680 14),
    (PairReceipts.route2680 15),
    (PairReceipts.route2680 16),
    trivial⟩)
theorem case68: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,16,some 16⟩:=PairRoute.start _ allAxes43
private theorem allAxes79:PairRoute.Done (2:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route2660 2),
    (PairReceipts.route2660 3),
    (PairReceipts.route2660 4),
    (PairReceipts.route2660 5),
    (PairReceipts.route2660 6),
    (PairReceipts.route2660 7),
    (PairReceipts.route2660 8),
    (PairReceipts.route2660 9),
    (PairReceipts.route2660 10),
    (PairReceipts.route2660 11),
    (PairReceipts.route2660 12),
    (PairReceipts.route2660 13),
    (PairReceipts.route2660 14),
    (PairReceipts.route2660 15),
    (PairReceipts.route2660 16),
    (PairReceipts.route2660 17),
    (PairReceipts.route2660 18),
    (PairReceipts.route2660 19),
    trivial⟩)
theorem case69: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,17,some 17⟩:=PairRoute.start _ allAxes79
end Research6969.HardFit3At060
end Z6969Source2775

-- Source: Research6969.PairReceipts132
section Z6969Source2776
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2640 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,20,some 20,0,none,385979,[MeasuredChoices.test856],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨33,40,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩]
private theorem paid2640 : StockPairs.checked rows2640 = true := by decide +kernel
theorem route2640 (i : Fin 20) : (rows2640.get i).Done :=
  StockPairs.doneAt paid2640 i

end Research6969.PairReceipts
end Z6969Source2776

-- Source: Research6969.HardFit3At070
section Z6969Source2777
set_option autoImplicit true
namespace Research6969.HardFit3At070
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2660 1)
theorem case70: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,18,some 18⟩:=PairRoute.start _ leaf0
private theorem allAxes40:PairRoute.Done (2:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route2640 1),
    (PairReceipts.route2640 2),
    (PairReceipts.route2640 3),
    (PairReceipts.route2640 4),
    (PairReceipts.route2640 5),
    (PairReceipts.route2640 6),
    (PairReceipts.route2640 7),
    (PairReceipts.route2640 8),
    (PairReceipts.route2640 9),
    (PairReceipts.route2640 10),
    (PairReceipts.route2640 11),
    (PairReceipts.route2640 12),
    (PairReceipts.route2640 13),
    (PairReceipts.route2640 14),
    (PairReceipts.route2640 15),
    (PairReceipts.route2640 16),
    (PairReceipts.route2640 17),
    (PairReceipts.route2640 18),
    (PairReceipts.route2640 19),
    (PairReceipts.route2660 0),
    trivial⟩)
theorem case71: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,19,some 19⟩:=PairRoute.start _ allAxes40
private def leaf41 := (PairReceipts.route2640 0)
theorem case72: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,20,some 20⟩:=PairRoute.start _ leaf41
private def leaf42 := (PairReceipts.route2620 20)
theorem case73: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,21,some 21⟩:=PairRoute.start _ leaf42
private def leaf43 := (PairReceipts.route2620 19)
theorem case74: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,22,some 22⟩:=PairRoute.start _ leaf43
private def leaf44 := (PairReceipts.route2620 18)
theorem case75: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,23,some 24⟩:=PairRoute.start _ leaf44
private def leaf45 := (PairReceipts.route2620 17)
theorem case76: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,25,some 26⟩:=PairRoute.start _ leaf45
private def leaf46 := (PairReceipts.route2620 16)
theorem case77: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,27,some 28⟩:=PairRoute.start _ leaf46
private def leaf47 := (PairReceipts.route2620 15)
theorem case78: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,29,some 32⟩:=PairRoute.start _ leaf47
private theorem leaf48:PairRoute.Done (2:Fin 18) ⟨⟨33,40,9,3,33,some 40⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5401 PairReceipts.check5401 (by decide) (none)
theorem case79: NormalRoute.Done (2:Fin 18) ⟨33,40,9,3,33,some 40⟩:=PairRoute.start _ leaf48
end Research6969.HardFit3At070
end Z6969Source2777

-- Source: Research6969.PairReceipts138
section Z6969Source2778
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell2760:PairCell.Row:=⟨41,49,9,2,49,some 64,57,some 57,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2760:(cell2760.cap (2:Fin 18)).grade<cell2760.lowerGrade-cell2760.off:=by decide +kernel
def cell2761:PairCell.Row:=⟨41,49,9,2,49,some 64,58,some 58,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2761:(cell2761.cap (2:Fin 18)).grade<cell2761.lowerGrade-cell2761.off:=by decide +kernel
def cell2762:PairCell.Row:=⟨41,49,9,2,49,some 64,59,some 59,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2762:(cell2762.cap (2:Fin 18)).grade<cell2762.lowerGrade-cell2762.off:=by decide +kernel
def cell2763:PairCell.Row:=⟨41,49,9,2,49,some 64,60,some 60,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2763:(cell2763.cap (2:Fin 18)).grade<cell2763.lowerGrade-cell2763.off:=by decide +kernel
def cell2764:PairCell.Row:=⟨41,49,9,2,49,some 64,61,some 61,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2764:(cell2764.cap (2:Fin 18)).grade<cell2764.lowerGrade-cell2764.off:=by decide +kernel
def cell2765:PairCell.Row:=⟨41,49,9,2,49,some 64,62,some 62,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2765:(cell2765.cap (2:Fin 18)).grade<cell2765.lowerGrade-cell2765.off:=by decide +kernel
def cell2766:PairCell.Row:=⟨41,49,9,2,49,some 64,63,some 63,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2766:(cell2766.cap (2:Fin 18)).grade<cell2766.lowerGrade-cell2766.off:=by decide +kernel
def cell2767:PairCell.Row:=⟨41,49,9,2,49,some 64,64,some 64,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2767:(cell2767.cap (2:Fin 18)).grade<cell2767.lowerGrade-cell2767.off:=by decide +kernel
private def rows2768 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,2,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,2,⟨(.node 12156969814651320),.intersection,.impossible,305579⟩⟩,
  ⟨⟨41,49,9,2,23,some 24,0,none,305579,[MeasuredChoices.test299],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,4,some 8,0,none,257319,[],[]⟩,2,surfaceIntersection⟩]
private theorem paid2768 : StockPairs.checked rows2768 = true := by decide +kernel
theorem route2768 (i : Fin 12) : (rows2768.get i).Done :=
  StockPairs.doneAt paid2768 i

end Research6969.PairReceipts
end Z6969Source2778

-- Source: Research6969.HardFit3At080
section Z6969Source2779
set_option autoImplicit true
namespace Research6969.HardFit3At080
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2700 1)
theorem case80: NormalRoute.Done (2:Fin 18) ⟨33,40,9,4,25,some 28⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2768 11)
theorem case81: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,4,some 8⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2768 10)
theorem case82: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2768 9)
theorem case83: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route2768 8)
theorem case84: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2768 7)
theorem case85: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,21,some 22⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route2768 5)
private def leaf7 := (PairReceipts.route2768 6)
private def weight8 := PairRoute.weight 305579 leaf6 leaf7
theorem case86: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,23,some 24⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route2768 3)
private def leaf10 := (PairReceipts.route2768 4)
private def weight11 := PairRoute.weight 302619 leaf9 leaf10
theorem case87: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ weight11
private def leaf12 := (PairReceipts.route2768 2)
theorem case88: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,29,some 32⟩:=PairRoute.start _ leaf12
private def leaf13 := (PairReceipts.route2768 1)
theorem case89: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,33,some 40⟩:=PairRoute.start _ leaf13
end Research6969.HardFit3At080
end Z6969Source2779

-- Source: Research6969.PairReceipts136
section Z6969Source2780
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2720 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,17,some 17,257319,[MeasuredChoices.test62],[AxisChoices.test1780]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,18,some 18,257319,[MeasuredChoices.test62],[AxisChoices.test1781]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,19,some 19,257319,[MeasuredChoices.test62],[AxisChoices.test1782]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,20,some 20,257319,[MeasuredChoices.test62],[AxisChoices.test1783]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,21,some 21,257319,[MeasuredChoices.test62],[AxisChoices.test1784]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,22,some 22,257319,[MeasuredChoices.test62],[AxisChoices.test1785]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,23,some 23,257319,[MeasuredChoices.test62],[AxisChoices.test1786]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,24,some 24,257319,[MeasuredChoices.test62],[AxisChoices.test1787]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,25,some 25,257319,[MeasuredChoices.test62],[AxisChoices.test1788]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,26,some 26,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1789]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,27,some 27,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1790]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,28,some 28,257319,[MeasuredChoices.test62],[AxisChoices.test1791]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,29,some 29,257319,[MeasuredChoices.test62],[AxisChoices.test1791,AxisChoices.test1792]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,30,some 30,257319,[MeasuredChoices.test62],[AxisChoices.test1792,AxisChoices.test1793]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,31,some 31,257319,[MeasuredChoices.test62],[AxisChoices.test1793,AxisChoices.test1794]⟩,2,markedAxisIntersection⟩]
private theorem paid2720 : StockPairs.checked rows2720 = true := by decide +kernel
theorem route2720 (i : Fin 15) : (rows2720.get i).Done :=
  StockPairs.doneAt paid2720 i

def cell2735:PairCell.Row:=⟨41,49,9,2,49,some 64,32,some 32,257319,[MeasuredChoices.test62],[AxisChoices.test1795]⟩
theorem check2735:(cell2735.cap (2:Fin 18)).grade<cell2735.lowerGrade-cell2735.off:=by decide +kernel
def cell2736:PairCell.Row:=⟨41,49,9,2,49,some 64,33,some 33,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check2736:(cell2736.cap (2:Fin 18)).grade<cell2736.lowerGrade-cell2736.off:=by decide +kernel
def cell2737:PairCell.Row:=⟨41,49,9,2,49,some 64,34,some 34,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check2737:(cell2737.cap (2:Fin 18)).grade<cell2737.lowerGrade-cell2737.off:=by decide +kernel
def cell2738:PairCell.Row:=⟨41,49,9,2,49,some 64,35,some 35,257319,[MeasuredChoices.test62],[AxisChoices.test1798]⟩
theorem check2738:(cell2738.cap (2:Fin 18)).grade<cell2738.lowerGrade-cell2738.off:=by decide +kernel
def cell2739:PairCell.Row:=⟨41,49,9,2,49,some 64,36,some 36,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check2739:(cell2739.cap (2:Fin 18)).grade<cell2739.lowerGrade-cell2739.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2780

-- Source: Research6969.PairReceipts137
section Z6969Source2781
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell2740:PairCell.Row:=⟨41,49,9,2,49,some 64,37,some 37,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check2740:(cell2740.cap (2:Fin 18)).grade<cell2740.lowerGrade-cell2740.off:=by decide +kernel
def cell2741:PairCell.Row:=⟨41,49,9,2,49,some 64,38,some 38,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check2741:(cell2741.cap (2:Fin 18)).grade<cell2741.lowerGrade-cell2741.off:=by decide +kernel
def cell2742:PairCell.Row:=⟨41,49,9,2,49,some 64,39,some 39,257319,[MeasuredChoices.test62],[AxisChoices.test1802]⟩
theorem check2742:(cell2742.cap (2:Fin 18)).grade<cell2742.lowerGrade-cell2742.off:=by decide +kernel
def cell2743:PairCell.Row:=⟨41,49,9,2,49,some 64,40,some 40,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check2743:(cell2743.cap (2:Fin 18)).grade<cell2743.lowerGrade-cell2743.off:=by decide +kernel
def cell2744:PairCell.Row:=⟨41,49,9,2,49,some 64,41,some 41,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check2744:(cell2744.cap (2:Fin 18)).grade<cell2744.lowerGrade-cell2744.off:=by decide +kernel
def cell2745:PairCell.Row:=⟨41,49,9,2,49,some 64,42,some 42,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check2745:(cell2745.cap (2:Fin 18)).grade<cell2745.lowerGrade-cell2745.off:=by decide +kernel
def cell2746:PairCell.Row:=⟨41,49,9,2,49,some 64,43,some 43,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check2746:(cell2746.cap (2:Fin 18)).grade<cell2746.lowerGrade-cell2746.off:=by decide +kernel
def cell2747:PairCell.Row:=⟨41,49,9,2,49,some 64,44,some 44,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check2747:(cell2747.cap (2:Fin 18)).grade<cell2747.lowerGrade-cell2747.off:=by decide +kernel
def cell2748:PairCell.Row:=⟨41,49,9,2,49,some 64,45,some 45,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check2748:(cell2748.cap (2:Fin 18)).grade<cell2748.lowerGrade-cell2748.off:=by decide +kernel
def cell2749:PairCell.Row:=⟨41,49,9,2,49,some 64,46,some 46,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check2749:(cell2749.cap (2:Fin 18)).grade<cell2749.lowerGrade-cell2749.off:=by decide +kernel
def cell2750:PairCell.Row:=⟨41,49,9,2,49,some 64,47,some 47,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check2750:(cell2750.cap (2:Fin 18)).grade<cell2750.lowerGrade-cell2750.off:=by decide +kernel
def cell2751:PairCell.Row:=⟨41,49,9,2,49,some 64,48,some 48,257319,[MeasuredChoices.test62],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check2751:(cell2751.cap (2:Fin 18)).grade<cell2751.lowerGrade-cell2751.off:=by decide +kernel
def cell2752:PairCell.Row:=⟨41,49,9,2,49,some 64,49,some 49,257319,[MeasuredChoices.test62],[AxisChoices.test1812]⟩
theorem check2752:(cell2752.cap (2:Fin 18)).grade<cell2752.lowerGrade-cell2752.off:=by decide +kernel
def cell2753:PairCell.Row:=⟨41,49,9,2,49,some 64,50,some 50,257319,[MeasuredChoices.test62],[AxisChoices.test1813]⟩
theorem check2753:(cell2753.cap (2:Fin 18)).grade<cell2753.lowerGrade-cell2753.off:=by decide +kernel
def cell2754:PairCell.Row:=⟨41,49,9,2,49,some 64,51,some 51,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check2754:(cell2754.cap (2:Fin 18)).grade<cell2754.lowerGrade-cell2754.off:=by decide +kernel
def cell2755:PairCell.Row:=⟨41,49,9,2,49,some 64,52,some 52,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check2755:(cell2755.cap (2:Fin 18)).grade<cell2755.lowerGrade-cell2755.off:=by decide +kernel
def cell2756:PairCell.Row:=⟨41,49,9,2,49,some 64,53,some 53,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check2756:(cell2756.cap (2:Fin 18)).grade<cell2756.lowerGrade-cell2756.off:=by decide +kernel
def cell2757:PairCell.Row:=⟨41,49,9,2,49,some 64,54,some 54,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check2757:(cell2757.cap (2:Fin 18)).grade<cell2757.lowerGrade-cell2757.off:=by decide +kernel
def cell2758:PairCell.Row:=⟨41,49,9,2,49,some 64,55,some 55,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check2758:(cell2758.cap (2:Fin 18)).grade<cell2758.lowerGrade-cell2758.off:=by decide +kernel
def cell2759:PairCell.Row:=⟨41,49,9,2,49,some 64,56,some 56,257319,[MeasuredChoices.test62],[AxisChoices.test1819]⟩
theorem check2759:(cell2759.cap (2:Fin 18)).grade<cell2759.lowerGrade-cell2759.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2781

-- Source: Research6969.PairReceipts144
section Z6969Source2782
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2880 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,21,some 21,0,none,385979,[MeasuredChoices.test869],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,20,some 20,0,none,385979,[MeasuredChoices.test856],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,19,some 19,0,none,385979,[MeasuredChoices.test843],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,18,some 18,0,none,385979,[MeasuredChoices.test831],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,17,some 17,0,none,385979,[MeasuredChoices.test821],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,16,some 16,0,none,385979,[MeasuredChoices.test807],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,15,some 15,0,none,385979,[MeasuredChoices.test797],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,61,some 64,0,none,257319,[MeasuredChoices.test82,MeasuredChoices.test85],[]⟩,2,markedWhole⟩,
  ⟨⟨50,63,10,2,59,some 60,0,none,257319,[MeasuredChoices.test82],[]⟩,2,markedWhole⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,2,⟨(.node 8025893007439878),.intersection,.impossible,283522⟩⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩,2,markedWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,0,some 0,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,1,some 1,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,2,some 2,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,3,some 3,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,4,some 4,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,2,separateWhole⟩]
private theorem paid2880 : StockPairs.checked rows2880 = true := by decide +kernel
theorem route2880 (i : Fin 20) : (rows2880.get i).Done :=
  StockPairs.doneAt paid2880 i

end Research6969.PairReceipts
end Z6969Source2782

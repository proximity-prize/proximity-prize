import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0941
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0938

set_option Elab.async false

-- Source: Research6969.HardFit2At010
section Z6969Source2663
set_option autoImplicit true
namespace Research6969.HardFit2At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes29:PairRoute.Done (1:Fin 18) ⟨⟨23,24,9,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route1180 1),
    (PairReceipts.route1180 2),
    (PairReceipts.route1180 3),
    (PairReceipts.route1180 4),
    (PairReceipts.route1180 5),
    (PairReceipts.route1180 6),
    (PairReceipts.route1180 7),
    (PairReceipts.route1180 8),
    (PairReceipts.route1180 9),
    (PairReceipts.route1180 10),
    (PairReceipts.route1180 11),
    (PairReceipts.route1180 12),
    (PairReceipts.route1180 13),
    (PairReceipts.route1180 14),
    (PairReceipts.route1180 15),
    trivial⟩)
theorem case10: NormalRoute.Done (1:Fin 18) ⟨23,24,9,3,14,some 14⟩:=PairRoute.start _ allAxes29
private theorem allAxes61:PairRoute.Done (1:Fin 18) ⟨⟨23,24,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route1160 5),
    (PairReceipts.route1160 6),
    (PairReceipts.route1160 7),
    (PairReceipts.route1160 8),
    (PairReceipts.route1160 9),
    (PairReceipts.route1160 10),
    (PairReceipts.route1160 11),
    (PairReceipts.route1160 12),
    (PairReceipts.route1160 13),
    (PairReceipts.route1160 14),
    (PairReceipts.route1160 15),
    (PairReceipts.route1160 16),
    (PairReceipts.route1160 17),
    (PairReceipts.route1160 18),
    (PairReceipts.route1160 19),
    (PairReceipts.route1180 0),
    trivial⟩)
theorem case11: NormalRoute.Done (1:Fin 18) ⟨23,24,9,3,15,some 15⟩:=PairRoute.start _ allAxes61
private theorem allAxes95:PairRoute.Done (1:Fin 18) ⟨⟨23,24,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route1140 8),
    (PairReceipts.route1140 9),
    (PairReceipts.route1140 10),
    (PairReceipts.route1140 11),
    (PairReceipts.route1140 12),
    (PairReceipts.route1140 13),
    (PairReceipts.route1140 14),
    (PairReceipts.route1140 15),
    (PairReceipts.route1140 16),
    (PairReceipts.route1140 17),
    (PairReceipts.route1140 18),
    (PairReceipts.route1140 19),
    (PairReceipts.route1160 0),
    (PairReceipts.route1160 1),
    (PairReceipts.route1160 2),
    (PairReceipts.route1160 3),
    (PairReceipts.route1160 4),
    trivial⟩)
theorem case12: NormalRoute.Done (1:Fin 18) ⟨23,24,9,3,16,some 16⟩:=PairRoute.start _ allAxes95
private theorem allAxes137:PairRoute.Done (1:Fin 18) ⟨⟨23,24,9,3,17,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route1120 7),
    (PairReceipts.route1120 8),
    (PairReceipts.route1120 9),
    (PairReceipts.route1120 10),
    (PairReceipts.route1120 11),
    (PairReceipts.route1120 12),
    (PairReceipts.route1120 13),
    (PairReceipts.route1120 14),
    (PairReceipts.route1120 15),
    (PairReceipts.route1120 16),
    (PairReceipts.route1120 17),
    (PairReceipts.route1120 18),
    (PairReceipts.route1120 19),
    (PairReceipts.route1140 0),
    (PairReceipts.route1140 1),
    (PairReceipts.route1140 2),
    (PairReceipts.route1140 3),
    (PairReceipts.route1140 4),
    (PairReceipts.route1140 5),
    (PairReceipts.route1140 6),
    (PairReceipts.route1140 7),
    trivial⟩)
theorem case13: NormalRoute.Done (1:Fin 18) ⟨23,24,9,3,17,some 20⟩:=PairRoute.start _ allAxes137
private def leaf138 := (PairReceipts.route1120 6)
theorem case14: NormalRoute.Done (1:Fin 18) ⟨23,24,9,3,21,some 24⟩:=PairRoute.start _ leaf138
private def leaf139 := (PairReceipts.route1200 7)
theorem case15: NormalRoute.Done (1:Fin 18) ⟨25,27,9,2,4,some 8⟩:=PairRoute.start _ leaf139
private def leaf140 := (PairReceipts.route1200 6)
theorem case16: NormalRoute.Done (1:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf140
private def leaf141 := (PairReceipts.route1200 5)
theorem case17: NormalRoute.Done (1:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf141
private def leaf142 := (PairReceipts.route1200 4)
theorem case18: NormalRoute.Done (1:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf142
private def leaf143 := (PairReceipts.route1200 3)
theorem case19: NormalRoute.Done (1:Fin 18) ⟨25,27,9,2,21,some 24⟩:=PairRoute.start _ leaf143
end Research6969.HardFit2At010
end Z6969Source2663

-- Source: Research6969.PairReceipts063
section Z6969Source2664
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1260 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩]
private theorem paid1260 : StockPairs.checked rows1260 = true := by decide +kernel
theorem route1260 (i : Fin 20) : (rows1260.get i).Done :=
  StockPairs.doneAt paid1260 i

end Research6969.PairReceipts
end Z6969Source2664

-- Source: Research6969.PairReceipts064
section Z6969Source2665
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1280 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩]
private theorem paid1280 : StockPairs.checked rows1280 = true := by decide +kernel
theorem route1280 (i : Fin 20) : (rows1280.get i).Done :=
  StockPairs.doneAt paid1280 i

end Research6969.PairReceipts
end Z6969Source2665

-- Source: Research6969.PairReceipts065
section Z6969Source2666
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1300 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩]
private theorem paid1300 : StockPairs.checked rows1300 = true := by decide +kernel
theorem route1300 (i : Fin 20) : (rows1300.get i).Done :=
  StockPairs.doneAt paid1300 i

end Research6969.PairReceipts
end Z6969Source2666

-- Source: Research6969.PairReceipts066
section Z6969Source2667
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1320 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,surfaceWhole⟩]
private theorem paid1320 : StockPairs.checked rows1320 = true := by decide +kernel
theorem route1320 (i : Fin 20) : (rows1320.get i).Done :=
  StockPairs.doneAt paid1320 i

end Research6969.PairReceipts
end Z6969Source2667

-- Source: Research6969.HardFit2At020
section Z6969Source2668
set_option autoImplicit true
namespace Research6969.HardFit2At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1200 1)
private def leaf1 := (PairReceipts.route1200 2)
private def weight2 := PairRoute.weight 302619 leaf0 leaf1
theorem case20: NormalRoute.Done (1:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route1200 0)
theorem case21: NormalRoute.Done (1:Fin 18) ⟨25,27,9,2,29,some 32⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1180 19)
theorem case22: NormalRoute.Done (1:Fin 18) ⟨25,27,9,2,33,some 40⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1320 17)
theorem case23: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,4,some 8⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1320 16)
theorem case24: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1320 15)
theorem case25: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,13,some 13⟩:=PairRoute.start _ leaf7
private theorem allAxes37:PairRoute.Done (1:Fin 18) ⟨⟨25,27,9,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route1320 0),
    (PairReceipts.route1320 1),
    (PairReceipts.route1320 2),
    (PairReceipts.route1320 3),
    (PairReceipts.route1320 4),
    (PairReceipts.route1320 5),
    (PairReceipts.route1320 6),
    (PairReceipts.route1320 7),
    (PairReceipts.route1320 8),
    (PairReceipts.route1320 9),
    (PairReceipts.route1320 10),
    (PairReceipts.route1320 11),
    (PairReceipts.route1320 12),
    (PairReceipts.route1320 13),
    (PairReceipts.route1320 14),
    trivial⟩)
theorem case26: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,14,some 14⟩:=PairRoute.start _ allAxes37
private theorem allAxes69:PairRoute.Done (1:Fin 18) ⟨⟨25,27,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route1300 4),
    (PairReceipts.route1300 5),
    (PairReceipts.route1300 6),
    (PairReceipts.route1300 7),
    (PairReceipts.route1300 8),
    (PairReceipts.route1300 9),
    (PairReceipts.route1300 10),
    (PairReceipts.route1300 11),
    (PairReceipts.route1300 12),
    (PairReceipts.route1300 13),
    (PairReceipts.route1300 14),
    (PairReceipts.route1300 15),
    (PairReceipts.route1300 16),
    (PairReceipts.route1300 17),
    (PairReceipts.route1300 18),
    (PairReceipts.route1300 19),
    trivial⟩)
theorem case27: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,15,some 15⟩:=PairRoute.start _ allAxes69
private theorem allAxes103:PairRoute.Done (1:Fin 18) ⟨⟨25,27,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route1280 7),
    (PairReceipts.route1280 8),
    (PairReceipts.route1280 9),
    (PairReceipts.route1280 10),
    (PairReceipts.route1280 11),
    (PairReceipts.route1280 12),
    (PairReceipts.route1280 13),
    (PairReceipts.route1280 14),
    (PairReceipts.route1280 15),
    (PairReceipts.route1280 16),
    (PairReceipts.route1280 17),
    (PairReceipts.route1280 18),
    (PairReceipts.route1280 19),
    (PairReceipts.route1300 0),
    (PairReceipts.route1300 1),
    (PairReceipts.route1300 2),
    (PairReceipts.route1300 3),
    trivial⟩)
theorem case28: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,16,some 16⟩:=PairRoute.start _ allAxes103
private theorem allAxes139:PairRoute.Done (1:Fin 18) ⟨⟨25,27,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route1260 9),
    (PairReceipts.route1260 10),
    (PairReceipts.route1260 11),
    (PairReceipts.route1260 12),
    (PairReceipts.route1260 13),
    (PairReceipts.route1260 14),
    (PairReceipts.route1260 15),
    (PairReceipts.route1260 16),
    (PairReceipts.route1260 17),
    (PairReceipts.route1260 18),
    (PairReceipts.route1260 19),
    (PairReceipts.route1280 0),
    (PairReceipts.route1280 1),
    (PairReceipts.route1280 2),
    (PairReceipts.route1280 3),
    (PairReceipts.route1280 4),
    (PairReceipts.route1280 5),
    (PairReceipts.route1280 6),
    trivial⟩)
theorem case29: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,17,some 17⟩:=PairRoute.start _ allAxes139
end Research6969.HardFit2At020
end Z6969Source2668

-- Source: Research6969.PairReceipts061
section Z6969Source2669
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1220 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩]
private theorem paid1220 : StockPairs.checked rows1220 = true := by decide +kernel
theorem route1220 (i : Fin 20) : (rows1220.get i).Done :=
  StockPairs.doneAt paid1220 i

end Research6969.PairReceipts
end Z6969Source2669

-- Source: Research6969.PairReceipts062
section Z6969Source2670
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1240 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩]
private theorem paid1240 : StockPairs.checked rows1240 = true := by decide +kernel
theorem route1240 (i : Fin 20) : (rows1240.get i).Done :=
  StockPairs.doneAt paid1240 i

end Research6969.PairReceipts
end Z6969Source2670

-- Source: Research6969.PairReceipts067
section Z6969Source2671
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1340 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,2,4,some 8,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,1,markedWhole⟩,
  ⟨⟨28,32,9,3,24,some 24,0,none,385979,[MeasuredChoices.test910],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,3,23,some 23,0,none,385979,[MeasuredChoices.test896],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,0,some 0,385979,[MeasuredChoices.test882],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,1,some 1,385979,[MeasuredChoices.test882],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,2,some 2,385979,[MeasuredChoices.test882],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,3,some 3,385979,[MeasuredChoices.test882],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,4,some 4,385979,[MeasuredChoices.test882],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,5,some 5,385979,[MeasuredChoices.test882],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,6,some 6,385979,[MeasuredChoices.test882],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,7,some 7,385979,[MeasuredChoices.test882],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,8,some 8,385979,[MeasuredChoices.test882],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,9,some 9,385979,[MeasuredChoices.test882],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩]
private theorem paid1340 : StockPairs.checked rows1340 = true := by decide +kernel
theorem route1340 (i : Fin 20) : (rows1340.get i).Done :=
  StockPairs.doneAt paid1340 i

end Research6969.PairReceipts
end Z6969Source2671

-- Source: Research6969.HardFit2At030
section Z6969Source2672
set_option autoImplicit true
namespace Research6969.HardFit2At030
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes37:PairRoute.Done (1:Fin 18) ⟨⟨25,27,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route1240 10),
    (PairReceipts.route1240 11),
    (PairReceipts.route1240 12),
    (PairReceipts.route1240 13),
    (PairReceipts.route1240 14),
    (PairReceipts.route1240 15),
    (PairReceipts.route1240 16),
    (PairReceipts.route1240 17),
    (PairReceipts.route1240 18),
    (PairReceipts.route1240 19),
    (PairReceipts.route1260 0),
    (PairReceipts.route1260 1),
    (PairReceipts.route1260 2),
    (PairReceipts.route1260 3),
    (PairReceipts.route1260 4),
    (PairReceipts.route1260 5),
    (PairReceipts.route1260 6),
    (PairReceipts.route1260 7),
    (PairReceipts.route1260 8),
    trivial⟩)
theorem case30: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,18,some 18⟩:=PairRoute.start _ allAxes37
private theorem allAxes77:PairRoute.Done (1:Fin 18) ⟨⟨25,27,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route1220 10),
    (PairReceipts.route1220 11),
    (PairReceipts.route1220 12),
    (PairReceipts.route1220 13),
    (PairReceipts.route1220 14),
    (PairReceipts.route1220 15),
    (PairReceipts.route1220 16),
    (PairReceipts.route1220 17),
    (PairReceipts.route1220 18),
    (PairReceipts.route1220 19),
    (PairReceipts.route1240 0),
    (PairReceipts.route1240 1),
    (PairReceipts.route1240 2),
    (PairReceipts.route1240 3),
    (PairReceipts.route1240 4),
    (PairReceipts.route1240 5),
    (PairReceipts.route1240 6),
    (PairReceipts.route1240 7),
    (PairReceipts.route1240 8),
    (PairReceipts.route1240 9),
    trivial⟩)
theorem case31: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,19,some 19⟩:=PairRoute.start _ allAxes77
private theorem allAxes119:PairRoute.Done (1:Fin 18) ⟨⟨25,27,9,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route1200 9),
    (PairReceipts.route1200 10),
    (PairReceipts.route1200 11),
    (PairReceipts.route1200 12),
    (PairReceipts.route1200 13),
    (PairReceipts.route1200 14),
    (PairReceipts.route1200 15),
    (PairReceipts.route1200 16),
    (PairReceipts.route1200 17),
    (PairReceipts.route1200 18),
    (PairReceipts.route1200 19),
    (PairReceipts.route1220 0),
    (PairReceipts.route1220 1),
    (PairReceipts.route1220 2),
    (PairReceipts.route1220 3),
    (PairReceipts.route1220 4),
    (PairReceipts.route1220 5),
    (PairReceipts.route1220 6),
    (PairReceipts.route1220 7),
    (PairReceipts.route1220 8),
    (PairReceipts.route1220 9),
    trivial⟩)
theorem case32: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,20,some 20⟩:=PairRoute.start _ allAxes119
private theorem leaf120:PairRoute.Done (1:Fin 18) ⟨⟨25,27,9,3,21,some 24⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5169 PairReceipts.check5169 (by decide) (none)
theorem case33: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,21,some 24⟩:=PairRoute.start _ leaf120
private def leaf121 := (PairReceipts.route1200 8)
theorem case34: NormalRoute.Done (1:Fin 18) ⟨25,27,9,3,25,some 28⟩:=PairRoute.start _ leaf121
private def leaf122 := (PairReceipts.route1340 6)
theorem case35: NormalRoute.Done (1:Fin 18) ⟨28,32,9,2,4,some 8⟩:=PairRoute.start _ leaf122
private def leaf123 := (PairReceipts.route1340 5)
theorem case36: NormalRoute.Done (1:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf123
private def leaf124 := (PairReceipts.route1340 4)
theorem case37: NormalRoute.Done (1:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf124
private def leaf125 := (PairReceipts.route1340 3)
theorem case38: NormalRoute.Done (1:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf125
private def leaf126 := (PairReceipts.route1340 2)
theorem case39: NormalRoute.Done (1:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf126
end Research6969.HardFit2At030
end Z6969Source2672

-- Source: Research6969.PairReceipts072
section Z6969Source2673
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1440 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,1,separateWhole⟩]
private theorem paid1440 : StockPairs.checked rows1440 = true := by decide +kernel
theorem route1440 (i : Fin 20) : (rows1440.get i).Done :=
  StockPairs.doneAt paid1440 i

end Research6969.PairReceipts
end Z6969Source2673

-- Source: Research6969.PairReceipts073
section Z6969Source2674
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1460 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,1,separateWhole⟩]
private theorem paid1460 : StockPairs.checked rows1460 = true := by decide +kernel
theorem route1460 (i : Fin 20) : (rows1460.get i).Done :=
  StockPairs.doneAt paid1460 i

end Research6969.PairReceipts
end Z6969Source2674

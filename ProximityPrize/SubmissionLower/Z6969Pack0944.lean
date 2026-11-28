import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0943
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0938
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0682

set_option Elab.async false

-- Source: Research6969.PairReceipts081
section Z6969Source2687
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1620 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,1,separateWhole⟩]
private theorem paid1620 : StockPairs.checked rows1620 = true := by decide +kernel
theorem route1620 (i : Fin 20) : (rows1620.get i).Done :=
  StockPairs.doneAt paid1620 i

end Research6969.PairReceipts
end Z6969Source2687

-- Source: Research6969.PairReceipts082
section Z6969Source2688
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1640 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,1,separateWhole⟩]
private theorem paid1640 : StockPairs.checked rows1640 = true := by decide +kernel
theorem route1640 (i : Fin 20) : (rows1640.get i).Done :=
  StockPairs.doneAt paid1640 i

end Research6969.PairReceipts
end Z6969Source2688

-- Source: Research6969.PairReceipts083
section Z6969Source2689
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1660 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩]
private theorem paid1660 : StockPairs.checked rows1660 = true := by decide +kernel
theorem route1660 (i : Fin 20) : (rows1660.get i).Done :=
  StockPairs.doneAt paid1660 i

end Research6969.PairReceipts
end Z6969Source2689

-- Source: Research6969.PairReceipts084
section Z6969Source2690
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1680 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩]
private theorem paid1680 : StockPairs.checked rows1680 = true := by decide +kernel
theorem route1680 (i : Fin 20) : (rows1680.get i).Done :=
  StockPairs.doneAt paid1680 i

end Research6969.PairReceipts
end Z6969Source2690

-- Source: Research6969.PairReceipts085
section Z6969Source2691
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1700 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,4,29,some 32,0,none,514639,[MeasuredChoices.test1285],[]⟩,1,markedIntersection⟩]
private theorem paid1700 : StockPairs.checked rows1700 = true := by decide +kernel
theorem route1700 (i : Fin 20) : (rows1700.get i).Done :=
  StockPairs.doneAt paid1700 i

end Research6969.PairReceipts
end Z6969Source2691

-- Source: Research6969.HardFit2At070
section Z6969Source2692
set_option autoImplicit true
namespace Research6969.HardFit2At070
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1700 18)
theorem case70: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,4,some 8⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1700 17)
theorem case71: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1700 16)
theorem case72: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,13,some 13⟩:=PairRoute.start _ leaf2
private theorem allAxes32:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route1700 1),
    (PairReceipts.route1700 2),
    (PairReceipts.route1700 3),
    (PairReceipts.route1700 4),
    (PairReceipts.route1700 5),
    (PairReceipts.route1700 6),
    (PairReceipts.route1700 7),
    (PairReceipts.route1700 8),
    (PairReceipts.route1700 9),
    (PairReceipts.route1700 10),
    (PairReceipts.route1700 11),
    (PairReceipts.route1700 12),
    (PairReceipts.route1700 13),
    (PairReceipts.route1700 14),
    (PairReceipts.route1700 15),
    trivial⟩)
theorem case73: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,14,some 14⟩:=PairRoute.start _ allAxes32
private theorem allAxes64:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route1680 5),
    (PairReceipts.route1680 6),
    (PairReceipts.route1680 7),
    (PairReceipts.route1680 8),
    (PairReceipts.route1680 9),
    (PairReceipts.route1680 10),
    (PairReceipts.route1680 11),
    (PairReceipts.route1680 12),
    (PairReceipts.route1680 13),
    (PairReceipts.route1680 14),
    (PairReceipts.route1680 15),
    (PairReceipts.route1680 16),
    (PairReceipts.route1680 17),
    (PairReceipts.route1680 18),
    (PairReceipts.route1680 19),
    (PairReceipts.route1700 0),
    trivial⟩)
theorem case74: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,15,some 15⟩:=PairRoute.start _ allAxes64
private theorem allAxes98:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route1660 8),
    (PairReceipts.route1660 9),
    (PairReceipts.route1660 10),
    (PairReceipts.route1660 11),
    (PairReceipts.route1660 12),
    (PairReceipts.route1660 13),
    (PairReceipts.route1660 14),
    (PairReceipts.route1660 15),
    (PairReceipts.route1660 16),
    (PairReceipts.route1660 17),
    (PairReceipts.route1660 18),
    (PairReceipts.route1660 19),
    (PairReceipts.route1680 0),
    (PairReceipts.route1680 1),
    (PairReceipts.route1680 2),
    (PairReceipts.route1680 3),
    (PairReceipts.route1680 4),
    trivial⟩)
theorem case75: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,16,some 16⟩:=PairRoute.start _ allAxes98
private theorem allAxes134:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route1640 10),
    (PairReceipts.route1640 11),
    (PairReceipts.route1640 12),
    (PairReceipts.route1640 13),
    (PairReceipts.route1640 14),
    (PairReceipts.route1640 15),
    (PairReceipts.route1640 16),
    (PairReceipts.route1640 17),
    (PairReceipts.route1640 18),
    (PairReceipts.route1640 19),
    (PairReceipts.route1660 0),
    (PairReceipts.route1660 1),
    (PairReceipts.route1660 2),
    (PairReceipts.route1660 3),
    (PairReceipts.route1660 4),
    (PairReceipts.route1660 5),
    (PairReceipts.route1660 6),
    (PairReceipts.route1660 7),
    trivial⟩)
theorem case76: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,17,some 17⟩:=PairRoute.start _ allAxes134
private theorem allAxes172:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route1620 11),
    (PairReceipts.route1620 12),
    (PairReceipts.route1620 13),
    (PairReceipts.route1620 14),
    (PairReceipts.route1620 15),
    (PairReceipts.route1620 16),
    (PairReceipts.route1620 17),
    (PairReceipts.route1620 18),
    (PairReceipts.route1620 19),
    (PairReceipts.route1640 0),
    (PairReceipts.route1640 1),
    (PairReceipts.route1640 2),
    (PairReceipts.route1640 3),
    (PairReceipts.route1640 4),
    (PairReceipts.route1640 5),
    (PairReceipts.route1640 6),
    (PairReceipts.route1640 7),
    (PairReceipts.route1640 8),
    (PairReceipts.route1640 9),
    trivial⟩)
theorem case77: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,18,some 18⟩:=PairRoute.start _ allAxes172
private theorem allAxes212:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route1600 11),
    (PairReceipts.route1600 12),
    (PairReceipts.route1600 13),
    (PairReceipts.route1600 14),
    (PairReceipts.route1600 15),
    (PairReceipts.route1600 16),
    (PairReceipts.route1600 17),
    (PairReceipts.route1600 18),
    (PairReceipts.route1600 19),
    (PairReceipts.route1620 0),
    (PairReceipts.route1620 1),
    (PairReceipts.route1620 2),
    (PairReceipts.route1620 3),
    (PairReceipts.route1620 4),
    (PairReceipts.route1620 5),
    (PairReceipts.route1620 6),
    (PairReceipts.route1620 7),
    (PairReceipts.route1620 8),
    (PairReceipts.route1620 9),
    (PairReceipts.route1620 10),
    trivial⟩)
theorem case78: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,19,some 19⟩:=PairRoute.start _ allAxes212
private theorem allAxes254:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route1580 10),
    (PairReceipts.route1580 11),
    (PairReceipts.route1580 12),
    (PairReceipts.route1580 13),
    (PairReceipts.route1580 14),
    (PairReceipts.route1580 15),
    (PairReceipts.route1580 16),
    (PairReceipts.route1580 17),
    (PairReceipts.route1580 18),
    (PairReceipts.route1580 19),
    (PairReceipts.route1600 0),
    (PairReceipts.route1600 1),
    (PairReceipts.route1600 2),
    (PairReceipts.route1600 3),
    (PairReceipts.route1600 4),
    (PairReceipts.route1600 5),
    (PairReceipts.route1600 6),
    (PairReceipts.route1600 7),
    (PairReceipts.route1600 8),
    (PairReceipts.route1600 9),
    (PairReceipts.route1600 10),
    trivial⟩)
theorem case79: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,20,some 20⟩:=PairRoute.start _ allAxes254
end Research6969.HardFit2At070
end Z6969Source2692

-- Source: Research6969.PairReceipts077
section Z6969Source2693
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1540 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,26,some 26,0,none,385979,[MeasuredChoices.test939],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,25,some 25,0,none,385979,[MeasuredChoices.test924],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,24,some 24,0,none,385979,[MeasuredChoices.test910],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,23,some 23,0,none,385979,[MeasuredChoices.test896],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,0,some 0,385979,[MeasuredChoices.test882],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,1,some 1,385979,[MeasuredChoices.test882],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,2,some 2,385979,[MeasuredChoices.test882],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,3,some 3,385979,[MeasuredChoices.test882],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,4,some 4,385979,[MeasuredChoices.test882],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,5,some 5,385979,[MeasuredChoices.test882],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,6,some 6,385979,[MeasuredChoices.test882],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,7,some 7,385979,[MeasuredChoices.test882],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,8,some 8,385979,[MeasuredChoices.test882],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,9,some 9,385979,[MeasuredChoices.test882],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,10,some 10,385979,[MeasuredChoices.test882],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,11,some 11,385979,[MeasuredChoices.test882],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,12,some 12,385979,[MeasuredChoices.test882],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,13,some 13,385979,[MeasuredChoices.test882],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,14,some 14,385979,[MeasuredChoices.test882],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩]
private theorem paid1540 : StockPairs.checked rows1540 = true := by decide +kernel
theorem route1540 (i : Fin 20) : (rows1540.get i).Done :=
  StockPairs.doneAt paid1540 i

end Research6969.PairReceipts
end Z6969Source2693

-- Source: Research6969.PairReceipts078
section Z6969Source2694
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1560 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,22,some 22,15,some 15,385979,[MeasuredChoices.test882],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,16,some 16,385979,[MeasuredChoices.test882],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,17,some 17,385979,[MeasuredChoices.test882],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,18,some 18,385979,[MeasuredChoices.test882],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,19,some 19,385979,[MeasuredChoices.test882],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,20,some 20,385979,[MeasuredChoices.test882],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,21,some 21,385979,[MeasuredChoices.test882],[AxisChoices.test1842]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,22,some 22,385979,[MeasuredChoices.test882],[AxisChoices.test1843]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩]
private theorem paid1560 : StockPairs.checked rows1560 = true := by decide +kernel
theorem route1560 (i : Fin 20) : (rows1560.get i).Done :=
  StockPairs.doneAt paid1560 i

end Research6969.PairReceipts
end Z6969Source2694

-- Source: Research6969.HardFit2At080
section Z6969Source2695
set_option autoImplicit true
namespace Research6969.HardFit2At080
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes43:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 21 ⟨
    (PairReceipts.route1560 8),
    (PairReceipts.route1560 9),
    (PairReceipts.route1560 10),
    (PairReceipts.route1560 11),
    (PairReceipts.route1560 12),
    (PairReceipts.route1560 13),
    (PairReceipts.route1560 14),
    (PairReceipts.route1560 15),
    (PairReceipts.route1560 16),
    (PairReceipts.route1560 17),
    (PairReceipts.route1560 18),
    (PairReceipts.route1560 19),
    (PairReceipts.route1580 0),
    (PairReceipts.route1580 1),
    (PairReceipts.route1580 2),
    (PairReceipts.route1580 3),
    (PairReceipts.route1580 4),
    (PairReceipts.route1580 5),
    (PairReceipts.route1580 6),
    (PairReceipts.route1580 7),
    (PairReceipts.route1580 8),
    (PairReceipts.route1580 9),
    trivial⟩)
theorem case80: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,21,some 21⟩:=PairRoute.start _ allAxes43
private theorem allAxes89:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,22,some 22⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 22 ⟨
    (PairReceipts.route1540 5),
    (PairReceipts.route1540 6),
    (PairReceipts.route1540 7),
    (PairReceipts.route1540 8),
    (PairReceipts.route1540 9),
    (PairReceipts.route1540 10),
    (PairReceipts.route1540 11),
    (PairReceipts.route1540 12),
    (PairReceipts.route1540 13),
    (PairReceipts.route1540 14),
    (PairReceipts.route1540 15),
    (PairReceipts.route1540 16),
    (PairReceipts.route1540 17),
    (PairReceipts.route1540 18),
    (PairReceipts.route1540 19),
    (PairReceipts.route1560 0),
    (PairReceipts.route1560 1),
    (PairReceipts.route1560 2),
    (PairReceipts.route1560 3),
    (PairReceipts.route1560 4),
    (PairReceipts.route1560 5),
    (PairReceipts.route1560 6),
    (PairReceipts.route1560 7),
    trivial⟩)
theorem case81: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,22,some 22⟩:=PairRoute.start _ allAxes89
private def leaf90 := (PairReceipts.route1540 4)
theorem case82: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,23,some 23⟩:=PairRoute.start _ leaf90
private def leaf91 := (PairReceipts.route1540 3)
theorem case83: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,24,some 24⟩:=PairRoute.start _ leaf91
private def leaf92 := (PairReceipts.route1540 2)
theorem case84: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,25,some 25⟩:=PairRoute.start _ leaf92
private def leaf93 := (PairReceipts.route1540 1)
theorem case85: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,26,some 26⟩:=PairRoute.start _ leaf93
private def leaf94 := (PairReceipts.route1540 0)
theorem case86: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,27,some 28⟩:=PairRoute.start _ leaf94
private def leaf95 := (PairReceipts.route1520 19)
theorem case87: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,29,some 30⟩:=PairRoute.start _ leaf95
private def leaf96 := (PairReceipts.route1520 18)
theorem case88: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,31,some 32⟩:=PairRoute.start _ leaf96
private theorem leaf97:PairRoute.Done (1:Fin 18) ⟨⟨33,40,9,3,33,some 40⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5171 PairReceipts.check5171 (by decide) (none)
theorem case89: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,33,some 40⟩:=PairRoute.start _ leaf97
end Research6969.HardFit2At080
end Z6969Source2695

-- Source: Research6969.PairReceipts086
section Z6969Source2696
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1720 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,4,25,some 28,0,none,514639,[MeasuredChoices.test1272],[]⟩,1,surfaceIntersection⟩,
  ⟨⟨33,40,9,4,21,some 24,0,none,514639,[MeasuredChoices.test1270],[]⟩,1,surfaceIntersection⟩,
  ⟨⟨33,40,9,4,17,some 20,0,none,514639,[MeasuredChoices.test1268],[]⟩,1,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,65,some 96,0,none,257319,[MeasuredChoices.test86,MeasuredChoices.test87],[]⟩,1,markedWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,0,some 0,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,1,some 1,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,2,some 2,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,3,some 3,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,4,some 4,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,5,some 5,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,6,some 6,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,7,some 7,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,8,some 8,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,9,some 9,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,10,some 10,257319,[MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,11,some 11,257319,[MeasuredChoices.test79],[AxisChoices.test1774]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,12,some 12,257319,[MeasuredChoices.test79],[AxisChoices.test1775]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,13,some 13,257319,[MeasuredChoices.test79],[AxisChoices.test1776]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,14,some 14,257319,[MeasuredChoices.test79],[AxisChoices.test1777]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,15,some 15,257319,[MeasuredChoices.test79],[AxisChoices.test1778]⟩,1,markedAxisWhole⟩]
private theorem paid1720 : StockPairs.checked rows1720 = true := by decide +kernel
theorem route1720 (i : Fin 20) : (rows1720.get i).Done :=
  StockPairs.doneAt paid1720 i

end Research6969.PairReceipts
end Z6969Source2696

-- Source: Research6969.PairReceipts092
section Z6969Source2697
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell1840:PairCell.Row:=⟨41,49,9,2,49,some 56,51,some 51,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check1840:(cell1840.cap (1:Fin 18)).grade<cell1840.lowerGrade-cell1840.off:=by decide +kernel
def cell1841:PairCell.Row:=⟨41,49,9,2,49,some 56,52,some 52,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check1841:(cell1841.cap (1:Fin 18)).grade<cell1841.lowerGrade-cell1841.off:=by decide +kernel
def cell1842:PairCell.Row:=⟨41,49,9,2,49,some 56,53,some 53,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check1842:(cell1842.cap (1:Fin 18)).grade<cell1842.lowerGrade-cell1842.off:=by decide +kernel
def cell1843:PairCell.Row:=⟨41,49,9,2,49,some 56,54,some 54,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check1843:(cell1843.cap (1:Fin 18)).grade<cell1843.lowerGrade-cell1843.off:=by decide +kernel
def cell1844:PairCell.Row:=⟨41,49,9,2,49,some 56,55,some 55,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check1844:(cell1844.cap (1:Fin 18)).grade<cell1844.lowerGrade-cell1844.off:=by decide +kernel
def cell1845:PairCell.Row:=⟨41,49,9,2,49,some 56,56,some 56,257319,[MeasuredChoices.test62],[AxisChoices.test1819]⟩
theorem check1845:(cell1845.cap (1:Fin 18)).grade<cell1845.lowerGrade-cell1845.off:=by decide +kernel
private def rows1846 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,2,4,some 8,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,39,some 40,0,none,385979,[MeasuredChoices.test1105],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,37,some 38,0,none,385979,[MeasuredChoices.test1079],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,35,some 36,0,none,385979,[MeasuredChoices.test1055],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,33,some 34,0,none,385979,[MeasuredChoices.test1029],[]⟩,1,surfaceWhole⟩]
private theorem paid1846 : StockPairs.checked rows1846 = true := by decide +kernel
theorem route1846 (i : Fin 14) : (rows1846.get i).Done :=
  StockPairs.doneAt paid1846 i

end Research6969.PairReceipts
end Z6969Source2697

-- Source: Research6969.HardFit2At090
section Z6969Source2698
set_option autoImplicit true
namespace Research6969.HardFit2At090
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1520 17)
theorem case90: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,41,some 48⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1520 16)
theorem case91: NormalRoute.Done (1:Fin 18) ⟨33,40,9,3,49,some 64⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1720 2)
theorem case92: NormalRoute.Done (1:Fin 18) ⟨33,40,9,4,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1720 1)
theorem case93: NormalRoute.Done (1:Fin 18) ⟨33,40,9,4,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1720 0)
theorem case94: NormalRoute.Done (1:Fin 18) ⟨33,40,9,4,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1700 19)
theorem case95: NormalRoute.Done (1:Fin 18) ⟨33,40,9,4,29,some 32⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1846 9)
theorem case96: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,4,some 8⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1846 8)
theorem case97: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1846 7)
theorem case98: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1846 6)
theorem case99: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit2At090
end Z6969Source2698

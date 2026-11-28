import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0942
import ProximityPrize.SubmissionLower.Z6969Pack0938

set_option Elab.async false

-- Source: Research6969.PairReceipts074
section Z6969Source2675
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1480 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩]
private theorem paid1480 : StockPairs.checked rows1480 = true := by decide +kernel
theorem route1480 (i : Fin 20) : (rows1480.get i).Done :=
  StockPairs.doneAt paid1480 i

end Research6969.PairReceipts
end Z6969Source2675

-- Source: Research6969.PairReceipts075
section Z6969Source2676
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1500 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩]
private theorem paid1500 : StockPairs.checked rows1500 = true := by decide +kernel
theorem route1500 (i : Fin 20) : (rows1500.get i).Done :=
  StockPairs.doneAt paid1500 i

end Research6969.PairReceipts
end Z6969Source2676

-- Source: Research6969.PairReceipts076
section Z6969Source2677
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1520 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,surfaceWhole⟩,
  ⟨⟨28,32,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,65,some 96,0,none,257319,[MeasuredChoices.test87],[]⟩,1,markedWhole⟩,
  ⟨⟨33,40,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,1,markedWhole⟩,
  ⟨⟨33,40,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,2,4,some 8,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩,1,markedWhole⟩,
  ⟨⟨33,40,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,1,markedWhole⟩,
  ⟨⟨33,40,9,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,1,surfaceWhole⟩,
  ⟨⟨33,40,9,3,29,some 30,0,none,385979,[MeasuredChoices.test977],[]⟩,1,surfaceWhole⟩]
private theorem paid1520 : StockPairs.checked rows1520 = true := by decide +kernel
theorem route1520 (i : Fin 20) : (rows1520.get i).Done :=
  StockPairs.doneAt paid1520 i

end Research6969.PairReceipts
end Z6969Source2677

-- Source: Research6969.HardFit2At040
section Z6969Source2678
set_option autoImplicit true
namespace Research6969.HardFit2At040
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1340 0)
private def leaf1 := (PairReceipts.route1340 1)
private def weight2 := PairRoute.weight 302619 leaf0 leaf1
theorem case40: NormalRoute.Done (1:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route1320 19)
theorem case41: NormalRoute.Done (1:Fin 18) ⟨28,32,9,2,29,some 32⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1320 18)
theorem case42: NormalRoute.Done (1:Fin 18) ⟨28,32,9,2,33,some 40⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1520 3)
theorem case43: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,4,some 8⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1520 2)
theorem case44: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1520 1)
theorem case45: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,13,some 13⟩:=PairRoute.start _ leaf7
private theorem allAxes37:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,14,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route1500 6),
    (PairReceipts.route1500 7),
    (PairReceipts.route1500 8),
    (PairReceipts.route1500 9),
    (PairReceipts.route1500 10),
    (PairReceipts.route1500 11),
    (PairReceipts.route1500 12),
    (PairReceipts.route1500 13),
    (PairReceipts.route1500 14),
    (PairReceipts.route1500 15),
    (PairReceipts.route1500 16),
    (PairReceipts.route1500 17),
    (PairReceipts.route1500 18),
    (PairReceipts.route1500 19),
    (PairReceipts.route1520 0),
    trivial⟩)
theorem case46: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,14,some 14⟩:=PairRoute.start _ allAxes37
private theorem allAxes69:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route1480 10),
    (PairReceipts.route1480 11),
    (PairReceipts.route1480 12),
    (PairReceipts.route1480 13),
    (PairReceipts.route1480 14),
    (PairReceipts.route1480 15),
    (PairReceipts.route1480 16),
    (PairReceipts.route1480 17),
    (PairReceipts.route1480 18),
    (PairReceipts.route1480 19),
    (PairReceipts.route1500 0),
    (PairReceipts.route1500 1),
    (PairReceipts.route1500 2),
    (PairReceipts.route1500 3),
    (PairReceipts.route1500 4),
    (PairReceipts.route1500 5),
    trivial⟩)
theorem case47: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,15,some 15⟩:=PairRoute.start _ allAxes69
private theorem allAxes103:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route1460 13),
    (PairReceipts.route1460 14),
    (PairReceipts.route1460 15),
    (PairReceipts.route1460 16),
    (PairReceipts.route1460 17),
    (PairReceipts.route1460 18),
    (PairReceipts.route1460 19),
    (PairReceipts.route1480 0),
    (PairReceipts.route1480 1),
    (PairReceipts.route1480 2),
    (PairReceipts.route1480 3),
    (PairReceipts.route1480 4),
    (PairReceipts.route1480 5),
    (PairReceipts.route1480 6),
    (PairReceipts.route1480 7),
    (PairReceipts.route1480 8),
    (PairReceipts.route1480 9),
    trivial⟩)
theorem case48: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,16,some 16⟩:=PairRoute.start _ allAxes103
private theorem allAxes139:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route1440 15),
    (PairReceipts.route1440 16),
    (PairReceipts.route1440 17),
    (PairReceipts.route1440 18),
    (PairReceipts.route1440 19),
    (PairReceipts.route1460 0),
    (PairReceipts.route1460 1),
    (PairReceipts.route1460 2),
    (PairReceipts.route1460 3),
    (PairReceipts.route1460 4),
    (PairReceipts.route1460 5),
    (PairReceipts.route1460 6),
    (PairReceipts.route1460 7),
    (PairReceipts.route1460 8),
    (PairReceipts.route1460 9),
    (PairReceipts.route1460 10),
    (PairReceipts.route1460 11),
    (PairReceipts.route1460 12),
    trivial⟩)
theorem case49: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,17,some 17⟩:=PairRoute.start _ allAxes139
end Research6969.HardFit2At040
end Z6969Source2678

-- Source: Research6969.PairReceipts068
section Z6969Source2679
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1360 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,22,some 22,10,some 10,385979,[MeasuredChoices.test882],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,11,some 11,385979,[MeasuredChoices.test882],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,12,some 12,385979,[MeasuredChoices.test882],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,13,some 13,385979,[MeasuredChoices.test882],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,14,some 14,385979,[MeasuredChoices.test882],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,15,some 15,385979,[MeasuredChoices.test882],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,16,some 16,385979,[MeasuredChoices.test882],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,17,some 17,385979,[MeasuredChoices.test882],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,18,some 18,385979,[MeasuredChoices.test882],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,19,some 19,385979,[MeasuredChoices.test882],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,20,some 20,385979,[MeasuredChoices.test882],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,21,some 21,385979,[MeasuredChoices.test882],[AxisChoices.test1842]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,22,some 22,385979,[MeasuredChoices.test882],[AxisChoices.test1843]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,1,separateWhole⟩]
private theorem paid1360 : StockPairs.checked rows1360 = true := by decide +kernel
theorem route1360 (i : Fin 20) : (rows1360.get i).Done :=
  StockPairs.doneAt paid1360 i

end Research6969.PairReceipts
end Z6969Source2679

-- Source: Research6969.PairReceipts069
section Z6969Source2680
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1380 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,21,some 21,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,1,separateWhole⟩]
private theorem paid1380 : StockPairs.checked rows1380 = true := by decide +kernel
theorem route1380 (i : Fin 20) : (rows1380.get i).Done :=
  StockPairs.doneAt paid1380 i

end Research6969.PairReceipts
end Z6969Source2680

-- Source: Research6969.PairReceipts070
section Z6969Source2681
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1400 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,1,separateWhole⟩]
private theorem paid1400 : StockPairs.checked rows1400 = true := by decide +kernel
theorem route1400 (i : Fin 20) : (rows1400.get i).Done :=
  StockPairs.doneAt paid1400 i

end Research6969.PairReceipts
end Z6969Source2681

-- Source: Research6969.PairReceipts071
section Z6969Source2682
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1420 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,1,separateWhole⟩]
private theorem paid1420 : StockPairs.checked rows1420 = true := by decide +kernel
theorem route1420 (i : Fin 20) : (rows1420.get i).Done :=
  StockPairs.doneAt paid1420 i

end Research6969.PairReceipts
end Z6969Source2682

-- Source: Research6969.HardFit2At050
section Z6969Source2683
set_option autoImplicit true
namespace Research6969.HardFit2At050
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes37:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route1420 16),
    (PairReceipts.route1420 17),
    (PairReceipts.route1420 18),
    (PairReceipts.route1420 19),
    (PairReceipts.route1440 0),
    (PairReceipts.route1440 1),
    (PairReceipts.route1440 2),
    (PairReceipts.route1440 3),
    (PairReceipts.route1440 4),
    (PairReceipts.route1440 5),
    (PairReceipts.route1440 6),
    (PairReceipts.route1440 7),
    (PairReceipts.route1440 8),
    (PairReceipts.route1440 9),
    (PairReceipts.route1440 10),
    (PairReceipts.route1440 11),
    (PairReceipts.route1440 12),
    (PairReceipts.route1440 13),
    (PairReceipts.route1440 14),
    trivial⟩)
theorem case50: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,18,some 18⟩:=PairRoute.start _ allAxes37
private theorem allAxes77:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route1400 16),
    (PairReceipts.route1400 17),
    (PairReceipts.route1400 18),
    (PairReceipts.route1400 19),
    (PairReceipts.route1420 0),
    (PairReceipts.route1420 1),
    (PairReceipts.route1420 2),
    (PairReceipts.route1420 3),
    (PairReceipts.route1420 4),
    (PairReceipts.route1420 5),
    (PairReceipts.route1420 6),
    (PairReceipts.route1420 7),
    (PairReceipts.route1420 8),
    (PairReceipts.route1420 9),
    (PairReceipts.route1420 10),
    (PairReceipts.route1420 11),
    (PairReceipts.route1420 12),
    (PairReceipts.route1420 13),
    (PairReceipts.route1420 14),
    (PairReceipts.route1420 15),
    trivial⟩)
theorem case51: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,19,some 19⟩:=PairRoute.start _ allAxes77
private theorem allAxes119:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route1380 15),
    (PairReceipts.route1380 16),
    (PairReceipts.route1380 17),
    (PairReceipts.route1380 18),
    (PairReceipts.route1380 19),
    (PairReceipts.route1400 0),
    (PairReceipts.route1400 1),
    (PairReceipts.route1400 2),
    (PairReceipts.route1400 3),
    (PairReceipts.route1400 4),
    (PairReceipts.route1400 5),
    (PairReceipts.route1400 6),
    (PairReceipts.route1400 7),
    (PairReceipts.route1400 8),
    (PairReceipts.route1400 9),
    (PairReceipts.route1400 10),
    (PairReceipts.route1400 11),
    (PairReceipts.route1400 12),
    (PairReceipts.route1400 13),
    (PairReceipts.route1400 14),
    (PairReceipts.route1400 15),
    trivial⟩)
theorem case52: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,20,some 20⟩:=PairRoute.start _ allAxes119
private theorem allAxes163:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 21 ⟨
    (PairReceipts.route1360 13),
    (PairReceipts.route1360 14),
    (PairReceipts.route1360 15),
    (PairReceipts.route1360 16),
    (PairReceipts.route1360 17),
    (PairReceipts.route1360 18),
    (PairReceipts.route1360 19),
    (PairReceipts.route1380 0),
    (PairReceipts.route1380 1),
    (PairReceipts.route1380 2),
    (PairReceipts.route1380 3),
    (PairReceipts.route1380 4),
    (PairReceipts.route1380 5),
    (PairReceipts.route1380 6),
    (PairReceipts.route1380 7),
    (PairReceipts.route1380 8),
    (PairReceipts.route1380 9),
    (PairReceipts.route1380 10),
    (PairReceipts.route1380 11),
    (PairReceipts.route1380 12),
    (PairReceipts.route1380 13),
    (PairReceipts.route1380 14),
    trivial⟩)
theorem case53: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,21,some 21⟩:=PairRoute.start _ allAxes163
private theorem allAxes209:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 22 ⟨
    (PairReceipts.route1340 10),
    (PairReceipts.route1340 11),
    (PairReceipts.route1340 12),
    (PairReceipts.route1340 13),
    (PairReceipts.route1340 14),
    (PairReceipts.route1340 15),
    (PairReceipts.route1340 16),
    (PairReceipts.route1340 17),
    (PairReceipts.route1340 18),
    (PairReceipts.route1340 19),
    (PairReceipts.route1360 0),
    (PairReceipts.route1360 1),
    (PairReceipts.route1360 2),
    (PairReceipts.route1360 3),
    (PairReceipts.route1360 4),
    (PairReceipts.route1360 5),
    (PairReceipts.route1360 6),
    (PairReceipts.route1360 7),
    (PairReceipts.route1360 8),
    (PairReceipts.route1360 9),
    (PairReceipts.route1360 10),
    (PairReceipts.route1360 11),
    (PairReceipts.route1360 12),
    trivial⟩)
theorem case54: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,22,some 22⟩:=PairRoute.start _ allAxes209
private def leaf210 := (PairReceipts.route1340 9)
theorem case55: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,23,some 23⟩:=PairRoute.start _ leaf210
private def leaf211 := (PairReceipts.route1340 8)
theorem case56: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,24,some 24⟩:=PairRoute.start _ leaf211
private theorem leaf212:PairRoute.Done (1:Fin 18) ⟨⟨28,32,9,3,25,some 28⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5170 PairReceipts.check5170 (by decide) (none)
theorem case57: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,25,some 28⟩:=PairRoute.start _ leaf212
private def leaf213 := (PairReceipts.route1340 7)
theorem case58: NormalRoute.Done (1:Fin 18) ⟨28,32,9,3,29,some 32⟩:=PairRoute.start _ leaf213
private def leaf214 := (PairReceipts.route1520 15)
theorem case59: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,4,some 8⟩:=PairRoute.start _ leaf214
end Research6969.HardFit2At050
end Z6969Source2683

-- Source: Research6969.HardFit2At060
section Z6969Source2684
set_option autoImplicit true
namespace Research6969.HardFit2At060
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1520 14)
theorem case60: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1520 13)
theorem case61: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1520 12)
theorem case62: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1520 11)
theorem case63: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1520 9)
private def leaf5 := (PairReceipts.route1520 10)
private def weight6 := PairRoute.weight 302619 leaf4 leaf5
theorem case64: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ weight6
private def leaf7 := (PairReceipts.route1520 8)
theorem case65: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,29,some 32⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1520 7)
theorem case66: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,33,some 40⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1520 6)
theorem case67: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,41,some 48⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route1520 5)
theorem case68: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,49,some 64⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route1520 4)
theorem case69: NormalRoute.Done (1:Fin 18) ⟨33,40,9,2,65,some 96⟩:=PairRoute.start _ leaf11
end Research6969.HardFit2At060
end Z6969Source2684

-- Source: Research6969.PairReceipts079
section Z6969Source2685
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1580 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,21,some 21,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,1,separateWhole⟩]
private theorem paid1580 : StockPairs.checked rows1580 = true := by decide +kernel
theorem route1580 (i : Fin 20) : (rows1580.get i).Done :=
  StockPairs.doneAt paid1580 i

end Research6969.PairReceipts
end Z6969Source2685

-- Source: Research6969.PairReceipts080
section Z6969Source2686
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1600 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,1,separateWhole⟩]
private theorem paid1600 : StockPairs.checked rows1600 = true := by decide +kernel
theorem route1600 (i : Fin 20) : (rows1600.get i).Done :=
  StockPairs.doneAt paid1600 i

end Research6969.PairReceipts
end Z6969Source2686

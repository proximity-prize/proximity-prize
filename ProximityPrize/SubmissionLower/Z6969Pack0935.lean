import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0667

set_option Elab.async false

-- Source: Research6969.PairReceipts000
section Z6969Source2579
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows0 : List StockPairs.Receipt := [
  ⟨⟨22,22,9,1,129,some 256,0,none,128659,[MeasuredChoices.test11],[]⟩,0,markedWhole⟩,
  ⟨⟨22,22,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,markedWhole⟩,
  ⟨⟨22,22,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨22,22,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,surfaceWhole⟩,
  ⟨⟨22,22,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,surfaceWhole⟩,
  ⟨⟨22,22,9,2,17,some 20,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨22,22,9,2,13,some 16,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨22,22,9,2,9,some 12,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨22,22,9,2,4,some 8,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨22,22,9,3,513,some 1024,0,none,385979,[MeasuredChoices.test1154,MeasuredChoices.test1155],[]⟩,0,markedWhole⟩,
  ⟨⟨22,22,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,0,markedWhole⟩,
  ⟨⟨22,22,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,0,markedWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩]
private theorem paid0 : StockPairs.checked rows0 = true := by decide +kernel
theorem route0 (i : Fin 20) : (rows0.get i).Done :=
  StockPairs.doneAt paid0 i

end Research6969.PairReceipts
end Z6969Source2579

-- Source: Research6969.PairReceipts002
section Z6969Source2580
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows40 : List StockPairs.Receipt := [
  ⟨⟨22,22,9,3,13,some 14,11,some 11,385979,[MeasuredChoices.test770],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,12,some 12,385979,[MeasuredChoices.test770],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,13,some 13,385979,[MeasuredChoices.test770],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,14,some 14,385979,[MeasuredChoices.test770],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,surfaceWhole⟩,
  ⟨⟨22,22,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,surfaceWhole⟩,
  ⟨⟨22,22,9,4,513,some 1024,0,none,514639,[MeasuredChoices.test1378],[]⟩,0,markedWhole⟩,
  ⟨⟨22,22,9,5,1025,some 1536,0,none,643299,[MeasuredChoices.test1535],[]⟩,0,markedIntersection⟩,
  ⟨⟨22,22,9,6,1025,some 1536,0,none,771959,[MeasuredChoices.test1669],[]⟩,0,markedIntersection⟩,
  ⟨⟨23,24,9,1,129,some 256,0,none,128659,[MeasuredChoices.test11],[]⟩,0,markedWhole⟩,
  ⟨⟨23,24,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,markedWhole⟩,
  ⟨⟨23,24,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,2,17,some 20,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,2,13,some 16,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,2,9,some 12,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,2,4,some 8,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,3,513,some 1024,0,none,385979,[MeasuredChoices.test1154,MeasuredChoices.test1155],[]⟩,0,markedWhole⟩]
private theorem paid40 : StockPairs.checked rows40 = true := by decide +kernel
theorem route40 (i : Fin 20) : (rows40.get i).Done :=
  StockPairs.doneAt paid40 i

end Research6969.PairReceipts
end Z6969Source2580

-- Source: Research6969.HardFit1At000
section Z6969Source2581
set_option autoImplicit true
namespace Research6969.HardFit1At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route0 0)
theorem case0: NormalRoute.Done (0:Fin 18) ⟨22,22,9,1,129,some 256⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route0 8)
theorem case1: NormalRoute.Done (0:Fin 18) ⟨22,22,9,2,4,some 8⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route0 7)
theorem case2: NormalRoute.Done (0:Fin 18) ⟨22,22,9,2,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route0 6)
theorem case3: NormalRoute.Done (0:Fin 18) ⟨22,22,9,2,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route0 5)
theorem case4: NormalRoute.Done (0:Fin 18) ⟨22,22,9,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route0 4)
theorem case5: NormalRoute.Done (0:Fin 18) ⟨22,22,9,2,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route0 2)
private def leaf7 := (PairReceipts.route0 3)
private def weight8 := PairRoute.weight 302619 leaf6 leaf7
theorem case6: NormalRoute.Done (0:Fin 18) ⟨22,22,9,2,25,some 28⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route0 1)
theorem case7: NormalRoute.Done (0:Fin 18) ⟨22,22,9,2,29,some 32⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route40 5)
theorem case8: NormalRoute.Done (0:Fin 18) ⟨22,22,9,3,4,some 8⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route40 4)
theorem case9: NormalRoute.Done (0:Fin 18) ⟨22,22,9,3,9,some 12⟩:=PairRoute.start _ leaf11
end Research6969.HardFit1At000
end Z6969Source2581

-- Source: Research6969.PairReceipts001
section Z6969Source2582
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows20 : List StockPairs.Receipt := [
  ⟨⟨22,22,9,3,15,some 16,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,15,some 16,16,some 16,385979,[MeasuredChoices.test797],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,0,some 0,385979,[MeasuredChoices.test770],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,1,some 1,385979,[MeasuredChoices.test770],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,2,some 2,385979,[MeasuredChoices.test770],[AxisChoices.test1823]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,3,some 3,385979,[MeasuredChoices.test770],[AxisChoices.test1824]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,4,some 4,385979,[MeasuredChoices.test770],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,5,some 5,385979,[MeasuredChoices.test770],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,6,some 6,385979,[MeasuredChoices.test770],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,7,some 7,385979,[MeasuredChoices.test770],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,8,some 8,385979,[MeasuredChoices.test770],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,9,some 9,385979,[MeasuredChoices.test770],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨22,22,9,3,13,some 14,10,some 10,385979,[MeasuredChoices.test770],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩]
private theorem paid20 : StockPairs.checked rows20 = true := by decide +kernel
theorem route20 (i : Fin 20) : (rows20.get i).Done :=
  StockPairs.doneAt paid20 i

end Research6969.PairReceipts
end Z6969Source2582

-- Source: Research6969.HardFit1At010
section Z6969Source2583
set_option autoImplicit true
namespace Research6969.HardFit1At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes29:PairRoute.Done (0:Fin 18) ⟨⟨22,22,9,3,13,some 14⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 14 ⟨
    (PairReceipts.route20 9),
    (PairReceipts.route20 10),
    (PairReceipts.route20 11),
    (PairReceipts.route20 12),
    (PairReceipts.route20 13),
    (PairReceipts.route20 14),
    (PairReceipts.route20 15),
    (PairReceipts.route20 16),
    (PairReceipts.route20 17),
    (PairReceipts.route20 18),
    (PairReceipts.route20 19),
    (PairReceipts.route40 0),
    (PairReceipts.route40 1),
    (PairReceipts.route40 2),
    (PairReceipts.route40 3),
    trivial⟩)
theorem case10: NormalRoute.Done (0:Fin 18) ⟨22,22,9,3,13,some 14⟩:=PairRoute.start _ allAxes29
private theorem allAxes63:PairRoute.Done (0:Fin 18) ⟨⟨22,22,9,3,15,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route0 12),
    (PairReceipts.route0 13),
    (PairReceipts.route0 14),
    (PairReceipts.route0 15),
    (PairReceipts.route0 16),
    (PairReceipts.route0 17),
    (PairReceipts.route0 18),
    (PairReceipts.route0 19),
    (PairReceipts.route20 0),
    (PairReceipts.route20 1),
    (PairReceipts.route20 2),
    (PairReceipts.route20 3),
    (PairReceipts.route20 4),
    (PairReceipts.route20 5),
    (PairReceipts.route20 6),
    (PairReceipts.route20 7),
    (PairReceipts.route20 8),
    trivial⟩)
theorem case11: NormalRoute.Done (0:Fin 18) ⟨22,22,9,3,15,some 16⟩:=PairRoute.start _ allAxes63
private def leaf64 := (PairReceipts.route0 11)
theorem case12: NormalRoute.Done (0:Fin 18) ⟨22,22,9,3,17,some 20⟩:=PairRoute.start _ leaf64
private def leaf65 := (PairReceipts.route0 10)
theorem case13: NormalRoute.Done (0:Fin 18) ⟨22,22,9,3,21,some 24⟩:=PairRoute.start _ leaf65
private def leaf66 := (PairReceipts.route0 9)
theorem case14: NormalRoute.Done (0:Fin 18) ⟨22,22,9,3,513,some 1024⟩:=PairRoute.start _ leaf66
private def leaf67 := (PairReceipts.route40 6)
theorem case15: NormalRoute.Done (0:Fin 18) ⟨22,22,9,4,513,some 1024⟩:=PairRoute.start _ leaf67
private def leaf68 := (PairReceipts.route40 7)
theorem case16: NormalRoute.Done (0:Fin 18) ⟨22,22,9,5,1025,some 1536⟩:=PairRoute.start _ leaf68
private def leaf69 := (PairReceipts.route40 8)
theorem case17: NormalRoute.Done (0:Fin 18) ⟨22,22,9,6,1025,some 1536⟩:=PairRoute.start _ leaf69
private def leaf70 := (PairReceipts.route40 9)
theorem case18: NormalRoute.Done (0:Fin 18) ⟨23,24,9,1,129,some 256⟩:=PairRoute.start _ leaf70
private def leaf71 := (PairReceipts.route40 18)
theorem case19: NormalRoute.Done (0:Fin 18) ⟨23,24,9,2,4,some 8⟩:=PairRoute.start _ leaf71
end Research6969.HardFit1At010
end Z6969Source2583

-- Source: Research6969.PairReceipts006
section Z6969Source2584
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows120 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,0,none,385979,[MeasuredChoices.test785],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,surfaceWhole⟩,
  ⟨⟨23,24,9,4,513,some 1024,0,none,514639,[MeasuredChoices.test1377,MeasuredChoices.test1378],[]⟩,0,markedWhole⟩,
  ⟨⟨23,24,9,5,513,some 1024,0,none,643299,[MeasuredChoices.test1533],[]⟩,0,markedIntersection⟩,
  ⟨⟨23,24,9,6,513,some 1024,0,none,771959,[MeasuredChoices.test1667],[]⟩,0,markedIntersection⟩,
  ⟨⟨25,27,9,1,129,some 256,0,none,128659,[MeasuredChoices.test11],[]⟩,0,markedWhole⟩]
private theorem paid120 : StockPairs.checked rows120 = true := by decide +kernel
theorem route120 (i : Fin 20) : (rows120.get i).Done :=
  StockPairs.doneAt paid120 i

end Research6969.PairReceipts
end Z6969Source2584

-- Source: Research6969.HardFit1At020
section Z6969Source2585
set_option autoImplicit true
namespace Research6969.HardFit1At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route40 17)
theorem case20: NormalRoute.Done (0:Fin 18) ⟨23,24,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route40 16)
theorem case21: NormalRoute.Done (0:Fin 18) ⟨23,24,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route40 15)
theorem case22: NormalRoute.Done (0:Fin 18) ⟨23,24,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route40 14)
theorem case23: NormalRoute.Done (0:Fin 18) ⟨23,24,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route40 12)
private def leaf5 := (PairReceipts.route40 13)
private def weight6 := PairRoute.weight 302619 leaf4 leaf5
theorem case24: NormalRoute.Done (0:Fin 18) ⟨23,24,9,2,25,some 28⟩:=PairRoute.start _ weight6
private def leaf7 := (PairReceipts.route40 11)
theorem case25: NormalRoute.Done (0:Fin 18) ⟨23,24,9,2,29,some 32⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route40 10)
theorem case26: NormalRoute.Done (0:Fin 18) ⟨23,24,9,2,33,some 40⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route120 15)
theorem case27: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,4,some 8⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route120 14)
theorem case28: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,9,some 12⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route120 13)
theorem case29: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,13,some 13⟩:=PairRoute.start _ leaf11
end Research6969.HardFit1At020
end Z6969Source2585

-- Source: Research6969.PairReceipts003
section Z6969Source2586
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows60 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,0,markedWhole⟩,
  ⟨⟨23,24,9,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,0,markedWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩]
private theorem paid60 : StockPairs.checked rows60 = true := by decide +kernel
theorem route60 (i : Fin 20) : (rows60.get i).Done :=
  StockPairs.doneAt paid60 i

end Research6969.PairReceipts
end Z6969Source2586

-- Source: Research6969.PairReceipts004
section Z6969Source2587
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows80 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,0,separateWhole⟩]
private theorem paid80 : StockPairs.checked rows80 = true := by decide +kernel
theorem route80 (i : Fin 20) : (rows80.get i).Done :=
  StockPairs.doneAt paid80 i

end Research6969.PairReceipts
end Z6969Source2587

-- Source: Research6969.PairReceipts005
section Z6969Source2588
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows100 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,0,markedAxisWhole⟩]
private theorem paid100 : StockPairs.checked rows100 = true := by decide +kernel
theorem route100 (i : Fin 20) : (rows100.get i).Done :=
  StockPairs.doneAt paid100 i

end Research6969.PairReceipts
end Z6969Source2588

-- Source: Research6969.HardFit1At030
section Z6969Source2589
set_option autoImplicit true
namespace Research6969.HardFit1At030
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route120 12)
theorem case30: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,14,some 14⟩:=PairRoute.start _ leaf0
private theorem allAxes32:PairRoute.Done (0:Fin 18) ⟨⟨23,24,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route100 16),
    (PairReceipts.route100 17),
    (PairReceipts.route100 18),
    (PairReceipts.route100 19),
    (PairReceipts.route120 0),
    (PairReceipts.route120 1),
    (PairReceipts.route120 2),
    (PairReceipts.route120 3),
    (PairReceipts.route120 4),
    (PairReceipts.route120 5),
    (PairReceipts.route120 6),
    (PairReceipts.route120 7),
    (PairReceipts.route120 8),
    (PairReceipts.route120 9),
    (PairReceipts.route120 10),
    (PairReceipts.route120 11),
    trivial⟩)
theorem case31: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,15,some 15⟩:=PairRoute.start _ allAxes32
private theorem allAxes66:PairRoute.Done (0:Fin 18) ⟨⟨23,24,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route80 19),
    (PairReceipts.route100 0),
    (PairReceipts.route100 1),
    (PairReceipts.route100 2),
    (PairReceipts.route100 3),
    (PairReceipts.route100 4),
    (PairReceipts.route100 5),
    (PairReceipts.route100 6),
    (PairReceipts.route100 7),
    (PairReceipts.route100 8),
    (PairReceipts.route100 9),
    (PairReceipts.route100 10),
    (PairReceipts.route100 11),
    (PairReceipts.route100 12),
    (PairReceipts.route100 13),
    (PairReceipts.route100 14),
    (PairReceipts.route100 15),
    trivial⟩)
theorem case32: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,16,some 16⟩:=PairRoute.start _ allAxes66
private theorem allAxes102:PairRoute.Done (0:Fin 18) ⟨⟨23,24,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route80 1),
    (PairReceipts.route80 2),
    (PairReceipts.route80 3),
    (PairReceipts.route80 4),
    (PairReceipts.route80 5),
    (PairReceipts.route80 6),
    (PairReceipts.route80 7),
    (PairReceipts.route80 8),
    (PairReceipts.route80 9),
    (PairReceipts.route80 10),
    (PairReceipts.route80 11),
    (PairReceipts.route80 12),
    (PairReceipts.route80 13),
    (PairReceipts.route80 14),
    (PairReceipts.route80 15),
    (PairReceipts.route80 16),
    (PairReceipts.route80 17),
    (PairReceipts.route80 18),
    trivial⟩)
theorem case33: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,17,some 17⟩:=PairRoute.start _ allAxes102
private theorem allAxes140:PairRoute.Done (0:Fin 18) ⟨⟨23,24,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route60 2),
    (PairReceipts.route60 3),
    (PairReceipts.route60 4),
    (PairReceipts.route60 5),
    (PairReceipts.route60 6),
    (PairReceipts.route60 7),
    (PairReceipts.route60 8),
    (PairReceipts.route60 9),
    (PairReceipts.route60 10),
    (PairReceipts.route60 11),
    (PairReceipts.route60 12),
    (PairReceipts.route60 13),
    (PairReceipts.route60 14),
    (PairReceipts.route60 15),
    (PairReceipts.route60 16),
    (PairReceipts.route60 17),
    (PairReceipts.route60 18),
    (PairReceipts.route60 19),
    (PairReceipts.route80 0),
    trivial⟩)
theorem case34: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,18,some 18⟩:=PairRoute.start _ allAxes140
private def leaf141 := (PairReceipts.route60 1)
theorem case35: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,19,some 20⟩:=PairRoute.start _ leaf141
private def leaf142 := (PairReceipts.route60 0)
theorem case36: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,21,some 24⟩:=PairRoute.start _ leaf142
private def leaf143 := (PairReceipts.route40 19)
theorem case37: NormalRoute.Done (0:Fin 18) ⟨23,24,9,3,513,some 1024⟩:=PairRoute.start _ leaf143
private def leaf144 := (PairReceipts.route120 16)
theorem case38: NormalRoute.Done (0:Fin 18) ⟨23,24,9,4,513,some 1024⟩:=PairRoute.start _ leaf144
private def leaf145 := (PairReceipts.route120 17)
theorem case39: NormalRoute.Done (0:Fin 18) ⟨23,24,9,5,513,some 1024⟩:=PairRoute.start _ leaf145
end Research6969.HardFit1At030
end Z6969Source2589

-- Source: Research6969.PairReceipts007
section Z6969Source2590
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows140 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,1,65,some 96,0,none,128659,[MeasuredChoices.test7],[]⟩,0,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨25,27,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,markedWhole⟩,
  ⟨⟨25,27,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,2,4,some 8,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,0,markedWhole⟩,
  ⟨⟨25,27,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,0,markedWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩]
private theorem paid140 : StockPairs.checked rows140 = true := by decide +kernel
theorem route140 (i : Fin 20) : (rows140.get i).Done :=
  StockPairs.doneAt paid140 i

end Research6969.PairReceipts
end Z6969Source2590

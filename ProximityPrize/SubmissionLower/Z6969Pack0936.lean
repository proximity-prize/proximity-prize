import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0935
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.HardFit1At040
section Z6969Source2591
set_option autoImplicit true
namespace Research6969.HardFit1At040
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route120 18)
theorem case40: NormalRoute.Done (0:Fin 18) ⟨23,24,9,6,513,some 1024⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route140 0)
theorem case41: NormalRoute.Done (0:Fin 18) ⟨25,27,9,1,65,some 96⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route120 19)
theorem case42: NormalRoute.Done (0:Fin 18) ⟨25,27,9,1,129,some 256⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route140 9)
theorem case43: NormalRoute.Done (0:Fin 18) ⟨25,27,9,2,4,some 8⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route140 8)
theorem case44: NormalRoute.Done (0:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route140 7)
theorem case45: NormalRoute.Done (0:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route140 6)
theorem case46: NormalRoute.Done (0:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route140 5)
theorem case47: NormalRoute.Done (0:Fin 18) ⟨25,27,9,2,21,some 24⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route140 3)
private def leaf9 := (PairReceipts.route140 4)
private def weight10 := PairRoute.weight 302619 leaf8 leaf9
theorem case48: NormalRoute.Done (0:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ weight10
private def leaf11 := (PairReceipts.route140 2)
theorem case49: NormalRoute.Done (0:Fin 18) ⟨25,27,9,2,29,some 32⟩:=PairRoute.start _ leaf11
end Research6969.HardFit1At040
end Z6969Source2591

-- Source: Research6969.PairReceipts009
section Z6969Source2592
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows180 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,0,separateWhole⟩]
private theorem paid180 : StockPairs.checked rows180 = true := by decide +kernel
theorem route180 (i : Fin 20) : (rows180.get i).Done :=
  StockPairs.doneAt paid180 i

end Research6969.PairReceipts
end Z6969Source2592

-- Source: Research6969.PairReceipts010
section Z6969Source2593
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows200 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,0,separateWhole⟩]
private theorem paid200 : StockPairs.checked rows200 = true := by decide +kernel
theorem route200 (i : Fin 20) : (rows200.get i).Done :=
  StockPairs.doneAt paid200 i

end Research6969.PairReceipts
end Z6969Source2593

-- Source: Research6969.PairReceipts011
section Z6969Source2594
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows220 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,0,separateWhole⟩]
private theorem paid220 : StockPairs.checked rows220 = true := by decide +kernel
theorem route220 (i : Fin 20) : (rows220.get i).Done :=
  StockPairs.doneAt paid220 i

end Research6969.PairReceipts
end Z6969Source2594

-- Source: Research6969.PairReceipts012
section Z6969Source2595
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows240 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩]
private theorem paid240 : StockPairs.checked rows240 = true := by decide +kernel
theorem route240 (i : Fin 20) : (rows240.get i).Done :=
  StockPairs.doneAt paid240 i

end Research6969.PairReceipts
end Z6969Source2595

-- Source: Research6969.PairReceipts013
section Z6969Source2596
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows260 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩]
private theorem paid260 : StockPairs.checked rows260 = true := by decide +kernel
theorem route260 (i : Fin 20) : (rows260.get i).Done :=
  StockPairs.doneAt paid260 i

end Research6969.PairReceipts
end Z6969Source2596

-- Source: Research6969.PairReceipts014
section Z6969Source2597
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows280 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,14,some 14,0,none,385979,[MeasuredChoices.test785],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,surfaceWhole⟩,
  ⟨⟨25,27,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,1,129,some 256,0,none,128659,[MeasuredChoices.test11],[]⟩,0,markedWhole⟩,
  ⟨⟨28,32,9,1,65,some 96,0,none,128659,[MeasuredChoices.test7],[]⟩,0,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨28,32,9,2,65,some 96,0,none,257319,[MeasuredChoices.test87],[]⟩,0,markedWhole⟩,
  ⟨⟨28,32,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,0,markedWhole⟩,
  ⟨⟨28,32,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,0,markedWhole⟩,
  ⟨⟨28,32,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,surfaceWhole⟩]
private theorem paid280 : StockPairs.checked rows280 = true := by decide +kernel
theorem route280 (i : Fin 20) : (rows280.get i).Done :=
  StockPairs.doneAt paid280 i

end Research6969.PairReceipts
end Z6969Source2597

-- Source: Research6969.HardFit1At050
section Z6969Source2598
set_option autoImplicit true
namespace Research6969.HardFit1At050
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route140 1)
theorem case50: NormalRoute.Done (0:Fin 18) ⟨25,27,9,2,33,some 40⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route280 9)
theorem case51: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,4,some 8⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route280 8)
theorem case52: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route280 7)
theorem case53: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,13,some 13⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route280 6)
theorem case54: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,14,some 14⟩:=PairRoute.start _ leaf4
private theorem allAxes36:PairRoute.Done (0:Fin 18) ⟨⟨25,27,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route260 10),
    (PairReceipts.route260 11),
    (PairReceipts.route260 12),
    (PairReceipts.route260 13),
    (PairReceipts.route260 14),
    (PairReceipts.route260 15),
    (PairReceipts.route260 16),
    (PairReceipts.route260 17),
    (PairReceipts.route260 18),
    (PairReceipts.route260 19),
    (PairReceipts.route280 0),
    (PairReceipts.route280 1),
    (PairReceipts.route280 2),
    (PairReceipts.route280 3),
    (PairReceipts.route280 4),
    (PairReceipts.route280 5),
    trivial⟩)
theorem case55: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,15,some 15⟩:=PairRoute.start _ allAxes36
private theorem allAxes70:PairRoute.Done (0:Fin 18) ⟨⟨25,27,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route240 13),
    (PairReceipts.route240 14),
    (PairReceipts.route240 15),
    (PairReceipts.route240 16),
    (PairReceipts.route240 17),
    (PairReceipts.route240 18),
    (PairReceipts.route240 19),
    (PairReceipts.route260 0),
    (PairReceipts.route260 1),
    (PairReceipts.route260 2),
    (PairReceipts.route260 3),
    (PairReceipts.route260 4),
    (PairReceipts.route260 5),
    (PairReceipts.route260 6),
    (PairReceipts.route260 7),
    (PairReceipts.route260 8),
    (PairReceipts.route260 9),
    trivial⟩)
theorem case56: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,16,some 16⟩:=PairRoute.start _ allAxes70
private theorem allAxes106:PairRoute.Done (0:Fin 18) ⟨⟨25,27,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route220 15),
    (PairReceipts.route220 16),
    (PairReceipts.route220 17),
    (PairReceipts.route220 18),
    (PairReceipts.route220 19),
    (PairReceipts.route240 0),
    (PairReceipts.route240 1),
    (PairReceipts.route240 2),
    (PairReceipts.route240 3),
    (PairReceipts.route240 4),
    (PairReceipts.route240 5),
    (PairReceipts.route240 6),
    (PairReceipts.route240 7),
    (PairReceipts.route240 8),
    (PairReceipts.route240 9),
    (PairReceipts.route240 10),
    (PairReceipts.route240 11),
    (PairReceipts.route240 12),
    trivial⟩)
theorem case57: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,17,some 17⟩:=PairRoute.start _ allAxes106
private theorem allAxes144:PairRoute.Done (0:Fin 18) ⟨⟨25,27,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route200 16),
    (PairReceipts.route200 17),
    (PairReceipts.route200 18),
    (PairReceipts.route200 19),
    (PairReceipts.route220 0),
    (PairReceipts.route220 1),
    (PairReceipts.route220 2),
    (PairReceipts.route220 3),
    (PairReceipts.route220 4),
    (PairReceipts.route220 5),
    (PairReceipts.route220 6),
    (PairReceipts.route220 7),
    (PairReceipts.route220 8),
    (PairReceipts.route220 9),
    (PairReceipts.route220 10),
    (PairReceipts.route220 11),
    (PairReceipts.route220 12),
    (PairReceipts.route220 13),
    (PairReceipts.route220 14),
    trivial⟩)
theorem case58: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,18,some 18⟩:=PairRoute.start _ allAxes144
private theorem allAxes184:PairRoute.Done (0:Fin 18) ⟨⟨25,27,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route180 16),
    (PairReceipts.route180 17),
    (PairReceipts.route180 18),
    (PairReceipts.route180 19),
    (PairReceipts.route200 0),
    (PairReceipts.route200 1),
    (PairReceipts.route200 2),
    (PairReceipts.route200 3),
    (PairReceipts.route200 4),
    (PairReceipts.route200 5),
    (PairReceipts.route200 6),
    (PairReceipts.route200 7),
    (PairReceipts.route200 8),
    (PairReceipts.route200 9),
    (PairReceipts.route200 10),
    (PairReceipts.route200 11),
    (PairReceipts.route200 12),
    (PairReceipts.route200 13),
    (PairReceipts.route200 14),
    (PairReceipts.route200 15),
    trivial⟩)
theorem case59: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,19,some 19⟩:=PairRoute.start _ allAxes184
end Research6969.HardFit1At050
end Z6969Source2598

-- Source: Research6969.PairReceipts008
section Z6969Source2599
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows160 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,21,some 22,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,21,some 22,22,some 22,385979,[MeasuredChoices.test869],[AxisChoices.test1843]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,0,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,0,markedAxisWhole⟩]
private theorem paid160 : StockPairs.checked rows160 = true := by decide +kernel
theorem route160 (i : Fin 20) : (rows160.get i).Done :=
  StockPairs.doneAt paid160 i

end Research6969.PairReceipts
end Z6969Source2599

-- Source: Research6969.PairReceipts015
section Z6969Source2600
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows300 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,2,4,some 8,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,0,markedWhole⟩,
  ⟨⟨28,32,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,0,markedWhole⟩,
  ⟨⟨28,32,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,0,some 0,385979,[MeasuredChoices.test882],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,1,some 1,385979,[MeasuredChoices.test882],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,2,some 2,385979,[MeasuredChoices.test882],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,3,some 3,385979,[MeasuredChoices.test882],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,4,some 4,385979,[MeasuredChoices.test882],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,5,some 5,385979,[MeasuredChoices.test882],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,6,some 6,385979,[MeasuredChoices.test882],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,7,some 7,385979,[MeasuredChoices.test882],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,8,some 8,385979,[MeasuredChoices.test882],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,9,some 9,385979,[MeasuredChoices.test882],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,10,some 10,385979,[MeasuredChoices.test882],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩]
private theorem paid300 : StockPairs.checked rows300 = true := by decide +kernel
theorem route300 (i : Fin 20) : (rows300.get i).Done :=
  StockPairs.doneAt paid300 i

end Research6969.PairReceipts
end Z6969Source2600

-- Source: Research6969.HardFit1At060
section Z6969Source2601
set_option autoImplicit true
namespace Research6969.HardFit1At060
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes41:PairRoute.Done (0:Fin 18) ⟨⟨25,27,9,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route160 15),
    (PairReceipts.route160 16),
    (PairReceipts.route160 17),
    (PairReceipts.route160 18),
    (PairReceipts.route160 19),
    (PairReceipts.route180 0),
    (PairReceipts.route180 1),
    (PairReceipts.route180 2),
    (PairReceipts.route180 3),
    (PairReceipts.route180 4),
    (PairReceipts.route180 5),
    (PairReceipts.route180 6),
    (PairReceipts.route180 7),
    (PairReceipts.route180 8),
    (PairReceipts.route180 9),
    (PairReceipts.route180 10),
    (PairReceipts.route180 11),
    (PairReceipts.route180 12),
    (PairReceipts.route180 13),
    (PairReceipts.route180 14),
    (PairReceipts.route180 15),
    trivial⟩)
theorem case60: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,20,some 20⟩:=PairRoute.start _ allAxes41
private theorem allAxes87:PairRoute.Done (0:Fin 18) ⟨⟨25,27,9,3,21,some 22⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 22 ⟨
    (PairReceipts.route140 12),
    (PairReceipts.route140 13),
    (PairReceipts.route140 14),
    (PairReceipts.route140 15),
    (PairReceipts.route140 16),
    (PairReceipts.route140 17),
    (PairReceipts.route140 18),
    (PairReceipts.route140 19),
    (PairReceipts.route160 0),
    (PairReceipts.route160 1),
    (PairReceipts.route160 2),
    (PairReceipts.route160 3),
    (PairReceipts.route160 4),
    (PairReceipts.route160 5),
    (PairReceipts.route160 6),
    (PairReceipts.route160 7),
    (PairReceipts.route160 8),
    (PairReceipts.route160 9),
    (PairReceipts.route160 10),
    (PairReceipts.route160 11),
    (PairReceipts.route160 12),
    (PairReceipts.route160 13),
    (PairReceipts.route160 14),
    trivial⟩)
theorem case61: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,21,some 22⟩:=PairRoute.start _ allAxes87
private def leaf88 := (PairReceipts.route140 11)
theorem case62: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,23,some 24⟩:=PairRoute.start _ leaf88
private def leaf89 := (PairReceipts.route140 10)
theorem case63: NormalRoute.Done (0:Fin 18) ⟨25,27,9,3,25,some 28⟩:=PairRoute.start _ leaf89
private def leaf90 := (PairReceipts.route280 11)
theorem case64: NormalRoute.Done (0:Fin 18) ⟨28,32,9,1,65,some 96⟩:=PairRoute.start _ leaf90
private def leaf91 := (PairReceipts.route280 10)
theorem case65: NormalRoute.Done (0:Fin 18) ⟨28,32,9,1,129,some 256⟩:=PairRoute.start _ leaf91
private def leaf92 := (PairReceipts.route300 3)
theorem case66: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,4,some 8⟩:=PairRoute.start _ leaf92
private def leaf93 := (PairReceipts.route300 2)
theorem case67: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf93
private def leaf94 := (PairReceipts.route300 1)
theorem case68: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf94
private def leaf95 := (PairReceipts.route300 0)
theorem case69: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf95
end Research6969.HardFit1At060
end Z6969Source2601

-- Source: Research6969.PairReceipts023
section Z6969Source2602
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows460 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,4,21,some 24,0,none,514639,[MeasuredChoices.test1270],[]⟩,0,markedWhole⟩,
  ⟨⟨28,32,9,4,17,some 20,0,none,514639,[MeasuredChoices.test1268],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,4,13,some 16,0,none,514639,[MeasuredChoices.test1256],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,1,65,some 96,0,none,128659,[MeasuredChoices.test7],[]⟩,0,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨33,40,9,2,65,some 96,0,none,257319,[MeasuredChoices.test87],[]⟩,0,markedWhole⟩,
  ⟨⟨33,40,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,0,markedWhole⟩,
  ⟨⟨33,40,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,surfaceWhole⟩]
private theorem paid460 : StockPairs.checked rows460 = true := by decide +kernel
theorem route460 (i : Fin 20) : (rows460.get i).Done :=
  StockPairs.doneAt paid460 i

end Research6969.PairReceipts
end Z6969Source2602

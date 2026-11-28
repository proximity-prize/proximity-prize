import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0936
import ProximityPrize.SubmissionLower.Z6969Pack0937
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.HardFit1At100
section Z6969Source2615
set_option autoImplicit true
namespace Research6969.HardFit1At100
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route480 0)
theorem case100: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route460 19)
theorem case101: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route460 17)
private def leaf3 := (PairReceipts.route460 18)
private def weight4 := PairRoute.weight 302619 leaf2 leaf3
theorem case102: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ weight4
private def leaf5 := (PairReceipts.route460 16)
theorem case103: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,29,some 32⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route460 15)
theorem case104: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,33,some 40⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route460 14)
theorem case105: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,41,some 48⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route460 13)
theorem case106: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,49,some 64⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route460 12)
theorem case107: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,65,some 96⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route620 9)
theorem case108: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,4,some 8⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route620 8)
theorem case109: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf11
end Research6969.HardFit1At100
end Z6969Source2615

-- Source: Research6969.PairReceipts025
section Z6969Source2616
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows500 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,21,some 21,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,0,separateWhole⟩]
private theorem paid500 : StockPairs.checked rows500 = true := by decide +kernel
theorem route500 (i : Fin 20) : (rows500.get i).Done :=
  StockPairs.doneAt paid500 i

end Research6969.PairReceipts
end Z6969Source2616

-- Source: Research6969.PairReceipts026
section Z6969Source2617
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows520 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,0,separateWhole⟩]
private theorem paid520 : StockPairs.checked rows520 = true := by decide +kernel
theorem route520 (i : Fin 20) : (rows520.get i).Done :=
  StockPairs.doneAt paid520 i

end Research6969.PairReceipts
end Z6969Source2617

-- Source: Research6969.PairReceipts027
section Z6969Source2618
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows540 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,0,separateWhole⟩]
private theorem paid540 : StockPairs.checked rows540 = true := by decide +kernel
theorem route540 (i : Fin 20) : (rows540.get i).Done :=
  StockPairs.doneAt paid540 i

end Research6969.PairReceipts
end Z6969Source2618

-- Source: Research6969.PairReceipts028
section Z6969Source2619
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows560 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,0,separateWhole⟩]
private theorem paid560 : StockPairs.checked rows560 = true := by decide +kernel
theorem route560 (i : Fin 20) : (rows560.get i).Done :=
  StockPairs.doneAt paid560 i

end Research6969.PairReceipts
end Z6969Source2619

-- Source: Research6969.PairReceipts029
section Z6969Source2620
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows580 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,0,separateWhole⟩]
private theorem paid580 : StockPairs.checked rows580 = true := by decide +kernel
theorem route580 (i : Fin 20) : (rows580.get i).Done :=
  StockPairs.doneAt paid580 i

end Research6969.PairReceipts
end Z6969Source2620

-- Source: Research6969.PairReceipts030
section Z6969Source2621
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows600 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,0,separateWhole⟩]
private theorem paid600 : StockPairs.checked rows600 = true := by decide +kernel
theorem route600 (i : Fin 20) : (rows600.get i).Done :=
  StockPairs.doneAt paid600 i

end Research6969.PairReceipts
end Z6969Source2621

-- Source: Research6969.HardFit1At110
section Z6969Source2622
set_option autoImplicit true
namespace Research6969.HardFit1At110
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route620 7)
theorem case110: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,13,some 14⟩:=PairRoute.start _ leaf0
private theorem allAxes32:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route600 11),
    (PairReceipts.route600 12),
    (PairReceipts.route600 13),
    (PairReceipts.route600 14),
    (PairReceipts.route600 15),
    (PairReceipts.route600 16),
    (PairReceipts.route600 17),
    (PairReceipts.route600 18),
    (PairReceipts.route600 19),
    (PairReceipts.route620 0),
    (PairReceipts.route620 1),
    (PairReceipts.route620 2),
    (PairReceipts.route620 3),
    (PairReceipts.route620 4),
    (PairReceipts.route620 5),
    (PairReceipts.route620 6),
    trivial⟩)
theorem case111: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,15,some 15⟩:=PairRoute.start _ allAxes32
private theorem allAxes66:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route580 14),
    (PairReceipts.route580 15),
    (PairReceipts.route580 16),
    (PairReceipts.route580 17),
    (PairReceipts.route580 18),
    (PairReceipts.route580 19),
    (PairReceipts.route600 0),
    (PairReceipts.route600 1),
    (PairReceipts.route600 2),
    (PairReceipts.route600 3),
    (PairReceipts.route600 4),
    (PairReceipts.route600 5),
    (PairReceipts.route600 6),
    (PairReceipts.route600 7),
    (PairReceipts.route600 8),
    (PairReceipts.route600 9),
    (PairReceipts.route600 10),
    trivial⟩)
theorem case112: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,16,some 16⟩:=PairRoute.start _ allAxes66
private theorem allAxes102:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route560 16),
    (PairReceipts.route560 17),
    (PairReceipts.route560 18),
    (PairReceipts.route560 19),
    (PairReceipts.route580 0),
    (PairReceipts.route580 1),
    (PairReceipts.route580 2),
    (PairReceipts.route580 3),
    (PairReceipts.route580 4),
    (PairReceipts.route580 5),
    (PairReceipts.route580 6),
    (PairReceipts.route580 7),
    (PairReceipts.route580 8),
    (PairReceipts.route580 9),
    (PairReceipts.route580 10),
    (PairReceipts.route580 11),
    (PairReceipts.route580 12),
    (PairReceipts.route580 13),
    trivial⟩)
theorem case113: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,17,some 17⟩:=PairRoute.start _ allAxes102
private theorem allAxes140:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route540 17),
    (PairReceipts.route540 18),
    (PairReceipts.route540 19),
    (PairReceipts.route560 0),
    (PairReceipts.route560 1),
    (PairReceipts.route560 2),
    (PairReceipts.route560 3),
    (PairReceipts.route560 4),
    (PairReceipts.route560 5),
    (PairReceipts.route560 6),
    (PairReceipts.route560 7),
    (PairReceipts.route560 8),
    (PairReceipts.route560 9),
    (PairReceipts.route560 10),
    (PairReceipts.route560 11),
    (PairReceipts.route560 12),
    (PairReceipts.route560 13),
    (PairReceipts.route560 14),
    (PairReceipts.route560 15),
    trivial⟩)
theorem case114: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,18,some 18⟩:=PairRoute.start _ allAxes140
private theorem allAxes180:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route520 17),
    (PairReceipts.route520 18),
    (PairReceipts.route520 19),
    (PairReceipts.route540 0),
    (PairReceipts.route540 1),
    (PairReceipts.route540 2),
    (PairReceipts.route540 3),
    (PairReceipts.route540 4),
    (PairReceipts.route540 5),
    (PairReceipts.route540 6),
    (PairReceipts.route540 7),
    (PairReceipts.route540 8),
    (PairReceipts.route540 9),
    (PairReceipts.route540 10),
    (PairReceipts.route540 11),
    (PairReceipts.route540 12),
    (PairReceipts.route540 13),
    (PairReceipts.route540 14),
    (PairReceipts.route540 15),
    (PairReceipts.route540 16),
    trivial⟩)
theorem case115: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,19,some 19⟩:=PairRoute.start _ allAxes180
private theorem allAxes222:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route500 16),
    (PairReceipts.route500 17),
    (PairReceipts.route500 18),
    (PairReceipts.route500 19),
    (PairReceipts.route520 0),
    (PairReceipts.route520 1),
    (PairReceipts.route520 2),
    (PairReceipts.route520 3),
    (PairReceipts.route520 4),
    (PairReceipts.route520 5),
    (PairReceipts.route520 6),
    (PairReceipts.route520 7),
    (PairReceipts.route520 8),
    (PairReceipts.route520 9),
    (PairReceipts.route520 10),
    (PairReceipts.route520 11),
    (PairReceipts.route520 12),
    (PairReceipts.route520 13),
    (PairReceipts.route520 14),
    (PairReceipts.route520 15),
    (PairReceipts.route520 16),
    trivial⟩)
theorem case116: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,20,some 20⟩:=PairRoute.start _ allAxes222
private theorem allAxes266:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 21 ⟨
    (PairReceipts.route480 14),
    (PairReceipts.route480 15),
    (PairReceipts.route480 16),
    (PairReceipts.route480 17),
    (PairReceipts.route480 18),
    (PairReceipts.route480 19),
    (PairReceipts.route500 0),
    (PairReceipts.route500 1),
    (PairReceipts.route500 2),
    (PairReceipts.route500 3),
    (PairReceipts.route500 4),
    (PairReceipts.route500 5),
    (PairReceipts.route500 6),
    (PairReceipts.route500 7),
    (PairReceipts.route500 8),
    (PairReceipts.route500 9),
    (PairReceipts.route500 10),
    (PairReceipts.route500 11),
    (PairReceipts.route500 12),
    (PairReceipts.route500 13),
    (PairReceipts.route500 14),
    (PairReceipts.route500 15),
    trivial⟩)
theorem case117: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,21,some 21⟩:=PairRoute.start _ allAxes266
private def leaf267 := (PairReceipts.route480 13)
theorem case118: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,22,some 22⟩:=PairRoute.start _ leaf267
private def leaf268 := (PairReceipts.route480 12)
theorem case119: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,23,some 24⟩:=PairRoute.start _ leaf268
end Research6969.HardFit1At110
end Z6969Source2622

-- Source: Research6969.HardFit1At120
section Z6969Source2623
set_option autoImplicit true
namespace Research6969.HardFit1At120
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route480 11)
theorem case120: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,25,some 26⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route480 10)
theorem case121: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,27,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route480 9)
theorem case122: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,29,some 32⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route480 8)
theorem case123: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,33,some 36⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route480 7)
theorem case124: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,37,some 40⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route480 6)
theorem case125: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,41,some 48⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route480 5)
theorem case126: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,49,some 64⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route480 4)
theorem case127: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,65,some 96⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route620 14)
theorem case128: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route620 13)
theorem case129: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit1At120
end Z6969Source2623

-- Source: Research6969.PairReceipts035
section Z6969Source2624
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell700:PairCell.Row:=⟨41,49,9,2,57,some 64,63,some 63,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check700:(cell700.cap (0:Fin 18)).grade<cell700.lowerGrade-cell700.off:=by decide +kernel
def cell701:PairCell.Row:=⟨41,49,9,2,57,some 64,64,some 64,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check701:(cell701.cap (0:Fin 18)).grade<cell701.lowerGrade-cell701.off:=by decide +kernel
private def rows702 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 56,0,none,257319,[MeasuredChoices.test62],[]⟩,0,⟨(.node 8026411704957730),.whole,.impossible,285209⟩⟩,
  ⟨⟨41,49,9,2,49,some 56,0,none,285209,[MeasuredChoices.test104],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,0,⟨(.node 8059959167344767),.whole,.impossible,302619⟩⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,2,4,some 8,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,3,47,some 48,0,some 0,385979,[MeasuredChoices.test1141],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨41,49,9,3,47,some 48,1,some 1,385979,[MeasuredChoices.test1141],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨41,49,9,3,47,some 48,2,some 2,385979,[MeasuredChoices.test1141],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨41,49,9,3,47,some 48,3,some 3,385979,[MeasuredChoices.test1141],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨41,49,9,3,47,some 48,4,some 4,385979,[MeasuredChoices.test1141],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨41,49,9,3,47,some 48,5,some 5,385979,[MeasuredChoices.test1141],[AxisChoices.test1826]⟩,0,separateWhole⟩]
private theorem paid702 : StockPairs.checked rows702 = true := by decide +kernel
theorem route702 (i : Fin 18) : (rows702.get i).Done :=
  StockPairs.doneAt paid702 i

end Research6969.PairReceipts
end Z6969Source2624

-- Source: Research6969.PairReceipts258
section Z6969Source2625
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5160 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,25,some 28,0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩,8,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,8,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,17,some 20,0,none,257319,[],[]⟩,8,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,13,some 16,0,none,257319,[],[]⟩,8,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,9,some 12,0,none,257319,[],[]⟩,8,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨50,50,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨50,50,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨50,50,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨50,50,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩]
private theorem paid5160 : StockPairs.checked rows5160 = true := by decide +kernel
theorem route5160 (i : Fin 9) : (rows5160.get i).Done :=
  StockPairs.doneAt paid5160 i

def cell5165:PairCell.Row:=⟨33,40,9,4,25,some 28,0,none,514639,[MeasuredChoices.test1272],[]⟩
theorem check5165:ThreeRule.check cell5165 (0:Fin 18)=true:=by decide +kernel
def cell5166:PairCell.Row:=⟨41,49,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩
theorem check5166:ThreeRule.check cell5166 (0:Fin 18)=true:=by decide +kernel
def cell5167:PairCell.Row:=⟨41,49,9,3,57,some 64,0,none,385979,[MeasuredChoices.test1144],[]⟩
theorem check5167:ThreeRule.check cell5167 (0:Fin 18)=true:=by decide +kernel
def cell5168:PairCell.Row:=⟨41,49,9,3,49,some 56,0,none,385979,[MeasuredChoices.test1143],[]⟩
theorem check5168:ThreeRule.check cell5168 (0:Fin 18)=true:=by decide +kernel
def cell5169:PairCell.Row:=⟨25,27,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩
theorem check5169:ThreeRule.check cell5169 (1:Fin 18)=true:=by decide +kernel
def cell5170:PairCell.Row:=⟨28,32,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩
theorem check5170:ThreeRule.check cell5170 (1:Fin 18)=true:=by decide +kernel
def cell5171:PairCell.Row:=⟨33,40,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩
theorem check5171:ThreeRule.check cell5171 (1:Fin 18)=true:=by decide +kernel
def cell5172:PairCell.Row:=⟨41,49,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩
theorem check5172:ThreeRule.check cell5172 (1:Fin 18)=true:=by decide +kernel
def cell5173:PairCell.Row:=⟨41,49,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩
theorem check5173:ThreeRule.check cell5173 (1:Fin 18)=true:=by decide +kernel
def cell5174:PairCell.Row:=⟨41,49,9,3,45,some 48,0,none,385979,[MeasuredChoices.test1139],[]⟩
theorem check5174:ThreeRule.check cell5174 (1:Fin 18)=true:=by decide +kernel
def cell5175:PairCell.Row:=⟨41,49,9,3,41,some 44,0,none,385979,[MeasuredChoices.test1133],[]⟩
theorem check5175:ThreeRule.check cell5175 (1:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2625

-- Source: Research6969.HardFit1At130
section Z6969Source2626
set_option autoImplicit true
namespace Research6969.HardFit1At130
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route620 12)
theorem case130: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,21,some 24⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,4,25,some 28⟩,0,none,514639,none⟩:=PairLeaves.three PairReceipts.cell5165 PairReceipts.check5165 (by decide) (none)
theorem case131: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,25,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route620 11)
theorem case132: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,29,some 32⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route620 10)
theorem case133: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,33,some 40⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route620 15)
theorem case134: NormalRoute.Done (0:Fin 18) ⟨41,49,9,1,65,some 96⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route702 11)
theorem case135: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,4,some 8⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route702 10)
theorem case136: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route702 9)
theorem case137: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route702 8)
theorem case138: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route702 7)
theorem case139: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf9
end Research6969.HardFit1At130
end Z6969Source2626

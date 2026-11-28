import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0936
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.HardFit1At070
section Z6969Source2603
set_option autoImplicit true
namespace Research6969.HardFit1At070
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route280 19)
theorem case70: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route280 17)
private def leaf2 := (PairReceipts.route280 18)
private def weight3 := PairRoute.weight 302619 leaf1 leaf2
theorem case71: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ weight3
private def leaf4 := (PairReceipts.route280 16)
theorem case72: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,29,some 32⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route280 15)
theorem case73: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,33,some 40⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route280 14)
theorem case74: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,41,some 48⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route280 13)
theorem case75: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,49,some 64⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route280 12)
theorem case76: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,65,some 96⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route460 7)
theorem case77: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,4,some 8⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route460 6)
theorem case78: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route460 5)
theorem case79: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,13,some 14⟩:=PairRoute.start _ leaf11
end Research6969.HardFit1At070
end Z6969Source2603

-- Source: Research6969.PairReceipts016
section Z6969Source2604
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows320 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,22,some 22,11,some 11,385979,[MeasuredChoices.test882],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,12,some 12,385979,[MeasuredChoices.test882],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,13,some 13,385979,[MeasuredChoices.test882],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,14,some 14,385979,[MeasuredChoices.test882],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,15,some 15,385979,[MeasuredChoices.test882],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,16,some 16,385979,[MeasuredChoices.test882],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,17,some 17,385979,[MeasuredChoices.test882],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,18,some 18,385979,[MeasuredChoices.test882],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,19,some 19,385979,[MeasuredChoices.test882],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,20,some 20,385979,[MeasuredChoices.test882],[AxisChoices.test1841]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,21,some 21,385979,[MeasuredChoices.test882],[AxisChoices.test1842]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,22,some 22,22,some 22,385979,[MeasuredChoices.test882],[AxisChoices.test1843]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩]
private theorem paid320 : StockPairs.checked rows320 = true := by decide +kernel
theorem route320 (i : Fin 20) : (rows320.get i).Done :=
  StockPairs.doneAt paid320 i

end Research6969.PairReceipts
end Z6969Source2604

-- Source: Research6969.PairReceipts017
section Z6969Source2605
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows340 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,21,some 21,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,21,some 21,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,0,separateWhole⟩]
private theorem paid340 : StockPairs.checked rows340 = true := by decide +kernel
theorem route340 (i : Fin 20) : (rows340.get i).Done :=
  StockPairs.doneAt paid340 i

end Research6969.PairReceipts
end Z6969Source2605

-- Source: Research6969.PairReceipts018
section Z6969Source2606
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows360 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,0,separateWhole⟩]
private theorem paid360 : StockPairs.checked rows360 = true := by decide +kernel
theorem route360 (i : Fin 20) : (rows360.get i).Done :=
  StockPairs.doneAt paid360 i

end Research6969.PairReceipts
end Z6969Source2606

-- Source: Research6969.PairReceipts019
section Z6969Source2607
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows380 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,0,separateWhole⟩]
private theorem paid380 : StockPairs.checked rows380 = true := by decide +kernel
theorem route380 (i : Fin 20) : (rows380.get i).Done :=
  StockPairs.doneAt paid380 i

end Research6969.PairReceipts
end Z6969Source2607

-- Source: Research6969.PairReceipts020
section Z6969Source2608
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows400 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,0,separateWhole⟩]
private theorem paid400 : StockPairs.checked rows400 = true := by decide +kernel
theorem route400 (i : Fin 20) : (rows400.get i).Done :=
  StockPairs.doneAt paid400 i

end Research6969.PairReceipts
end Z6969Source2608

-- Source: Research6969.PairReceipts021
section Z6969Source2609
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows420 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,0,separateWhole⟩]
private theorem paid420 : StockPairs.checked rows420 = true := by decide +kernel
theorem route420 (i : Fin 20) : (rows420.get i).Done :=
  StockPairs.doneAt paid420 i

end Research6969.PairReceipts
end Z6969Source2609

-- Source: Research6969.PairReceipts022
section Z6969Source2610
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows440 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,0,separateWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,0,markedAxisWhole⟩,
  ⟨⟨28,32,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩]
private theorem paid440 : StockPairs.checked rows440 = true := by decide +kernel
theorem route440 (i : Fin 20) : (rows440.get i).Done :=
  StockPairs.doneAt paid440 i

end Research6969.PairReceipts
end Z6969Source2610

-- Source: Research6969.HardFit1At080
section Z6969Source2611
set_option autoImplicit true
namespace Research6969.HardFit1At080
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes31:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route440 9),
    (PairReceipts.route440 10),
    (PairReceipts.route440 11),
    (PairReceipts.route440 12),
    (PairReceipts.route440 13),
    (PairReceipts.route440 14),
    (PairReceipts.route440 15),
    (PairReceipts.route440 16),
    (PairReceipts.route440 17),
    (PairReceipts.route440 18),
    (PairReceipts.route440 19),
    (PairReceipts.route460 0),
    (PairReceipts.route460 1),
    (PairReceipts.route460 2),
    (PairReceipts.route460 3),
    (PairReceipts.route460 4),
    trivial⟩)
theorem case80: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,15,some 15⟩:=PairRoute.start _ allAxes31
private theorem allAxes65:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route420 12),
    (PairReceipts.route420 13),
    (PairReceipts.route420 14),
    (PairReceipts.route420 15),
    (PairReceipts.route420 16),
    (PairReceipts.route420 17),
    (PairReceipts.route420 18),
    (PairReceipts.route420 19),
    (PairReceipts.route440 0),
    (PairReceipts.route440 1),
    (PairReceipts.route440 2),
    (PairReceipts.route440 3),
    (PairReceipts.route440 4),
    (PairReceipts.route440 5),
    (PairReceipts.route440 6),
    (PairReceipts.route440 7),
    (PairReceipts.route440 8),
    trivial⟩)
theorem case81: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,16,some 16⟩:=PairRoute.start _ allAxes65
private theorem allAxes101:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route400 14),
    (PairReceipts.route400 15),
    (PairReceipts.route400 16),
    (PairReceipts.route400 17),
    (PairReceipts.route400 18),
    (PairReceipts.route400 19),
    (PairReceipts.route420 0),
    (PairReceipts.route420 1),
    (PairReceipts.route420 2),
    (PairReceipts.route420 3),
    (PairReceipts.route420 4),
    (PairReceipts.route420 5),
    (PairReceipts.route420 6),
    (PairReceipts.route420 7),
    (PairReceipts.route420 8),
    (PairReceipts.route420 9),
    (PairReceipts.route420 10),
    (PairReceipts.route420 11),
    trivial⟩)
theorem case82: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,17,some 17⟩:=PairRoute.start _ allAxes101
private theorem allAxes139:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route380 15),
    (PairReceipts.route380 16),
    (PairReceipts.route380 17),
    (PairReceipts.route380 18),
    (PairReceipts.route380 19),
    (PairReceipts.route400 0),
    (PairReceipts.route400 1),
    (PairReceipts.route400 2),
    (PairReceipts.route400 3),
    (PairReceipts.route400 4),
    (PairReceipts.route400 5),
    (PairReceipts.route400 6),
    (PairReceipts.route400 7),
    (PairReceipts.route400 8),
    (PairReceipts.route400 9),
    (PairReceipts.route400 10),
    (PairReceipts.route400 11),
    (PairReceipts.route400 12),
    (PairReceipts.route400 13),
    trivial⟩)
theorem case83: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,18,some 18⟩:=PairRoute.start _ allAxes139
private theorem allAxes179:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route360 15),
    (PairReceipts.route360 16),
    (PairReceipts.route360 17),
    (PairReceipts.route360 18),
    (PairReceipts.route360 19),
    (PairReceipts.route380 0),
    (PairReceipts.route380 1),
    (PairReceipts.route380 2),
    (PairReceipts.route380 3),
    (PairReceipts.route380 4),
    (PairReceipts.route380 5),
    (PairReceipts.route380 6),
    (PairReceipts.route380 7),
    (PairReceipts.route380 8),
    (PairReceipts.route380 9),
    (PairReceipts.route380 10),
    (PairReceipts.route380 11),
    (PairReceipts.route380 12),
    (PairReceipts.route380 13),
    (PairReceipts.route380 14),
    trivial⟩)
theorem case84: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,19,some 19⟩:=PairRoute.start _ allAxes179
private theorem allAxes221:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route340 14),
    (PairReceipts.route340 15),
    (PairReceipts.route340 16),
    (PairReceipts.route340 17),
    (PairReceipts.route340 18),
    (PairReceipts.route340 19),
    (PairReceipts.route360 0),
    (PairReceipts.route360 1),
    (PairReceipts.route360 2),
    (PairReceipts.route360 3),
    (PairReceipts.route360 4),
    (PairReceipts.route360 5),
    (PairReceipts.route360 6),
    (PairReceipts.route360 7),
    (PairReceipts.route360 8),
    (PairReceipts.route360 9),
    (PairReceipts.route360 10),
    (PairReceipts.route360 11),
    (PairReceipts.route360 12),
    (PairReceipts.route360 13),
    (PairReceipts.route360 14),
    trivial⟩)
theorem case85: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,20,some 20⟩:=PairRoute.start _ allAxes221
private theorem allAxes265:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 21 ⟨
    (PairReceipts.route320 12),
    (PairReceipts.route320 13),
    (PairReceipts.route320 14),
    (PairReceipts.route320 15),
    (PairReceipts.route320 16),
    (PairReceipts.route320 17),
    (PairReceipts.route320 18),
    (PairReceipts.route320 19),
    (PairReceipts.route340 0),
    (PairReceipts.route340 1),
    (PairReceipts.route340 2),
    (PairReceipts.route340 3),
    (PairReceipts.route340 4),
    (PairReceipts.route340 5),
    (PairReceipts.route340 6),
    (PairReceipts.route340 7),
    (PairReceipts.route340 8),
    (PairReceipts.route340 9),
    (PairReceipts.route340 10),
    (PairReceipts.route340 11),
    (PairReceipts.route340 12),
    (PairReceipts.route340 13),
    trivial⟩)
theorem case86: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,21,some 21⟩:=PairRoute.start _ allAxes265
private theorem allAxes311:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 22 ⟨
    (PairReceipts.route300 9),
    (PairReceipts.route300 10),
    (PairReceipts.route300 11),
    (PairReceipts.route300 12),
    (PairReceipts.route300 13),
    (PairReceipts.route300 14),
    (PairReceipts.route300 15),
    (PairReceipts.route300 16),
    (PairReceipts.route300 17),
    (PairReceipts.route300 18),
    (PairReceipts.route300 19),
    (PairReceipts.route320 0),
    (PairReceipts.route320 1),
    (PairReceipts.route320 2),
    (PairReceipts.route320 3),
    (PairReceipts.route320 4),
    (PairReceipts.route320 5),
    (PairReceipts.route320 6),
    (PairReceipts.route320 7),
    (PairReceipts.route320 8),
    (PairReceipts.route320 9),
    (PairReceipts.route320 10),
    (PairReceipts.route320 11),
    trivial⟩)
theorem case87: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,22,some 22⟩:=PairRoute.start _ allAxes311
private def leaf312 := (PairReceipts.route300 8)
theorem case88: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,23,some 24⟩:=PairRoute.start _ leaf312
private def leaf313 := (PairReceipts.route300 7)
theorem case89: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,25,some 26⟩:=PairRoute.start _ leaf313
end Research6969.HardFit1At080
end Z6969Source2611

-- Source: Research6969.PairReceipts024
section Z6969Source2612
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows480 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,2,4,some 8,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,65,some 96,0,none,385979,[MeasuredChoices.test1147],[]⟩,0,markedWhole⟩,
  ⟨⟨33,40,9,3,49,some 64,0,none,385979,[MeasuredChoices.test1143],[]⟩,0,markedWhole⟩,
  ⟨⟨33,40,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,0,markedWhole⟩,
  ⟨⟨33,40,9,3,37,some 40,0,none,385979,[MeasuredChoices.test1079],[]⟩,0,markedWhole⟩,
  ⟨⟨33,40,9,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,21,some 21,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,0,separateWhole⟩]
private theorem paid480 : StockPairs.checked rows480 = true := by decide +kernel
theorem route480 (i : Fin 20) : (rows480.get i).Done :=
  StockPairs.doneAt paid480 i

end Research6969.PairReceipts
end Z6969Source2612

-- Source: Research6969.HardFit1At090
section Z6969Source2613
set_option autoImplicit true
namespace Research6969.HardFit1At090
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route300 6)
theorem case90: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,27,some 28⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route300 5)
theorem case91: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,29,some 32⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route300 4)
theorem case92: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,33,some 40⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route460 10)
theorem case93: NormalRoute.Done (0:Fin 18) ⟨28,32,9,4,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route460 9)
theorem case94: NormalRoute.Done (0:Fin 18) ⟨28,32,9,4,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route460 8)
theorem case95: NormalRoute.Done (0:Fin 18) ⟨28,32,9,4,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route460 11)
theorem case96: NormalRoute.Done (0:Fin 18) ⟨33,40,9,1,65,some 96⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route480 3)
theorem case97: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,4,some 8⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route480 2)
theorem case98: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route480 1)
theorem case99: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6969.HardFit1At090
end Z6969Source2613

-- Source: Research6969.PairReceipts031
section Z6969Source2614
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows620 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,0,separateWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,0,markedAxisWhole⟩,
  ⟨⟨33,40,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,4,33,some 40,0,none,514639,[MeasuredChoices.test1298],[]⟩,0,markedWhole⟩,
  ⟨⟨33,40,9,4,29,some 32,0,none,514639,[MeasuredChoices.test1285],[]⟩,0,markedWhole⟩,
  ⟨⟨33,40,9,4,21,some 24,0,none,514639,[MeasuredChoices.test1270],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,4,17,some 20,0,none,514639,[MeasuredChoices.test1268],[]⟩,0,surfaceWhole⟩,
  ⟨⟨33,40,9,4,13,some 16,0,none,514639,[MeasuredChoices.test1256],[]⟩,0,surfaceWhole⟩,
  ⟨⟨41,49,9,1,65,some 96,0,none,128659,[MeasuredChoices.test7],[]⟩,0,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨41,49,9,2,65,some 96,0,none,257319,[MeasuredChoices.test86,MeasuredChoices.test87],[]⟩,0,markedWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,0,some 0,257319,[MeasuredChoices.test79],[]⟩,0,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,1,some 1,257319,[MeasuredChoices.test79],[]⟩,0,separateWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,2,some 2,257319,[MeasuredChoices.test79],[]⟩,0,separateWhole⟩]
private theorem paid620 : StockPairs.checked rows620 = true := by decide +kernel
theorem route620 (i : Fin 20) : (rows620.get i).Done :=
  StockPairs.doneAt paid620 i

end Research6969.PairReceipts
end Z6969Source2614

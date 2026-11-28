import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.PairReceipts163
section Z6969Source2819
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3260 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,23,some 23,3,some 3,385979,[MeasuredChoices.test896],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,4,some 4,385979,[MeasuredChoices.test896],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,5,some 5,385979,[MeasuredChoices.test896],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,6,some 6,385979,[MeasuredChoices.test896],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,7,some 7,385979,[MeasuredChoices.test896],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,8,some 8,385979,[MeasuredChoices.test896],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,9,some 9,385979,[MeasuredChoices.test896],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,10,some 10,385979,[MeasuredChoices.test896],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,11,some 11,385979,[MeasuredChoices.test896],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,12,some 12,385979,[MeasuredChoices.test896],[AxisChoices.test1833]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,13,some 13,385979,[MeasuredChoices.test896],[AxisChoices.test1834]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,14,some 14,385979,[MeasuredChoices.test896],[AxisChoices.test1835]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,15,some 15,385979,[MeasuredChoices.test896],[AxisChoices.test1836]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,16,some 16,385979,[MeasuredChoices.test896],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,17,some 17,385979,[MeasuredChoices.test896],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,18,some 18,385979,[MeasuredChoices.test896],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,19,some 19,385979,[MeasuredChoices.test896],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,20,some 20,385979,[MeasuredChoices.test896],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,21,some 21,385979,[MeasuredChoices.test896],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,23,some 23,22,some 22,385979,[MeasuredChoices.test896],[AxisChoices.test1843]⟩,2,markedAxisIntersection⟩]
private theorem paid3260 : StockPairs.checked rows3260 = true := by decide +kernel
theorem route3260 (i : Fin 20) : (rows3260.get i).Done :=
  StockPairs.doneAt paid3260 i

end Research6969.PairReceipts
end Z6969Source2819

-- Source: Research6969.PairReceipts164
section Z6969Source2820
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3280 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,23,some 23,23,some 23,385979,[MeasuredChoices.test896],[AxisChoices.test1844]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,0,some 0,385979,[MeasuredChoices.test882],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,1,some 1,385979,[MeasuredChoices.test882],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,2,some 2,385979,[MeasuredChoices.test882],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,3,some 3,385979,[MeasuredChoices.test882],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,4,some 4,385979,[MeasuredChoices.test882],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,5,some 5,385979,[MeasuredChoices.test882],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,6,some 6,385979,[MeasuredChoices.test882],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,7,some 7,385979,[MeasuredChoices.test882],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,8,some 8,385979,[MeasuredChoices.test882],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,9,some 9,385979,[MeasuredChoices.test882],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,10,some 10,385979,[MeasuredChoices.test882],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,11,some 11,385979,[MeasuredChoices.test882],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,12,some 12,385979,[MeasuredChoices.test882],[AxisChoices.test1833]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,13,some 13,385979,[MeasuredChoices.test882],[AxisChoices.test1834]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,14,some 14,385979,[MeasuredChoices.test882],[AxisChoices.test1835]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,15,some 15,385979,[MeasuredChoices.test882],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,16,some 16,385979,[MeasuredChoices.test882],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,17,some 17,385979,[MeasuredChoices.test882],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,18,some 18,385979,[MeasuredChoices.test882],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩]
private theorem paid3280 : StockPairs.checked rows3280 = true := by decide +kernel
theorem route3280 (i : Fin 20) : (rows3280.get i).Done :=
  StockPairs.doneAt paid3280 i

end Research6969.PairReceipts
end Z6969Source2820

-- Source: Research6969.PairReceipts165
section Z6969Source2821
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3300 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,22,some 22,19,some 19,385979,[MeasuredChoices.test882],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,20,some 20,385979,[MeasuredChoices.test882],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,21,some 21,385979,[MeasuredChoices.test882],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,22,some 22,385979,[MeasuredChoices.test882],[AxisChoices.test1843]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩]
private theorem paid3300 : StockPairs.checked rows3300 = true := by decide +kernel
theorem route3300 (i : Fin 20) : (rows3300.get i).Done :=
  StockPairs.doneAt paid3300 i

end Research6969.PairReceipts
end Z6969Source2821

-- Source: Research6969.PairReceipts166
section Z6969Source2822
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3320 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,21,some 21,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,2,separateIntersection⟩]
private theorem paid3320 : StockPairs.checked rows3320 = true := by decide +kernel
theorem route3320 (i : Fin 20) : (rows3320.get i).Done :=
  StockPairs.doneAt paid3320 i

end Research6969.PairReceipts
end Z6969Source2822

-- Source: Research6969.PairReceipts167
section Z6969Source2823
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3340 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,2,separateIntersection⟩]
private theorem paid3340 : StockPairs.checked rows3340 = true := by decide +kernel
theorem route3340 (i : Fin 20) : (rows3340.get i).Done :=
  StockPairs.doneAt paid3340 i

end Research6969.PairReceipts
end Z6969Source2823

-- Source: Research6969.PairReceipts168
section Z6969Source2824
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3360 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,2,separateIntersection⟩]
private theorem paid3360 : StockPairs.checked rows3360 = true := by decide +kernel
theorem route3360 (i : Fin 20) : (rows3360.get i).Done :=
  StockPairs.doneAt paid3360 i

end Research6969.PairReceipts
end Z6969Source2824

-- Source: Research6969.PairReceipts296
section Z6969Source2825
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5920:PairCell.Row:=⟨63,63,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5920:ThreeRule.check cell5920 (2:Fin 18)=true:=by decide +kernel
def cell5921:PairCell.Row:=⟨63,63,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5921:ThreeRule.check cell5921 (2:Fin 18)=true:=by decide +kernel
def cell5922:PairCell.Row:=⟨63,63,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5922:ThreeRule.check cell5922 (2:Fin 18)=true:=by decide +kernel
def cell5923:PairCell.Row:=⟨63,63,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5923:ThreeRule.check cell5923 (2:Fin 18)=true:=by decide +kernel
def cell5924:PairCell.Row:=⟨63,63,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5924:ThreeRule.check cell5924 (2:Fin 18)=true:=by decide +kernel
def cell5925:PairCell.Row:=⟨63,63,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5925:ThreeRule.check cell5925 (2:Fin 18)=true:=by decide +kernel
def cell5926:PairCell.Row:=⟨63,63,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5926:ThreeRule.check cell5926 (2:Fin 18)=true:=by decide +kernel
def cell5927:PairCell.Row:=⟨63,63,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5927:ThreeRule.check cell5927 (2:Fin 18)=true:=by decide +kernel
def cell5928:PairCell.Row:=⟨63,63,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5928:ThreeRule.check cell5928 (2:Fin 18)=true:=by decide +kernel
def cell5929:PairCell.Row:=⟨63,63,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5929:ThreeRule.check cell5929 (2:Fin 18)=true:=by decide +kernel
def cell5930:PairCell.Row:=⟨63,63,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5930:ThreeRule.check cell5930 (2:Fin 18)=true:=by decide +kernel
def cell5931:PairCell.Row:=⟨63,63,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5931:ThreeRule.check cell5931 (2:Fin 18)=true:=by decide +kernel
def cell5932:PairCell.Row:=⟨63,63,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5932:ThreeRule.check cell5932 (2:Fin 18)=true:=by decide +kernel
def cell5933:PairCell.Row:=⟨63,63,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5933:ThreeRule.check cell5933 (2:Fin 18)=true:=by decide +kernel
def cell5934:PairCell.Row:=⟨63,63,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5934:ThreeRule.check cell5934 (2:Fin 18)=true:=by decide +kernel
def cell5935:PairCell.Row:=⟨63,63,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5935:ThreeRule.check cell5935 (2:Fin 18)=true:=by decide +kernel
private def rows5936 : List StockPairs.Receipt := [
  ⟨⟨50,50,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩]
private theorem paid5936 : StockPairs.checked rows5936 = true := by decide +kernel
theorem route5936 (i : Fin 4) : (rows5936.get i).Done :=
  StockPairs.doneAt paid5936 i

end Research6969.PairReceipts
end Z6969Source2825

-- Source: Research6969.PairReceipts297
section Z6969Source2826
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5940 : List StockPairs.Receipt := [
  ⟨⟨50,50,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩]
private theorem paid5940 : StockPairs.checked rows5940 = true := by decide +kernel
theorem route5940 (i : Fin 12) : (rows5940.get i).Done :=
  StockPairs.doneAt paid5940 i

def cell5946:PairCell.Row:=⟨50,50,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩
theorem check5946:ThreeRule.check cell5946 (2:Fin 18)=true:=by decide +kernel
def cell5947:PairCell.Row:=⟨50,50,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩
theorem check5947:ThreeRule.check cell5947 (2:Fin 18)=true:=by decide +kernel
def cell5948:PairCell.Row:=⟨50,50,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check5948:ThreeRule.check cell5948 (2:Fin 18)=true:=by decide +kernel
def cell5949:PairCell.Row:=⟨50,50,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check5949:ThreeRule.check cell5949 (2:Fin 18)=true:=by decide +kernel
def cell5950:PairCell.Row:=⟨50,50,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check5950:ThreeRule.check cell5950 (2:Fin 18)=true:=by decide +kernel
def cell5951:PairCell.Row:=⟨50,50,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check5951:ThreeRule.check cell5951 (2:Fin 18)=true:=by decide +kernel
def cell5952:PairCell.Row:=⟨50,50,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check5952:ThreeRule.check cell5952 (2:Fin 18)=true:=by decide +kernel
def cell5953:PairCell.Row:=⟨50,50,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check5953:ThreeRule.check cell5953 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2826

-- Source: Research6969.PairReceipts298
section Z6969Source2827
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5960 : List StockPairs.Receipt := [
  ⟨⟨51,51,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩]
private theorem paid5960 : StockPairs.checked rows5960 = true := by decide +kernel
theorem route5960 (i : Fin 13) : (rows5960.get i).Done :=
  StockPairs.doneAt paid5960 i

def cell5965:PairCell.Row:=⟨51,51,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩
theorem check5965:ThreeRule.check cell5965 (2:Fin 18)=true:=by decide +kernel
def cell5966:PairCell.Row:=⟨51,51,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check5966:ThreeRule.check cell5966 (2:Fin 18)=true:=by decide +kernel
def cell5967:PairCell.Row:=⟨51,51,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check5967:ThreeRule.check cell5967 (2:Fin 18)=true:=by decide +kernel
def cell5968:PairCell.Row:=⟨51,51,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check5968:ThreeRule.check cell5968 (2:Fin 18)=true:=by decide +kernel
def cell5969:PairCell.Row:=⟨51,51,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check5969:ThreeRule.check cell5969 (2:Fin 18)=true:=by decide +kernel
def cell5970:PairCell.Row:=⟨51,51,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check5970:ThreeRule.check cell5970 (2:Fin 18)=true:=by decide +kernel
def cell5971:PairCell.Row:=⟨51,51,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check5971:ThreeRule.check cell5971 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2827

-- Source: Research6969.PairReceipts299
section Z6969Source2828
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5980 : List StockPairs.Receipt := [
  ⟨⟨52,52,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid5980 : StockPairs.checked rows5980 = true := by decide +kernel
theorem route5980 (i : Fin 13) : (rows5980.get i).Done :=
  StockPairs.doneAt paid5980 i

def cell5983:PairCell.Row:=⟨52,52,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩
theorem check5983:ThreeRule.check cell5983 (2:Fin 18)=true:=by decide +kernel
def cell5984:PairCell.Row:=⟨52,52,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check5984:ThreeRule.check cell5984 (2:Fin 18)=true:=by decide +kernel
def cell5985:PairCell.Row:=⟨52,52,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check5985:ThreeRule.check cell5985 (2:Fin 18)=true:=by decide +kernel
def cell5986:PairCell.Row:=⟨52,52,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check5986:ThreeRule.check cell5986 (2:Fin 18)=true:=by decide +kernel
def cell5987:PairCell.Row:=⟨52,52,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check5987:ThreeRule.check cell5987 (2:Fin 18)=true:=by decide +kernel
def cell5988:PairCell.Row:=⟨52,52,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check5988:ThreeRule.check cell5988 (2:Fin 18)=true:=by decide +kernel
def cell5989:PairCell.Row:=⟨52,52,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check5989:ThreeRule.check cell5989 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2828

-- Source: Research6969.PairReceipts300
section Z6969Source2829
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6000 : List StockPairs.Receipt := [
  ⟨⟨53,53,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid6000 : StockPairs.checked rows6000 = true := by decide +kernel
theorem route6000 (i : Fin 12) : (rows6000.get i).Done :=
  StockPairs.doneAt paid6000 i
def cell6001:PairCell.Row:=⟨53,53,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩
theorem check6001:ThreeRule.check cell6001 (2:Fin 18)=true:=by decide +kernel
def cell6002:PairCell.Row:=⟨53,53,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6002:ThreeRule.check cell6002 (2:Fin 18)=true:=by decide +kernel
def cell6003:PairCell.Row:=⟨53,53,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6003:ThreeRule.check cell6003 (2:Fin 18)=true:=by decide +kernel
def cell6004:PairCell.Row:=⟨53,53,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6004:ThreeRule.check cell6004 (2:Fin 18)=true:=by decide +kernel
def cell6005:PairCell.Row:=⟨53,53,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6005:ThreeRule.check cell6005 (2:Fin 18)=true:=by decide +kernel
def cell6006:PairCell.Row:=⟨53,53,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6006:ThreeRule.check cell6006 (2:Fin 18)=true:=by decide +kernel
def cell6007:PairCell.Row:=⟨53,53,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6007:ThreeRule.check cell6007 (2:Fin 18)=true:=by decide +kernel

def cell6019:PairCell.Row:=⟨54,54,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩
theorem check6019:ThreeRule.check cell6019 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2829

-- Source: Research6969.PairReceipts301
section Z6969Source2830
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6020:PairCell.Row:=⟨54,54,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6020:ThreeRule.check cell6020 (2:Fin 18)=true:=by decide +kernel
def cell6021:PairCell.Row:=⟨54,54,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6021:ThreeRule.check cell6021 (2:Fin 18)=true:=by decide +kernel
def cell6022:PairCell.Row:=⟨54,54,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6022:ThreeRule.check cell6022 (2:Fin 18)=true:=by decide +kernel
def cell6023:PairCell.Row:=⟨54,54,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6023:ThreeRule.check cell6023 (2:Fin 18)=true:=by decide +kernel
def cell6024:PairCell.Row:=⟨54,54,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6024:ThreeRule.check cell6024 (2:Fin 18)=true:=by decide +kernel
def cell6025:PairCell.Row:=⟨54,54,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6025:ThreeRule.check cell6025 (2:Fin 18)=true:=by decide +kernel
private def rows6026 : List StockPairs.Receipt := [
  ⟨⟨55,55,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid6026 : StockPairs.checked rows6026 = true := by decide +kernel
theorem route6026 (i : Fin 11) : (rows6026.get i).Done :=
  StockPairs.doneAt paid6026 i

def cell6037:PairCell.Row:=⟨55,55,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩
theorem check6037:ThreeRule.check cell6037 (2:Fin 18)=true:=by decide +kernel
def cell6038:PairCell.Row:=⟨55,55,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6038:ThreeRule.check cell6038 (2:Fin 18)=true:=by decide +kernel
def cell6039:PairCell.Row:=⟨55,55,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6039:ThreeRule.check cell6039 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2830

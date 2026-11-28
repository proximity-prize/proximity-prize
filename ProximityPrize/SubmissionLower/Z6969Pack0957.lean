import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666

set_option Elab.async false

-- Source: Research6969.PairReceipts314
section Z6969Source2843
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6280 : List StockPairs.Receipt := [
  ⟨⟨55,55,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6280 : StockPairs.checked rows6280 = true := by decide +kernel
theorem route6280 (i : Fin 14) : (rows6280.get i).Done :=
  StockPairs.doneAt paid6280 i

def cell6284:PairCell.Row:=⟨55,55,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩
theorem check6284:ThreeRule.check cell6284 (2:Fin 18)=true:=by decide +kernel
def cell6285:PairCell.Row:=⟨55,55,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6285:ThreeRule.check cell6285 (2:Fin 18)=true:=by decide +kernel
def cell6286:PairCell.Row:=⟨55,55,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6286:ThreeRule.check cell6286 (2:Fin 18)=true:=by decide +kernel
def cell6287:PairCell.Row:=⟨55,55,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6287:ThreeRule.check cell6287 (2:Fin 18)=true:=by decide +kernel
def cell6288:PairCell.Row:=⟨55,55,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6288:ThreeRule.check cell6288 (2:Fin 18)=true:=by decide +kernel
def cell6289:PairCell.Row:=⟨55,55,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6289:ThreeRule.check cell6289 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2843

-- Source: Research6969.PairReceipts315
section Z6969Source2844
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6300 : List StockPairs.Receipt := [
  ⟨⟨56,56,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid6300 : StockPairs.checked rows6300 = true := by decide +kernel
theorem route6300 (i : Fin 14) : (rows6300.get i).Done :=
  StockPairs.doneAt paid6300 i

def cell6302:PairCell.Row:=⟨56,56,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6302:ThreeRule.check cell6302 (2:Fin 18)=true:=by decide +kernel
def cell6303:PairCell.Row:=⟨56,56,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6303:ThreeRule.check cell6303 (2:Fin 18)=true:=by decide +kernel
def cell6304:PairCell.Row:=⟨56,56,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6304:ThreeRule.check cell6304 (2:Fin 18)=true:=by decide +kernel
def cell6305:PairCell.Row:=⟨56,56,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6305:ThreeRule.check cell6305 (2:Fin 18)=true:=by decide +kernel
def cell6306:PairCell.Row:=⟨56,56,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6306:ThreeRule.check cell6306 (2:Fin 18)=true:=by decide +kernel

def cell6319:PairCell.Row:=⟨57,57,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6319:ThreeRule.check cell6319 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2844

-- Source: Research6969.PairReceipts316
section Z6969Source2845
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6320:PairCell.Row:=⟨57,57,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6320:ThreeRule.check cell6320 (2:Fin 18)=true:=by decide +kernel
def cell6321:PairCell.Row:=⟨57,57,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6321:ThreeRule.check cell6321 (2:Fin 18)=true:=by decide +kernel
def cell6322:PairCell.Row:=⟨57,57,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6322:ThreeRule.check cell6322 (2:Fin 18)=true:=by decide +kernel
def cell6323:PairCell.Row:=⟨57,57,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6323:ThreeRule.check cell6323 (2:Fin 18)=true:=by decide +kernel
private def rows6324 : List StockPairs.Receipt := [
  ⟨⟨58,58,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid6324 : StockPairs.checked rows6324 = true := by decide +kernel
theorem route6324 (i : Fin 12) : (rows6324.get i).Done :=
  StockPairs.doneAt paid6324 i

def cell6336:PairCell.Row:=⟨58,58,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6336:ThreeRule.check cell6336 (2:Fin 18)=true:=by decide +kernel
def cell6337:PairCell.Row:=⟨58,58,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6337:ThreeRule.check cell6337 (2:Fin 18)=true:=by decide +kernel
def cell6338:PairCell.Row:=⟨58,58,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6338:ThreeRule.check cell6338 (2:Fin 18)=true:=by decide +kernel
def cell6339:PairCell.Row:=⟨58,58,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6339:ThreeRule.check cell6339 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2845

-- Source: Research6969.PairReceipts317
section Z6969Source2846
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6340:PairCell.Row:=⟨58,58,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6340:ThreeRule.check cell6340 (2:Fin 18)=true:=by decide +kernel
private def rows6341 : List StockPairs.Receipt := [
  ⟨⟨59,59,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid6341 : StockPairs.checked rows6341 = true := by decide +kernel
theorem route6341 (i : Fin 14) : (rows6341.get i).Done :=
  StockPairs.doneAt paid6341 i

def cell6353:PairCell.Row:=⟨59,59,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6353:ThreeRule.check cell6353 (2:Fin 18)=true:=by decide +kernel
def cell6354:PairCell.Row:=⟨59,59,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6354:ThreeRule.check cell6354 (2:Fin 18)=true:=by decide +kernel
def cell6355:PairCell.Row:=⟨59,59,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6355:ThreeRule.check cell6355 (2:Fin 18)=true:=by decide +kernel
def cell6356:PairCell.Row:=⟨59,59,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6356:ThreeRule.check cell6356 (2:Fin 18)=true:=by decide +kernel
def cell6357:PairCell.Row:=⟨59,59,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6357:ThreeRule.check cell6357 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2846

-- Source: Research6969.PairReceipts318
section Z6969Source2847
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6360 : List StockPairs.Receipt := [
  ⟨⟨60,60,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩]
private theorem paid6360 : StockPairs.checked rows6360 = true := by decide +kernel
theorem route6360 (i : Fin 15) : (rows6360.get i).Done :=
  StockPairs.doneAt paid6360 i

def cell6370:PairCell.Row:=⟨60,60,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6370:ThreeRule.check cell6370 (2:Fin 18)=true:=by decide +kernel
def cell6371:PairCell.Row:=⟨60,60,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6371:ThreeRule.check cell6371 (2:Fin 18)=true:=by decide +kernel
def cell6372:PairCell.Row:=⟨60,60,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6372:ThreeRule.check cell6372 (2:Fin 18)=true:=by decide +kernel
def cell6373:PairCell.Row:=⟨60,60,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6373:ThreeRule.check cell6373 (2:Fin 18)=true:=by decide +kernel
def cell6374:PairCell.Row:=⟨60,60,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6374:ThreeRule.check cell6374 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2847

-- Source: Research6969.PairReceipts319
section Z6969Source2848
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6380 : List StockPairs.Receipt := [
  ⟨⟨61,61,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩]
private theorem paid6380 : StockPairs.checked rows6380 = true := by decide +kernel
theorem route6380 (i : Fin 15) : (rows6380.get i).Done :=
  StockPairs.doneAt paid6380 i

def cell6387:PairCell.Row:=⟨61,61,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6387:ThreeRule.check cell6387 (2:Fin 18)=true:=by decide +kernel
def cell6388:PairCell.Row:=⟨61,61,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6388:ThreeRule.check cell6388 (2:Fin 18)=true:=by decide +kernel
def cell6389:PairCell.Row:=⟨61,61,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6389:ThreeRule.check cell6389 (2:Fin 18)=true:=by decide +kernel
def cell6390:PairCell.Row:=⟨61,61,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6390:ThreeRule.check cell6390 (2:Fin 18)=true:=by decide +kernel
def cell6391:PairCell.Row:=⟨61,61,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6391:ThreeRule.check cell6391 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2848

-- Source: Research6969.PairReceipts320
section Z6969Source2849
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6400 : List StockPairs.Receipt := [
  ⟨⟨62,62,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid6400 : StockPairs.checked rows6400 = true := by decide +kernel
theorem route6400 (i : Fin 15) : (rows6400.get i).Done :=
  StockPairs.doneAt paid6400 i

def cell6404:PairCell.Row:=⟨62,62,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6404:ThreeRule.check cell6404 (2:Fin 18)=true:=by decide +kernel
def cell6405:PairCell.Row:=⟨62,62,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6405:ThreeRule.check cell6405 (2:Fin 18)=true:=by decide +kernel
def cell6406:PairCell.Row:=⟨62,62,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6406:ThreeRule.check cell6406 (2:Fin 18)=true:=by decide +kernel
def cell6407:PairCell.Row:=⟨62,62,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6407:ThreeRule.check cell6407 (2:Fin 18)=true:=by decide +kernel
def cell6408:PairCell.Row:=⟨62,62,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6408:ThreeRule.check cell6408 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2849

-- Source: Research6969.PairReceipts321
section Z6969Source2850
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6420 : List StockPairs.Receipt := [
  ⟨⟨63,63,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6420 : StockPairs.checked rows6420 = true := by decide +kernel
theorem route6420 (i : Fin 11) : (rows6420.get i).Done :=
  StockPairs.doneAt paid6420 i
def cell6421:PairCell.Row:=⟨63,63,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6421:ThreeRule.check cell6421 (2:Fin 18)=true:=by decide +kernel
def cell6422:PairCell.Row:=⟨63,63,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6422:ThreeRule.check cell6422 (2:Fin 18)=true:=by decide +kernel
def cell6423:PairCell.Row:=⟨63,63,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6423:ThreeRule.check cell6423 (2:Fin 18)=true:=by decide +kernel
def cell6424:PairCell.Row:=⟨63,63,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6424:ThreeRule.check cell6424 (2:Fin 18)=true:=by decide +kernel
def cell6425:PairCell.Row:=⟨63,63,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6425:ThreeRule.check cell6425 (2:Fin 18)=true:=by decide +kernel

def cell6436:PairCell.Row:=⟨50,50,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩
theorem check6436:ThreeRule.check cell6436 (2:Fin 18)=true:=by decide +kernel
def cell6437:PairCell.Row:=⟨50,50,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩
theorem check6437:ThreeRule.check cell6437 (2:Fin 18)=true:=by decide +kernel
def cell6438:PairCell.Row:=⟨50,50,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6438:ThreeRule.check cell6438 (2:Fin 18)=true:=by decide +kernel
def cell6439:PairCell.Row:=⟨50,50,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6439:ThreeRule.check cell6439 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2850

-- Source: Research6969.PairReceipts322
section Z6969Source2851
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6440:PairCell.Row:=⟨50,50,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6440:ThreeRule.check cell6440 (2:Fin 18)=true:=by decide +kernel
def cell6441:PairCell.Row:=⟨50,50,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6441:ThreeRule.check cell6441 (2:Fin 18)=true:=by decide +kernel
private def rows6442 : List StockPairs.Receipt := [
  ⟨⟨51,51,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid6442 : StockPairs.checked rows6442 = true := by decide +kernel
theorem route6442 (i : Fin 13) : (rows6442.get i).Done :=
  StockPairs.doneAt paid6442 i

def cell6453:PairCell.Row:=⟨51,51,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩
theorem check6453:ThreeRule.check cell6453 (2:Fin 18)=true:=by decide +kernel
def cell6454:PairCell.Row:=⟨51,51,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6454:ThreeRule.check cell6454 (2:Fin 18)=true:=by decide +kernel
def cell6455:PairCell.Row:=⟨51,51,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6455:ThreeRule.check cell6455 (2:Fin 18)=true:=by decide +kernel
def cell6456:PairCell.Row:=⟨51,51,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6456:ThreeRule.check cell6456 (2:Fin 18)=true:=by decide +kernel
def cell6457:PairCell.Row:=⟨51,51,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6457:ThreeRule.check cell6457 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2851

-- Source: Research6969.PairReceipts323
section Z6969Source2852
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6460 : List StockPairs.Receipt := [
  ⟨⟨52,52,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩]
private theorem paid6460 : StockPairs.checked rows6460 = true := by decide +kernel
theorem route6460 (i : Fin 15) : (rows6460.get i).Done :=
  StockPairs.doneAt paid6460 i

def cell6469:PairCell.Row:=⟨52,52,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩
theorem check6469:ThreeRule.check cell6469 (2:Fin 18)=true:=by decide +kernel
def cell6470:PairCell.Row:=⟨52,52,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6470:ThreeRule.check cell6470 (2:Fin 18)=true:=by decide +kernel
def cell6471:PairCell.Row:=⟨52,52,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6471:ThreeRule.check cell6471 (2:Fin 18)=true:=by decide +kernel
def cell6472:PairCell.Row:=⟨52,52,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6472:ThreeRule.check cell6472 (2:Fin 18)=true:=by decide +kernel
def cell6473:PairCell.Row:=⟨52,52,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6473:ThreeRule.check cell6473 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2852

-- Source: Research6969.PairReceipts324
section Z6969Source2853
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6480 : List StockPairs.Receipt := [
  ⟨⟨53,53,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6480 : StockPairs.checked rows6480 = true := by decide +kernel
theorem route6480 (i : Fin 15) : (rows6480.get i).Done :=
  StockPairs.doneAt paid6480 i

def cell6485:PairCell.Row:=⟨53,53,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩
theorem check6485:ThreeRule.check cell6485 (2:Fin 18)=true:=by decide +kernel
def cell6486:PairCell.Row:=⟨53,53,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6486:ThreeRule.check cell6486 (2:Fin 18)=true:=by decide +kernel
def cell6487:PairCell.Row:=⟨53,53,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6487:ThreeRule.check cell6487 (2:Fin 18)=true:=by decide +kernel
def cell6488:PairCell.Row:=⟨53,53,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6488:ThreeRule.check cell6488 (2:Fin 18)=true:=by decide +kernel
def cell6489:PairCell.Row:=⟨53,53,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6489:ThreeRule.check cell6489 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2853

-- Source: Research6969.PairReceipts325
section Z6969Source2854
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6500 : List StockPairs.Receipt := [
  ⟨⟨54,54,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid6500 : StockPairs.checked rows6500 = true := by decide +kernel
theorem route6500 (i : Fin 12) : (rows6500.get i).Done :=
  StockPairs.doneAt paid6500 i
def cell6501:PairCell.Row:=⟨54,54,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩
theorem check6501:ThreeRule.check cell6501 (2:Fin 18)=true:=by decide +kernel
def cell6502:PairCell.Row:=⟨54,54,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6502:ThreeRule.check cell6502 (2:Fin 18)=true:=by decide +kernel
def cell6503:PairCell.Row:=⟨54,54,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6503:ThreeRule.check cell6503 (2:Fin 18)=true:=by decide +kernel
def cell6504:PairCell.Row:=⟨54,54,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check6504:ThreeRule.check cell6504 (2:Fin 18)=true:=by decide +kernel
def cell6505:PairCell.Row:=⟨54,54,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check6505:ThreeRule.check cell6505 (2:Fin 18)=true:=by decide +kernel

def cell6517:PairCell.Row:=⟨55,55,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩
theorem check6517:ThreeRule.check cell6517 (2:Fin 18)=true:=by decide +kernel
def cell6518:PairCell.Row:=⟨55,55,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check6518:ThreeRule.check cell6518 (2:Fin 18)=true:=by decide +kernel
def cell6519:PairCell.Row:=⟨55,55,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check6519:ThreeRule.check cell6519 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2854

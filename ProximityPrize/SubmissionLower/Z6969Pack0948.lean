import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0945
import ProximityPrize.SubmissionLower.Z6969Pack0947
import ProximityPrize.SubmissionLower.Z6969Pack0938
import ProximityPrize.SubmissionLower.Z6969Pack0946
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.PairReceipts265
section Z6969Source2735
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5300:PairCell.Row:=⟨57,57,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check5300:ThreeRule.check cell5300 (1:Fin 18)=true:=by decide +kernel
def cell5301:PairCell.Row:=⟨57,57,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check5301:ThreeRule.check cell5301 (1:Fin 18)=true:=by decide +kernel
def cell5302:PairCell.Row:=⟨57,57,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check5302:ThreeRule.check cell5302 (1:Fin 18)=true:=by decide +kernel
def cell5303:PairCell.Row:=⟨57,57,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check5303:ThreeRule.check cell5303 (1:Fin 18)=true:=by decide +kernel
private def rows5304 : List StockPairs.Receipt := [
  ⟨⟨58,58,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨58,58,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,separateWhole⟩]
private theorem paid5304 : StockPairs.checked rows5304 = true := by decide +kernel
theorem route5304 (i : Fin 12) : (rows5304.get i).Done :=
  StockPairs.doneAt paid5304 i

def cell5316:PairCell.Row:=⟨58,58,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check5316:ThreeRule.check cell5316 (1:Fin 18)=true:=by decide +kernel
def cell5317:PairCell.Row:=⟨58,58,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check5317:ThreeRule.check cell5317 (1:Fin 18)=true:=by decide +kernel
def cell5318:PairCell.Row:=⟨58,58,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check5318:ThreeRule.check cell5318 (1:Fin 18)=true:=by decide +kernel
def cell5319:PairCell.Row:=⟨58,58,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check5319:ThreeRule.check cell5319 (1:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2735

-- Source: Research6969.PairReceipts266
section Z6969Source2736
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5320 : List StockPairs.Receipt := [
  ⟨⟨59,59,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨59,59,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩]
private theorem paid5320 : StockPairs.checked rows5320 = true := by decide +kernel
theorem route5320 (i : Fin 16) : (rows5320.get i).Done :=
  StockPairs.doneAt paid5320 i

def cell5332:PairCell.Row:=⟨59,59,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check5332:ThreeRule.check cell5332 (1:Fin 18)=true:=by decide +kernel
def cell5333:PairCell.Row:=⟨59,59,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check5333:ThreeRule.check cell5333 (1:Fin 18)=true:=by decide +kernel
def cell5334:PairCell.Row:=⟨59,59,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check5334:ThreeRule.check cell5334 (1:Fin 18)=true:=by decide +kernel
def cell5335:PairCell.Row:=⟨59,59,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check5335:ThreeRule.check cell5335 (1:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2736

-- Source: Research6969.PairReceipts267
section Z6969Source2737
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5340 : List StockPairs.Receipt := [
  ⟨⟨60,60,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨60,60,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩]
private theorem paid5340 : StockPairs.checked rows5340 = true := by decide +kernel
theorem route5340 (i : Fin 16) : (rows5340.get i).Done :=
  StockPairs.doneAt paid5340 i

def cell5348:PairCell.Row:=⟨60,60,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check5348:ThreeRule.check cell5348 (1:Fin 18)=true:=by decide +kernel
def cell5349:PairCell.Row:=⟨60,60,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check5349:ThreeRule.check cell5349 (1:Fin 18)=true:=by decide +kernel
def cell5350:PairCell.Row:=⟨60,60,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check5350:ThreeRule.check cell5350 (1:Fin 18)=true:=by decide +kernel
def cell5351:PairCell.Row:=⟨60,60,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check5351:ThreeRule.check cell5351 (1:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2737

-- Source: Research6969.PairReceipts268
section Z6969Source2738
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5360 : List StockPairs.Receipt := [
  ⟨⟨61,61,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨61,61,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨62,62,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,separateWhole⟩]
private theorem paid5360 : StockPairs.checked rows5360 = true := by decide +kernel
theorem route5360 (i : Fin 16) : (rows5360.get i).Done :=
  StockPairs.doneAt paid5360 i

def cell5364:PairCell.Row:=⟨61,61,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check5364:ThreeRule.check cell5364 (1:Fin 18)=true:=by decide +kernel
def cell5365:PairCell.Row:=⟨61,61,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check5365:ThreeRule.check cell5365 (1:Fin 18)=true:=by decide +kernel
def cell5366:PairCell.Row:=⟨61,61,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check5366:ThreeRule.check cell5366 (1:Fin 18)=true:=by decide +kernel
def cell5367:PairCell.Row:=⟨61,61,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check5367:ThreeRule.check cell5367 (1:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2738

-- Source: Research6969.PairReceipts269
section Z6969Source2739
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5380:PairCell.Row:=⟨62,62,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check5380:ThreeRule.check cell5380 (1:Fin 18)=true:=by decide +kernel
def cell5381:PairCell.Row:=⟨62,62,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check5381:ThreeRule.check cell5381 (1:Fin 18)=true:=by decide +kernel
def cell5382:PairCell.Row:=⟨62,62,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check5382:ThreeRule.check cell5382 (1:Fin 18)=true:=by decide +kernel
def cell5383:PairCell.Row:=⟨62,62,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check5383:ThreeRule.check cell5383 (1:Fin 18)=true:=by decide +kernel
private def rows5384 : List StockPairs.Receipt := [
  ⟨⟨63,63,10,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨63,63,10,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,separateWhole⟩]
private theorem paid5384 : StockPairs.checked rows5384 = true := by decide +kernel
theorem route5384 (i : Fin 12) : (rows5384.get i).Done :=
  StockPairs.doneAt paid5384 i

def cell5396:PairCell.Row:=⟨63,63,10,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
theorem check5396:ThreeRule.check cell5396 (1:Fin 18)=true:=by decide +kernel
def cell5397:PairCell.Row:=⟨63,63,10,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
theorem check5397:ThreeRule.check cell5397 (1:Fin 18)=true:=by decide +kernel
def cell5398:PairCell.Row:=⟨63,63,10,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
theorem check5398:ThreeRule.check cell5398 (1:Fin 18)=true:=by decide +kernel
def cell5399:PairCell.Row:=⟨63,63,10,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
theorem check5399:ThreeRule.check cell5399 (1:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2739

-- Source: Research6969.HardFit2At150
section Z6969Source2740
set_option autoImplicit true
namespace Research6969.HardFit2At150
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2020 8)
theorem case150: NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,59,some 60⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2020 7)
theorem case151: NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,61,some 64⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2300 15)
theorem case152: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,4,some 8⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2300 14)
theorem case153: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,9,some 12⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route2300 13)
theorem case154: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,13,some 13⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2300 12)
theorem case155: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,14,some 14⟩:=PairRoute.start _ leaf5
private theorem allAxes37:PairRoute.Done (1:Fin 18) ⟨⟨50,50,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5160 5),
    (PairReceipts.route5160 6),
    (PairReceipts.route5160 7),
    (PairReceipts.route5160 8),
    (PairReceipts.route5180 0),
    (PairReceipts.route5180 1),
    (PairReceipts.route5180 2),
    (PairReceipts.route5180 3),
    (PairReceipts.route5180 4),
    (PairReceipts.route5180 5),
    PairLeaves.three PairReceipts.cell5186 PairReceipts.check5186 (by decide) (none),
    PairLeaves.three PairReceipts.cell5187 PairReceipts.check5187 (by decide) (none),
    PairLeaves.three PairReceipts.cell5188 PairReceipts.check5188 (by decide) (none),
    PairLeaves.three PairReceipts.cell5189 PairReceipts.check5189 (by decide) (none),
    PairLeaves.three PairReceipts.cell5190 PairReceipts.check5190 (by decide) (none),
    PairLeaves.three PairReceipts.cell5191 PairReceipts.check5191 (by decide) (none),
    trivial⟩)
private theorem allAxes69:PairRoute.Done (1:Fin 18) ⟨⟨51,51,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5180 6),
    (PairReceipts.route5180 7),
    (PairReceipts.route5180 8),
    (PairReceipts.route5180 9),
    (PairReceipts.route5180 10),
    (PairReceipts.route5180 11),
    (PairReceipts.route5180 12),
    (PairReceipts.route5180 13),
    (PairReceipts.route5200 0),
    (PairReceipts.route5200 1),
    (PairReceipts.route5200 2),
    PairLeaves.three PairReceipts.cell5203 PairReceipts.check5203 (by decide) (none),
    PairLeaves.three PairReceipts.cell5204 PairReceipts.check5204 (by decide) (none),
    PairLeaves.three PairReceipts.cell5205 PairReceipts.check5205 (by decide) (none),
    PairLeaves.three PairReceipts.cell5206 PairReceipts.check5206 (by decide) (none),
    PairLeaves.three PairReceipts.cell5207 PairReceipts.check5207 (by decide) (none),
    trivial⟩)
private theorem allAxes101:PairRoute.Done (1:Fin 18) ⟨⟨52,52,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5200 3),
    (PairReceipts.route5200 4),
    (PairReceipts.route5200 5),
    (PairReceipts.route5200 6),
    (PairReceipts.route5200 7),
    (PairReceipts.route5200 8),
    (PairReceipts.route5200 9),
    (PairReceipts.route5200 10),
    (PairReceipts.route5200 11),
    (PairReceipts.route5200 12),
    (PairReceipts.route5200 13),
    PairLeaves.three PairReceipts.cell5219 PairReceipts.check5219 (by decide) (none),
    PairLeaves.three PairReceipts.cell5220 PairReceipts.check5220 (by decide) (none),
    PairLeaves.three PairReceipts.cell5221 PairReceipts.check5221 (by decide) (none),
    PairLeaves.three PairReceipts.cell5222 PairReceipts.check5222 (by decide) (none),
    PairLeaves.three PairReceipts.cell5223 PairReceipts.check5223 (by decide) (none),
    trivial⟩)
private theorem allAxes133:PairRoute.Done (1:Fin 18) ⟨⟨53,53,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5224 0),
    (PairReceipts.route5224 1),
    (PairReceipts.route5224 2),
    (PairReceipts.route5224 3),
    (PairReceipts.route5224 4),
    (PairReceipts.route5224 5),
    (PairReceipts.route5224 6),
    (PairReceipts.route5224 7),
    (PairReceipts.route5224 8),
    (PairReceipts.route5224 9),
    (PairReceipts.route5224 10),
    PairLeaves.three PairReceipts.cell5235 PairReceipts.check5235 (by decide) (none),
    PairLeaves.three PairReceipts.cell5236 PairReceipts.check5236 (by decide) (none),
    PairLeaves.three PairReceipts.cell5237 PairReceipts.check5237 (by decide) (none),
    PairLeaves.three PairReceipts.cell5238 PairReceipts.check5238 (by decide) (none),
    PairLeaves.three PairReceipts.cell5239 PairReceipts.check5239 (by decide) (none),
    trivial⟩)
private theorem allAxes165:PairRoute.Done (1:Fin 18) ⟨⟨54,54,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5240 0),
    (PairReceipts.route5240 1),
    (PairReceipts.route5240 2),
    (PairReceipts.route5240 3),
    (PairReceipts.route5240 4),
    (PairReceipts.route5240 5),
    (PairReceipts.route5240 6),
    (PairReceipts.route5240 7),
    (PairReceipts.route5240 8),
    (PairReceipts.route5240 9),
    (PairReceipts.route5240 10),
    PairLeaves.three PairReceipts.cell5251 PairReceipts.check5251 (by decide) (none),
    PairLeaves.three PairReceipts.cell5252 PairReceipts.check5252 (by decide) (none),
    PairLeaves.three PairReceipts.cell5253 PairReceipts.check5253 (by decide) (none),
    PairLeaves.three PairReceipts.cell5254 PairReceipts.check5254 (by decide) (none),
    PairLeaves.three PairReceipts.cell5255 PairReceipts.check5255 (by decide) (none),
    trivial⟩)
private theorem allAxes197:PairRoute.Done (1:Fin 18) ⟨⟨55,55,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5240 11),
    (PairReceipts.route5240 12),
    (PairReceipts.route5240 13),
    (PairReceipts.route5240 14),
    (PairReceipts.route5260 0),
    (PairReceipts.route5260 1),
    (PairReceipts.route5260 2),
    (PairReceipts.route5260 3),
    (PairReceipts.route5260 4),
    (PairReceipts.route5260 5),
    (PairReceipts.route5260 6),
    PairLeaves.three PairReceipts.cell5267 PairReceipts.check5267 (by decide) (none),
    PairLeaves.three PairReceipts.cell5268 PairReceipts.check5268 (by decide) (none),
    PairLeaves.three PairReceipts.cell5269 PairReceipts.check5269 (by decide) (none),
    PairLeaves.three PairReceipts.cell5270 PairReceipts.check5270 (by decide) (none),
    PairLeaves.three PairReceipts.cell5271 PairReceipts.check5271 (by decide) (none),
    trivial⟩)
private theorem allAxes229:PairRoute.Done (1:Fin 18) ⟨⟨56,56,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5260 7),
    (PairReceipts.route5260 8),
    (PairReceipts.route5260 9),
    (PairReceipts.route5260 10),
    (PairReceipts.route5260 11),
    (PairReceipts.route5260 12),
    (PairReceipts.route5260 13),
    (PairReceipts.route5260 14),
    (PairReceipts.route5280 0),
    (PairReceipts.route5280 1),
    (PairReceipts.route5280 2),
    PairLeaves.three PairReceipts.cell5283 PairReceipts.check5283 (by decide) (none),
    PairLeaves.three PairReceipts.cell5284 PairReceipts.check5284 (by decide) (none),
    PairLeaves.three PairReceipts.cell5285 PairReceipts.check5285 (by decide) (none),
    PairLeaves.three PairReceipts.cell5286 PairReceipts.check5286 (by decide) (none),
    PairLeaves.three PairReceipts.cell5287 PairReceipts.check5287 (by decide) (none),
    trivial⟩)
private theorem allAxes261:PairRoute.Done (1:Fin 18) ⟨⟨57,57,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5280 3),
    (PairReceipts.route5280 4),
    (PairReceipts.route5280 5),
    (PairReceipts.route5280 6),
    (PairReceipts.route5280 7),
    (PairReceipts.route5280 8),
    (PairReceipts.route5280 9),
    (PairReceipts.route5280 10),
    (PairReceipts.route5280 11),
    (PairReceipts.route5280 12),
    (PairReceipts.route5280 13),
    (PairReceipts.route5280 14),
    PairLeaves.three PairReceipts.cell5300 PairReceipts.check5300 (by decide) (none),
    PairLeaves.three PairReceipts.cell5301 PairReceipts.check5301 (by decide) (none),
    PairLeaves.three PairReceipts.cell5302 PairReceipts.check5302 (by decide) (none),
    PairLeaves.three PairReceipts.cell5303 PairReceipts.check5303 (by decide) (none),
    trivial⟩)
private theorem allAxes293:PairRoute.Done (1:Fin 18) ⟨⟨58,58,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5304 0),
    (PairReceipts.route5304 1),
    (PairReceipts.route5304 2),
    (PairReceipts.route5304 3),
    (PairReceipts.route5304 4),
    (PairReceipts.route5304 5),
    (PairReceipts.route5304 6),
    (PairReceipts.route5304 7),
    (PairReceipts.route5304 8),
    (PairReceipts.route5304 9),
    (PairReceipts.route5304 10),
    (PairReceipts.route5304 11),
    PairLeaves.three PairReceipts.cell5316 PairReceipts.check5316 (by decide) (none),
    PairLeaves.three PairReceipts.cell5317 PairReceipts.check5317 (by decide) (none),
    PairLeaves.three PairReceipts.cell5318 PairReceipts.check5318 (by decide) (none),
    PairLeaves.three PairReceipts.cell5319 PairReceipts.check5319 (by decide) (none),
    trivial⟩)
private theorem allAxes325:PairRoute.Done (1:Fin 18) ⟨⟨59,59,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5320 0),
    (PairReceipts.route5320 1),
    (PairReceipts.route5320 2),
    (PairReceipts.route5320 3),
    (PairReceipts.route5320 4),
    (PairReceipts.route5320 5),
    (PairReceipts.route5320 6),
    (PairReceipts.route5320 7),
    (PairReceipts.route5320 8),
    (PairReceipts.route5320 9),
    (PairReceipts.route5320 10),
    (PairReceipts.route5320 11),
    PairLeaves.three PairReceipts.cell5332 PairReceipts.check5332 (by decide) (none),
    PairLeaves.three PairReceipts.cell5333 PairReceipts.check5333 (by decide) (none),
    PairLeaves.three PairReceipts.cell5334 PairReceipts.check5334 (by decide) (none),
    PairLeaves.three PairReceipts.cell5335 PairReceipts.check5335 (by decide) (none),
    trivial⟩)
private theorem allAxes357:PairRoute.Done (1:Fin 18) ⟨⟨60,60,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5320 12),
    (PairReceipts.route5320 13),
    (PairReceipts.route5320 14),
    (PairReceipts.route5320 15),
    (PairReceipts.route5340 0),
    (PairReceipts.route5340 1),
    (PairReceipts.route5340 2),
    (PairReceipts.route5340 3),
    (PairReceipts.route5340 4),
    (PairReceipts.route5340 5),
    (PairReceipts.route5340 6),
    (PairReceipts.route5340 7),
    PairLeaves.three PairReceipts.cell5348 PairReceipts.check5348 (by decide) (none),
    PairLeaves.three PairReceipts.cell5349 PairReceipts.check5349 (by decide) (none),
    PairLeaves.three PairReceipts.cell5350 PairReceipts.check5350 (by decide) (none),
    PairLeaves.three PairReceipts.cell5351 PairReceipts.check5351 (by decide) (none),
    trivial⟩)
private theorem allAxes389:PairRoute.Done (1:Fin 18) ⟨⟨61,61,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5340 8),
    (PairReceipts.route5340 9),
    (PairReceipts.route5340 10),
    (PairReceipts.route5340 11),
    (PairReceipts.route5340 12),
    (PairReceipts.route5340 13),
    (PairReceipts.route5340 14),
    (PairReceipts.route5340 15),
    (PairReceipts.route5360 0),
    (PairReceipts.route5360 1),
    (PairReceipts.route5360 2),
    (PairReceipts.route5360 3),
    PairLeaves.three PairReceipts.cell5364 PairReceipts.check5364 (by decide) (none),
    PairLeaves.three PairReceipts.cell5365 PairReceipts.check5365 (by decide) (none),
    PairLeaves.three PairReceipts.cell5366 PairReceipts.check5366 (by decide) (none),
    PairLeaves.three PairReceipts.cell5367 PairReceipts.check5367 (by decide) (none),
    trivial⟩)
private theorem allAxes421:PairRoute.Done (1:Fin 18) ⟨⟨62,62,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5360 4),
    (PairReceipts.route5360 5),
    (PairReceipts.route5360 6),
    (PairReceipts.route5360 7),
    (PairReceipts.route5360 8),
    (PairReceipts.route5360 9),
    (PairReceipts.route5360 10),
    (PairReceipts.route5360 11),
    (PairReceipts.route5360 12),
    (PairReceipts.route5360 13),
    (PairReceipts.route5360 14),
    (PairReceipts.route5360 15),
    PairLeaves.three PairReceipts.cell5380 PairReceipts.check5380 (by decide) (none),
    PairLeaves.three PairReceipts.cell5381 PairReceipts.check5381 (by decide) (none),
    PairLeaves.three PairReceipts.cell5382 PairReceipts.check5382 (by decide) (none),
    PairLeaves.three PairReceipts.cell5383 PairReceipts.check5383 (by decide) (none),
    trivial⟩)
private theorem allAxes453:PairRoute.Done (1:Fin 18) ⟨⟨63,63,10,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route5384 0),
    (PairReceipts.route5384 1),
    (PairReceipts.route5384 2),
    (PairReceipts.route5384 3),
    (PairReceipts.route5384 4),
    (PairReceipts.route5384 5),
    (PairReceipts.route5384 6),
    (PairReceipts.route5384 7),
    (PairReceipts.route5384 8),
    (PairReceipts.route5384 9),
    (PairReceipts.route5384 10),
    (PairReceipts.route5384 11),
    PairLeaves.three PairReceipts.cell5396 PairReceipts.check5396 (by decide) (none),
    PairLeaves.three PairReceipts.cell5397 PairReceipts.check5397 (by decide) (none),
    PairLeaves.three PairReceipts.cell5398 PairReceipts.check5398 (by decide) (none),
    PairLeaves.three PairReceipts.cell5399 PairReceipts.check5399 (by decide) (none),
    trivial⟩)
private def grade454 := PairRoute.grade 62 allAxes421 allAxes453
private def grade455 := PairRoute.grade 61 allAxes389 grade454
private def grade456 := PairRoute.grade 60 allAxes357 grade455
private def grade457 := PairRoute.grade 59 allAxes325 grade456
private def grade458 := PairRoute.grade 58 allAxes293 grade457
private def grade459 := PairRoute.grade 57 allAxes261 grade458
private def grade460 := PairRoute.grade 56 allAxes229 grade459
private def grade461 := PairRoute.grade 55 allAxes197 grade460
private def grade462 := PairRoute.grade 54 allAxes165 grade461
private def grade463 := PairRoute.grade 53 allAxes133 grade462
private def grade464 := PairRoute.grade 52 allAxes101 grade463
private def grade465 := PairRoute.grade 51 allAxes69 grade464
private def grade466 := PairRoute.grade 50 allAxes37 grade465
theorem case156: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,15,some 15⟩:=PairRoute.start _ grade466
private theorem allAxes500:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route2280 15),
    (PairReceipts.route2280 16),
    (PairReceipts.route2280 17),
    (PairReceipts.route2280 18),
    (PairReceipts.route2280 19),
    (PairReceipts.route2300 0),
    (PairReceipts.route2300 1),
    (PairReceipts.route2300 2),
    (PairReceipts.route2300 3),
    (PairReceipts.route2300 4),
    (PairReceipts.route2300 5),
    (PairReceipts.route2300 6),
    (PairReceipts.route2300 7),
    (PairReceipts.route2300 8),
    (PairReceipts.route2300 9),
    (PairReceipts.route2300 10),
    (PairReceipts.route2300 11),
    trivial⟩)
theorem case157: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,16,some 16⟩:=PairRoute.start _ allAxes500
private theorem allAxes536:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route2260 17),
    (PairReceipts.route2260 18),
    (PairReceipts.route2260 19),
    (PairReceipts.route2280 0),
    (PairReceipts.route2280 1),
    (PairReceipts.route2280 2),
    (PairReceipts.route2280 3),
    (PairReceipts.route2280 4),
    (PairReceipts.route2280 5),
    (PairReceipts.route2280 6),
    (PairReceipts.route2280 7),
    (PairReceipts.route2280 8),
    (PairReceipts.route2280 9),
    (PairReceipts.route2280 10),
    (PairReceipts.route2280 11),
    (PairReceipts.route2280 12),
    (PairReceipts.route2280 13),
    (PairReceipts.route2280 14),
    trivial⟩)
theorem case158: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,17,some 17⟩:=PairRoute.start _ allAxes536
private theorem allAxes574:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route2240 18),
    (PairReceipts.route2240 19),
    (PairReceipts.route2260 0),
    (PairReceipts.route2260 1),
    (PairReceipts.route2260 2),
    (PairReceipts.route2260 3),
    (PairReceipts.route2260 4),
    (PairReceipts.route2260 5),
    (PairReceipts.route2260 6),
    (PairReceipts.route2260 7),
    (PairReceipts.route2260 8),
    (PairReceipts.route2260 9),
    (PairReceipts.route2260 10),
    (PairReceipts.route2260 11),
    (PairReceipts.route2260 12),
    (PairReceipts.route2260 13),
    (PairReceipts.route2260 14),
    (PairReceipts.route2260 15),
    (PairReceipts.route2260 16),
    trivial⟩)
theorem case159: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,18,some 18⟩:=PairRoute.start _ allAxes574
end Research6969.HardFit2At150
end Z6969Source2740

-- Source: Research6969.PairReceipts109
section Z6969Source2741
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2180 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,22,some 22,8,some 8,385979,[MeasuredChoices.test882],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,9,some 9,385979,[MeasuredChoices.test882],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,10,some 10,385979,[MeasuredChoices.test882],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,11,some 11,385979,[MeasuredChoices.test882],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,12,some 12,385979,[MeasuredChoices.test882],[AxisChoices.test1833]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,13,some 13,385979,[MeasuredChoices.test882],[AxisChoices.test1834]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,14,some 14,385979,[MeasuredChoices.test882],[AxisChoices.test1835]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,15,some 15,385979,[MeasuredChoices.test882],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,16,some 16,385979,[MeasuredChoices.test882],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,17,some 17,385979,[MeasuredChoices.test882],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,18,some 18,385979,[MeasuredChoices.test882],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,19,some 19,385979,[MeasuredChoices.test882],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,20,some 20,385979,[MeasuredChoices.test882],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,21,some 21,385979,[MeasuredChoices.test882],[AxisChoices.test1842]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,22,some 22,385979,[MeasuredChoices.test882],[AxisChoices.test1843]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,1,separateWhole⟩]
private theorem paid2180 : StockPairs.checked rows2180 = true := by decide +kernel
theorem route2180 (i : Fin 20) : (rows2180.get i).Done :=
  StockPairs.doneAt paid2180 i

end Research6969.PairReceipts
end Z6969Source2741

-- Source: Research6969.PairReceipts110
section Z6969Source2742
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2200 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,21,some 21,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,21,some 21,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,1,separateWhole⟩]
private theorem paid2200 : StockPairs.checked rows2200 = true := by decide +kernel
theorem route2200 (i : Fin 20) : (rows2200.get i).Done :=
  StockPairs.doneAt paid2200 i

end Research6969.PairReceipts
end Z6969Source2742

-- Source: Research6969.PairReceipts111
section Z6969Source2743
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2220 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,1,separateWhole⟩]
private theorem paid2220 : StockPairs.checked rows2220 = true := by decide +kernel
theorem route2220 (i : Fin 20) : (rows2220.get i).Done :=
  StockPairs.doneAt paid2220 i

end Research6969.PairReceipts
end Z6969Source2743

-- Source: Research6969.HardFit2At160
section Z6969Source2744
set_option autoImplicit true
namespace Research6969.HardFit2At160
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes39:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route2220 18),
    (PairReceipts.route2220 19),
    (PairReceipts.route2240 0),
    (PairReceipts.route2240 1),
    (PairReceipts.route2240 2),
    (PairReceipts.route2240 3),
    (PairReceipts.route2240 4),
    (PairReceipts.route2240 5),
    (PairReceipts.route2240 6),
    (PairReceipts.route2240 7),
    (PairReceipts.route2240 8),
    (PairReceipts.route2240 9),
    (PairReceipts.route2240 10),
    (PairReceipts.route2240 11),
    (PairReceipts.route2240 12),
    (PairReceipts.route2240 13),
    (PairReceipts.route2240 14),
    (PairReceipts.route2240 15),
    (PairReceipts.route2240 16),
    (PairReceipts.route2240 17),
    trivial⟩)
theorem case160: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,19,some 19⟩:=PairRoute.start _ allAxes39
private theorem allAxes81:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route2200 17),
    (PairReceipts.route2200 18),
    (PairReceipts.route2200 19),
    (PairReceipts.route2220 0),
    (PairReceipts.route2220 1),
    (PairReceipts.route2220 2),
    (PairReceipts.route2220 3),
    (PairReceipts.route2220 4),
    (PairReceipts.route2220 5),
    (PairReceipts.route2220 6),
    (PairReceipts.route2220 7),
    (PairReceipts.route2220 8),
    (PairReceipts.route2220 9),
    (PairReceipts.route2220 10),
    (PairReceipts.route2220 11),
    (PairReceipts.route2220 12),
    (PairReceipts.route2220 13),
    (PairReceipts.route2220 14),
    (PairReceipts.route2220 15),
    (PairReceipts.route2220 16),
    (PairReceipts.route2220 17),
    trivial⟩)
theorem case161: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,20,some 20⟩:=PairRoute.start _ allAxes81
private theorem allAxes125:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,3,21,some 21⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 21 ⟨
    (PairReceipts.route2180 15),
    (PairReceipts.route2180 16),
    (PairReceipts.route2180 17),
    (PairReceipts.route2180 18),
    (PairReceipts.route2180 19),
    (PairReceipts.route2200 0),
    (PairReceipts.route2200 1),
    (PairReceipts.route2200 2),
    (PairReceipts.route2200 3),
    (PairReceipts.route2200 4),
    (PairReceipts.route2200 5),
    (PairReceipts.route2200 6),
    (PairReceipts.route2200 7),
    (PairReceipts.route2200 8),
    (PairReceipts.route2200 9),
    (PairReceipts.route2200 10),
    (PairReceipts.route2200 11),
    (PairReceipts.route2200 12),
    (PairReceipts.route2200 13),
    (PairReceipts.route2200 14),
    (PairReceipts.route2200 15),
    (PairReceipts.route2200 16),
    trivial⟩)
theorem case162: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,21,some 21⟩:=PairRoute.start _ allAxes125
private theorem allAxes171:PairRoute.Done (1:Fin 18) ⟨⟨50,63,10,3,22,some 22⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 22 ⟨
    (PairReceipts.route2160 13),
    (PairReceipts.route2160 14),
    (PairReceipts.route2160 15),
    (PairReceipts.route2160 16),
    (PairReceipts.route2160 17),
    (PairReceipts.route2160 18),
    (PairReceipts.route2160 19),
    (PairReceipts.route2160 20),
    (PairReceipts.route2180 0),
    (PairReceipts.route2180 1),
    (PairReceipts.route2180 2),
    (PairReceipts.route2180 3),
    (PairReceipts.route2180 4),
    (PairReceipts.route2180 5),
    (PairReceipts.route2180 6),
    (PairReceipts.route2180 7),
    (PairReceipts.route2180 8),
    (PairReceipts.route2180 9),
    (PairReceipts.route2180 10),
    (PairReceipts.route2180 11),
    (PairReceipts.route2180 12),
    (PairReceipts.route2180 13),
    (PairReceipts.route2180 14),
    trivial⟩)
theorem case163: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,22,some 22⟩:=PairRoute.start _ allAxes171
private def leaf172 := (PairReceipts.route2160 12)
theorem case164: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,23,some 23⟩:=PairRoute.start _ leaf172
private def leaf173 := (PairReceipts.route2160 11)
theorem case165: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,24,some 24⟩:=PairRoute.start _ leaf173
private def leaf174 := (PairReceipts.route2160 10)
theorem case166: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,25,some 25⟩:=PairRoute.start _ leaf174
private def leaf175 := (PairReceipts.route2160 9)
theorem case167: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,26,some 26⟩:=PairRoute.start _ leaf175
private def leaf176 := (PairReceipts.route2160 8)
theorem case168: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,27,some 28⟩:=PairRoute.start _ leaf176
private def leaf177 := (PairReceipts.route2160 7)
theorem case169: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,29,some 30⟩:=PairRoute.start _ leaf177
end Research6969.HardFit2At160
end Z6969Source2744

-- Source: Research6969.PairReceipts116
section Z6969Source2745
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2320 : List StockPairs.Receipt := [
  ⟨⟨64,722,12,1,25,some 28,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,21,some 24,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,17,some 20,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,13,some 16,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,9,some 12,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,4,some 8,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,2,some 3,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,1,some 1,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,0,some 0,0,none,128659,[],[]⟩,1,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,2,49,some 52,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,1,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,722,12,2,49,some 52,0,none,288407,[MeasuredChoices.test104,MeasuredChoices.test114],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,45,some 48,0,none,257319,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,41,some 44,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,37,some 40,0,none,257319,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,33,some 36,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨64,722,12,2,29,some 32,0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,1,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨64,722,12,2,25,some 28,0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,21,some 24,0,none,257319,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩,1,surfaceWhole⟩]
private theorem paid2320 : StockPairs.checked rows2320 = true := by decide +kernel
theorem route2320 (i : Fin 20) : (rows2320.get i).Done :=
  StockPairs.doneAt paid2320 i

end Research6969.PairReceipts
end Z6969Source2745

-- Source: Research6969.HardFit2At170
section Z6969Source2746
set_option autoImplicit true
namespace Research6969.HardFit2At170
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2160 6)
theorem case170: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,31,some 32⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2160 5)
theorem case171: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,33,some 34⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2160 4)
theorem case172: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,35,some 36⟩:=PairRoute.start _ leaf2
private def terminalLeaf7040 := (PairReceipts.route2160 2)
private def terminalLeaf7041 := (PairReceipts.route2160 3)
private def leaf3 := PairRoute.splitSeed 37 terminalLeaf7040 terminalLeaf7041
theorem case173: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,37,some 38⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route2160 1)
theorem case174: NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,39,some 39⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2320 8)
theorem case175: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,0,some 0⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route2320 7)
theorem case176: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,1,some 1⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route2320 6)
theorem case177: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,2,some 3⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route2320 5)
theorem case178: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,4,some 8⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route2320 4)
theorem case179: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,9,some 12⟩:=PairRoute.start _ leaf9
end Research6969.HardFit2At170
end Z6969Source2746

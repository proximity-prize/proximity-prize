import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666

set_option Elab.async false

-- Source: Research6969.PairReceipts302
section Z6969Source2831
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6040:PairCell.Row:=⟨55,55,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6040:ThreeRule.check cell6040 (2:Fin 18)=true:=by decide +kernel
def cell6041:PairCell.Row:=⟨55,55,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6041:ThreeRule.check cell6041 (2:Fin 18)=true:=by decide +kernel
def cell6042:PairCell.Row:=⟨55,55,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6042:ThreeRule.check cell6042 (2:Fin 18)=true:=by decide +kernel
def cell6043:PairCell.Row:=⟨55,55,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6043:ThreeRule.check cell6043 (2:Fin 18)=true:=by decide +kernel
private def rows6044 : List StockPairs.Receipt := [
  ⟨⟨56,56,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨56,56,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid6044 : StockPairs.checked rows6044 = true := by decide +kernel
theorem route6044 (i : Fin 12) : (rows6044.get i).Done :=
  StockPairs.doneAt paid6044 i

def cell6056:PairCell.Row:=⟨56,56,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6056:ThreeRule.check cell6056 (2:Fin 18)=true:=by decide +kernel
def cell6057:PairCell.Row:=⟨56,56,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6057:ThreeRule.check cell6057 (2:Fin 18)=true:=by decide +kernel
def cell6058:PairCell.Row:=⟨56,56,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6058:ThreeRule.check cell6058 (2:Fin 18)=true:=by decide +kernel
def cell6059:PairCell.Row:=⟨56,56,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6059:ThreeRule.check cell6059 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2831

-- Source: Research6969.PairReceipts303
section Z6969Source2832
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6060:PairCell.Row:=⟨56,56,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6060:ThreeRule.check cell6060 (2:Fin 18)=true:=by decide +kernel
def cell6061:PairCell.Row:=⟨56,56,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6061:ThreeRule.check cell6061 (2:Fin 18)=true:=by decide +kernel
private def rows6062 : List StockPairs.Receipt := [
  ⟨⟨57,57,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨57,57,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid6062 : StockPairs.checked rows6062 = true := by decide +kernel
theorem route6062 (i : Fin 12) : (rows6062.get i).Done :=
  StockPairs.doneAt paid6062 i

def cell6074:PairCell.Row:=⟨57,57,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6074:ThreeRule.check cell6074 (2:Fin 18)=true:=by decide +kernel
def cell6075:PairCell.Row:=⟨57,57,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6075:ThreeRule.check cell6075 (2:Fin 18)=true:=by decide +kernel
def cell6076:PairCell.Row:=⟨57,57,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6076:ThreeRule.check cell6076 (2:Fin 18)=true:=by decide +kernel
def cell6077:PairCell.Row:=⟨57,57,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6077:ThreeRule.check cell6077 (2:Fin 18)=true:=by decide +kernel
def cell6078:PairCell.Row:=⟨57,57,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6078:ThreeRule.check cell6078 (2:Fin 18)=true:=by decide +kernel
def cell6079:PairCell.Row:=⟨57,57,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6079:ThreeRule.check cell6079 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2832

-- Source: Research6969.PairReceipts304
section Z6969Source2833
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6080 : List StockPairs.Receipt := [
  ⟨⟨58,58,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨58,58,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid6080 : StockPairs.checked rows6080 = true := by decide +kernel
theorem route6080 (i : Fin 14) : (rows6080.get i).Done :=
  StockPairs.doneAt paid6080 i

def cell6092:PairCell.Row:=⟨58,58,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6092:ThreeRule.check cell6092 (2:Fin 18)=true:=by decide +kernel
def cell6093:PairCell.Row:=⟨58,58,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6093:ThreeRule.check cell6093 (2:Fin 18)=true:=by decide +kernel
def cell6094:PairCell.Row:=⟨58,58,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6094:ThreeRule.check cell6094 (2:Fin 18)=true:=by decide +kernel
def cell6095:PairCell.Row:=⟨58,58,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6095:ThreeRule.check cell6095 (2:Fin 18)=true:=by decide +kernel
def cell6096:PairCell.Row:=⟨58,58,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6096:ThreeRule.check cell6096 (2:Fin 18)=true:=by decide +kernel
def cell6097:PairCell.Row:=⟨58,58,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6097:ThreeRule.check cell6097 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2833

-- Source: Research6969.PairReceipts305
section Z6969Source2834
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6100 : List StockPairs.Receipt := [
  ⟨⟨59,59,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨59,59,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩]
private theorem paid6100 : StockPairs.checked rows6100 = true := by decide +kernel
theorem route6100 (i : Fin 14) : (rows6100.get i).Done :=
  StockPairs.doneAt paid6100 i

def cell6110:PairCell.Row:=⟨59,59,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6110:ThreeRule.check cell6110 (2:Fin 18)=true:=by decide +kernel
def cell6111:PairCell.Row:=⟨59,59,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6111:ThreeRule.check cell6111 (2:Fin 18)=true:=by decide +kernel
def cell6112:PairCell.Row:=⟨59,59,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6112:ThreeRule.check cell6112 (2:Fin 18)=true:=by decide +kernel
def cell6113:PairCell.Row:=⟨59,59,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6113:ThreeRule.check cell6113 (2:Fin 18)=true:=by decide +kernel
def cell6114:PairCell.Row:=⟨59,59,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6114:ThreeRule.check cell6114 (2:Fin 18)=true:=by decide +kernel
def cell6115:PairCell.Row:=⟨59,59,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6115:ThreeRule.check cell6115 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2834

-- Source: Research6969.PairReceipts306
section Z6969Source2835
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6120 : List StockPairs.Receipt := [
  ⟨⟨60,60,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩]
private theorem paid6120 : StockPairs.checked rows6120 = true := by decide +kernel
theorem route6120 (i : Fin 14) : (rows6120.get i).Done :=
  StockPairs.doneAt paid6120 i

def cell6128:PairCell.Row:=⟨60,60,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6128:ThreeRule.check cell6128 (2:Fin 18)=true:=by decide +kernel
def cell6129:PairCell.Row:=⟨60,60,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6129:ThreeRule.check cell6129 (2:Fin 18)=true:=by decide +kernel
def cell6130:PairCell.Row:=⟨60,60,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6130:ThreeRule.check cell6130 (2:Fin 18)=true:=by decide +kernel
def cell6131:PairCell.Row:=⟨60,60,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6131:ThreeRule.check cell6131 (2:Fin 18)=true:=by decide +kernel
def cell6132:PairCell.Row:=⟨60,60,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6132:ThreeRule.check cell6132 (2:Fin 18)=true:=by decide +kernel
def cell6133:PairCell.Row:=⟨60,60,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6133:ThreeRule.check cell6133 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2835

-- Source: Research6969.PairReceipts307
section Z6969Source2836
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6140 : List StockPairs.Receipt := [
  ⟨⟨61,61,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩]
private theorem paid6140 : StockPairs.checked rows6140 = true := by decide +kernel
theorem route6140 (i : Fin 14) : (rows6140.get i).Done :=
  StockPairs.doneAt paid6140 i

def cell6146:PairCell.Row:=⟨61,61,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6146:ThreeRule.check cell6146 (2:Fin 18)=true:=by decide +kernel
def cell6147:PairCell.Row:=⟨61,61,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6147:ThreeRule.check cell6147 (2:Fin 18)=true:=by decide +kernel
def cell6148:PairCell.Row:=⟨61,61,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6148:ThreeRule.check cell6148 (2:Fin 18)=true:=by decide +kernel
def cell6149:PairCell.Row:=⟨61,61,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6149:ThreeRule.check cell6149 (2:Fin 18)=true:=by decide +kernel
def cell6150:PairCell.Row:=⟨61,61,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6150:ThreeRule.check cell6150 (2:Fin 18)=true:=by decide +kernel
def cell6151:PairCell.Row:=⟨61,61,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6151:ThreeRule.check cell6151 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2836

-- Source: Research6969.PairReceipts308
section Z6969Source2837
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6160 : List StockPairs.Receipt := [
  ⟨⟨62,62,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6160 : StockPairs.checked rows6160 = true := by decide +kernel
theorem route6160 (i : Fin 14) : (rows6160.get i).Done :=
  StockPairs.doneAt paid6160 i

def cell6164:PairCell.Row:=⟨62,62,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6164:ThreeRule.check cell6164 (2:Fin 18)=true:=by decide +kernel
def cell6165:PairCell.Row:=⟨62,62,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6165:ThreeRule.check cell6165 (2:Fin 18)=true:=by decide +kernel
def cell6166:PairCell.Row:=⟨62,62,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6166:ThreeRule.check cell6166 (2:Fin 18)=true:=by decide +kernel
def cell6167:PairCell.Row:=⟨62,62,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6167:ThreeRule.check cell6167 (2:Fin 18)=true:=by decide +kernel
def cell6168:PairCell.Row:=⟨62,62,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6168:ThreeRule.check cell6168 (2:Fin 18)=true:=by decide +kernel
def cell6169:PairCell.Row:=⟨62,62,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6169:ThreeRule.check cell6169 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2837

-- Source: Research6969.PairReceipts309
section Z6969Source2838
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6180 : List StockPairs.Receipt := [
  ⟨⟨63,63,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,50,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid6180 : StockPairs.checked rows6180 = true := by decide +kernel
theorem route6180 (i : Fin 12) : (rows6180.get i).Done :=
  StockPairs.doneAt paid6180 i

def cell6182:PairCell.Row:=⟨63,63,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
theorem check6182:ThreeRule.check cell6182 (2:Fin 18)=true:=by decide +kernel
def cell6183:PairCell.Row:=⟨63,63,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
theorem check6183:ThreeRule.check cell6183 (2:Fin 18)=true:=by decide +kernel
def cell6184:PairCell.Row:=⟨63,63,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
theorem check6184:ThreeRule.check cell6184 (2:Fin 18)=true:=by decide +kernel
def cell6185:PairCell.Row:=⟨63,63,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
theorem check6185:ThreeRule.check cell6185 (2:Fin 18)=true:=by decide +kernel
def cell6186:PairCell.Row:=⟨63,63,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
theorem check6186:ThreeRule.check cell6186 (2:Fin 18)=true:=by decide +kernel
def cell6187:PairCell.Row:=⟨63,63,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
theorem check6187:ThreeRule.check cell6187 (2:Fin 18)=true:=by decide +kernel

def cell6198:PairCell.Row:=⟨50,50,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩
theorem check6198:ThreeRule.check cell6198 (2:Fin 18)=true:=by decide +kernel
def cell6199:PairCell.Row:=⟨50,50,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩
theorem check6199:ThreeRule.check cell6199 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2838

-- Source: Research6969.PairReceipts310
section Z6969Source2839
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6200:PairCell.Row:=⟨50,50,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6200:ThreeRule.check cell6200 (2:Fin 18)=true:=by decide +kernel
def cell6201:PairCell.Row:=⟨50,50,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6201:ThreeRule.check cell6201 (2:Fin 18)=true:=by decide +kernel
def cell6202:PairCell.Row:=⟨50,50,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6202:ThreeRule.check cell6202 (2:Fin 18)=true:=by decide +kernel
def cell6203:PairCell.Row:=⟨50,50,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6203:ThreeRule.check cell6203 (2:Fin 18)=true:=by decide +kernel
def cell6204:PairCell.Row:=⟨50,50,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6204:ThreeRule.check cell6204 (2:Fin 18)=true:=by decide +kernel
private def rows6205 : List StockPairs.Receipt := [
  ⟨⟨51,51,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid6205 : StockPairs.checked rows6205 = true := by decide +kernel
theorem route6205 (i : Fin 11) : (rows6205.get i).Done :=
  StockPairs.doneAt paid6205 i

def cell6216:PairCell.Row:=⟨51,51,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩
theorem check6216:ThreeRule.check cell6216 (2:Fin 18)=true:=by decide +kernel
def cell6217:PairCell.Row:=⟨51,51,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6217:ThreeRule.check cell6217 (2:Fin 18)=true:=by decide +kernel
def cell6218:PairCell.Row:=⟨51,51,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6218:ThreeRule.check cell6218 (2:Fin 18)=true:=by decide +kernel
def cell6219:PairCell.Row:=⟨51,51,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6219:ThreeRule.check cell6219 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2839

-- Source: Research6969.PairReceipts311
section Z6969Source2840
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell6220:PairCell.Row:=⟨51,51,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6220:ThreeRule.check cell6220 (2:Fin 18)=true:=by decide +kernel
def cell6221:PairCell.Row:=⟨51,51,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6221:ThreeRule.check cell6221 (2:Fin 18)=true:=by decide +kernel
private def rows6222 : List StockPairs.Receipt := [
  ⟨⟨52,52,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩]
private theorem paid6222 : StockPairs.checked rows6222 = true := by decide +kernel
theorem route6222 (i : Fin 12) : (rows6222.get i).Done :=
  StockPairs.doneAt paid6222 i

def cell6233:PairCell.Row:=⟨52,52,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩
theorem check6233:ThreeRule.check cell6233 (2:Fin 18)=true:=by decide +kernel
def cell6234:PairCell.Row:=⟨52,52,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6234:ThreeRule.check cell6234 (2:Fin 18)=true:=by decide +kernel
def cell6235:PairCell.Row:=⟨52,52,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6235:ThreeRule.check cell6235 (2:Fin 18)=true:=by decide +kernel
def cell6236:PairCell.Row:=⟨52,52,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6236:ThreeRule.check cell6236 (2:Fin 18)=true:=by decide +kernel
def cell6237:PairCell.Row:=⟨52,52,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6237:ThreeRule.check cell6237 (2:Fin 18)=true:=by decide +kernel
def cell6238:PairCell.Row:=⟨52,52,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6238:ThreeRule.check cell6238 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2840

-- Source: Research6969.PairReceipts312
section Z6969Source2841
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6240 : List StockPairs.Receipt := [
  ⟨⟨53,53,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩]
private theorem paid6240 : StockPairs.checked rows6240 = true := by decide +kernel
theorem route6240 (i : Fin 14) : (rows6240.get i).Done :=
  StockPairs.doneAt paid6240 i

def cell6250:PairCell.Row:=⟨53,53,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩
theorem check6250:ThreeRule.check cell6250 (2:Fin 18)=true:=by decide +kernel
def cell6251:PairCell.Row:=⟨53,53,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6251:ThreeRule.check cell6251 (2:Fin 18)=true:=by decide +kernel
def cell6252:PairCell.Row:=⟨53,53,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6252:ThreeRule.check cell6252 (2:Fin 18)=true:=by decide +kernel
def cell6253:PairCell.Row:=⟨53,53,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6253:ThreeRule.check cell6253 (2:Fin 18)=true:=by decide +kernel
def cell6254:PairCell.Row:=⟨53,53,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6254:ThreeRule.check cell6254 (2:Fin 18)=true:=by decide +kernel
def cell6255:PairCell.Row:=⟨53,53,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6255:ThreeRule.check cell6255 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2841

-- Source: Research6969.PairReceipts313
section Z6969Source2842
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows6260 : List StockPairs.Receipt := [
  ⟨⟨54,54,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨54,54,10,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨55,55,10,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,2,separateIntersection⟩]
private theorem paid6260 : StockPairs.checked rows6260 = true := by decide +kernel
theorem route6260 (i : Fin 14) : (rows6260.get i).Done :=
  StockPairs.doneAt paid6260 i

def cell6267:PairCell.Row:=⟨54,54,10,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩
theorem check6267:ThreeRule.check cell6267 (2:Fin 18)=true:=by decide +kernel
def cell6268:PairCell.Row:=⟨54,54,10,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
theorem check6268:ThreeRule.check cell6268 (2:Fin 18)=true:=by decide +kernel
def cell6269:PairCell.Row:=⟨54,54,10,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
theorem check6269:ThreeRule.check cell6269 (2:Fin 18)=true:=by decide +kernel
def cell6270:PairCell.Row:=⟨54,54,10,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
theorem check6270:ThreeRule.check cell6270 (2:Fin 18)=true:=by decide +kernel
def cell6271:PairCell.Row:=⟨54,54,10,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
theorem check6271:ThreeRule.check cell6271 (2:Fin 18)=true:=by decide +kernel
def cell6272:PairCell.Row:=⟨54,54,10,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
theorem check6272:ThreeRule.check cell6272 (2:Fin 18)=true:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2842

import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0954
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0682

set_option Elab.async false

-- Source: Research6969.PairReceipts161
section Z6969Source2862
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3220 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,36,some 36,0,none,385979,[MeasuredChoices.test1068],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,35,some 35,0,none,385979,[MeasuredChoices.test1055],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,34,some 34,0,none,385979,[MeasuredChoices.test1042],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,33,some 33,0,none,385979,[MeasuredChoices.test1029],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,30,some 30,0,none,385979,[MeasuredChoices.test990],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,29,some 29,0,none,385979,[MeasuredChoices.test977],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,28,some 28,0,none,385979,[MeasuredChoices.test966],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,27,some 27,0,none,385979,[MeasuredChoices.test952],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,26,some 26,0,none,385979,[MeasuredChoices.test939],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,0,some 0,385979,[MeasuredChoices.test924],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,1,some 1,385979,[MeasuredChoices.test924],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,2,some 2,385979,[MeasuredChoices.test924],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,3,some 3,385979,[MeasuredChoices.test924],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,4,some 4,385979,[MeasuredChoices.test924],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,5,some 5,385979,[MeasuredChoices.test924],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,6,some 6,385979,[MeasuredChoices.test924],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,7,some 7,385979,[MeasuredChoices.test924],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,8,some 8,385979,[MeasuredChoices.test924],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,25,some 25,9,some 9,385979,[MeasuredChoices.test924],[AxisChoices.test1830]⟩,2,separateIntersection⟩]
private theorem paid3220 : StockPairs.checked rows3220 = true := by decide +kernel
theorem route3220 (i : Fin 20) : (rows3220.get i).Done :=
  StockPairs.doneAt paid3220 i

end Research6969.PairReceipts
end Z6969Source2862

-- Source: Research6969.HardFit3At150
section Z6969Source2863
set_option autoImplicit true
namespace Research6969.HardFit3At150
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes51:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,25,some 25⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 25 ⟨
    (PairReceipts.route3220 10),
    (PairReceipts.route3220 11),
    (PairReceipts.route3220 12),
    (PairReceipts.route3220 13),
    (PairReceipts.route3220 14),
    (PairReceipts.route3220 15),
    (PairReceipts.route3220 16),
    (PairReceipts.route3220 17),
    (PairReceipts.route3220 18),
    (PairReceipts.route3220 19),
    (PairReceipts.route3240 0),
    (PairReceipts.route3240 1),
    (PairReceipts.route3240 2),
    (PairReceipts.route3240 3),
    (PairReceipts.route3240 4),
    (PairReceipts.route3240 5),
    (PairReceipts.route3240 6),
    (PairReceipts.route3240 7),
    (PairReceipts.route3240 8),
    (PairReceipts.route3240 9),
    (PairReceipts.route3240 10),
    (PairReceipts.route3240 11),
    (PairReceipts.route3240 12),
    (PairReceipts.route3240 13),
    (PairReceipts.route3240 14),
    (PairReceipts.route3240 15),
    trivial⟩)
theorem case150: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,25,some 25⟩:=PairRoute.start _ allAxes51
private def leaf52 := (PairReceipts.route3220 9)
theorem case151: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,26,some 26⟩:=PairRoute.start _ leaf52
private def leaf53 := (PairReceipts.route3220 8)
theorem case152: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,27,some 27⟩:=PairRoute.start _ leaf53
private def leaf54 := (PairReceipts.route3220 7)
theorem case153: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,28,some 28⟩:=PairRoute.start _ leaf54
private def leaf55 := (PairReceipts.route3220 6)
theorem case154: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,29,some 29⟩:=PairRoute.start _ leaf55
private def leaf56 := (PairReceipts.route3220 5)
theorem case155: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,30,some 30⟩:=PairRoute.start _ leaf56
private def leaf57 := (PairReceipts.route3220 4)
theorem case156: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,31,some 32⟩:=PairRoute.start _ leaf57
private def leaf58 := (PairReceipts.route3220 3)
theorem case157: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,33,some 33⟩:=PairRoute.start _ leaf58
private def leaf59 := (PairReceipts.route3220 2)
theorem case158: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,34,some 34⟩:=PairRoute.start _ leaf59
private def leaf60 := (PairReceipts.route3220 1)
theorem case159: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,35,some 35⟩:=PairRoute.start _ leaf60
end Research6969.HardFit3At150
end Z6969Source2863

-- Source: Research6969.PairReceipts158
section Z6969Source2864
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3160 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,39,some 39,19,some 19,385979,[MeasuredChoices.test1105],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,20,some 20,385979,[MeasuredChoices.test1105],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,21,some 21,385979,[MeasuredChoices.test1105],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,22,some 22,385979,[MeasuredChoices.test1105],[AxisChoices.test1843]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,23,some 23,385979,[MeasuredChoices.test1105],[AxisChoices.test1844]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,24,some 24,385979,[MeasuredChoices.test1105],[AxisChoices.test1845]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,25,some 25,385979,[MeasuredChoices.test1105],[AxisChoices.test1845,AxisChoices.test1846]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,26,some 26,385979,[MeasuredChoices.test1105],[AxisChoices.test1847]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,27,some 27,385979,[MeasuredChoices.test1105],[AxisChoices.test1848]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,28,some 28,385979,[MeasuredChoices.test1105],[AxisChoices.test1848,AxisChoices.test1849]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,29,some 29,385979,[MeasuredChoices.test1105],[AxisChoices.test1848,AxisChoices.test1849]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,30,some 30,385979,[MeasuredChoices.test1105],[AxisChoices.test1848,AxisChoices.test1851]⟩,2,markedAxisIntersection⟩]
private theorem paid3160 : StockPairs.checked rows3160 = true := by decide +kernel
theorem route3160 (i : Fin 12) : (rows3160.get i).Done :=
  StockPairs.doneAt paid3160 i

def cell3172:PairCell.Row:=⟨50,63,10,3,39,some 39,31,some 31,385979,[MeasuredChoices.test1105],[AxisChoices.test1852]⟩
theorem check3172:(cell3172.cap (2:Fin 18)).grade<cell3172.lowerGrade-cell3172.off:=by decide +kernel
def cell3173:PairCell.Row:=⟨50,63,10,3,39,some 39,32,some 32,385979,[MeasuredChoices.test1105],[AxisChoices.test1853]⟩
theorem check3173:(cell3173.cap (2:Fin 18)).grade<cell3173.lowerGrade-cell3173.off:=by decide +kernel
def cell3174:PairCell.Row:=⟨50,63,10,3,39,some 39,33,some 33,385979,[MeasuredChoices.test1105],[AxisChoices.test1854]⟩
theorem check3174:(cell3174.cap (2:Fin 18)).grade<cell3174.lowerGrade-cell3174.off:=by decide +kernel
def cell3175:PairCell.Row:=⟨50,63,10,3,39,some 39,34,some 34,385979,[MeasuredChoices.test1105],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check3175:(cell3175.cap (2:Fin 18)).grade<cell3175.lowerGrade-cell3175.off:=by decide +kernel
def cell3176:PairCell.Row:=⟨50,63,10,3,39,some 39,35,some 35,385979,[MeasuredChoices.test1105],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check3176:(cell3176.cap (2:Fin 18)).grade<cell3176.lowerGrade-cell3176.off:=by decide +kernel
def cell3177:PairCell.Row:=⟨50,63,10,3,39,some 39,36,some 36,385979,[MeasuredChoices.test1105],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check3177:(cell3177.cap (2:Fin 18)).grade<cell3177.lowerGrade-cell3177.off:=by decide +kernel
def cell3178:PairCell.Row:=⟨50,63,10,3,39,some 39,37,some 37,385979,[MeasuredChoices.test1105],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check3178:(cell3178.cap (2:Fin 18)).grade<cell3178.lowerGrade-cell3178.off:=by decide +kernel
def cell3179:PairCell.Row:=⟨50,63,10,3,39,some 39,38,some 38,385979,[MeasuredChoices.test1105],[AxisChoices.test1859]⟩
theorem check3179:(cell3179.cap (2:Fin 18)).grade<cell3179.lowerGrade-cell3179.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2864

-- Source: Research6969.PairReceipts159
section Z6969Source2865
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3180:PairCell.Row:=⟨50,63,10,3,39,some 39,39,some 39,385979,[MeasuredChoices.test1105],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check3180:(cell3180.cap (2:Fin 18)).grade<cell3180.lowerGrade-cell3180.off:=by decide +kernel
private def rows3181 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,38,some 38,0,some 0,385979,[MeasuredChoices.test1092],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,1,some 1,385979,[MeasuredChoices.test1092],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,2,some 2,385979,[MeasuredChoices.test1092],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,3,some 3,385979,[MeasuredChoices.test1092],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,4,some 4,385979,[MeasuredChoices.test1092],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,5,some 5,385979,[MeasuredChoices.test1092],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,6,some 6,385979,[MeasuredChoices.test1092],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,7,some 7,385979,[MeasuredChoices.test1092],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,8,some 8,385979,[MeasuredChoices.test1092],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,9,some 9,385979,[MeasuredChoices.test1092],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,10,some 10,385979,[MeasuredChoices.test1092],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,11,some 11,385979,[MeasuredChoices.test1092],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,12,some 12,385979,[MeasuredChoices.test1092],[AxisChoices.test1833]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,13,some 13,385979,[MeasuredChoices.test1092],[AxisChoices.test1834]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,14,some 14,385979,[MeasuredChoices.test1092],[AxisChoices.test1835]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,15,some 15,385979,[MeasuredChoices.test1092],[AxisChoices.test1836]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,16,some 16,385979,[MeasuredChoices.test1092],[AxisChoices.test1837]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,17,some 17,385979,[MeasuredChoices.test1092],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,18,some 18,385979,[MeasuredChoices.test1092],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩]
private theorem paid3181 : StockPairs.checked rows3181 = true := by decide +kernel
theorem route3181 (i : Fin 19) : (rows3181.get i).Done :=
  StockPairs.doneAt paid3181 i

end Research6969.PairReceipts
end Z6969Source2865

-- Source: Research6969.PairReceipts160
section Z6969Source2866
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3200 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,38,some 38,19,some 19,385979,[MeasuredChoices.test1092],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,20,some 20,385979,[MeasuredChoices.test1092],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,21,some 21,385979,[MeasuredChoices.test1092],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,22,some 22,385979,[MeasuredChoices.test1092],[AxisChoices.test1843]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,23,some 23,385979,[MeasuredChoices.test1092],[AxisChoices.test1844]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,24,some 24,385979,[MeasuredChoices.test1092],[AxisChoices.test1845]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,25,some 25,385979,[MeasuredChoices.test1092],[AxisChoices.test1845,AxisChoices.test1846]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,26,some 26,385979,[MeasuredChoices.test1092],[AxisChoices.test1847]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,27,some 27,385979,[MeasuredChoices.test1092],[AxisChoices.test1848]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,28,some 28,385979,[MeasuredChoices.test1092],[AxisChoices.test1848,AxisChoices.test1849]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,29,some 29,385979,[MeasuredChoices.test1092],[AxisChoices.test1848,AxisChoices.test1849]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,38,some 38,30,some 30,385979,[MeasuredChoices.test1092],[AxisChoices.test1848,AxisChoices.test1851]⟩,2,markedAxisIntersection⟩]
private theorem paid3200 : StockPairs.checked rows3200 = true := by decide +kernel
theorem route3200 (i : Fin 12) : (rows3200.get i).Done :=
  StockPairs.doneAt paid3200 i

def cell3212:PairCell.Row:=⟨50,63,10,3,38,some 38,31,some 31,385979,[MeasuredChoices.test1092],[AxisChoices.test1852]⟩
theorem check3212:(cell3212.cap (2:Fin 18)).grade<cell3212.lowerGrade-cell3212.off:=by decide +kernel
def cell3213:PairCell.Row:=⟨50,63,10,3,38,some 38,32,some 32,385979,[MeasuredChoices.test1092],[AxisChoices.test1853]⟩
theorem check3213:(cell3213.cap (2:Fin 18)).grade<cell3213.lowerGrade-cell3213.off:=by decide +kernel
def cell3214:PairCell.Row:=⟨50,63,10,3,38,some 38,33,some 33,385979,[MeasuredChoices.test1092],[AxisChoices.test1854]⟩
theorem check3214:(cell3214.cap (2:Fin 18)).grade<cell3214.lowerGrade-cell3214.off:=by decide +kernel
def cell3215:PairCell.Row:=⟨50,63,10,3,38,some 38,34,some 34,385979,[MeasuredChoices.test1092],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check3215:(cell3215.cap (2:Fin 18)).grade<cell3215.lowerGrade-cell3215.off:=by decide +kernel
def cell3216:PairCell.Row:=⟨50,63,10,3,38,some 38,35,some 35,385979,[MeasuredChoices.test1092],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check3216:(cell3216.cap (2:Fin 18)).grade<cell3216.lowerGrade-cell3216.off:=by decide +kernel
def cell3217:PairCell.Row:=⟨50,63,10,3,38,some 38,36,some 36,385979,[MeasuredChoices.test1092],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check3217:(cell3217.cap (2:Fin 18)).grade<cell3217.lowerGrade-cell3217.off:=by decide +kernel
def cell3218:PairCell.Row:=⟨50,63,10,3,38,some 38,37,some 37,385979,[MeasuredChoices.test1092],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check3218:(cell3218.cap (2:Fin 18)).grade<cell3218.lowerGrade-cell3218.off:=by decide +kernel
def cell3219:PairCell.Row:=⟨50,63,10,3,38,some 38,38,some 38,385979,[MeasuredChoices.test1092],[AxisChoices.test1859]⟩
theorem check3219:(cell3219.cap (2:Fin 18)).grade<cell3219.lowerGrade-cell3219.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2866

-- Source: Research6969.PairReceipts170
section Z6969Source2867
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3400 : List StockPairs.Receipt := [
  ⟨⟨64,722,12,1,1,some 1,0,none,128659,[],[]⟩,2,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,1,0,some 0,0,none,128659,[],[]⟩,2,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,722,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,2,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,722,12,2,51,some 51,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,49,some 50,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,2,⟨(.node 8029306683929914),.intersection,.impossible,289917⟩⟩,
  ⟨⟨64,722,12,2,49,some 50,0,none,289917,[MeasuredChoices.test104,MeasuredChoices.test118],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,45,some 48,0,none,257319,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,41,some 44,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,2,⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨⟨64,722,12,2,41,some 44,0,none,294092,[MeasuredChoices.test124,MeasuredChoices.test140],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,37,some 40,0,none,257319,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,33,some 36,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨64,722,12,2,29,some 32,0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,2,⟨(.node 12122407664504094),.intersection,.impossible,304553⟩⟩,
  ⟨⟨64,722,12,2,25,some 28,0,none,304553,[MeasuredChoices.test216,MeasuredChoices.test230],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,23,some 24,0,none,257319,[MeasuredChoices.test29,MeasuredChoices.test32],[]⟩,2,⟨(.node 8075014212150647),.intersection,.impossible,304158⟩⟩,
  ⟨⟨64,722,12,2,23,some 24,0,none,304158,[MeasuredChoices.test215,MeasuredChoices.test216],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,21,some 22,0,none,257319,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,17,some 20,0,none,257319,[],[]⟩,2,surfaceWhole⟩]
private theorem paid3400 : StockPairs.checked rows3400 = true := by decide +kernel
theorem route3400 (i : Fin 19) : (rows3400.get i).Done :=
  StockPairs.doneAt paid3400 i

def cell3403:PairCell.Row:=⟨64,722,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩
theorem check3403:(cell3403.cap (2:Fin 18)).grade<cell3403.lowerGrade-cell3403.off:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2867

-- Source: Research6969.PairReceipts271
section Z6969Source2868
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5420:PairCell.Row:=⟨50,50,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5420:ThreeRule.check cell5420 (2:Fin 18)=true:=by decide +kernel
def cell5421:PairCell.Row:=⟨50,50,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5421:ThreeRule.check cell5421 (2:Fin 18)=true:=by decide +kernel
def cell5422:PairCell.Row:=⟨50,50,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5422:ThreeRule.check cell5422 (2:Fin 18)=true:=by decide +kernel
def cell5423:PairCell.Row:=⟨50,50,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5423:ThreeRule.check cell5423 (2:Fin 18)=true:=by decide +kernel
def cell5424:PairCell.Row:=⟨50,50,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5424:ThreeRule.check cell5424 (2:Fin 18)=true:=by decide +kernel
def cell5425:PairCell.Row:=⟨50,50,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5425:ThreeRule.check cell5425 (2:Fin 18)=true:=by decide +kernel
def cell5426:PairCell.Row:=⟨50,50,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5426:ThreeRule.check cell5426 (2:Fin 18)=true:=by decide +kernel
def cell5427:PairCell.Row:=⟨50,50,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5427:ThreeRule.check cell5427 (2:Fin 18)=true:=by decide +kernel
def cell5428:PairCell.Row:=⟨50,50,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5428:ThreeRule.check cell5428 (2:Fin 18)=true:=by decide +kernel
def cell5429:PairCell.Row:=⟨50,50,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5429:ThreeRule.check cell5429 (2:Fin 18)=true:=by decide +kernel
def cell5430:PairCell.Row:=⟨50,50,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5430:ThreeRule.check cell5430 (2:Fin 18)=true:=by decide +kernel
def cell5431:PairCell.Row:=⟨50,50,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5431:ThreeRule.check cell5431 (2:Fin 18)=true:=by decide +kernel
def cell5432:PairCell.Row:=⟨50,50,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5432:ThreeRule.check cell5432 (2:Fin 18)=true:=by decide +kernel
def cell5433:PairCell.Row:=⟨50,50,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5433:ThreeRule.check cell5433 (2:Fin 18)=true:=by decide +kernel
def cell5434:PairCell.Row:=⟨50,50,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5434:ThreeRule.check cell5434 (2:Fin 18)=true:=by decide +kernel
def cell5435:PairCell.Row:=⟨50,50,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5435:ThreeRule.check cell5435 (2:Fin 18)=true:=by decide +kernel
def cell5436:PairCell.Row:=⟨50,50,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5436:ThreeRule.check cell5436 (2:Fin 18)=true:=by decide +kernel
def cell5437:PairCell.Row:=⟨50,50,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5437:ThreeRule.check cell5437 (2:Fin 18)=true:=by decide +kernel
def cell5438:PairCell.Row:=⟨50,50,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5438:ThreeRule.check cell5438 (2:Fin 18)=true:=by decide +kernel
def cell5439:PairCell.Row:=⟨50,50,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5439:ThreeRule.check cell5439 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2868

-- Source: Research6969.PairReceipts272
section Z6969Source2869
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5440:PairCell.Row:=⟨50,50,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5440:ThreeRule.check cell5440 (2:Fin 18)=true:=by decide +kernel
def cell5441:PairCell.Row:=⟨50,50,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5441:ThreeRule.check cell5441 (2:Fin 18)=true:=by decide +kernel
private def rows5442 : List StockPairs.Receipt := [
  ⟨⟨51,51,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩,
  ⟨⟨51,51,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid5442 : StockPairs.checked rows5442 = true := by decide +kernel
theorem route5442 (i : Fin 11) : (rows5442.get i).Done :=
  StockPairs.doneAt paid5442 i

def cell5453:PairCell.Row:=⟨51,51,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩
theorem check5453:ThreeRule.check cell5453 (2:Fin 18)=true:=by decide +kernel
def cell5454:PairCell.Row:=⟨51,51,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5454:ThreeRule.check cell5454 (2:Fin 18)=true:=by decide +kernel
def cell5455:PairCell.Row:=⟨51,51,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5455:ThreeRule.check cell5455 (2:Fin 18)=true:=by decide +kernel
def cell5456:PairCell.Row:=⟨51,51,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5456:ThreeRule.check cell5456 (2:Fin 18)=true:=by decide +kernel
def cell5457:PairCell.Row:=⟨51,51,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5457:ThreeRule.check cell5457 (2:Fin 18)=true:=by decide +kernel
def cell5458:PairCell.Row:=⟨51,51,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5458:ThreeRule.check cell5458 (2:Fin 18)=true:=by decide +kernel
def cell5459:PairCell.Row:=⟨51,51,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5459:ThreeRule.check cell5459 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2869

-- Source: Research6969.PairReceipts273
section Z6969Source2870
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5460:PairCell.Row:=⟨51,51,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5460:ThreeRule.check cell5460 (2:Fin 18)=true:=by decide +kernel
def cell5461:PairCell.Row:=⟨51,51,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5461:ThreeRule.check cell5461 (2:Fin 18)=true:=by decide +kernel
def cell5462:PairCell.Row:=⟨51,51,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5462:ThreeRule.check cell5462 (2:Fin 18)=true:=by decide +kernel
def cell5463:PairCell.Row:=⟨51,51,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5463:ThreeRule.check cell5463 (2:Fin 18)=true:=by decide +kernel
def cell5464:PairCell.Row:=⟨51,51,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5464:ThreeRule.check cell5464 (2:Fin 18)=true:=by decide +kernel
def cell5465:PairCell.Row:=⟨51,51,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5465:ThreeRule.check cell5465 (2:Fin 18)=true:=by decide +kernel
def cell5466:PairCell.Row:=⟨51,51,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5466:ThreeRule.check cell5466 (2:Fin 18)=true:=by decide +kernel
def cell5467:PairCell.Row:=⟨51,51,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5467:ThreeRule.check cell5467 (2:Fin 18)=true:=by decide +kernel
def cell5468:PairCell.Row:=⟨51,51,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5468:ThreeRule.check cell5468 (2:Fin 18)=true:=by decide +kernel
def cell5469:PairCell.Row:=⟨51,51,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5469:ThreeRule.check cell5469 (2:Fin 18)=true:=by decide +kernel
def cell5470:PairCell.Row:=⟨51,51,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5470:ThreeRule.check cell5470 (2:Fin 18)=true:=by decide +kernel
def cell5471:PairCell.Row:=⟨51,51,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5471:ThreeRule.check cell5471 (2:Fin 18)=true:=by decide +kernel
def cell5472:PairCell.Row:=⟨51,51,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5472:ThreeRule.check cell5472 (2:Fin 18)=true:=by decide +kernel
def cell5473:PairCell.Row:=⟨51,51,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5473:ThreeRule.check cell5473 (2:Fin 18)=true:=by decide +kernel
def cell5474:PairCell.Row:=⟨51,51,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5474:ThreeRule.check cell5474 (2:Fin 18)=true:=by decide +kernel
def cell5475:PairCell.Row:=⟨51,51,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5475:ThreeRule.check cell5475 (2:Fin 18)=true:=by decide +kernel
def cell5476:PairCell.Row:=⟨51,51,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5476:ThreeRule.check cell5476 (2:Fin 18)=true:=by decide +kernel
def cell5477:PairCell.Row:=⟨51,51,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5477:ThreeRule.check cell5477 (2:Fin 18)=true:=by decide +kernel
def cell5478:PairCell.Row:=⟨51,51,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5478:ThreeRule.check cell5478 (2:Fin 18)=true:=by decide +kernel
def cell5479:PairCell.Row:=⟨51,51,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5479:ThreeRule.check cell5479 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2870

-- Source: Research6969.PairReceipts274
section Z6969Source2871
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5480 : List StockPairs.Receipt := [
  ⟨⟨52,52,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩,
  ⟨⟨52,52,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid5480 : StockPairs.checked rows5480 = true := by decide +kernel
theorem route5480 (i : Fin 11) : (rows5480.get i).Done :=
  StockPairs.doneAt paid5480 i

def cell5491:PairCell.Row:=⟨52,52,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩
theorem check5491:ThreeRule.check cell5491 (2:Fin 18)=true:=by decide +kernel
def cell5492:PairCell.Row:=⟨52,52,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5492:ThreeRule.check cell5492 (2:Fin 18)=true:=by decide +kernel
def cell5493:PairCell.Row:=⟨52,52,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5493:ThreeRule.check cell5493 (2:Fin 18)=true:=by decide +kernel
def cell5494:PairCell.Row:=⟨52,52,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5494:ThreeRule.check cell5494 (2:Fin 18)=true:=by decide +kernel
def cell5495:PairCell.Row:=⟨52,52,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5495:ThreeRule.check cell5495 (2:Fin 18)=true:=by decide +kernel
def cell5496:PairCell.Row:=⟨52,52,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5496:ThreeRule.check cell5496 (2:Fin 18)=true:=by decide +kernel
def cell5497:PairCell.Row:=⟨52,52,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5497:ThreeRule.check cell5497 (2:Fin 18)=true:=by decide +kernel
def cell5498:PairCell.Row:=⟨52,52,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5498:ThreeRule.check cell5498 (2:Fin 18)=true:=by decide +kernel
def cell5499:PairCell.Row:=⟨52,52,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5499:ThreeRule.check cell5499 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2871

-- Source: Research6969.PairReceipts275
section Z6969Source2872
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5500:PairCell.Row:=⟨52,52,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5500:ThreeRule.check cell5500 (2:Fin 18)=true:=by decide +kernel
def cell5501:PairCell.Row:=⟨52,52,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5501:ThreeRule.check cell5501 (2:Fin 18)=true:=by decide +kernel
def cell5502:PairCell.Row:=⟨52,52,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5502:ThreeRule.check cell5502 (2:Fin 18)=true:=by decide +kernel
def cell5503:PairCell.Row:=⟨52,52,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5503:ThreeRule.check cell5503 (2:Fin 18)=true:=by decide +kernel
def cell5504:PairCell.Row:=⟨52,52,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5504:ThreeRule.check cell5504 (2:Fin 18)=true:=by decide +kernel
def cell5505:PairCell.Row:=⟨52,52,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5505:ThreeRule.check cell5505 (2:Fin 18)=true:=by decide +kernel
def cell5506:PairCell.Row:=⟨52,52,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5506:ThreeRule.check cell5506 (2:Fin 18)=true:=by decide +kernel
def cell5507:PairCell.Row:=⟨52,52,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5507:ThreeRule.check cell5507 (2:Fin 18)=true:=by decide +kernel
def cell5508:PairCell.Row:=⟨52,52,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5508:ThreeRule.check cell5508 (2:Fin 18)=true:=by decide +kernel
def cell5509:PairCell.Row:=⟨52,52,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5509:ThreeRule.check cell5509 (2:Fin 18)=true:=by decide +kernel
def cell5510:PairCell.Row:=⟨52,52,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5510:ThreeRule.check cell5510 (2:Fin 18)=true:=by decide +kernel
def cell5511:PairCell.Row:=⟨52,52,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5511:ThreeRule.check cell5511 (2:Fin 18)=true:=by decide +kernel
def cell5512:PairCell.Row:=⟨52,52,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5512:ThreeRule.check cell5512 (2:Fin 18)=true:=by decide +kernel
def cell5513:PairCell.Row:=⟨52,52,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5513:ThreeRule.check cell5513 (2:Fin 18)=true:=by decide +kernel
def cell5514:PairCell.Row:=⟨52,52,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5514:ThreeRule.check cell5514 (2:Fin 18)=true:=by decide +kernel
def cell5515:PairCell.Row:=⟨52,52,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5515:ThreeRule.check cell5515 (2:Fin 18)=true:=by decide +kernel
def cell5516:PairCell.Row:=⟨52,52,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5516:ThreeRule.check cell5516 (2:Fin 18)=true:=by decide +kernel
def cell5517:PairCell.Row:=⟨52,52,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5517:ThreeRule.check cell5517 (2:Fin 18)=true:=by decide +kernel
private def rows5518 : List StockPairs.Receipt := [
  ⟨⟨53,53,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid5518 : StockPairs.checked rows5518 = true := by decide +kernel
theorem route5518 (i : Fin 2) : (rows5518.get i).Done :=
  StockPairs.doneAt paid5518 i

end Research6969.PairReceipts
end Z6969Source2872

-- Source: Research6969.PairReceipts276
section Z6969Source2873
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5520 : List StockPairs.Receipt := [
  ⟨⟨53,53,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,surfaceIntersection⟩,
  ⟨⟨53,53,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid5520 : StockPairs.checked rows5520 = true := by decide +kernel
theorem route5520 (i : Fin 9) : (rows5520.get i).Done :=
  StockPairs.doneAt paid5520 i

def cell5529:PairCell.Row:=⟨53,53,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩
theorem check5529:ThreeRule.check cell5529 (2:Fin 18)=true:=by decide +kernel
def cell5530:PairCell.Row:=⟨53,53,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5530:ThreeRule.check cell5530 (2:Fin 18)=true:=by decide +kernel
def cell5531:PairCell.Row:=⟨53,53,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5531:ThreeRule.check cell5531 (2:Fin 18)=true:=by decide +kernel
def cell5532:PairCell.Row:=⟨53,53,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5532:ThreeRule.check cell5532 (2:Fin 18)=true:=by decide +kernel
def cell5533:PairCell.Row:=⟨53,53,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5533:ThreeRule.check cell5533 (2:Fin 18)=true:=by decide +kernel
def cell5534:PairCell.Row:=⟨53,53,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5534:ThreeRule.check cell5534 (2:Fin 18)=true:=by decide +kernel
def cell5535:PairCell.Row:=⟨53,53,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5535:ThreeRule.check cell5535 (2:Fin 18)=true:=by decide +kernel
def cell5536:PairCell.Row:=⟨53,53,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5536:ThreeRule.check cell5536 (2:Fin 18)=true:=by decide +kernel
def cell5537:PairCell.Row:=⟨53,53,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5537:ThreeRule.check cell5537 (2:Fin 18)=true:=by decide +kernel
def cell5538:PairCell.Row:=⟨53,53,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5538:ThreeRule.check cell5538 (2:Fin 18)=true:=by decide +kernel
def cell5539:PairCell.Row:=⟨53,53,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5539:ThreeRule.check cell5539 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2873

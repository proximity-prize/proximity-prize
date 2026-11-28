import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0672
import ProximityPrize.SubmissionLower.Z6969Pack0964
import ProximityPrize.SubmissionLower.Z6969Pack0966
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0963

set_option Elab.async false

-- Source: Research6969.PairReceipts209
section Z6969Source2944
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4180 : List StockPairs.Receipt := [
  ⟨⟨64,650,12,2,47,some 48,0,none,257319,[MeasuredChoices.test57,MeasuredChoices.test58],[]⟩,3,⟨(.node 30268515783660603),.intersection,.impossible,303874⟩⟩,
  ⟨⟨64,650,12,2,47,some 48,0,none,303874,[MeasuredChoices.test170,MeasuredChoices.test171],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,45,some 46,0,none,257319,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,41,some 44,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,3,⟨(.node 8033475077956950),.intersection,.impossible,294092⟩⟩,
  ⟨⟨64,650,12,2,41,some 44,0,none,294092,[MeasuredChoices.test124,MeasuredChoices.test140],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,37,some 40,0,none,257319,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩,3,⟨(.node 8037210057961988),.intersection,.impossible,296579⟩⟩,
  ⟨⟨64,650,12,2,37,some 40,0,none,296579,[MeasuredChoices.test158],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,33,some 36,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,3,⟨(.node 8042152515659111),.intersection,.impossible,298829⟩⟩,
  ⟨⟨64,650,12,2,33,some 36,0,none,298829,[MeasuredChoices.test156,MeasuredChoices.test161],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,3,⟨(.node 8048914296280450),.intersection,.impossible,300842⟩⟩,
  ⟨⟨64,650,12,2,29,some 32,0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,27,some 28,0,none,257319,[MeasuredChoices.test37],[]⟩,3,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨64,650,12,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,25,some 26,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,3,⟨(.node 8066455423319456),.intersection,.impossible,303418⟩⟩,
  ⟨⟨64,650,12,2,25,some 26,0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,23,some 24,0,none,257319,[MeasuredChoices.test29,MeasuredChoices.test32],[]⟩,3,⟨(.node 30786469546942771),.intersection,.impossible,307280⟩⟩,
  ⟨⟨64,650,12,2,23,some 24,0,none,307280,[MeasuredChoices.test425],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,21,some 22,0,none,257319,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,17,some 20,0,none,257319,[],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,13,some 16,0,none,257319,[],[]⟩,3,surfaceWhole⟩]
private theorem paid4180 : StockPairs.checked rows4180 = true := by decide +kernel
theorem route4180 (i : Fin 20) : (rows4180.get i).Done :=
  StockPairs.doneAt paid4180 i

end Research6969.PairReceipts
end Z6969Source2944

-- Source: Research6969.PairReceipts210
section Z6969Source2945
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4200 : List StockPairs.Receipt := [
  ⟨⟨64,650,12,2,9,some 12,0,none,257319,[],[]⟩,3,surfaceWhole⟩,
  ⟨⟨64,650,12,2,4,some 8,0,none,257319,[],[]⟩,3,⟨.surface,.whole,.surface,0⟩⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,4,markedIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,4,separateIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,4,separateIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,4,separateIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,4,markedAxisIntersection⟩]
private theorem paid4200 : StockPairs.checked rows4200 = true := by decide +kernel
theorem route4200 (i : Fin 20) : (rows4200.get i).Done :=
  StockPairs.doneAt paid4200 i

end Research6969.PairReceipts
end Z6969Source2945

-- Source: Research6969.HardFit4At120
section Z6969Source2946
set_option autoImplicit true
namespace Research6969.HardFit4At120
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4000 17)
theorem case120: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,37,some 38⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4000 16)
theorem case121: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,39,some 40⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4060 12)
theorem case122: NormalRoute.Done (3:Fin 18) ⟨64,650,12,1,41,some 48⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4060 11)
theorem case123: NormalRoute.Done (3:Fin 18) ⟨64,650,12,1,49,some 64⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4200 1)
theorem case124: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,4,some 8⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4200 0)
theorem case125: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4180 19)
theorem case126: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4180 18)
theorem case127: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4180 17)
theorem case128: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,21,some 22⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4180 15)
private def leaf10 := (PairReceipts.route4180 16)
private def weight11 := PairRoute.weight 307280 leaf9 leaf10
theorem case129: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,23,some 24⟩:=PairRoute.start _ weight11
end Research6969.HardFit4At120
end Z6969Source2946

-- Source: Research6969.PairReceipts206
section Z6969Source2947
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4120:PairCell.Row:=⟨64,650,12,2,51,some 51,45,some 45,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4120:(cell4120.cap (3:Fin 18)).grade<cell4120.lowerGrade-cell4120.off:=by decide +kernel
def cell4121:PairCell.Row:=⟨64,650,12,2,51,some 51,46,some 46,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4121:(cell4121.cap (3:Fin 18)).grade<cell4121.lowerGrade-cell4121.off:=by decide +kernel
def cell4122:PairCell.Row:=⟨64,650,12,2,51,some 51,47,some 47,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4122:(cell4122.cap (3:Fin 18)).grade<cell4122.lowerGrade-cell4122.off:=by decide +kernel
def cell4123:PairCell.Row:=⟨64,650,12,2,51,some 51,48,some 48,257319,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4123:(cell4123.cap (3:Fin 18)).grade<cell4123.lowerGrade-cell4123.off:=by decide +kernel
def cell4124:PairCell.Row:=⟨64,650,12,2,51,some 51,49,some 49,257319,[MeasuredChoices.test66],[AxisChoices.test1812]⟩
theorem check4124:(cell4124.cap (3:Fin 18)).grade<cell4124.lowerGrade-cell4124.off:=by decide +kernel
def cell4125:PairCell.Row:=⟨64,650,12,2,51,some 51,50,some 50,257319,[MeasuredChoices.test66],[AxisChoices.test1813]⟩
theorem check4125:(cell4125.cap (3:Fin 18)).grade<cell4125.lowerGrade-cell4125.off:=by decide +kernel
def cell4126:PairCell.Row:=⟨64,650,12,2,51,some 51,51,some 51,257319,[MeasuredChoices.test66],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4126:(cell4126.cap (3:Fin 18)).grade<cell4126.lowerGrade-cell4126.off:=by decide +kernel
private def rows4127 : List StockPairs.Receipt := [
  ⟨⟨64,650,12,2,50,some 50,0,some 0,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,1,some 1,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,2,some 2,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,3,some 3,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,4,some 4,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,5,some 5,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,6,some 6,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,7,some 7,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,8,some 8,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,9,some 9,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,10,some 10,257319,[MeasuredChoices.test64],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,11,some 11,257319,[MeasuredChoices.test64],[AxisChoices.test1774]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,12,some 12,257319,[MeasuredChoices.test64],[AxisChoices.test1775]⟩,3,separateWhole⟩]
private theorem paid4127 : StockPairs.checked rows4127 = true := by decide +kernel
theorem route4127 (i : Fin 13) : (rows4127.get i).Done :=
  StockPairs.doneAt paid4127 i

end Research6969.PairReceipts
end Z6969Source2947

-- Source: Research6969.PairReceipts207
section Z6969Source2948
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4140 : List StockPairs.Receipt := [
  ⟨⟨64,650,12,2,50,some 50,13,some 13,257319,[MeasuredChoices.test64],[AxisChoices.test1776]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,14,some 14,257319,[MeasuredChoices.test64],[AxisChoices.test1777]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,15,some 15,257319,[MeasuredChoices.test64],[AxisChoices.test1778]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,16,some 16,257319,[MeasuredChoices.test64],[AxisChoices.test1779]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,17,some 17,257319,[MeasuredChoices.test64],[AxisChoices.test1780]⟩,3,markedAxisWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,18,some 18,257319,[MeasuredChoices.test64],[AxisChoices.test1781]⟩,3,markedAxisWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,19,some 19,257319,[MeasuredChoices.test64],[AxisChoices.test1782]⟩,3,markedAxisWhole⟩,
  ⟨⟨64,650,12,2,50,some 50,20,some 20,257319,[MeasuredChoices.test64],[AxisChoices.test1783]⟩,3,markedAxisWhole⟩]
private theorem paid4140 : StockPairs.checked rows4140 = true := by decide +kernel
theorem route4140 (i : Fin 8) : (rows4140.get i).Done :=
  StockPairs.doneAt paid4140 i

def cell4148:PairCell.Row:=⟨64,650,12,2,50,some 50,21,some 21,257319,[MeasuredChoices.test64],[AxisChoices.test1784]⟩
theorem check4148:(cell4148.cap (3:Fin 18)).grade<cell4148.lowerGrade-cell4148.off:=by decide +kernel
def cell4149:PairCell.Row:=⟨64,650,12,2,50,some 50,22,some 22,257319,[MeasuredChoices.test64],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4149:(cell4149.cap (3:Fin 18)).grade<cell4149.lowerGrade-cell4149.off:=by decide +kernel
def cell4150:PairCell.Row:=⟨64,650,12,2,50,some 50,23,some 23,257319,[MeasuredChoices.test64],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4150:(cell4150.cap (3:Fin 18)).grade<cell4150.lowerGrade-cell4150.off:=by decide +kernel
def cell4151:PairCell.Row:=⟨64,650,12,2,50,some 50,24,some 24,257319,[MeasuredChoices.test64],[AxisChoices.test1787]⟩
theorem check4151:(cell4151.cap (3:Fin 18)).grade<cell4151.lowerGrade-cell4151.off:=by decide +kernel
def cell4152:PairCell.Row:=⟨64,650,12,2,50,some 50,25,some 25,257319,[MeasuredChoices.test64],[AxisChoices.test1788]⟩
theorem check4152:(cell4152.cap (3:Fin 18)).grade<cell4152.lowerGrade-cell4152.off:=by decide +kernel
def cell4153:PairCell.Row:=⟨64,650,12,2,50,some 50,26,some 26,257319,[MeasuredChoices.test64],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4153:(cell4153.cap (3:Fin 18)).grade<cell4153.lowerGrade-cell4153.off:=by decide +kernel
def cell4154:PairCell.Row:=⟨64,650,12,2,50,some 50,27,some 27,257319,[MeasuredChoices.test64],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4154:(cell4154.cap (3:Fin 18)).grade<cell4154.lowerGrade-cell4154.off:=by decide +kernel
def cell4155:PairCell.Row:=⟨64,650,12,2,50,some 50,28,some 28,257319,[MeasuredChoices.test64],[AxisChoices.test1791]⟩
theorem check4155:(cell4155.cap (3:Fin 18)).grade<cell4155.lowerGrade-cell4155.off:=by decide +kernel
def cell4156:PairCell.Row:=⟨64,650,12,2,50,some 50,29,some 29,257319,[MeasuredChoices.test64],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4156:(cell4156.cap (3:Fin 18)).grade<cell4156.lowerGrade-cell4156.off:=by decide +kernel
def cell4157:PairCell.Row:=⟨64,650,12,2,50,some 50,30,some 30,257319,[MeasuredChoices.test64],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4157:(cell4157.cap (3:Fin 18)).grade<cell4157.lowerGrade-cell4157.off:=by decide +kernel
def cell4158:PairCell.Row:=⟨64,650,12,2,50,some 50,31,some 31,257319,[MeasuredChoices.test64],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4158:(cell4158.cap (3:Fin 18)).grade<cell4158.lowerGrade-cell4158.off:=by decide +kernel
def cell4159:PairCell.Row:=⟨64,650,12,2,50,some 50,32,some 32,257319,[MeasuredChoices.test64],[AxisChoices.test1795]⟩
theorem check4159:(cell4159.cap (3:Fin 18)).grade<cell4159.lowerGrade-cell4159.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2948

-- Source: Research6969.PairReceipts208
section Z6969Source2949
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4160:PairCell.Row:=⟨64,650,12,2,50,some 50,33,some 33,257319,[MeasuredChoices.test64],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4160:(cell4160.cap (3:Fin 18)).grade<cell4160.lowerGrade-cell4160.off:=by decide +kernel
def cell4161:PairCell.Row:=⟨64,650,12,2,50,some 50,34,some 34,257319,[MeasuredChoices.test64],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4161:(cell4161.cap (3:Fin 18)).grade<cell4161.lowerGrade-cell4161.off:=by decide +kernel
def cell4162:PairCell.Row:=⟨64,650,12,2,50,some 50,35,some 35,257319,[MeasuredChoices.test64],[AxisChoices.test1798]⟩
theorem check4162:(cell4162.cap (3:Fin 18)).grade<cell4162.lowerGrade-cell4162.off:=by decide +kernel
def cell4163:PairCell.Row:=⟨64,650,12,2,50,some 50,36,some 36,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4163:(cell4163.cap (3:Fin 18)).grade<cell4163.lowerGrade-cell4163.off:=by decide +kernel
def cell4164:PairCell.Row:=⟨64,650,12,2,50,some 50,37,some 37,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4164:(cell4164.cap (3:Fin 18)).grade<cell4164.lowerGrade-cell4164.off:=by decide +kernel
def cell4165:PairCell.Row:=⟨64,650,12,2,50,some 50,38,some 38,257319,[MeasuredChoices.test64],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4165:(cell4165.cap (3:Fin 18)).grade<cell4165.lowerGrade-cell4165.off:=by decide +kernel
def cell4166:PairCell.Row:=⟨64,650,12,2,50,some 50,39,some 39,257319,[MeasuredChoices.test64],[AxisChoices.test1802]⟩
theorem check4166:(cell4166.cap (3:Fin 18)).grade<cell4166.lowerGrade-cell4166.off:=by decide +kernel
def cell4167:PairCell.Row:=⟨64,650,12,2,50,some 50,40,some 40,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4167:(cell4167.cap (3:Fin 18)).grade<cell4167.lowerGrade-cell4167.off:=by decide +kernel
def cell4168:PairCell.Row:=⟨64,650,12,2,50,some 50,41,some 41,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4168:(cell4168.cap (3:Fin 18)).grade<cell4168.lowerGrade-cell4168.off:=by decide +kernel
def cell4169:PairCell.Row:=⟨64,650,12,2,50,some 50,42,some 42,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4169:(cell4169.cap (3:Fin 18)).grade<cell4169.lowerGrade-cell4169.off:=by decide +kernel
def cell4170:PairCell.Row:=⟨64,650,12,2,50,some 50,43,some 43,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4170:(cell4170.cap (3:Fin 18)).grade<cell4170.lowerGrade-cell4170.off:=by decide +kernel
def cell4171:PairCell.Row:=⟨64,650,12,2,50,some 50,44,some 44,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4171:(cell4171.cap (3:Fin 18)).grade<cell4171.lowerGrade-cell4171.off:=by decide +kernel
def cell4172:PairCell.Row:=⟨64,650,12,2,50,some 50,45,some 45,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4172:(cell4172.cap (3:Fin 18)).grade<cell4172.lowerGrade-cell4172.off:=by decide +kernel
def cell4173:PairCell.Row:=⟨64,650,12,2,50,some 50,46,some 46,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4173:(cell4173.cap (3:Fin 18)).grade<cell4173.lowerGrade-cell4173.off:=by decide +kernel
def cell4174:PairCell.Row:=⟨64,650,12,2,50,some 50,47,some 47,257319,[MeasuredChoices.test64],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4174:(cell4174.cap (3:Fin 18)).grade<cell4174.lowerGrade-cell4174.off:=by decide +kernel
def cell4175:PairCell.Row:=⟨64,650,12,2,50,some 50,48,some 48,257319,[MeasuredChoices.test64],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4175:(cell4175.cap (3:Fin 18)).grade<cell4175.lowerGrade-cell4175.off:=by decide +kernel
def cell4176:PairCell.Row:=⟨64,650,12,2,50,some 50,49,some 49,257319,[MeasuredChoices.test64],[AxisChoices.test1812]⟩
theorem check4176:(cell4176.cap (3:Fin 18)).grade<cell4176.lowerGrade-cell4176.off:=by decide +kernel
def cell4177:PairCell.Row:=⟨64,650,12,2,50,some 50,50,some 50,257319,[MeasuredChoices.test64],[AxisChoices.test1813]⟩
theorem check4177:(cell4177.cap (3:Fin 18)).grade<cell4177.lowerGrade-cell4177.off:=by decide +kernel
private def rows4178 : List StockPairs.Receipt := [
  ⟨⟨64,650,12,2,49,some 49,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,3,⟨(.node 8029965254169422),.intersection,.impossible,290650⟩⟩,
  ⟨⟨64,650,12,2,49,some 49,0,none,290650,[MeasuredChoices.test104,MeasuredChoices.test120],[]⟩,3,surfaceWhole⟩]
private theorem paid4178 : StockPairs.checked rows4178 = true := by decide +kernel
theorem route4178 (i : Fin 2) : (rows4178.get i).Done :=
  StockPairs.doneAt paid4178 i

end Research6969.PairReceipts
end Z6969Source2949

-- Source: Research6969.HardFit4At130
section Z6969Source2950
set_option autoImplicit true
namespace Research6969.HardFit4At130
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4180 13)
private def leaf1 := (PairReceipts.route4180 14)
private def weight2 := PairRoute.weight 303418 leaf0 leaf1
theorem case130: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,25,some 26⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route4180 11)
private def leaf4 := (PairReceipts.route4180 12)
private def weight5 := PairRoute.weight 302619 leaf3 leaf4
theorem case131: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,27,some 28⟩:=PairRoute.start _ weight5
private def leaf6 := (PairReceipts.route4180 9)
private def leaf7 := (PairReceipts.route4180 10)
private def weight8 := PairRoute.weight 300842 leaf6 leaf7
theorem case132: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,29,some 32⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route4180 7)
private def leaf10 := (PairReceipts.route4180 8)
private def weight11 := PairRoute.weight 298829 leaf9 leaf10
theorem case133: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,33,some 36⟩:=PairRoute.start _ weight11
private def leaf12 := (PairReceipts.route4180 5)
private def leaf13 := (PairReceipts.route4180 6)
private def weight14 := PairRoute.weight 296579 leaf12 leaf13
theorem case134: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,37,some 40⟩:=PairRoute.start _ weight14
private def leaf15 := (PairReceipts.route4180 3)
private def leaf16 := (PairReceipts.route4180 4)
private def weight17 := PairRoute.weight 294092 leaf15 leaf16
theorem case135: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,41,some 44⟩:=PairRoute.start _ weight17
private def leaf18 := (PairReceipts.route4180 2)
theorem case136: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,45,some 46⟩:=PairRoute.start _ leaf18
private def leaf19 := (PairReceipts.route4180 0)
private def leaf20 := (PairReceipts.route4180 1)
private def weight21 := PairRoute.weight 303874 leaf19 leaf20
theorem case137: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,47,some 48⟩:=PairRoute.start _ weight21
private def leaf22 := (PairReceipts.route4178 0)
private def leaf23 := (PairReceipts.route4178 1)
private def weight24 := PairRoute.weight 290650 leaf22 leaf23
theorem case138: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,49,some 49⟩:=PairRoute.start _ weight24
private theorem allAxes126:PairRoute.Done (3:Fin 18) ⟨⟨64,650,12,2,50,some 50⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 50 ⟨
    (PairReceipts.route4127 0),
    (PairReceipts.route4127 1),
    (PairReceipts.route4127 2),
    (PairReceipts.route4127 3),
    (PairReceipts.route4127 4),
    (PairReceipts.route4127 5),
    (PairReceipts.route4127 6),
    (PairReceipts.route4127 7),
    (PairReceipts.route4127 8),
    (PairReceipts.route4127 9),
    (PairReceipts.route4127 10),
    (PairReceipts.route4127 11),
    (PairReceipts.route4127 12),
    (PairReceipts.route4140 0),
    (PairReceipts.route4140 1),
    (PairReceipts.route4140 2),
    (PairReceipts.route4140 3),
    (PairReceipts.route4140 4),
    (PairReceipts.route4140 5),
    (PairReceipts.route4140 6),
    (PairReceipts.route4140 7),
    PairLeaves.excluded PairReceipts.cell4148 PairReceipts.check4148 (none),
    PairLeaves.excluded PairReceipts.cell4149 PairReceipts.check4149 (none),
    PairLeaves.excluded PairReceipts.cell4150 PairReceipts.check4150 (none),
    PairLeaves.excluded PairReceipts.cell4151 PairReceipts.check4151 (none),
    PairLeaves.excluded PairReceipts.cell4152 PairReceipts.check4152 (none),
    PairLeaves.excluded PairReceipts.cell4153 PairReceipts.check4153 (none),
    PairLeaves.excluded PairReceipts.cell4154 PairReceipts.check4154 (none),
    PairLeaves.excluded PairReceipts.cell4155 PairReceipts.check4155 (none),
    PairLeaves.excluded PairReceipts.cell4156 PairReceipts.check4156 (none),
    PairLeaves.excluded PairReceipts.cell4157 PairReceipts.check4157 (none),
    PairLeaves.excluded PairReceipts.cell4158 PairReceipts.check4158 (none),
    PairLeaves.excluded PairReceipts.cell4159 PairReceipts.check4159 (none),
    PairLeaves.excluded PairReceipts.cell4160 PairReceipts.check4160 (none),
    PairLeaves.excluded PairReceipts.cell4161 PairReceipts.check4161 (none),
    PairLeaves.excluded PairReceipts.cell4162 PairReceipts.check4162 (none),
    PairLeaves.excluded PairReceipts.cell4163 PairReceipts.check4163 (none),
    PairLeaves.excluded PairReceipts.cell4164 PairReceipts.check4164 (none),
    PairLeaves.excluded PairReceipts.cell4165 PairReceipts.check4165 (none),
    PairLeaves.excluded PairReceipts.cell4166 PairReceipts.check4166 (none),
    PairLeaves.excluded PairReceipts.cell4167 PairReceipts.check4167 (none),
    PairLeaves.excluded PairReceipts.cell4168 PairReceipts.check4168 (none),
    PairLeaves.excluded PairReceipts.cell4169 PairReceipts.check4169 (none),
    PairLeaves.excluded PairReceipts.cell4170 PairReceipts.check4170 (none),
    PairLeaves.excluded PairReceipts.cell4171 PairReceipts.check4171 (none),
    PairLeaves.excluded PairReceipts.cell4172 PairReceipts.check4172 (none),
    PairLeaves.excluded PairReceipts.cell4173 PairReceipts.check4173 (none),
    PairLeaves.excluded PairReceipts.cell4174 PairReceipts.check4174 (none),
    PairLeaves.excluded PairReceipts.cell4175 PairReceipts.check4175 (none),
    PairLeaves.excluded PairReceipts.cell4176 PairReceipts.check4176 (none),
    PairLeaves.excluded PairReceipts.cell4177 PairReceipts.check4177 (none),
    trivial⟩)
theorem case139: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,50,some 50⟩:=PairRoute.start _ allAxes126
end Research6969.HardFit4At130
end Z6969Source2950

-- Source: Research6969.PairReceipts204
section Z6969Source2951
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4080 : List StockPairs.Receipt := [
  ⟨⟨64,650,12,2,51,some 51,5,some 5,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,6,some 6,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,7,some 7,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,8,some 8,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,9,some 9,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,10,some 10,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,11,some 11,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1774]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,12,some 12,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1775]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,13,some 13,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1776]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,14,some 14,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1777]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,15,some 15,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1778]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,16,some 16,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1779]⟩,3,markedAxisWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,17,some 17,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1780]⟩,3,markedAxisWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,18,some 18,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1781]⟩,3,markedAxisWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,19,some 19,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1782]⟩,3,markedAxisWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,20,some 20,257319,[MeasuredChoices.test66],[AxisChoices.test1783]⟩,3,markedAxisWhole⟩]
private theorem paid4080 : StockPairs.checked rows4080 = true := by decide +kernel
theorem route4080 (i : Fin 16) : (rows4080.get i).Done :=
  StockPairs.doneAt paid4080 i

def cell4096:PairCell.Row:=⟨64,650,12,2,51,some 51,21,some 21,257319,[MeasuredChoices.test66],[AxisChoices.test1784]⟩
theorem check4096:(cell4096.cap (3:Fin 18)).grade<cell4096.lowerGrade-cell4096.off:=by decide +kernel
def cell4097:PairCell.Row:=⟨64,650,12,2,51,some 51,22,some 22,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1785]⟩
theorem check4097:(cell4097.cap (3:Fin 18)).grade<cell4097.lowerGrade-cell4097.off:=by decide +kernel
def cell4098:PairCell.Row:=⟨64,650,12,2,51,some 51,23,some 23,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1786]⟩
theorem check4098:(cell4098.cap (3:Fin 18)).grade<cell4098.lowerGrade-cell4098.off:=by decide +kernel
def cell4099:PairCell.Row:=⟨64,650,12,2,51,some 51,24,some 24,257319,[MeasuredChoices.test66],[AxisChoices.test1787]⟩
theorem check4099:(cell4099.cap (3:Fin 18)).grade<cell4099.lowerGrade-cell4099.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2951

-- Source: Research6969.PairReceipts205
section Z6969Source2952
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4100:PairCell.Row:=⟨64,650,12,2,51,some 51,25,some 25,257319,[MeasuredChoices.test66],[AxisChoices.test1788]⟩
theorem check4100:(cell4100.cap (3:Fin 18)).grade<cell4100.lowerGrade-cell4100.off:=by decide +kernel
def cell4101:PairCell.Row:=⟨64,650,12,2,51,some 51,26,some 26,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check4101:(cell4101.cap (3:Fin 18)).grade<cell4101.lowerGrade-cell4101.off:=by decide +kernel
def cell4102:PairCell.Row:=⟨64,650,12,2,51,some 51,27,some 27,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check4102:(cell4102.cap (3:Fin 18)).grade<cell4102.lowerGrade-cell4102.off:=by decide +kernel
def cell4103:PairCell.Row:=⟨64,650,12,2,51,some 51,28,some 28,257319,[MeasuredChoices.test66],[AxisChoices.test1791]⟩
theorem check4103:(cell4103.cap (3:Fin 18)).grade<cell4103.lowerGrade-cell4103.off:=by decide +kernel
def cell4104:PairCell.Row:=⟨64,650,12,2,51,some 51,29,some 29,257319,[MeasuredChoices.test66],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check4104:(cell4104.cap (3:Fin 18)).grade<cell4104.lowerGrade-cell4104.off:=by decide +kernel
def cell4105:PairCell.Row:=⟨64,650,12,2,51,some 51,30,some 30,257319,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check4105:(cell4105.cap (3:Fin 18)).grade<cell4105.lowerGrade-cell4105.off:=by decide +kernel
def cell4106:PairCell.Row:=⟨64,650,12,2,51,some 51,31,some 31,257319,[MeasuredChoices.test66],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check4106:(cell4106.cap (3:Fin 18)).grade<cell4106.lowerGrade-cell4106.off:=by decide +kernel
def cell4107:PairCell.Row:=⟨64,650,12,2,51,some 51,32,some 32,257319,[MeasuredChoices.test66],[AxisChoices.test1795]⟩
theorem check4107:(cell4107.cap (3:Fin 18)).grade<cell4107.lowerGrade-cell4107.off:=by decide +kernel
def cell4108:PairCell.Row:=⟨64,650,12,2,51,some 51,33,some 33,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4108:(cell4108.cap (3:Fin 18)).grade<cell4108.lowerGrade-cell4108.off:=by decide +kernel
def cell4109:PairCell.Row:=⟨64,650,12,2,51,some 51,34,some 34,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4109:(cell4109.cap (3:Fin 18)).grade<cell4109.lowerGrade-cell4109.off:=by decide +kernel
def cell4110:PairCell.Row:=⟨64,650,12,2,51,some 51,35,some 35,257319,[MeasuredChoices.test66],[AxisChoices.test1798]⟩
theorem check4110:(cell4110.cap (3:Fin 18)).grade<cell4110.lowerGrade-cell4110.off:=by decide +kernel
def cell4111:PairCell.Row:=⟨64,650,12,2,51,some 51,36,some 36,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4111:(cell4111.cap (3:Fin 18)).grade<cell4111.lowerGrade-cell4111.off:=by decide +kernel
def cell4112:PairCell.Row:=⟨64,650,12,2,51,some 51,37,some 37,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4112:(cell4112.cap (3:Fin 18)).grade<cell4112.lowerGrade-cell4112.off:=by decide +kernel
def cell4113:PairCell.Row:=⟨64,650,12,2,51,some 51,38,some 38,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4113:(cell4113.cap (3:Fin 18)).grade<cell4113.lowerGrade-cell4113.off:=by decide +kernel
def cell4114:PairCell.Row:=⟨64,650,12,2,51,some 51,39,some 39,257319,[MeasuredChoices.test66],[AxisChoices.test1802]⟩
theorem check4114:(cell4114.cap (3:Fin 18)).grade<cell4114.lowerGrade-cell4114.off:=by decide +kernel
def cell4115:PairCell.Row:=⟨64,650,12,2,51,some 51,40,some 40,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4115:(cell4115.cap (3:Fin 18)).grade<cell4115.lowerGrade-cell4115.off:=by decide +kernel
def cell4116:PairCell.Row:=⟨64,650,12,2,51,some 51,41,some 41,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4116:(cell4116.cap (3:Fin 18)).grade<cell4116.lowerGrade-cell4116.off:=by decide +kernel
def cell4117:PairCell.Row:=⟨64,650,12,2,51,some 51,42,some 42,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4117:(cell4117.cap (3:Fin 18)).grade<cell4117.lowerGrade-cell4117.off:=by decide +kernel
def cell4118:PairCell.Row:=⟨64,650,12,2,51,some 51,43,some 43,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4118:(cell4118.cap (3:Fin 18)).grade<cell4118.lowerGrade-cell4118.off:=by decide +kernel
def cell4119:PairCell.Row:=⟨64,650,12,2,51,some 51,44,some 44,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4119:(cell4119.cap (3:Fin 18)).grade<cell4119.lowerGrade-cell4119.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2952

-- Source: Research6969.HardFit4At140
section Z6969Source2953
set_option autoImplicit true
namespace Research6969.HardFit4At140
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes103:PairRoute.Done (3:Fin 18) ⟨⟨64,650,12,2,51,some 51⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 51 ⟨
    (PairReceipts.route4060 14),
    (PairReceipts.route4060 15),
    (PairReceipts.route4060 16),
    (PairReceipts.route4060 17),
    (PairReceipts.route4060 18),
    (PairReceipts.route4080 0),
    (PairReceipts.route4080 1),
    (PairReceipts.route4080 2),
    (PairReceipts.route4080 3),
    (PairReceipts.route4080 4),
    (PairReceipts.route4080 5),
    (PairReceipts.route4080 6),
    (PairReceipts.route4080 7),
    (PairReceipts.route4080 8),
    (PairReceipts.route4080 9),
    (PairReceipts.route4080 10),
    (PairReceipts.route4080 11),
    (PairReceipts.route4080 12),
    (PairReceipts.route4080 13),
    (PairReceipts.route4080 14),
    (PairReceipts.route4080 15),
    PairLeaves.excluded PairReceipts.cell4096 PairReceipts.check4096 (none),
    PairLeaves.excluded PairReceipts.cell4097 PairReceipts.check4097 (none),
    PairLeaves.excluded PairReceipts.cell4098 PairReceipts.check4098 (none),
    PairLeaves.excluded PairReceipts.cell4099 PairReceipts.check4099 (none),
    PairLeaves.excluded PairReceipts.cell4100 PairReceipts.check4100 (none),
    PairLeaves.excluded PairReceipts.cell4101 PairReceipts.check4101 (none),
    PairLeaves.excluded PairReceipts.cell4102 PairReceipts.check4102 (none),
    PairLeaves.excluded PairReceipts.cell4103 PairReceipts.check4103 (none),
    PairLeaves.excluded PairReceipts.cell4104 PairReceipts.check4104 (none),
    PairLeaves.excluded PairReceipts.cell4105 PairReceipts.check4105 (none),
    PairLeaves.excluded PairReceipts.cell4106 PairReceipts.check4106 (none),
    PairLeaves.excluded PairReceipts.cell4107 PairReceipts.check4107 (none),
    PairLeaves.excluded PairReceipts.cell4108 PairReceipts.check4108 (none),
    PairLeaves.excluded PairReceipts.cell4109 PairReceipts.check4109 (none),
    PairLeaves.excluded PairReceipts.cell4110 PairReceipts.check4110 (none),
    PairLeaves.excluded PairReceipts.cell4111 PairReceipts.check4111 (none),
    PairLeaves.excluded PairReceipts.cell4112 PairReceipts.check4112 (none),
    PairLeaves.excluded PairReceipts.cell4113 PairReceipts.check4113 (none),
    PairLeaves.excluded PairReceipts.cell4114 PairReceipts.check4114 (none),
    PairLeaves.excluded PairReceipts.cell4115 PairReceipts.check4115 (none),
    PairLeaves.excluded PairReceipts.cell4116 PairReceipts.check4116 (none),
    PairLeaves.excluded PairReceipts.cell4117 PairReceipts.check4117 (none),
    PairLeaves.excluded PairReceipts.cell4118 PairReceipts.check4118 (none),
    PairLeaves.excluded PairReceipts.cell4119 PairReceipts.check4119 (none),
    PairLeaves.excluded PairReceipts.cell4120 PairReceipts.check4120 (none),
    PairLeaves.excluded PairReceipts.cell4121 PairReceipts.check4121 (none),
    PairLeaves.excluded PairReceipts.cell4122 PairReceipts.check4122 (none),
    PairLeaves.excluded PairReceipts.cell4123 PairReceipts.check4123 (none),
    PairLeaves.excluded PairReceipts.cell4124 PairReceipts.check4124 (none),
    PairLeaves.excluded PairReceipts.cell4125 PairReceipts.check4125 (none),
    PairLeaves.excluded PairReceipts.cell4126 PairReceipts.check4126 (none),
    trivial⟩)
theorem case140: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,51,some 51⟩:=PairRoute.start _ allAxes103
private def leaf104 := (PairReceipts.route4060 13)
private theorem leaf105:PairRoute.Done (3:Fin 18) ⟨⟨64,650,12,2,52,some 52⟩,0,none,288407,none⟩:=PairLeaves.excluded PairReceipts.cell4074 PairReceipts.check4074 (none)
private def weight106 := PairRoute.weight 288407 leaf104 leaf105
theorem case141: NormalRoute.Done (3:Fin 18) ⟨64,650,12,2,52,some 52⟩:=PairRoute.start _ weight106
end Research6969.HardFit4At140
end Z6969Source2953

-- Source: Research6969.HardComplete4
section Z6969Source2954
set_option autoImplicit true
namespace Research6969.HardComplete4
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_8 (j:Fin HighPendingSeed4.regions.size) (l:0≤j.val) (h:j.val<8):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At000.case0
  · exact HardFit4At000.case1
  · exact HardFit4At000.case2
  · exact HardFit4At000.case3
  · exact HardFit4At000.case4
  · exact HardFit4At000.case5
  · exact HardFit4At000.case6
  · exact HardFit4At000.case7
private theorem covered8_12 (j:Fin HighPendingSeed4.regions.size) (l:8≤j.val) (h:j.val<12):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At000.case8
  · exact HardFit4At000.case9
  · exact HardFit4At010.case10
  · exact HardFit4At010.case11
private theorem covered12_17 (j:Fin HighPendingSeed4.regions.size) (l:12≤j.val) (h:j.val<17):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At010.case12
  · exact HardFit4At010.case13
  · exact HardFit4At010.case14
  · exact HardFit4At010.case15
  · exact HardFit4At010.case16
private theorem covered8_17 (j:Fin HighPendingSeed4.regions.size) (l:8≤j.val) (h:j.val<17):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<12
  · exact covered8_12 j l low
  · exact covered12_17 j (by omega) h
private theorem covered0_17 (j:Fin HighPendingSeed4.regions.size) (l:0≤j.val) (h:j.val<17):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<8
  · exact covered0_8 j l low
  · exact covered8_17 j (by omega) h
private theorem covered17_21 (j:Fin HighPendingSeed4.regions.size) (l:17≤j.val) (h:j.val<21):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At010.case17
  · exact HardFit4At010.case18
  · exact HardFit4At010.case19
  · exact HardFit4At020.case20
private theorem covered21_26 (j:Fin HighPendingSeed4.regions.size) (l:21≤j.val) (h:j.val<26):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At020.case21
  · exact HardFit4At020.case22
  · exact HardFit4At020.case23
  · exact HardFit4At020.case24
  · exact HardFit4At020.case25
private theorem covered17_26 (j:Fin HighPendingSeed4.regions.size) (l:17≤j.val) (h:j.val<26):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<21
  · exact covered17_21 j l low
  · exact covered21_26 j (by omega) h
private theorem covered26_30 (j:Fin HighPendingSeed4.regions.size) (l:26≤j.val) (h:j.val<30):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At020.case26
  · exact HardFit4At020.case27
  · exact HardFit4At020.case28
  · exact HardFit4At020.case29
private theorem covered30_35 (j:Fin HighPendingSeed4.regions.size) (l:30≤j.val) (h:j.val<35):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At030.case30
  · exact HardFit4At030.case31
  · exact HardFit4At030.case32
  · exact HardFit4At030.case33
  · exact HardFit4At030.case34
private theorem covered26_35 (j:Fin HighPendingSeed4.regions.size) (l:26≤j.val) (h:j.val<35):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<30
  · exact covered26_30 j l low
  · exact covered30_35 j (by omega) h
private theorem covered17_35 (j:Fin HighPendingSeed4.regions.size) (l:17≤j.val) (h:j.val<35):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<26
  · exact covered17_26 j l low
  · exact covered26_35 j (by omega) h
private theorem covered0_35 (j:Fin HighPendingSeed4.regions.size) (l:0≤j.val) (h:j.val<35):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<17
  · exact covered0_17 j l low
  · exact covered17_35 j (by omega) h
private theorem covered35_39 (j:Fin HighPendingSeed4.regions.size) (l:35≤j.val) (h:j.val<39):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At030.case35
  · exact HardFit4At030.case36
  · exact HardFit4At030.case37
  · exact HardFit4At030.case38
private theorem covered39_44 (j:Fin HighPendingSeed4.regions.size) (l:39≤j.val) (h:j.val<44):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At030.case39
  · exact HardFit4At040.case40
  · exact HardFit4At040.case41
  · exact HardFit4At040.case42
  · exact HardFit4At040.case43
private theorem covered35_44 (j:Fin HighPendingSeed4.regions.size) (l:35≤j.val) (h:j.val<44):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<39
  · exact covered35_39 j l low
  · exact covered39_44 j (by omega) h
private theorem covered44_48 (j:Fin HighPendingSeed4.regions.size) (l:44≤j.val) (h:j.val<48):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At040.case44
  · exact HardFit4At040.case45
  · exact HardFit4At040.case46
  · exact HardFit4At040.case47
private theorem covered48_53 (j:Fin HighPendingSeed4.regions.size) (l:48≤j.val) (h:j.val<53):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At040.case48
  · exact HardFit4At040.case49
  · exact HardFit4At050.case50
  · exact HardFit4At050.case51
  · exact HardFit4At050.case52
private theorem covered44_53 (j:Fin HighPendingSeed4.regions.size) (l:44≤j.val) (h:j.val<53):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<48
  · exact covered44_48 j l low
  · exact covered48_53 j (by omega) h
private theorem covered35_53 (j:Fin HighPendingSeed4.regions.size) (l:35≤j.val) (h:j.val<53):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<44
  · exact covered35_44 j l low
  · exact covered44_53 j (by omega) h
private theorem covered53_57 (j:Fin HighPendingSeed4.regions.size) (l:53≤j.val) (h:j.val<57):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At050.case53
  · exact HardFit4At050.case54
  · exact HardFit4At050.case55
  · exact HardFit4At050.case56
private theorem covered57_62 (j:Fin HighPendingSeed4.regions.size) (l:57≤j.val) (h:j.val<62):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At050.case57
  · exact HardFit4At050.case58
  · exact HardFit4At050.case59
  · exact HardFit4At060.case60
  · exact HardFit4At060.case61
private theorem covered53_62 (j:Fin HighPendingSeed4.regions.size) (l:53≤j.val) (h:j.val<62):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<57
  · exact covered53_57 j l low
  · exact covered57_62 j (by omega) h
private theorem covered62_66 (j:Fin HighPendingSeed4.regions.size) (l:62≤j.val) (h:j.val<66):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At060.case62
  · exact HardFit4At060.case63
  · exact HardFit4At060.case64
  · exact HardFit4At060.case65
private theorem covered66_71 (j:Fin HighPendingSeed4.regions.size) (l:66≤j.val) (h:j.val<71):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At060.case66
  · exact HardFit4At060.case67
  · exact HardFit4At060.case68
  · exact HardFit4At060.case69
  · exact HardFit4At070.case70
private theorem covered62_71 (j:Fin HighPendingSeed4.regions.size) (l:62≤j.val) (h:j.val<71):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<66
  · exact covered62_66 j l low
  · exact covered66_71 j (by omega) h
private theorem covered53_71 (j:Fin HighPendingSeed4.regions.size) (l:53≤j.val) (h:j.val<71):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<62
  · exact covered53_62 j l low
  · exact covered62_71 j (by omega) h
private theorem covered35_71 (j:Fin HighPendingSeed4.regions.size) (l:35≤j.val) (h:j.val<71):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<53
  · exact covered35_53 j l low
  · exact covered53_71 j (by omega) h
private theorem covered0_71 (j:Fin HighPendingSeed4.regions.size) (l:0≤j.val) (h:j.val<71):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<35
  · exact covered0_35 j l low
  · exact covered35_71 j (by omega) h
private theorem covered71_79 (j:Fin HighPendingSeed4.regions.size) (l:71≤j.val) (h:j.val<79):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At070.case71
  · exact HardFit4At070.case72
  · exact HardFit4At070.case73
  · exact HardFit4At070.case74
  · exact HardFit4At070.case75
  · exact HardFit4At070.case76
  · exact HardFit4At070.case77
  · exact HardFit4At070.case78
private theorem covered79_83 (j:Fin HighPendingSeed4.regions.size) (l:79≤j.val) (h:j.val<83):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At070.case79
  · exact HardFit4At080.case80
  · exact HardFit4At080.case81
  · exact HardFit4At080.case82
private theorem covered83_88 (j:Fin HighPendingSeed4.regions.size) (l:83≤j.val) (h:j.val<88):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At080.case83
  · exact HardFit4At080.case84
  · exact HardFit4At080.case85
  · exact HardFit4At080.case86
  · exact HardFit4At080.case87
private theorem covered79_88 (j:Fin HighPendingSeed4.regions.size) (l:79≤j.val) (h:j.val<88):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<83
  · exact covered79_83 j l low
  · exact covered83_88 j (by omega) h
private theorem covered71_88 (j:Fin HighPendingSeed4.regions.size) (l:71≤j.val) (h:j.val<88):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<79
  · exact covered71_79 j l low
  · exact covered79_88 j (by omega) h
private theorem covered88_92 (j:Fin HighPendingSeed4.regions.size) (l:88≤j.val) (h:j.val<92):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At080.case88
  · exact HardFit4At080.case89
  · exact HardFit4At090.case90
  · exact HardFit4At090.case91
private theorem covered92_97 (j:Fin HighPendingSeed4.regions.size) (l:92≤j.val) (h:j.val<97):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At090.case92
  · exact HardFit4At090.case93
  · exact HardFit4At090.case94
  · exact HardFit4At090.case95
  · exact HardFit4At090.case96
private theorem covered88_97 (j:Fin HighPendingSeed4.regions.size) (l:88≤j.val) (h:j.val<97):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<92
  · exact covered88_92 j l low
  · exact covered92_97 j (by omega) h
private theorem covered97_101 (j:Fin HighPendingSeed4.regions.size) (l:97≤j.val) (h:j.val<101):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At090.case97
  · exact HardFit4At090.case98
  · exact HardFit4At090.case99
  · exact HardFit4At100.case100
private theorem covered101_106 (j:Fin HighPendingSeed4.regions.size) (l:101≤j.val) (h:j.val<106):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At100.case101
  · exact HardFit4At100.case102
  · exact HardFit4At100.case103
  · exact HardFit4At100.case104
  · exact HardFit4At100.case105
private theorem covered97_106 (j:Fin HighPendingSeed4.regions.size) (l:97≤j.val) (h:j.val<106):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<101
  · exact covered97_101 j l low
  · exact covered101_106 j (by omega) h
private theorem covered88_106 (j:Fin HighPendingSeed4.regions.size) (l:88≤j.val) (h:j.val<106):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<97
  · exact covered88_97 j l low
  · exact covered97_106 j (by omega) h
private theorem covered71_106 (j:Fin HighPendingSeed4.regions.size) (l:71≤j.val) (h:j.val<106):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<88
  · exact covered71_88 j l low
  · exact covered88_106 j (by omega) h
private theorem covered106_110 (j:Fin HighPendingSeed4.regions.size) (l:106≤j.val) (h:j.val<110):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At100.case106
  · exact HardFit4At100.case107
  · exact HardFit4At100.case108
  · exact HardFit4At100.case109
private theorem covered110_115 (j:Fin HighPendingSeed4.regions.size) (l:110≤j.val) (h:j.val<115):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At110.case110
  · exact HardFit4At110.case111
  · exact HardFit4At110.case112
  · exact HardFit4At110.case113
  · exact HardFit4At110.case114
private theorem covered106_115 (j:Fin HighPendingSeed4.regions.size) (l:106≤j.val) (h:j.val<115):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<110
  · exact covered106_110 j l low
  · exact covered110_115 j (by omega) h
private theorem covered115_119 (j:Fin HighPendingSeed4.regions.size) (l:115≤j.val) (h:j.val<119):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At110.case115
  · exact HardFit4At110.case116
  · exact HardFit4At110.case117
  · exact HardFit4At110.case118
private theorem covered119_124 (j:Fin HighPendingSeed4.regions.size) (l:119≤j.val) (h:j.val<124):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At110.case119
  · exact HardFit4At120.case120
  · exact HardFit4At120.case121
  · exact HardFit4At120.case122
  · exact HardFit4At120.case123
private theorem covered115_124 (j:Fin HighPendingSeed4.regions.size) (l:115≤j.val) (h:j.val<124):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<119
  · exact covered115_119 j l low
  · exact covered119_124 j (by omega) h
private theorem covered106_124 (j:Fin HighPendingSeed4.regions.size) (l:106≤j.val) (h:j.val<124):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<115
  · exact covered106_115 j l low
  · exact covered115_124 j (by omega) h
private theorem covered124_128 (j:Fin HighPendingSeed4.regions.size) (l:124≤j.val) (h:j.val<128):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At120.case124
  · exact HardFit4At120.case125
  · exact HardFit4At120.case126
  · exact HardFit4At120.case127
private theorem covered128_133 (j:Fin HighPendingSeed4.regions.size) (l:128≤j.val) (h:j.val<133):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At120.case128
  · exact HardFit4At120.case129
  · exact HardFit4At130.case130
  · exact HardFit4At130.case131
  · exact HardFit4At130.case132
private theorem covered124_133 (j:Fin HighPendingSeed4.regions.size) (l:124≤j.val) (h:j.val<133):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<128
  · exact covered124_128 j l low
  · exact covered128_133 j (by omega) h
private theorem covered133_137 (j:Fin HighPendingSeed4.regions.size) (l:133≤j.val) (h:j.val<137):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At130.case133
  · exact HardFit4At130.case134
  · exact HardFit4At130.case135
  · exact HardFit4At130.case136
private theorem covered137_142 (j:Fin HighPendingSeed4.regions.size) (l:137≤j.val) (h:j.val<142):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit4At130.case137
  · exact HardFit4At130.case138
  · exact HardFit4At130.case139
  · exact HardFit4At140.case140
  · exact HardFit4At140.case141
private theorem covered133_142 (j:Fin HighPendingSeed4.regions.size) (l:133≤j.val) (h:j.val<142):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<137
  · exact covered133_137 j l low
  · exact covered137_142 j (by omega) h
private theorem covered124_142 (j:Fin HighPendingSeed4.regions.size) (l:124≤j.val) (h:j.val<142):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<133
  · exact covered124_133 j l low
  · exact covered133_142 j (by omega) h
private theorem covered106_142 (j:Fin HighPendingSeed4.regions.size) (l:106≤j.val) (h:j.val<142):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<124
  · exact covered106_124 j l low
  · exact covered124_142 j (by omega) h
private theorem covered71_142 (j:Fin HighPendingSeed4.regions.size) (l:71≤j.val) (h:j.val<142):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<106
  · exact covered71_106 j l low
  · exact covered106_142 j (by omega) h
private theorem covered0_142 (j:Fin HighPendingSeed4.regions.size) (l:0≤j.val) (h:j.val<142):Done (3:Fin 18) (HighPendingSeed4.atIndex j):=by
  by_cases low:j.val<71
  · exact covered0_71 j l low
  · exact covered71_142 j (by omega) h
theorem required:HighPendingSeed4.Required:=fun j=>covered0_142 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete4
end Z6969Source2954

-- Source: Research6969.PairReceipts211
section Z6969Source2955
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4220 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,17,some 20,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,18,some 18,385979,[MeasuredChoices.test821],[AxisChoices.test1839]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,19,some 19,385979,[MeasuredChoices.test821],[AxisChoices.test1840]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 20,20,some 20,385979,[MeasuredChoices.test821],[AxisChoices.test1841]⟩,4,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,17,some 18,0,none,385979,[MeasuredChoices.test821],[]⟩,4,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,4,surfaceIntersection⟩]
private theorem paid4220 : StockPairs.checked rows4220 = true := by decide +kernel
theorem route4220 (i : Fin 20) : (rows4220.get i).Done :=
  StockPairs.doneAt paid4220 i

end Research6969.PairReceipts
end Z6969Source2955

import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0672
import ProximityPrize.SubmissionLower.Z6969Pack0964
import ProximityPrize.SubmissionLower.Z6969Pack0965

set_option Elab.async false

-- Source: Research6969.PairReceipts194
section Z6969Source2932
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3880:PairCell.Row:=⟨50,63,10,2,53,some 53,43,some 43,257319,[MeasuredChoices.test71],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check3880:(cell3880.cap (3:Fin 18)).grade<cell3880.lowerGrade-cell3880.off:=by decide +kernel
def cell3881:PairCell.Row:=⟨50,63,10,2,53,some 53,44,some 44,257319,[MeasuredChoices.test71],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check3881:(cell3881.cap (3:Fin 18)).grade<cell3881.lowerGrade-cell3881.off:=by decide +kernel
def cell3882:PairCell.Row:=⟨50,63,10,2,53,some 53,45,some 45,257319,[MeasuredChoices.test71],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check3882:(cell3882.cap (3:Fin 18)).grade<cell3882.lowerGrade-cell3882.off:=by decide +kernel
def cell3883:PairCell.Row:=⟨50,63,10,2,53,some 53,46,some 46,257319,[MeasuredChoices.test71],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check3883:(cell3883.cap (3:Fin 18)).grade<cell3883.lowerGrade-cell3883.off:=by decide +kernel
def cell3884:PairCell.Row:=⟨50,63,10,2,53,some 53,47,some 47,257319,[MeasuredChoices.test71],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check3884:(cell3884.cap (3:Fin 18)).grade<cell3884.lowerGrade-cell3884.off:=by decide +kernel
def cell3885:PairCell.Row:=⟨50,63,10,2,53,some 53,48,some 48,257319,[MeasuredChoices.test71],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check3885:(cell3885.cap (3:Fin 18)).grade<cell3885.lowerGrade-cell3885.off:=by decide +kernel
def cell3886:PairCell.Row:=⟨50,63,10,2,53,some 53,49,some 49,257319,[MeasuredChoices.test71],[AxisChoices.test1812]⟩
theorem check3886:(cell3886.cap (3:Fin 18)).grade<cell3886.lowerGrade-cell3886.off:=by decide +kernel
def cell3887:PairCell.Row:=⟨50,63,10,2,53,some 53,50,some 50,257319,[MeasuredChoices.test71],[AxisChoices.test1813]⟩
theorem check3887:(cell3887.cap (3:Fin 18)).grade<cell3887.lowerGrade-cell3887.off:=by decide +kernel
def cell3888:PairCell.Row:=⟨50,63,10,2,53,some 53,51,some 51,257319,[MeasuredChoices.test71],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3888:(cell3888.cap (3:Fin 18)).grade<cell3888.lowerGrade-cell3888.off:=by decide +kernel
def cell3889:PairCell.Row:=⟨50,63,10,2,53,some 53,52,some 52,257319,[MeasuredChoices.test71],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3889:(cell3889.cap (3:Fin 18)).grade<cell3889.lowerGrade-cell3889.off:=by decide +kernel
def cell3890:PairCell.Row:=⟨50,63,10,2,53,some 53,53,some 53,257319,[MeasuredChoices.test71],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check3890:(cell3890.cap (3:Fin 18)).grade<cell3890.lowerGrade-cell3890.off:=by decide +kernel
private def rows3891 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,52,some 52,0,some 0,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,1,some 1,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,2,some 2,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,3,some 3,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,4,some 4,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,5,some 5,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,6,some 6,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,7,some 7,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,8,some 8,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩]
private theorem paid3891 : StockPairs.checked rows3891 = true := by decide +kernel
theorem route3891 (i : Fin 9) : (rows3891.get i).Done :=
  StockPairs.doneAt paid3891 i

end Research6969.PairReceipts
end Z6969Source2932

-- Source: Research6969.PairReceipts195
section Z6969Source2933
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3900 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,52,some 52,9,some 9,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,10,some 10,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,11,some 11,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1774]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,12,some 12,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1775]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,13,some 13,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1776]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,14,some 14,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1777]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,15,some 15,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1778]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,16,some 16,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1779]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,17,some 17,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1780]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,18,some 18,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1781]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,19,some 19,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[AxisChoices.test1782]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,20,some 20,257319,[MeasuredChoices.test69],[AxisChoices.test1783]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,21,some 21,257319,[MeasuredChoices.test69],[AxisChoices.test1784]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,22,some 22,257319,[MeasuredChoices.test69],[AxisChoices.test1784,AxisChoices.test1785]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,23,some 23,257319,[MeasuredChoices.test69],[AxisChoices.test1784,AxisChoices.test1786]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,52,some 52,24,some 24,257319,[MeasuredChoices.test69],[AxisChoices.test1787]⟩,3,markedAxisIntersection⟩]
private theorem paid3900 : StockPairs.checked rows3900 = true := by decide +kernel
theorem route3900 (i : Fin 16) : (rows3900.get i).Done :=
  StockPairs.doneAt paid3900 i

def cell3916:PairCell.Row:=⟨50,63,10,2,52,some 52,25,some 25,257319,[MeasuredChoices.test69],[AxisChoices.test1788]⟩
theorem check3916:(cell3916.cap (3:Fin 18)).grade<cell3916.lowerGrade-cell3916.off:=by decide +kernel
def cell3917:PairCell.Row:=⟨50,63,10,2,52,some 52,26,some 26,257319,[MeasuredChoices.test69],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check3917:(cell3917.cap (3:Fin 18)).grade<cell3917.lowerGrade-cell3917.off:=by decide +kernel
def cell3918:PairCell.Row:=⟨50,63,10,2,52,some 52,27,some 27,257319,[MeasuredChoices.test69],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check3918:(cell3918.cap (3:Fin 18)).grade<cell3918.lowerGrade-cell3918.off:=by decide +kernel
def cell3919:PairCell.Row:=⟨50,63,10,2,52,some 52,28,some 28,257319,[MeasuredChoices.test69],[AxisChoices.test1791]⟩
theorem check3919:(cell3919.cap (3:Fin 18)).grade<cell3919.lowerGrade-cell3919.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2933

-- Source: Research6969.PairReceipts196
section Z6969Source2934
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3920:PairCell.Row:=⟨50,63,10,2,52,some 52,29,some 29,257319,[MeasuredChoices.test69],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check3920:(cell3920.cap (3:Fin 18)).grade<cell3920.lowerGrade-cell3920.off:=by decide +kernel
def cell3921:PairCell.Row:=⟨50,63,10,2,52,some 52,30,some 30,257319,[MeasuredChoices.test69],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check3921:(cell3921.cap (3:Fin 18)).grade<cell3921.lowerGrade-cell3921.off:=by decide +kernel
def cell3922:PairCell.Row:=⟨50,63,10,2,52,some 52,31,some 31,257319,[MeasuredChoices.test69],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check3922:(cell3922.cap (3:Fin 18)).grade<cell3922.lowerGrade-cell3922.off:=by decide +kernel
def cell3923:PairCell.Row:=⟨50,63,10,2,52,some 52,32,some 32,257319,[MeasuredChoices.test69],[AxisChoices.test1795]⟩
theorem check3923:(cell3923.cap (3:Fin 18)).grade<cell3923.lowerGrade-cell3923.off:=by decide +kernel
def cell3924:PairCell.Row:=⟨50,63,10,2,52,some 52,33,some 33,257319,[MeasuredChoices.test69],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check3924:(cell3924.cap (3:Fin 18)).grade<cell3924.lowerGrade-cell3924.off:=by decide +kernel
def cell3925:PairCell.Row:=⟨50,63,10,2,52,some 52,34,some 34,257319,[MeasuredChoices.test69],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check3925:(cell3925.cap (3:Fin 18)).grade<cell3925.lowerGrade-cell3925.off:=by decide +kernel
def cell3926:PairCell.Row:=⟨50,63,10,2,52,some 52,35,some 35,257319,[MeasuredChoices.test69],[AxisChoices.test1798]⟩
theorem check3926:(cell3926.cap (3:Fin 18)).grade<cell3926.lowerGrade-cell3926.off:=by decide +kernel
def cell3927:PairCell.Row:=⟨50,63,10,2,52,some 52,36,some 36,257319,[MeasuredChoices.test69],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check3927:(cell3927.cap (3:Fin 18)).grade<cell3927.lowerGrade-cell3927.off:=by decide +kernel
def cell3928:PairCell.Row:=⟨50,63,10,2,52,some 52,37,some 37,257319,[MeasuredChoices.test69],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check3928:(cell3928.cap (3:Fin 18)).grade<cell3928.lowerGrade-cell3928.off:=by decide +kernel
def cell3929:PairCell.Row:=⟨50,63,10,2,52,some 52,38,some 38,257319,[MeasuredChoices.test69],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check3929:(cell3929.cap (3:Fin 18)).grade<cell3929.lowerGrade-cell3929.off:=by decide +kernel
def cell3930:PairCell.Row:=⟨50,63,10,2,52,some 52,39,some 39,257319,[MeasuredChoices.test69],[AxisChoices.test1802]⟩
theorem check3930:(cell3930.cap (3:Fin 18)).grade<cell3930.lowerGrade-cell3930.off:=by decide +kernel
def cell3931:PairCell.Row:=⟨50,63,10,2,52,some 52,40,some 40,257319,[MeasuredChoices.test69],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check3931:(cell3931.cap (3:Fin 18)).grade<cell3931.lowerGrade-cell3931.off:=by decide +kernel
def cell3932:PairCell.Row:=⟨50,63,10,2,52,some 52,41,some 41,257319,[MeasuredChoices.test69],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check3932:(cell3932.cap (3:Fin 18)).grade<cell3932.lowerGrade-cell3932.off:=by decide +kernel
def cell3933:PairCell.Row:=⟨50,63,10,2,52,some 52,42,some 42,257319,[MeasuredChoices.test69],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check3933:(cell3933.cap (3:Fin 18)).grade<cell3933.lowerGrade-cell3933.off:=by decide +kernel
def cell3934:PairCell.Row:=⟨50,63,10,2,52,some 52,43,some 43,257319,[MeasuredChoices.test69],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check3934:(cell3934.cap (3:Fin 18)).grade<cell3934.lowerGrade-cell3934.off:=by decide +kernel
def cell3935:PairCell.Row:=⟨50,63,10,2,52,some 52,44,some 44,257319,[MeasuredChoices.test69],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check3935:(cell3935.cap (3:Fin 18)).grade<cell3935.lowerGrade-cell3935.off:=by decide +kernel
def cell3936:PairCell.Row:=⟨50,63,10,2,52,some 52,45,some 45,257319,[MeasuredChoices.test69],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check3936:(cell3936.cap (3:Fin 18)).grade<cell3936.lowerGrade-cell3936.off:=by decide +kernel
def cell3937:PairCell.Row:=⟨50,63,10,2,52,some 52,46,some 46,257319,[MeasuredChoices.test69],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check3937:(cell3937.cap (3:Fin 18)).grade<cell3937.lowerGrade-cell3937.off:=by decide +kernel
def cell3938:PairCell.Row:=⟨50,63,10,2,52,some 52,47,some 47,257319,[MeasuredChoices.test69],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check3938:(cell3938.cap (3:Fin 18)).grade<cell3938.lowerGrade-cell3938.off:=by decide +kernel
def cell3939:PairCell.Row:=⟨50,63,10,2,52,some 52,48,some 48,257319,[MeasuredChoices.test69],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check3939:(cell3939.cap (3:Fin 18)).grade<cell3939.lowerGrade-cell3939.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2934

-- Source: Research6969.PairReceipts197
section Z6969Source2935
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3940:PairCell.Row:=⟨50,63,10,2,52,some 52,49,some 49,257319,[MeasuredChoices.test69],[AxisChoices.test1812]⟩
theorem check3940:(cell3940.cap (3:Fin 18)).grade<cell3940.lowerGrade-cell3940.off:=by decide +kernel
def cell3941:PairCell.Row:=⟨50,63,10,2,52,some 52,50,some 50,257319,[MeasuredChoices.test69],[AxisChoices.test1813]⟩
theorem check3941:(cell3941.cap (3:Fin 18)).grade<cell3941.lowerGrade-cell3941.off:=by decide +kernel
def cell3942:PairCell.Row:=⟨50,63,10,2,52,some 52,51,some 51,257319,[MeasuredChoices.test69],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3942:(cell3942.cap (3:Fin 18)).grade<cell3942.lowerGrade-cell3942.off:=by decide +kernel
def cell3943:PairCell.Row:=⟨50,63,10,2,52,some 52,52,some 52,257319,[MeasuredChoices.test69],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3943:(cell3943.cap (3:Fin 18)).grade<cell3943.lowerGrade-cell3943.off:=by decide +kernel
private def rows3944 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,51,some 51,0,some 0,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,1,some 1,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,2,some 2,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,3,some 3,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,4,some 4,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,5,some 5,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,6,some 6,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,7,some 7,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,8,some 8,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,9,some 9,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,10,some 10,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,11,some 11,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1774]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,12,some 12,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1775]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,13,some 13,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1776]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,14,some 14,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1777]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,15,some 15,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1778]⟩,3,separateIntersection⟩]
private theorem paid3944 : StockPairs.checked rows3944 = true := by decide +kernel
theorem route3944 (i : Fin 16) : (rows3944.get i).Done :=
  StockPairs.doneAt paid3944 i

end Research6969.PairReceipts
end Z6969Source2935

-- Source: Research6969.PairReceipts198
section Z6969Source2936
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3960 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,51,some 51,16,some 16,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1779]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,17,some 17,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1780]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,18,some 18,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1781]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,19,some 19,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[AxisChoices.test1782]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,20,some 20,257319,[MeasuredChoices.test66],[AxisChoices.test1783]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,21,some 21,257319,[MeasuredChoices.test66],[AxisChoices.test1784]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,22,some 22,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1785]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,23,some 23,257319,[MeasuredChoices.test66],[AxisChoices.test1784,AxisChoices.test1786]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,2,51,some 51,24,some 24,257319,[MeasuredChoices.test66],[AxisChoices.test1787]⟩,3,markedAxisIntersection⟩]
private theorem paid3960 : StockPairs.checked rows3960 = true := by decide +kernel
theorem route3960 (i : Fin 9) : (rows3960.get i).Done :=
  StockPairs.doneAt paid3960 i

def cell3969:PairCell.Row:=⟨50,63,10,2,51,some 51,25,some 25,257319,[MeasuredChoices.test66],[AxisChoices.test1788]⟩
theorem check3969:(cell3969.cap (3:Fin 18)).grade<cell3969.lowerGrade-cell3969.off:=by decide +kernel
def cell3970:PairCell.Row:=⟨50,63,10,2,51,some 51,26,some 26,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check3970:(cell3970.cap (3:Fin 18)).grade<cell3970.lowerGrade-cell3970.off:=by decide +kernel
def cell3971:PairCell.Row:=⟨50,63,10,2,51,some 51,27,some 27,257319,[MeasuredChoices.test66],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check3971:(cell3971.cap (3:Fin 18)).grade<cell3971.lowerGrade-cell3971.off:=by decide +kernel
def cell3972:PairCell.Row:=⟨50,63,10,2,51,some 51,28,some 28,257319,[MeasuredChoices.test66],[AxisChoices.test1791]⟩
theorem check3972:(cell3972.cap (3:Fin 18)).grade<cell3972.lowerGrade-cell3972.off:=by decide +kernel
def cell3973:PairCell.Row:=⟨50,63,10,2,51,some 51,29,some 29,257319,[MeasuredChoices.test66],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check3973:(cell3973.cap (3:Fin 18)).grade<cell3973.lowerGrade-cell3973.off:=by decide +kernel
def cell3974:PairCell.Row:=⟨50,63,10,2,51,some 51,30,some 30,257319,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check3974:(cell3974.cap (3:Fin 18)).grade<cell3974.lowerGrade-cell3974.off:=by decide +kernel
def cell3975:PairCell.Row:=⟨50,63,10,2,51,some 51,31,some 31,257319,[MeasuredChoices.test66],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check3975:(cell3975.cap (3:Fin 18)).grade<cell3975.lowerGrade-cell3975.off:=by decide +kernel
def cell3976:PairCell.Row:=⟨50,63,10,2,51,some 51,32,some 32,257319,[MeasuredChoices.test66],[AxisChoices.test1795]⟩
theorem check3976:(cell3976.cap (3:Fin 18)).grade<cell3976.lowerGrade-cell3976.off:=by decide +kernel
def cell3977:PairCell.Row:=⟨50,63,10,2,51,some 51,33,some 33,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check3977:(cell3977.cap (3:Fin 18)).grade<cell3977.lowerGrade-cell3977.off:=by decide +kernel
def cell3978:PairCell.Row:=⟨50,63,10,2,51,some 51,34,some 34,257319,[MeasuredChoices.test66],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check3978:(cell3978.cap (3:Fin 18)).grade<cell3978.lowerGrade-cell3978.off:=by decide +kernel
def cell3979:PairCell.Row:=⟨50,63,10,2,51,some 51,35,some 35,257319,[MeasuredChoices.test66],[AxisChoices.test1798]⟩
theorem check3979:(cell3979.cap (3:Fin 18)).grade<cell3979.lowerGrade-cell3979.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2936

-- Source: Research6969.PairReceipts199
section Z6969Source2937
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3980:PairCell.Row:=⟨50,63,10,2,51,some 51,36,some 36,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check3980:(cell3980.cap (3:Fin 18)).grade<cell3980.lowerGrade-cell3980.off:=by decide +kernel
def cell3981:PairCell.Row:=⟨50,63,10,2,51,some 51,37,some 37,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check3981:(cell3981.cap (3:Fin 18)).grade<cell3981.lowerGrade-cell3981.off:=by decide +kernel
def cell3982:PairCell.Row:=⟨50,63,10,2,51,some 51,38,some 38,257319,[MeasuredChoices.test66],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check3982:(cell3982.cap (3:Fin 18)).grade<cell3982.lowerGrade-cell3982.off:=by decide +kernel
def cell3983:PairCell.Row:=⟨50,63,10,2,51,some 51,39,some 39,257319,[MeasuredChoices.test66],[AxisChoices.test1802]⟩
theorem check3983:(cell3983.cap (3:Fin 18)).grade<cell3983.lowerGrade-cell3983.off:=by decide +kernel
def cell3984:PairCell.Row:=⟨50,63,10,2,51,some 51,40,some 40,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check3984:(cell3984.cap (3:Fin 18)).grade<cell3984.lowerGrade-cell3984.off:=by decide +kernel
def cell3985:PairCell.Row:=⟨50,63,10,2,51,some 51,41,some 41,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check3985:(cell3985.cap (3:Fin 18)).grade<cell3985.lowerGrade-cell3985.off:=by decide +kernel
def cell3986:PairCell.Row:=⟨50,63,10,2,51,some 51,42,some 42,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check3986:(cell3986.cap (3:Fin 18)).grade<cell3986.lowerGrade-cell3986.off:=by decide +kernel
def cell3987:PairCell.Row:=⟨50,63,10,2,51,some 51,43,some 43,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check3987:(cell3987.cap (3:Fin 18)).grade<cell3987.lowerGrade-cell3987.off:=by decide +kernel
def cell3988:PairCell.Row:=⟨50,63,10,2,51,some 51,44,some 44,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check3988:(cell3988.cap (3:Fin 18)).grade<cell3988.lowerGrade-cell3988.off:=by decide +kernel
def cell3989:PairCell.Row:=⟨50,63,10,2,51,some 51,45,some 45,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check3989:(cell3989.cap (3:Fin 18)).grade<cell3989.lowerGrade-cell3989.off:=by decide +kernel
def cell3990:PairCell.Row:=⟨50,63,10,2,51,some 51,46,some 46,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check3990:(cell3990.cap (3:Fin 18)).grade<cell3990.lowerGrade-cell3990.off:=by decide +kernel
def cell3991:PairCell.Row:=⟨50,63,10,2,51,some 51,47,some 47,257319,[MeasuredChoices.test66],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check3991:(cell3991.cap (3:Fin 18)).grade<cell3991.lowerGrade-cell3991.off:=by decide +kernel
def cell3992:PairCell.Row:=⟨50,63,10,2,51,some 51,48,some 48,257319,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check3992:(cell3992.cap (3:Fin 18)).grade<cell3992.lowerGrade-cell3992.off:=by decide +kernel
def cell3993:PairCell.Row:=⟨50,63,10,2,51,some 51,49,some 49,257319,[MeasuredChoices.test66],[AxisChoices.test1812]⟩
theorem check3993:(cell3993.cap (3:Fin 18)).grade<cell3993.lowerGrade-cell3993.off:=by decide +kernel
def cell3994:PairCell.Row:=⟨50,63,10,2,51,some 51,50,some 50,257319,[MeasuredChoices.test66],[AxisChoices.test1813]⟩
theorem check3994:(cell3994.cap (3:Fin 18)).grade<cell3994.lowerGrade-cell3994.off:=by decide +kernel
def cell3995:PairCell.Row:=⟨50,63,10,2,51,some 51,51,some 51,257319,[MeasuredChoices.test66],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3995:(cell3995.cap (3:Fin 18)).grade<cell3995.lowerGrade-cell3995.off:=by decide +kernel
private def rows3996 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,49,some 50,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,3,⟨(.node 8029306683929914),.intersection,.impossible,289917⟩⟩,
  ⟨⟨50,63,10,2,49,some 50,0,none,289917,[MeasuredChoices.test104,MeasuredChoices.test118],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,45,some 48,0,none,257319,[MeasuredChoices.test56],[]⟩,3,⟨(.node 30268515783660603),.intersection,.impossible,303874⟩⟩,
  ⟨⟨50,63,10,2,45,some 48,0,none,303874,[MeasuredChoices.test174,MeasuredChoices.test175],[]⟩,3,surfaceIntersection⟩]
private theorem paid3996 : StockPairs.checked rows3996 = true := by decide +kernel
theorem route3996 (i : Fin 4) : (rows3996.get i).Done :=
  StockPairs.doneAt paid3996 i

end Research6969.PairReceipts
end Z6969Source2937

-- Source: Research6969.HardFit4At090
section Z6969Source2938
set_option autoImplicit true
namespace Research6969.HardFit4At090
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4000 0)
theorem case90: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,41,some 44⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3996 2)
private def leaf2 := (PairReceipts.route3996 3)
private def weight3 := PairRoute.weight 303874 leaf1 leaf2
theorem case91: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,45,some 48⟩:=PairRoute.start _ weight3
private def leaf4 := (PairReceipts.route3996 0)
private def leaf5 := (PairReceipts.route3996 1)
private def weight6 := PairRoute.weight 289917 leaf4 leaf5
theorem case92: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,49,some 50⟩:=PairRoute.start _ weight6
private theorem allAxes110:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,51,some 51⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 51 ⟨
    (PairReceipts.route3944 0),
    (PairReceipts.route3944 1),
    (PairReceipts.route3944 2),
    (PairReceipts.route3944 3),
    (PairReceipts.route3944 4),
    (PairReceipts.route3944 5),
    (PairReceipts.route3944 6),
    (PairReceipts.route3944 7),
    (PairReceipts.route3944 8),
    (PairReceipts.route3944 9),
    (PairReceipts.route3944 10),
    (PairReceipts.route3944 11),
    (PairReceipts.route3944 12),
    (PairReceipts.route3944 13),
    (PairReceipts.route3944 14),
    (PairReceipts.route3944 15),
    (PairReceipts.route3960 0),
    (PairReceipts.route3960 1),
    (PairReceipts.route3960 2),
    (PairReceipts.route3960 3),
    (PairReceipts.route3960 4),
    (PairReceipts.route3960 5),
    (PairReceipts.route3960 6),
    (PairReceipts.route3960 7),
    (PairReceipts.route3960 8),
    PairLeaves.excluded PairReceipts.cell3969 PairReceipts.check3969 (none),
    PairLeaves.excluded PairReceipts.cell3970 PairReceipts.check3970 (none),
    PairLeaves.excluded PairReceipts.cell3971 PairReceipts.check3971 (none),
    PairLeaves.excluded PairReceipts.cell3972 PairReceipts.check3972 (none),
    PairLeaves.excluded PairReceipts.cell3973 PairReceipts.check3973 (none),
    PairLeaves.excluded PairReceipts.cell3974 PairReceipts.check3974 (none),
    PairLeaves.excluded PairReceipts.cell3975 PairReceipts.check3975 (none),
    PairLeaves.excluded PairReceipts.cell3976 PairReceipts.check3976 (none),
    PairLeaves.excluded PairReceipts.cell3977 PairReceipts.check3977 (none),
    PairLeaves.excluded PairReceipts.cell3978 PairReceipts.check3978 (none),
    PairLeaves.excluded PairReceipts.cell3979 PairReceipts.check3979 (none),
    PairLeaves.excluded PairReceipts.cell3980 PairReceipts.check3980 (none),
    PairLeaves.excluded PairReceipts.cell3981 PairReceipts.check3981 (none),
    PairLeaves.excluded PairReceipts.cell3982 PairReceipts.check3982 (none),
    PairLeaves.excluded PairReceipts.cell3983 PairReceipts.check3983 (none),
    PairLeaves.excluded PairReceipts.cell3984 PairReceipts.check3984 (none),
    PairLeaves.excluded PairReceipts.cell3985 PairReceipts.check3985 (none),
    PairLeaves.excluded PairReceipts.cell3986 PairReceipts.check3986 (none),
    PairLeaves.excluded PairReceipts.cell3987 PairReceipts.check3987 (none),
    PairLeaves.excluded PairReceipts.cell3988 PairReceipts.check3988 (none),
    PairLeaves.excluded PairReceipts.cell3989 PairReceipts.check3989 (none),
    PairLeaves.excluded PairReceipts.cell3990 PairReceipts.check3990 (none),
    PairLeaves.excluded PairReceipts.cell3991 PairReceipts.check3991 (none),
    PairLeaves.excluded PairReceipts.cell3992 PairReceipts.check3992 (none),
    PairLeaves.excluded PairReceipts.cell3993 PairReceipts.check3993 (none),
    PairLeaves.excluded PairReceipts.cell3994 PairReceipts.check3994 (none),
    PairLeaves.excluded PairReceipts.cell3995 PairReceipts.check3995 (none),
    trivial⟩)
theorem case93: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,51,some 51⟩:=PairRoute.start _ allAxes110
private theorem allAxes216:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,52,some 52⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 52 ⟨
    (PairReceipts.route3891 0),
    (PairReceipts.route3891 1),
    (PairReceipts.route3891 2),
    (PairReceipts.route3891 3),
    (PairReceipts.route3891 4),
    (PairReceipts.route3891 5),
    (PairReceipts.route3891 6),
    (PairReceipts.route3891 7),
    (PairReceipts.route3891 8),
    (PairReceipts.route3900 0),
    (PairReceipts.route3900 1),
    (PairReceipts.route3900 2),
    (PairReceipts.route3900 3),
    (PairReceipts.route3900 4),
    (PairReceipts.route3900 5),
    (PairReceipts.route3900 6),
    (PairReceipts.route3900 7),
    (PairReceipts.route3900 8),
    (PairReceipts.route3900 9),
    (PairReceipts.route3900 10),
    (PairReceipts.route3900 11),
    (PairReceipts.route3900 12),
    (PairReceipts.route3900 13),
    (PairReceipts.route3900 14),
    (PairReceipts.route3900 15),
    PairLeaves.excluded PairReceipts.cell3916 PairReceipts.check3916 (none),
    PairLeaves.excluded PairReceipts.cell3917 PairReceipts.check3917 (none),
    PairLeaves.excluded PairReceipts.cell3918 PairReceipts.check3918 (none),
    PairLeaves.excluded PairReceipts.cell3919 PairReceipts.check3919 (none),
    PairLeaves.excluded PairReceipts.cell3920 PairReceipts.check3920 (none),
    PairLeaves.excluded PairReceipts.cell3921 PairReceipts.check3921 (none),
    PairLeaves.excluded PairReceipts.cell3922 PairReceipts.check3922 (none),
    PairLeaves.excluded PairReceipts.cell3923 PairReceipts.check3923 (none),
    PairLeaves.excluded PairReceipts.cell3924 PairReceipts.check3924 (none),
    PairLeaves.excluded PairReceipts.cell3925 PairReceipts.check3925 (none),
    PairLeaves.excluded PairReceipts.cell3926 PairReceipts.check3926 (none),
    PairLeaves.excluded PairReceipts.cell3927 PairReceipts.check3927 (none),
    PairLeaves.excluded PairReceipts.cell3928 PairReceipts.check3928 (none),
    PairLeaves.excluded PairReceipts.cell3929 PairReceipts.check3929 (none),
    PairLeaves.excluded PairReceipts.cell3930 PairReceipts.check3930 (none),
    PairLeaves.excluded PairReceipts.cell3931 PairReceipts.check3931 (none),
    PairLeaves.excluded PairReceipts.cell3932 PairReceipts.check3932 (none),
    PairLeaves.excluded PairReceipts.cell3933 PairReceipts.check3933 (none),
    PairLeaves.excluded PairReceipts.cell3934 PairReceipts.check3934 (none),
    PairLeaves.excluded PairReceipts.cell3935 PairReceipts.check3935 (none),
    PairLeaves.excluded PairReceipts.cell3936 PairReceipts.check3936 (none),
    PairLeaves.excluded PairReceipts.cell3937 PairReceipts.check3937 (none),
    PairLeaves.excluded PairReceipts.cell3938 PairReceipts.check3938 (none),
    PairLeaves.excluded PairReceipts.cell3939 PairReceipts.check3939 (none),
    PairLeaves.excluded PairReceipts.cell3940 PairReceipts.check3940 (none),
    PairLeaves.excluded PairReceipts.cell3941 PairReceipts.check3941 (none),
    PairLeaves.excluded PairReceipts.cell3942 PairReceipts.check3942 (none),
    PairLeaves.excluded PairReceipts.cell3943 PairReceipts.check3943 (none),
    trivial⟩)
theorem case94: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,52,some 52⟩:=PairRoute.start _ allAxes216
private theorem allAxes324:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,some 53⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 53 ⟨
    (PairReceipts.route3837 0),
    (PairReceipts.route3837 1),
    (PairReceipts.route3837 2),
    (PairReceipts.route3840 0),
    (PairReceipts.route3840 1),
    (PairReceipts.route3840 2),
    (PairReceipts.route3840 3),
    (PairReceipts.route3840 4),
    (PairReceipts.route3840 5),
    (PairReceipts.route3840 6),
    (PairReceipts.route3840 7),
    (PairReceipts.route3840 8),
    (PairReceipts.route3840 9),
    (PairReceipts.route3840 10),
    (PairReceipts.route3840 11),
    (PairReceipts.route3840 12),
    (PairReceipts.route3840 13),
    (PairReceipts.route3840 14),
    (PairReceipts.route3840 15),
    (PairReceipts.route3840 16),
    (PairReceipts.route3840 17),
    (PairReceipts.route3840 18),
    (PairReceipts.route3840 19),
    (PairReceipts.route3860 0),
    (PairReceipts.route3860 1),
    PairLeaves.excluded PairReceipts.cell3862 PairReceipts.check3862 (none),
    PairLeaves.excluded PairReceipts.cell3863 PairReceipts.check3863 (none),
    PairLeaves.excluded PairReceipts.cell3864 PairReceipts.check3864 (none),
    PairLeaves.excluded PairReceipts.cell3865 PairReceipts.check3865 (none),
    PairLeaves.excluded PairReceipts.cell3866 PairReceipts.check3866 (none),
    PairLeaves.excluded PairReceipts.cell3867 PairReceipts.check3867 (none),
    PairLeaves.excluded PairReceipts.cell3868 PairReceipts.check3868 (none),
    PairLeaves.excluded PairReceipts.cell3869 PairReceipts.check3869 (none),
    PairLeaves.excluded PairReceipts.cell3870 PairReceipts.check3870 (none),
    PairLeaves.excluded PairReceipts.cell3871 PairReceipts.check3871 (none),
    PairLeaves.excluded PairReceipts.cell3872 PairReceipts.check3872 (none),
    PairLeaves.excluded PairReceipts.cell3873 PairReceipts.check3873 (none),
    PairLeaves.excluded PairReceipts.cell3874 PairReceipts.check3874 (none),
    PairLeaves.excluded PairReceipts.cell3875 PairReceipts.check3875 (none),
    PairLeaves.excluded PairReceipts.cell3876 PairReceipts.check3876 (none),
    PairLeaves.excluded PairReceipts.cell3877 PairReceipts.check3877 (none),
    PairLeaves.excluded PairReceipts.cell3878 PairReceipts.check3878 (none),
    PairLeaves.excluded PairReceipts.cell3879 PairReceipts.check3879 (none),
    PairLeaves.excluded PairReceipts.cell3880 PairReceipts.check3880 (none),
    PairLeaves.excluded PairReceipts.cell3881 PairReceipts.check3881 (none),
    PairLeaves.excluded PairReceipts.cell3882 PairReceipts.check3882 (none),
    PairLeaves.excluded PairReceipts.cell3883 PairReceipts.check3883 (none),
    PairLeaves.excluded PairReceipts.cell3884 PairReceipts.check3884 (none),
    PairLeaves.excluded PairReceipts.cell3885 PairReceipts.check3885 (none),
    PairLeaves.excluded PairReceipts.cell3886 PairReceipts.check3886 (none),
    PairLeaves.excluded PairReceipts.cell3887 PairReceipts.check3887 (none),
    PairLeaves.excluded PairReceipts.cell3888 PairReceipts.check3888 (none),
    PairLeaves.excluded PairReceipts.cell3889 PairReceipts.check3889 (none),
    PairLeaves.excluded PairReceipts.cell3890 PairReceipts.check3890 (none),
    trivial⟩)
theorem case95: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,53,some 53⟩:=PairRoute.start _ allAxes324
private theorem allAxes434:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,some 54⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 54 ⟨
    (PairReceipts.route3782 0),
    (PairReceipts.route3782 1),
    (PairReceipts.route3782 2),
    (PairReceipts.route3782 3),
    (PairReceipts.route3782 4),
    (PairReceipts.route3782 5),
    (PairReceipts.route3782 6),
    (PairReceipts.route3782 7),
    (PairReceipts.route3782 8),
    (PairReceipts.route3782 9),
    (PairReceipts.route3782 10),
    (PairReceipts.route3782 11),
    (PairReceipts.route3782 12),
    (PairReceipts.route3782 13),
    (PairReceipts.route3782 14),
    (PairReceipts.route3782 15),
    (PairReceipts.route3782 16),
    (PairReceipts.route3782 17),
    (PairReceipts.route3800 0),
    (PairReceipts.route3800 1),
    (PairReceipts.route3800 2),
    (PairReceipts.route3800 3),
    (PairReceipts.route3800 4),
    (PairReceipts.route3800 5),
    (PairReceipts.route3800 6),
    PairLeaves.excluded PairReceipts.cell3807 PairReceipts.check3807 (none),
    PairLeaves.excluded PairReceipts.cell3808 PairReceipts.check3808 (none),
    PairLeaves.excluded PairReceipts.cell3809 PairReceipts.check3809 (none),
    PairLeaves.excluded PairReceipts.cell3810 PairReceipts.check3810 (none),
    PairLeaves.excluded PairReceipts.cell3811 PairReceipts.check3811 (none),
    PairLeaves.excluded PairReceipts.cell3812 PairReceipts.check3812 (none),
    PairLeaves.excluded PairReceipts.cell3813 PairReceipts.check3813 (none),
    PairLeaves.excluded PairReceipts.cell3814 PairReceipts.check3814 (none),
    PairLeaves.excluded PairReceipts.cell3815 PairReceipts.check3815 (none),
    PairLeaves.excluded PairReceipts.cell3816 PairReceipts.check3816 (none),
    PairLeaves.excluded PairReceipts.cell3817 PairReceipts.check3817 (none),
    PairLeaves.excluded PairReceipts.cell3818 PairReceipts.check3818 (none),
    PairLeaves.excluded PairReceipts.cell3819 PairReceipts.check3819 (none),
    PairLeaves.excluded PairReceipts.cell3820 PairReceipts.check3820 (none),
    PairLeaves.excluded PairReceipts.cell3821 PairReceipts.check3821 (none),
    PairLeaves.excluded PairReceipts.cell3822 PairReceipts.check3822 (none),
    PairLeaves.excluded PairReceipts.cell3823 PairReceipts.check3823 (none),
    PairLeaves.excluded PairReceipts.cell3824 PairReceipts.check3824 (none),
    PairLeaves.excluded PairReceipts.cell3825 PairReceipts.check3825 (none),
    PairLeaves.excluded PairReceipts.cell3826 PairReceipts.check3826 (none),
    PairLeaves.excluded PairReceipts.cell3827 PairReceipts.check3827 (none),
    PairLeaves.excluded PairReceipts.cell3828 PairReceipts.check3828 (none),
    PairLeaves.excluded PairReceipts.cell3829 PairReceipts.check3829 (none),
    PairLeaves.excluded PairReceipts.cell3830 PairReceipts.check3830 (none),
    PairLeaves.excluded PairReceipts.cell3831 PairReceipts.check3831 (none),
    PairLeaves.excluded PairReceipts.cell3832 PairReceipts.check3832 (none),
    PairLeaves.excluded PairReceipts.cell3833 PairReceipts.check3833 (none),
    PairLeaves.excluded PairReceipts.cell3834 PairReceipts.check3834 (none),
    PairLeaves.excluded PairReceipts.cell3835 PairReceipts.check3835 (none),
    PairLeaves.excluded PairReceipts.cell3836 PairReceipts.check3836 (none),
    trivial⟩)
theorem case96: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,54,some 54⟩:=PairRoute.start _ allAxes434
private theorem allAxes546:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,some 55⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 55 ⟨
    (PairReceipts.route3726 0),
    (PairReceipts.route3726 1),
    (PairReceipts.route3726 2),
    (PairReceipts.route3726 3),
    (PairReceipts.route3726 4),
    (PairReceipts.route3726 5),
    (PairReceipts.route3726 6),
    (PairReceipts.route3726 7),
    (PairReceipts.route3726 8),
    (PairReceipts.route3726 9),
    (PairReceipts.route3726 10),
    (PairReceipts.route3726 11),
    (PairReceipts.route3726 12),
    (PairReceipts.route3726 13),
    (PairReceipts.route3740 0),
    (PairReceipts.route3740 1),
    (PairReceipts.route3740 2),
    (PairReceipts.route3740 3),
    (PairReceipts.route3740 4),
    (PairReceipts.route3740 5),
    (PairReceipts.route3740 6),
    (PairReceipts.route3740 7),
    (PairReceipts.route3740 8),
    (PairReceipts.route3740 9),
    (PairReceipts.route3740 10),
    PairLeaves.excluded PairReceipts.cell3751 PairReceipts.check3751 (none),
    PairLeaves.excluded PairReceipts.cell3752 PairReceipts.check3752 (none),
    PairLeaves.excluded PairReceipts.cell3753 PairReceipts.check3753 (none),
    PairLeaves.excluded PairReceipts.cell3754 PairReceipts.check3754 (none),
    PairLeaves.excluded PairReceipts.cell3755 PairReceipts.check3755 (none),
    PairLeaves.excluded PairReceipts.cell3756 PairReceipts.check3756 (none),
    PairLeaves.excluded PairReceipts.cell3757 PairReceipts.check3757 (none),
    PairLeaves.excluded PairReceipts.cell3758 PairReceipts.check3758 (none),
    PairLeaves.excluded PairReceipts.cell3759 PairReceipts.check3759 (none),
    PairLeaves.excluded PairReceipts.cell3760 PairReceipts.check3760 (none),
    PairLeaves.excluded PairReceipts.cell3761 PairReceipts.check3761 (none),
    PairLeaves.excluded PairReceipts.cell3762 PairReceipts.check3762 (none),
    PairLeaves.excluded PairReceipts.cell3763 PairReceipts.check3763 (none),
    PairLeaves.excluded PairReceipts.cell3764 PairReceipts.check3764 (none),
    PairLeaves.excluded PairReceipts.cell3765 PairReceipts.check3765 (none),
    PairLeaves.excluded PairReceipts.cell3766 PairReceipts.check3766 (none),
    PairLeaves.excluded PairReceipts.cell3767 PairReceipts.check3767 (none),
    PairLeaves.excluded PairReceipts.cell3768 PairReceipts.check3768 (none),
    PairLeaves.excluded PairReceipts.cell3769 PairReceipts.check3769 (none),
    PairLeaves.excluded PairReceipts.cell3770 PairReceipts.check3770 (none),
    PairLeaves.excluded PairReceipts.cell3771 PairReceipts.check3771 (none),
    PairLeaves.excluded PairReceipts.cell3772 PairReceipts.check3772 (none),
    PairLeaves.excluded PairReceipts.cell3773 PairReceipts.check3773 (none),
    PairLeaves.excluded PairReceipts.cell3774 PairReceipts.check3774 (none),
    PairLeaves.excluded PairReceipts.cell3775 PairReceipts.check3775 (none),
    PairLeaves.excluded PairReceipts.cell3776 PairReceipts.check3776 (none),
    PairLeaves.excluded PairReceipts.cell3777 PairReceipts.check3777 (none),
    PairLeaves.excluded PairReceipts.cell3778 PairReceipts.check3778 (none),
    PairLeaves.excluded PairReceipts.cell3779 PairReceipts.check3779 (none),
    PairLeaves.excluded PairReceipts.cell3780 PairReceipts.check3780 (none),
    PairLeaves.excluded PairReceipts.cell3781 PairReceipts.check3781 (none),
    trivial⟩)
theorem case97: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,55,some 55⟩:=PairRoute.start _ allAxes546
private theorem allAxes660:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,some 56⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 56 ⟨
    (PairReceipts.route3669 0),
    (PairReceipts.route3669 1),
    (PairReceipts.route3669 2),
    (PairReceipts.route3669 3),
    (PairReceipts.route3669 4),
    (PairReceipts.route3669 5),
    (PairReceipts.route3669 6),
    (PairReceipts.route3669 7),
    (PairReceipts.route3669 8),
    (PairReceipts.route3669 9),
    (PairReceipts.route3669 10),
    (PairReceipts.route3680 0),
    (PairReceipts.route3680 1),
    (PairReceipts.route3680 2),
    (PairReceipts.route3680 3),
    (PairReceipts.route3680 4),
    (PairReceipts.route3680 5),
    (PairReceipts.route3680 6),
    (PairReceipts.route3680 7),
    (PairReceipts.route3680 8),
    (PairReceipts.route3680 9),
    (PairReceipts.route3680 10),
    (PairReceipts.route3680 11),
    (PairReceipts.route3680 12),
    (PairReceipts.route3680 13),
    PairLeaves.excluded PairReceipts.cell3694 PairReceipts.check3694 (none),
    PairLeaves.excluded PairReceipts.cell3695 PairReceipts.check3695 (none),
    PairLeaves.excluded PairReceipts.cell3696 PairReceipts.check3696 (none),
    PairLeaves.excluded PairReceipts.cell3697 PairReceipts.check3697 (none),
    PairLeaves.excluded PairReceipts.cell3698 PairReceipts.check3698 (none),
    PairLeaves.excluded PairReceipts.cell3699 PairReceipts.check3699 (none),
    PairLeaves.excluded PairReceipts.cell3700 PairReceipts.check3700 (none),
    PairLeaves.excluded PairReceipts.cell3701 PairReceipts.check3701 (none),
    PairLeaves.excluded PairReceipts.cell3702 PairReceipts.check3702 (none),
    PairLeaves.excluded PairReceipts.cell3703 PairReceipts.check3703 (none),
    PairLeaves.excluded PairReceipts.cell3704 PairReceipts.check3704 (none),
    PairLeaves.excluded PairReceipts.cell3705 PairReceipts.check3705 (none),
    PairLeaves.excluded PairReceipts.cell3706 PairReceipts.check3706 (none),
    PairLeaves.excluded PairReceipts.cell3707 PairReceipts.check3707 (none),
    PairLeaves.excluded PairReceipts.cell3708 PairReceipts.check3708 (none),
    PairLeaves.excluded PairReceipts.cell3709 PairReceipts.check3709 (none),
    PairLeaves.excluded PairReceipts.cell3710 PairReceipts.check3710 (none),
    PairLeaves.excluded PairReceipts.cell3711 PairReceipts.check3711 (none),
    PairLeaves.excluded PairReceipts.cell3712 PairReceipts.check3712 (none),
    PairLeaves.excluded PairReceipts.cell3713 PairReceipts.check3713 (none),
    PairLeaves.excluded PairReceipts.cell3714 PairReceipts.check3714 (none),
    PairLeaves.excluded PairReceipts.cell3715 PairReceipts.check3715 (none),
    PairLeaves.excluded PairReceipts.cell3716 PairReceipts.check3716 (none),
    PairLeaves.excluded PairReceipts.cell3717 PairReceipts.check3717 (none),
    PairLeaves.excluded PairReceipts.cell3718 PairReceipts.check3718 (none),
    PairLeaves.excluded PairReceipts.cell3719 PairReceipts.check3719 (none),
    PairLeaves.excluded PairReceipts.cell3720 PairReceipts.check3720 (none),
    PairLeaves.excluded PairReceipts.cell3721 PairReceipts.check3721 (none),
    PairLeaves.excluded PairReceipts.cell3722 PairReceipts.check3722 (none),
    PairLeaves.excluded PairReceipts.cell3723 PairReceipts.check3723 (none),
    PairLeaves.excluded PairReceipts.cell3724 PairReceipts.check3724 (none),
    PairLeaves.excluded PairReceipts.cell3725 PairReceipts.check3725 (none),
    trivial⟩)
theorem case98: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,56,some 56⟩:=PairRoute.start _ allAxes660
private theorem allAxes776:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,some 57⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 57 ⟨
    (PairReceipts.route3600 11),
    (PairReceipts.route3600 12),
    (PairReceipts.route3600 13),
    (PairReceipts.route3600 14),
    (PairReceipts.route3600 15),
    (PairReceipts.route3600 16),
    (PairReceipts.route3600 17),
    (PairReceipts.route3600 18),
    (PairReceipts.route3600 19),
    (PairReceipts.route3620 0),
    (PairReceipts.route3620 1),
    (PairReceipts.route3620 2),
    (PairReceipts.route3620 3),
    (PairReceipts.route3620 4),
    (PairReceipts.route3620 5),
    (PairReceipts.route3620 6),
    (PairReceipts.route3620 7),
    (PairReceipts.route3620 8),
    (PairReceipts.route3620 9),
    (PairReceipts.route3620 10),
    (PairReceipts.route3620 11),
    (PairReceipts.route3620 12),
    (PairReceipts.route3620 13),
    (PairReceipts.route3620 14),
    (PairReceipts.route3620 15),
    PairLeaves.excluded PairReceipts.cell3636 PairReceipts.check3636 (none),
    PairLeaves.excluded PairReceipts.cell3637 PairReceipts.check3637 (none),
    PairLeaves.excluded PairReceipts.cell3638 PairReceipts.check3638 (none),
    PairLeaves.excluded PairReceipts.cell3639 PairReceipts.check3639 (none),
    PairLeaves.excluded PairReceipts.cell3640 PairReceipts.check3640 (none),
    PairLeaves.excluded PairReceipts.cell3641 PairReceipts.check3641 (none),
    PairLeaves.excluded PairReceipts.cell3642 PairReceipts.check3642 (none),
    PairLeaves.excluded PairReceipts.cell3643 PairReceipts.check3643 (none),
    PairLeaves.excluded PairReceipts.cell3644 PairReceipts.check3644 (none),
    PairLeaves.excluded PairReceipts.cell3645 PairReceipts.check3645 (none),
    PairLeaves.excluded PairReceipts.cell3646 PairReceipts.check3646 (none),
    PairLeaves.excluded PairReceipts.cell3647 PairReceipts.check3647 (none),
    PairLeaves.excluded PairReceipts.cell3648 PairReceipts.check3648 (none),
    PairLeaves.excluded PairReceipts.cell3649 PairReceipts.check3649 (none),
    PairLeaves.excluded PairReceipts.cell3650 PairReceipts.check3650 (none),
    PairLeaves.excluded PairReceipts.cell3651 PairReceipts.check3651 (none),
    PairLeaves.excluded PairReceipts.cell3652 PairReceipts.check3652 (none),
    PairLeaves.excluded PairReceipts.cell3653 PairReceipts.check3653 (none),
    PairLeaves.excluded PairReceipts.cell3654 PairReceipts.check3654 (none),
    PairLeaves.excluded PairReceipts.cell3655 PairReceipts.check3655 (none),
    PairLeaves.excluded PairReceipts.cell3656 PairReceipts.check3656 (none),
    PairLeaves.excluded PairReceipts.cell3657 PairReceipts.check3657 (none),
    PairLeaves.excluded PairReceipts.cell3658 PairReceipts.check3658 (none),
    PairLeaves.excluded PairReceipts.cell3659 PairReceipts.check3659 (none),
    PairLeaves.excluded PairReceipts.cell3660 PairReceipts.check3660 (none),
    PairLeaves.excluded PairReceipts.cell3661 PairReceipts.check3661 (none),
    PairLeaves.excluded PairReceipts.cell3662 PairReceipts.check3662 (none),
    PairLeaves.excluded PairReceipts.cell3663 PairReceipts.check3663 (none),
    PairLeaves.excluded PairReceipts.cell3664 PairReceipts.check3664 (none),
    PairLeaves.excluded PairReceipts.cell3665 PairReceipts.check3665 (none),
    PairLeaves.excluded PairReceipts.cell3666 PairReceipts.check3666 (none),
    PairLeaves.excluded PairReceipts.cell3667 PairReceipts.check3667 (none),
    PairLeaves.excluded PairReceipts.cell3668 PairReceipts.check3668 (none),
    trivial⟩)
theorem case99: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,57,some 57⟩:=PairRoute.start _ allAxes776
end Research6969.HardFit4At090
end Z6969Source2938

-- Source: Research6969.PairReceipts202
section Z6969Source2939
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4040 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,18,some 18,0,none,385979,[MeasuredChoices.test831],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,3,separateIntersection⟩]
private theorem paid4040 : StockPairs.checked rows4040 = true := by decide +kernel
theorem route4040 (i : Fin 20) : (rows4040.get i).Done :=
  StockPairs.doneAt paid4040 i

end Research6969.PairReceipts
end Z6969Source2939

-- Source: Research6969.PairReceipts203
section Z6969Source2940
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4060 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,3,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,16,some 16,0,none,385979,[MeasuredChoices.test807],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,15,some 15,0,none,385979,[MeasuredChoices.test797],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨64,650,12,1,49,some 64,0,none,128659,[MeasuredChoices.test5,MeasuredChoices.test6],[]⟩,3,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,650,12,1,41,some 48,0,none,128659,[MeasuredChoices.test3,MeasuredChoices.test4],[]⟩,3,⟨.affine,.whole,.impossible,0⟩⟩,
  ⟨⟨64,650,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,3,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,650,12,2,51,some 51,0,some 0,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,1,some 1,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,2,some 2,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,3,some 3,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩,
  ⟨⟨64,650,12,2,51,some 51,4,some 4,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,3,separateWhole⟩]
private theorem paid4060 : StockPairs.checked rows4060 = true := by decide +kernel
theorem route4060 (i : Fin 19) : (rows4060.get i).Done :=
  StockPairs.doneAt paid4060 i

def cell4074:PairCell.Row:=⟨64,650,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩
theorem check4074:(cell4074.cap (3:Fin 18)).grade<cell4074.lowerGrade-cell4074.off:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2940

-- Source: Research6969.HardFit4At100
section Z6969Source2941
set_option autoImplicit true
namespace Research6969.HardFit4At100
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3600 9)
private def leaf1 := (PairReceipts.route3600 10)
private def weight2 := PairRoute.weight 283522 leaf0 leaf1
theorem case100: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,58,some 58⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route3600 8)
theorem case101: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,59,some 60⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route3600 7)
theorem case102: NormalRoute.Done (3:Fin 18) ⟨50,63,10,2,61,some 64⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4060 10)
theorem case103: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,4,some 8⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4060 9)
theorem case104: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4060 8)
theorem case105: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,13,some 14⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4060 7)
theorem case106: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,15,some 15⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4060 6)
theorem case107: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,16,some 16⟩:=PairRoute.start _ leaf9
private theorem allAxes45:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route4040 8),
    (PairReceipts.route4040 9),
    (PairReceipts.route4040 10),
    (PairReceipts.route4040 11),
    (PairReceipts.route4040 12),
    (PairReceipts.route4040 13),
    (PairReceipts.route4040 14),
    (PairReceipts.route4040 15),
    (PairReceipts.route4040 16),
    (PairReceipts.route4040 17),
    (PairReceipts.route4040 18),
    (PairReceipts.route4040 19),
    (PairReceipts.route4060 0),
    (PairReceipts.route4060 1),
    (PairReceipts.route4060 2),
    (PairReceipts.route4060 3),
    (PairReceipts.route4060 4),
    (PairReceipts.route4060 5),
    trivial⟩)
theorem case108: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,17,some 17⟩:=PairRoute.start _ allAxes45
private def leaf46 := (PairReceipts.route4040 7)
theorem case109: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,18,some 18⟩:=PairRoute.start _ leaf46
end Research6969.HardFit4At100
end Z6969Source2941

-- Source: Research6969.PairReceipts201
section Z6969Source2942
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4020 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,3,29,some 30,0,none,385979,[MeasuredChoices.test977],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,22,some 22,0,none,385979,[MeasuredChoices.test882],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,21,some 21,0,none,385979,[MeasuredChoices.test869],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,20,some 20,0,none,385979,[MeasuredChoices.test856],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,3,separateIntersection⟩,
  ⟨⟨50,63,10,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,3,separateIntersection⟩]
private theorem paid4020 : StockPairs.checked rows4020 = true := by decide +kernel
theorem route4020 (i : Fin 20) : (rows4020.get i).Done :=
  StockPairs.doneAt paid4020 i

end Research6969.PairReceipts
end Z6969Source2942

-- Source: Research6969.HardFit4At110
section Z6969Source2943
set_option autoImplicit true
namespace Research6969.HardFit4At110
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes39:PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route4020 7),
    (PairReceipts.route4020 8),
    (PairReceipts.route4020 9),
    (PairReceipts.route4020 10),
    (PairReceipts.route4020 11),
    (PairReceipts.route4020 12),
    (PairReceipts.route4020 13),
    (PairReceipts.route4020 14),
    (PairReceipts.route4020 15),
    (PairReceipts.route4020 16),
    (PairReceipts.route4020 17),
    (PairReceipts.route4020 18),
    (PairReceipts.route4020 19),
    (PairReceipts.route4040 0),
    (PairReceipts.route4040 1),
    (PairReceipts.route4040 2),
    (PairReceipts.route4040 3),
    (PairReceipts.route4040 4),
    (PairReceipts.route4040 5),
    (PairReceipts.route4040 6),
    trivial⟩)
theorem case110: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,19,some 19⟩:=PairRoute.start _ allAxes39
private def leaf40 := (PairReceipts.route4020 6)
theorem case111: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,20,some 20⟩:=PairRoute.start _ leaf40
private def leaf41 := (PairReceipts.route4020 5)
theorem case112: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,21,some 21⟩:=PairRoute.start _ leaf41
private def leaf42 := (PairReceipts.route4020 4)
theorem case113: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,22,some 22⟩:=PairRoute.start _ leaf42
private def leaf43 := (PairReceipts.route4020 3)
theorem case114: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,23,some 24⟩:=PairRoute.start _ leaf43
private def leaf44 := (PairReceipts.route4020 2)
theorem case115: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,25,some 26⟩:=PairRoute.start _ leaf44
private def leaf45 := (PairReceipts.route4020 1)
theorem case116: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,27,some 28⟩:=PairRoute.start _ leaf45
private def leaf46 := (PairReceipts.route4020 0)
theorem case117: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,29,some 30⟩:=PairRoute.start _ leaf46
private def leaf47 := (PairReceipts.route4000 19)
theorem case118: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,31,some 32⟩:=PairRoute.start _ leaf47
private def leaf48 := (PairReceipts.route4000 18)
theorem case119: NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,33,some 36⟩:=PairRoute.start _ leaf48
end Research6969.HardFit4At110
end Z6969Source2943

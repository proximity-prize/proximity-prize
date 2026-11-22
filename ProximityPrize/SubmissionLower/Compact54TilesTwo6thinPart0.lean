import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thin
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .two6thin 1
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [14882180103,36493532175,65955381275,74495655983,43490689419,43491290507,34817546643,9098345873]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [13039242725,34398312963]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 7 = true := by decide +kernel
private theorem rows : checks ts 130 3 47 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 3 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two6thin 2
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [36459976715,57516440599,82749518891,1900659781,39515092287,35186908479,860733757,47651896747]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4702629289,34397755905,30086635015,21937669]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 4 = true := by decide +kernel
private theorem rows : checks ts 130 6 44 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 4 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two6thin 3
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [36392870927,53221476379,78555741231,35102752091,30740947291,5038260569,47635122607,390887853]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [34448090613,25825288703,55492093]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 1 = true := by decide +kernel
private theorem rows : checks ts 130 9 41 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 5 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .two6thin 4
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [49211715603,78420992033,27418799167,43843608879,30891674927,17453395403,4568564169,47383327211]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [30153674231,38676226565,21793285]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 6 = true := by decide +kernel
private theorem rows : checks ts 130 12 38 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 6 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two6thin 5
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [45000637463,74126026789,23107055679,39548643635,30791012659,17436684743,290375109,25942594019]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [17352797667,47282798083,22004229,34364747273]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 3 = true := by decide +kernel
private theorem rows : checks ts 130 15 35 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 7 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .two6thin 6
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [48993617947,82682935337,35220191535,30791277871,9467444527,43273046461,34683516349,21664472543]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [8779642333,55351805,4333748737]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem rows : checks ts 130 18 32 = true := (checks_join i18 (checks_join i26 (checks_join i34 (i42))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 8 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two6thin 7
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [57264788509,61359098929,26428935515,22067128667,5004706139,43575170423,26395378037,17302465003]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4434345449,17252064761,22005253,8595091977]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 5 = true := by decide +kernel
private theorem rows : checks ts 130 21 29 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 9 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .two6thin 8
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [61442449441,44330228789,39380869469,26445711711,17738605955,13292648835,8712534503,156157415]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [25808374273,4316903941,22004229,17185023499]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 2 = true := by decide +kernel
private theorem rows : checks ts 130 24 26 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 10 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .two6thin 9
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [65586424869,27284581437,35220122941,26479268157,13259091371,8897084843,21614072297,13024274921]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4384013815,89048567,21936645]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 7 = true := by decide +kernel
private theorem rows : checks ts 130 27 23 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 11 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .two6thin 10
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [69915473961,10255711297,35085973835,26429201739,5105367369,4484678099,17319173609,4434342377]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [34431859195,4316971523,5227017,5228041]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 4 = true := by decide +kernel
private theorem rows : checks ts 130 30 20 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 12 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two6thin 11
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [65620509741,1732887621,26563151181,22167789903,9282894157,139380197,17268908533,8678979063]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [89047541,5228041]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 1 = true := by decide +kernel
private theorem rows : checks ts 130 33 17 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 13 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .two6thin 12
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [57080909873,22184300895,22000019805,4937597277,13074606557,4484676061,72270329,55494137]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [21479854601,5228041]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 6 = true := by decide +kernel
private theorem rows : checks ts 130 36 14 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 14 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo6thin

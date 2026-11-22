import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .one6 1
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [23439215623,36442874895,125413312539,6212206657,44077369579,56946488555,18392460521,34548026845]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [55923471863,43021126137,21512335873]) (by decide +kernel)]
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
    Covered 2 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one6 2
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [36459649035,53271280663,91507552299,47937122663,39347593575,47601040823,357330357,34397231617]) (by decide +kernel)]
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
    Covered 3 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one6 3
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [36375766029,61559228441,70166938671,47886518641,43575048563,34901632395,34464343537,42954684937]) (by decide +kernel)]
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
    Covered 4 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one6 4
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [45033664531,82799778849,27552820287,43792883011,43793549635,17319245289,42970395141]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 6 = true := by decide +kernel
private theorem rows : checks ts 130 12 38 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 5 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one6 5
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [44916227093,78504814629,19013219391,39481141575,39481807175,43071192557,12973947381]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 3 = true := by decide +kernel
private theorem rows : checks ts 130 15 35 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 6 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one6 6
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [53137066009,78521990189,39363968339,30807991635,776783185,47718746521,43424446873,30086702599]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem rows : checks ts 130 18 32 = true := (checks_join i18 (checks_join i26 (checks_join i34 (i42))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 7 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one6 7
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [61694039069,57248485425,34918404485,17738544517,52031018389,4786522517]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 5 = true := by decide +kernel
private theorem rows : checks ts 130 21 29 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 8 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one6 8
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [65821237281,40202838073,39296590193,39297255795,21832184237,21496771077]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 2 = true := by decide +kernel
private theorem rows : checks ts 130 24 26 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 9 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one6 9
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [61694438437,31696791609,47702633885,30505999775,8896953793,30069923337]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 7 = true := by decide +kernel
private theorem rows : checks ts 130 27 23 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 10 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one6 10
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [65821636649,14667921473,39212972409,26378805625,8712535533,38693272065]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 4 = true := by decide +kernel
private theorem rows : checks ts 130 30 20 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 11 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one6 11
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [69965612077,35052225881,30656997721,25909176809,139380201,34398307841]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 1 = true := by decide +kernel
private theorem rows : checks ts 130 33 17 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 12 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one6 12
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [57214930993,34951958909,17772098941]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 6 = true := by decide +kernel
private theorem rows : checks ts 130 36 14 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 13 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one6 13
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [44447472693,30505999773,9047948701,30069923337]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 3 = true := by decide +kernel
private theorem rows : checks ts 130 39 11 = true := (checks_join i39 (i47))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 14 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne6

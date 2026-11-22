import ProximityPrize.SubmissionLower.Compact54RetainedTiltedBatch
import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne3wide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .one3wide 1
private def p0 : List P := [⟨unpack [2164329477,1023479817,4613805065,18119990285,48454578193,121084010529,6006641755,39614111977], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [52197230825,22317087977,26946182385,9698283777,30956534069,30957066549,26259851657,17653212553], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [13375224201,8878999989,30303287761,17233978877,4349151741,54186493,8627198465,8627337729], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [37406209], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem i51 : checks ts 130 51 2 = true := by decide +kernel
private theorem rows : checks ts 130 3 50 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51)))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 2 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one3wide 2
private def p0 : List P := [⟨unpack [10285029387,22599836685,56809634837,95398229033,1597231177,22416342273,35386250497,35185129733], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [39245290757,9365079301,31057126685,17636498837,17535971733,9029097889,8795112897,221958601], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [25991281101,17435235789,38809060837,8711156205,4416257517,4349150709,70962677,34430479865], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [3854848,20484613,4315523589,20628997,20630021,3854852,20631048], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 7 = true := by decide +kernel
private theorem rows : checks ts 130 6 47 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 3 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one3wide 3
private def p0 : List P := [⟨unpack [26727031821,48303587353,103870722089,39412789481,43523414249,13660046569,26912630005,31074107673], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [31074771225,21931399541,17619857781,21864087969,13090080165,4416259545,121294297,104518105], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [8744710625,4449811937,17317796325,8744709605,3854836,54183417,20630009,20631032], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [20631036,21512028673,37407232,37407236,25773090313,12888611337,3779081,4298816009], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [3850761,54183432], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 4 = true := by decide +kernel
private theorem rows : checks ts 130 9 44 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 4 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one3wide 4
private def p0 : List P := [⟨unpack [31761248273,60920057885,74024389681,35520467165,26796324061,34933739813,30571869477,13140342177], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [8828667297,289067425,43355681193,17518989745,13190604209,25991542229,138069469,104516061], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [70962653,4449744353,4416257505,3854824,3854828,20631024,21562088949,20631028], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [37407224,8644044285,4349080061,37407228,37404161,20627969,54183424,17200353797], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [54183428,3848713,70959624], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 8 = true := by decide +kernel
private theorem i52 : checks ts 130 52 1 = true := by decide +kernel
private theorem rows : checks ts 130 12 41 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 5 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one3wide 5
private def p0 : List P := [⟨unpack [44109282325,73923258405,35604639805,30940293377,30755948801,13676816641,30939757869,26695654701], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [17535973737,4701408617,17569253801,13274488233,8845372865,4516854209,4432970177,188402113], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [87739853,54186445,25991543253,3854812,3854816,104514021,70960613,20631012], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [20631016,20631020,37407216,37407220,70957561,70958585,54183416,54183420], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [30101683713,4332301825,37336577,70959616,70959620,12888610313,4298745353,70959624], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 6 = true := by decide +kernel
private theorem rows : checks ts 130 15 38 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 6 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one3wide 6
private def p0 : List P := [⟨unpack [48236480537,78269020201,14230471749,35436579081,26678881545,26544998673,30537983249,13240804741], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [13207451013,8828601737,289001865,4382705093,104517061,17418258893,13106716109,20632017], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [4449744341,154779093,154845653,3854808,4483296733,70960605,37407197,3854812], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [20631008,30219398629,20631012,37407208,37407212,54183408,54183412,54183416], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [54113789,54180349,20626941,70959612,70959616,12905455109,87735812,12888542729], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [87735816], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem i50 : checks ts 130 50 3 = true := by decide +kernel
private theorem rows : checks ts 130 18 35 = true := (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 7 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one3wide 7
private def p0 : List P := [⟨unpack [52834292765,73923725361,1395904585,30672062733,30622132493,5036886285,30822847829,22233183573], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [13224225173,8862153109,322553237,221958553,17535700385,9029853601,138070465,87739841], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [3854800,3854804,171555289,154844633,104514009,20631000,20631004,20631008], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [20628965,37407204,4432965097,137999849,37407208,54183404,54183408,70959604], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [17250618873,70959608,70959612,87735808,20625925,87735812,87735816], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 8 = true := by decide +kernel
private theorem rows : checks ts 130 21 32 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 8 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one3wide 8
private def p0 : List P := [⟨unpack [61189349409,56844590133,35235520801,26528285985,22048842025,26176239913,8878930317,8761492877], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [221893005,8945967541,8845372853,4399482297,104517049,20632005,3854796,3854800], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [171555285,121224661,121291221,70960597,37407189,20630996,21663024601,205037017], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [20631000,20631004,37407200,37407204,54183400,54183404,54183408,30152024565], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [21562360309,4382633461,87668213,20626933,70959604,70959608,87735804,20625921], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [87735808,87735812,3709449,104512008], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 5 = true := by decide +kernel
private theorem rows : checks ts 130 24 29 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 9 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one3wide 9
private def p0 : List P := [⟨unpack [56894385189,48288212025,30907002149,22233320741,21964956981,21864496437,8795045269,8728005013], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [8929191341,8828596653,138070457,104517049,54186425,171556297,154845641,104515017], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [3854792,3854796,3854800,20630996,20631000,17368059357,8778195421,37407196], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [37407200,54183396,4365857257,87669225,54183400,54183404,30169066993,70959600], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [20626933,70959604,70959608,54112765,54113789,87735804,37334529,20625921], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [87735808,87735812,104512008], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem i51 : checks ts 130 51 2 = true := by decide +kernel
private theorem rows : checks ts 130 27 26 = true := (checks_join i27 (checks_join i35 (checks_join i43 (i51))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 10 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

end Compact50PriceTableOne3wide

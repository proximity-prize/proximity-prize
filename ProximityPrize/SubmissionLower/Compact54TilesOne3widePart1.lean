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

namespace Top10
private abbrev P := PaidBatch .one3wide 10
private def p0 : List P := [⟨unpack [69712640041,22686186561,26645592345,22166148377,17854672153,13173899621,372887909,4432970157], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4399483309,4617514429,4500075965,205110717,13190534593,4600669633,20632001,70961609], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20630985,3854792,3854796,121291217,70960593,20630992,20630996,20631000], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37407196,37407200,54183396,54183400,25890879981,54183404,104445425,37337585], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37404145,70959600,70959604,70959608,37403133,87735804,87735808,87735812], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [104512008], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 7 = true := by decide +kernel
private theorem rows : checks ts 130 30 23 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 11 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one3wide 11
private def p0 : List P := [⟨unpack [61173040173,18424774721,26511508777,22048842025,13492664617,8845379949,4382706093,87740845], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8945967541,8845372853,4466522557,171557309,154846653,70961605,37408197,3854788], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [3854792,3854796,20630992,20630996,37407192,21663024605,188259805,37407196], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37407200,54183396,87669225,70958569,20627945,54183400,54183404,70959600], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4382633461,87668213,70959604,70959608,87735804,20625921,87735808,87735812], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [104512008], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 4 = true := by decide +kernel
private theorem rows : checks ts 130 33 20 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 12 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one3wide 12
private def p0 : List P := [⟨unpack [65333792817,1345572937,26393874701,30555024653,4953001229,13241003397,8862154117,305777029], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [17535766949,8979522981,138071469,87740845,3854788,171556297,154845641,104515017], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [3854792,3854796,20629969,20630992,20630996,37407192,4432966109,138000861], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37407196,37407200,54183396,54183400,54183404,70959600,20626933,70959604], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [70959608,17233908221,87735804,37335553,37336577,20625921,87735808,8610489861], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [87735812,104512008], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 8 = true := by decide +kernel
private theorem i52 : checks ts 130 52 1 = true := by decide +kernel
private theorem rows : checks ts 130 36 17 = true := (checks_join i36 (checks_join i44 (i52)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 13 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one3wide 13
private def p0 : List P := [⟨unpack [56811035701,22132727073,21998712097,4902735137,8828597665,4483301793,221956513,104517045], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [54186421,13157047745,4600737217,3854788,3854792,3854796,121291217,70960593], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20630992,20630996,37407192,188331485,138000861,121290205,37407196,37407200], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [54183396,54183400,54183404,70959600,70959604,70959608,87735804,20625921], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [87735808,12905455109,87735812,104512008], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 6 = true := by decide +kernel
private theorem rows : checks ts 130 39 14 = true := (checks_join i39 (i47))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 14 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne3wide

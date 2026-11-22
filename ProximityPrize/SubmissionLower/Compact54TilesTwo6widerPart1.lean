import ProximityPrize.SubmissionLower.Compact54RetainedTiltedBatch
import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6wider
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top5
private abbrev P := PaidBatch .two6wider 5
private def p0 : List P := [⟨unpack [39935753239,56561984551,44014476343,22152307927,30709742807,17573649719,13194801463,4638490935], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [39215840587,17607130483,9017266547,26180150651,4437160323,4386830723,58311051,24757643], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [7980432,4537752983,4453868951,192523671,7980436,58309019,24755611,24756632], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [24756636,41532832,75084199,41530791,41532836,58309032,58309036,75085232], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [75085236,91861432,108635583,58304959,91861436,91861440,108637636,108637640], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [125413836,34400779731,41312721,4319714771,125413840,125413844,12892799451,4302868955], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [4302871003,7971291,142190040], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 118 15 8 = true := by decide +kernel
private theorem i23 : checks ts 118 23 8 = true := by decide +kernel
private theorem i31 : checks ts 118 31 8 = true := by decide +kernel
private theorem i39 : checks ts 118 39 8 = true := by decide +kernel
private theorem i47 : checks ts 118 47 3 = true := by decide +kernel
private theorem rows : checks ts 118 15 35 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 7 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .two6wider 6
private def p0 : List P := [⟨unpack [44046174235,60756292651,22673862719,30692439235,26532615363,35138980131,22254284067,13429605723], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [8816013663,8732130655,8966935931,8832721275,4521045371,125418883,91865475,58312067], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [7980432,108639639,75086231,7980436,24756632,24756636,41532832,41532836], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [58309032,58309036,75083187,41529779,75085232,158900663,158967223,108636599], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [75085236,75085240,91861436,91861440,108637636,108637640,108637644,125413840], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [4319647191,24747479,125413844,125413848], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 118 18 8 = true := by decide +kernel
private theorem i26 : checks ts 118 26 8 = true := by decide +kernel
private theorem i34 : checks ts 118 34 8 = true := by decide +kernel
private theorem i42 : checks ts 118 42 8 = true := by decide +kernel
private theorem rows : checks ts 118 18 32 = true := (checks_join i18 (checks_join i26 (checks_join i34 (i42))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 8 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two6wider 7
private def p0 : List P := [⟨unpack [43962291231,52183138351,18412450879,30743298251,17976238283,35189511443,18026428691,4537824615], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [4470717799,175752551,13329010031,8933383535,4487424395,209301899,58310035,24756627], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [7980432,7980436,24756632,24756636,75085219,24754595,41532832,41532836], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [58309032,58309036,58309040,75085236,108636603,58305979,75085240,91861436], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [4386758083,108635587,91861440,91861444,108637640,108637644,108637648,125413844], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [34367493595,8597835227,4302871003,7971291,125413848], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 118 21 8 = true := by decide +kernel
private theorem i29 : checks ts 118 29 8 = true := by decide +kernel
private theorem i37 : checks ts 118 37 8 = true := by decide +kernel
private theorem i45 : checks ts 118 45 5 = true := by decide +kernel
private theorem rows : checks ts 118 21 29 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 9 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .two6wider 8
private def p0 : List P := [⟨unpack [52350902307,52520522807,22236192999,26532215015,21969278243,17540099363,4722376995,4554599803], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [4470715771,175750523,58311051,24757643,7980432,7980436,8866272667,4520976795], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [259631515,24756632,30324122015,17439424927,24756636,24756640,75085223,24754599], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [41532836,41532840,58309036,58309040,58309044,75083195,24752571,75085240], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [75085244,91861440,91861444,91861448,108637644,4319715795,108637648,108637652], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [7971291,7972315,125413848], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 118 24 8 = true := by decide +kernel
private theorem i32 : checks ts 118 32 8 = true := by decide +kernel
private theorem i40 : checks ts 118 40 8 = true := by decide +kernel
private theorem i48 : checks ts 118 48 2 = true := by decide +kernel
private theorem rows : checks ts 118 24 26 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 10 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

end Compact50PriceTableTwo6wider

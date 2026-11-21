import ProximityPrize.SubmissionLower.Compact54Packed

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

namespace Top1
private abbrev P := PaidBatch .two6thin 1
private def p0 : List P := [p54 [47513865221,47715400725,95432371237,47497940041,47498792073,47766912137],p54 [47499644105,21744520457,21744657673,47784934665,47785340169,43490712841],p54 [21728005453,21728142669,21728267661,21728404877,47769337229,47500848525],p54 [43206352269,21728464333,21728732621,21730323917,21730788813,21731319245],p54 [17436620237]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 7 = true := by decide +kernel
private theorem rows : checks ts 130 3 47 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 3 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two6thin 2
private def p0 : List P := [p54 [90734270473,91137667113,43472001165,43471946893,43473115405,43473061133],p54 [43473596685,43474132237,43474229645,43474240909,43205882253,21730794893],p54 [17436030349,21730456013,17435822541,21731450317,17302205901,8712205805],p54 [4417307117]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 4 = true := by decide +kernel
private theorem rows : checks ts 130 6 44 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 4 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two6thin 3
private def p0 : List P := [p54 [86422004749,82547734569,43471938701,39177048205,43472921869,39178096909],p54 [39178696973,39179231501,43473970573,39179211149,38910917005,17435828621],p54 [17436161421,17435556301,17436020173,17436484045,17302336973,8712336877],p54 [4417438189]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 1 = true := by decide +kernel
private theorem rows : checks ts 130 9 41 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 5 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .two6thin 4
private def p0 : List P := [p54 [78370517009,78252899373,39177761041,34883131665,39178894609,34884330769],p54 [39161835921,34867337617,38911114641,17436026257,13141260689,17418911185],p54 [17419375057,17419838929,13007370705,4400593393,4400726513]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 6 = true := by decide +kernel
private theorem rows : checks ts 130 12 38 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 6 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two6thin 5
private def p0 : List P := [p54 [74058447893,69662835757,34882665745,34883264785,34883929361,30589364497],p54 [34866740625,34867536273,34616149393,30187104657,13006776753,13007108529],p54 [17419109841,13124409809,13124807121,13007436241,4400658929,4400792049]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 3 = true := by decide +kernel
private theorem rows : checks ts 130 15 35 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 7 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .two6thin 6
private def p0 : List P := [p54 [65468123161,65367935025,30570858773,30571456789,30572120341,30572652821],p54 [30571710865,30572505489,30321052049,30187170193,13006842289,13007174065],p54 [13124012497,13124475345,13124872657,13007501777,4400658929,4350394865],p54 [4333748737]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem rows : checks ts 130 18 32 = true := checks_join i18 (checks_join i26 (checks_join i34 (i42)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 8 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two6thin 7
private def p0 : List P := [p54 [60634780701,56256794673,60636222617,56341663897,60637598997,56090857749],p54 [26008654165,26009185621,30319859089,26025424273,26026086801,25892138385],p54 [13006974385,8712142257,30303540689,26009171409,25892196817,13007302097],p54 [8712469969,12990058993,8695292401,4400393713,4400592369,4350393841],p54 [55363057,4333682177,38716929]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 5 = true := by decide +kernel
private theorem rows : checks ts 130 21 29 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 9 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .two6thin 8
private def p0 : List P := [p54 [107881783329,52046028957,52046697629,52047339801,51795825945,26008786265],p54 [21714219353,26008183189,21713616277,26009376149,21714874773,26008576465],p54 [21714140625,25892263377,8712204753,8712535505,12990125553,8695358961],p54 [8695689713,4350393841,55428593,38518273,38650369,38782465]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 2 = true := by decide +kernel
private theorem rows : checks ts 130 24 26 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 10 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .two6thin 9
private def p0 : List P := [p54 [94996491301,47734287521,43439856801,47752375577,43458075929,47484530069],p54 [21714410901,17419777429,21713677777,21714339281,21597298129,8712336849],p54 [4417438161,8695160305,8695491057,8645359089,4316840433,21742073],p54 [21874169,4333549057,38583809,38650369,38782465]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 7 = true := by decide +kernel
private theorem rows : checks ts 130 27 23 = true := checks_join i27 (checks_join i35 (i43))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 11 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .two6thin 10
private def p0 : List P := [p54 [82615826473,39145404701,39146266909,38894336405,17419313557,17419842965],p54 [17418779089,17419308497,17419903441,8712336849,4417438161,8645359089],p54 [4316905969,21742073,21874169,4333549057,38583809,38650369],p54 [38782465]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 4 = true := by decide +kernel
private theorem rows : checks ts 130 30 20 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 12 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two6thin 11
private def p0 : List P := [p54 [69713691693,34850440477,30556072221,34599372181,13124348309,13124745621],p54 [17419109841,13124409809,13124872657,12940327377,4350130657,4350329313],p54 [4400724465,4316905969,21742073,21874169,38650369,38782465]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 1 = true := by decide +kernel
private theorem rows : checks ts 130 33 17 = true := checks_join i33 (checks_join i41 (i49))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 13 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .two6thin 12
private def p0 : List P := [p54 [56828530737,56074277153,26008719709,26009382237,26009309593,25892269465],p54 [12990262713,8695496121,25875354069,12990524885,8695758293,12989993457],p54 [8695226865,4400393713,4400592369,4350393841,55428593,38518273],p54 [38650369,38782465]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 6 = true := by decide +kernel
private theorem rows : checks ts 130 36 14 = true := checks_join i36 (i44)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 14 .two6thin a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo6thin

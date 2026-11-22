import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54TilesTwo7Part0

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top8
private abbrev P := PaidBatch .two7 8
private def p0 : List P := [⟨Compact54Packed.unpack [52045701153,47668040757,52030824605,47736591517,51796992277,21731579157], by decide +kernel⟩,⟨Compact54Packed.unpack [21732175125,26009231701,21714861397,21715653973,21598481749,8696474997], by decide +kernel⟩,⟨Compact54Packed.unpack [8696805749,26009887121,21715647889,8712852881,8713249169,8713645457], by decide +kernel⟩,⟨Compact54Packed.unpack [4351506833,56541585,4351703457,56738209,8696403377,8696865201], by decide +kernel⟩,⟨Compact54Packed.unpack [4351503793,56538545,23050673,23182769,6406576,6406580], by decide +kernel⟩,⟨Compact54Packed.unpack [23116217,23182776,23182780,4334923201], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [39957953,6404545,23182784,23181764], by decide +kernel⟩,⟨Compact54Packed.unpack [6406596,39958984,26010608077,21598600653], by decide +kernel⟩,⟨Compact54Packed.unpack [8713573837,4351435213,56469965,22982093,23114189,6403532], by decide +kernel⟩,⟨Compact54Packed.unpack [39958988,39957968], by decide +kernel⟩,⟨Compact54Packed.unpack [6406608,23113173,6402517,39957972], by decide +kernel⟩,⟨Compact54Packed.unpack [6406612,73511384], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [4351697373,56666589,23178717,39956956], by decide +kernel⟩,⟨Compact54Packed.unpack [23182812,56734176], by decide +kernel⟩,⟨Compact54Packed.unpack [6406624,73510372], by decide +kernel⟩,⟨Compact54Packed.unpack [6406628,73510376], by decide +kernel⟩,⟨Compact54Packed.unpack [6406632,8696135149,8696662509,8646661613,22913517,23111149], by decide +kernel⟩,⟨Compact54Packed.unpack [6400493,73510380], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [6406636,73509360], by decide +kernel⟩,⟨Compact54Packed.unpack [23182832,23044597,23176693,23177716], by decide +kernel⟩,⟨Compact54Packed.unpack [73511412,6400504], by decide +kernel⟩,⟨Compact54Packed.unpack [90287608], by decide +kernel⟩,⟨Compact54Packed.unpack [4334720509,39755261,39952893,39953916], by decide +kernel⟩,⟨Compact54Packed.unpack [73511420,6399488], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [90286592], by decide +kernel⟩,⟨Compact54Packed.unpack [6406656,73508356], by decide +kernel⟩,⟨Compact54Packed.unpack [39959044], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 129 24 8 = true := by decide +kernel
private theorem i32 : checks ts 129 32 8 = true := by decide +kernel
private theorem i40 : checks ts 129 40 8 = true := by decide +kernel
private theorem i48 : checks ts 129 48 1 = true := by decide +kernel
private theorem rows : checks ts 129 24 25 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 10 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .two7 9
private def p0 : List P := [⟨Compact54Packed.unpack [90703162405,43440696481,43441625249,43189890329,21714868505,17420300569], by decide +kernel⟩,⟨Compact54Packed.unpack [43190807893,21715720533,17303384405,8696541557,4401708405,21714988433], by decide +kernel⟩,⟨Compact54Packed.unpack [17420551569,8712984977,8713381265,8713777553,4351638929,22920609], by decide +kernel⟩,⟨Compact54Packed.unpack [23052705,23051689,23183785,8696535473,8696997297,4351635889], by decide +kernel⟩,⟨Compact54Packed.unpack [56670641,23182769,6406576,6406580,23182776], by decide +kernel⟩,⟨Compact54Packed.unpack [23182780,39760321,39957953,6404545,6405568], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [6406592,39958980,23181768], by decide +kernel⟩,⟨Compact54Packed.unpack [6406600,21715643853,17303504333,8713705933,4351567309,56602061], by decide +kernel⟩,⟨Compact54Packed.unpack [23114189,6403533,39958988,6403536], by decide +kernel⟩,⟨Compact54Packed.unpack [39958992,6402517,23180756], by decide +kernel⟩,⟨Compact54Packed.unpack [23182804,56734168], by decide +kernel⟩,⟨Compact54Packed.unpack [6406616,4318143965,23178717,39956956], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [23182812,56734176], by decide +kernel⟩,⟨Compact54Packed.unpack [6406624,22980069,23112165,39955940], by decide +kernel⟩,⟨Compact54Packed.unpack [39959012,39955944], by decide +kernel⟩,⟨Compact54Packed.unpack [39959016,8696464877,4401631725,4351498733], by decide +kernel⟩,⟨Compact54Packed.unpack [56533485,23045613,6400493,39955948], by decide +kernel⟩,⟨Compact54Packed.unpack [39959020,39954928], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [56735216,23176693,6400500], by decide +kernel⟩,⟨Compact54Packed.unpack [90287604], by decide +kernel⟩,⟨Compact54Packed.unpack [90286584], by decide +kernel⟩,⟨Compact54Packed.unpack [6406648,4334852605,39887357,6399485,23177724], by decide +kernel⟩,⟨Compact54Packed.unpack [73511420,6399488], by decide +kernel⟩,⟨Compact54Packed.unpack [90286592], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [6406656,73508356], by decide +kernel⟩,⟨Compact54Packed.unpack [39959044], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 129 27 8 = true := by decide +kernel
private theorem i35 : checks ts 129 35 8 = true := by decide +kernel
private theorem i43 : checks ts 129 43 6 = true := by decide +kernel
private theorem rows : checks ts 129 27 22 = true := checks_join i27 (checks_join i35 (i43))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 11 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .two7 10
private def p0 : List P := [⟨Compact54Packed.unpack [77800962089,39145666721,34851430561,39147501849,34600755481,17420755285], by decide +kernel⟩,⟨Compact54Packed.unpack [13126120789,17420089745,17420815761,8713249169,4418416017,4351374737], by decide +kernel⟩,⟨Compact54Packed.unpack [4351638929,4351571361,4318150049,23051689,23183785,8696799665], by decide +kernel⟩,⟨Compact54Packed.unpack [4401966513,4318148017,23182769,6406576,6406580,22984121], by decide +kernel⟩,⟨Compact54Packed.unpack [23116217,6405561,6406584,23182780,39892417], by decide +kernel⟩,⟨Compact54Packed.unpack [6404545,23182784,39958980], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [39958984,17420745165,8713178573,4418410957], by decide +kernel⟩,⟨Compact54Packed.unpack [8646664653,22916557,23114189,6403533,23181772], by decide +kernel⟩,⟨Compact54Packed.unpack [6406604,56735184,23047637], by decide +kernel⟩,⟨Compact54Packed.unpack [23179733,56735188,6403544], by decide +kernel⟩,⟨Compact54Packed.unpack [39959000,4351566301,56666589,23113181], by decide +kernel⟩,⟨Compact54Packed.unpack [73511388,6402528], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [56735200,6401509,6402532], by decide +kernel⟩,⟨Compact54Packed.unpack [56735204,23178728], by decide +kernel⟩,⟨Compact54Packed.unpack [56735208,8696729069,4401961453], by decide +kernel⟩,⟨Compact54Packed.unpack [4318142957,23177709,56733164], by decide +kernel⟩,⟨Compact54Packed.unpack [23182828,56733168], by decide +kernel⟩,⟨Compact54Packed.unpack [23182832,22979061,23111157,23177716], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [73511412,6400504], by decide +kernel⟩,⟨Compact54Packed.unpack [90287608], by decide +kernel⟩,⟨Compact54Packed.unpack [39887357,6399485,56732156], by decide +kernel⟩,⟨Compact54Packed.unpack [39959036,39953920], by decide +kernel⟩,⟨Compact54Packed.unpack [73511424,6399492], by decide +kernel⟩,⟨Compact54Packed.unpack [90286596], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [6406660], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 129 30 8 = true := by decide +kernel
private theorem i38 : checks ts 129 38 8 = true := by decide +kernel
private theorem i46 : checks ts 129 46 3 = true := by decide +kernel
private theorem rows : checks ts 129 30 19 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 12 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two7 11
private def p0 : List P := [⟨Compact54Packed.unpack [64915604525,30555604133,30556398757,30557308189,30305723677,13125657945], by decide +kernel⟩,⟨Compact54Packed.unpack [13126186329,13125256597,13125850517,13008676245,4351374741,4351638933], by decide +kernel⟩,⟨Compact54Packed.unpack [4351571365,22986149,23118245,23051693,6406573,6406576], by decide +kernel⟩,⟨Compact54Packed.unpack [4401702325,4402032053,4318148021,23182773,6406580,6406584], by decide +kernel⟩,⟨Compact54Packed.unpack [22984125,23181757,23182780,23182784], by decide +kernel⟩,⟨Compact54Packed.unpack [39957957,6404549,23182788,23181768], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [6406600,39958988,13109134801,4401436113], by decide +kernel⟩,⟨Compact54Packed.unpack [4401700305,4402030033,22982097,23114193,23180752], by decide +kernel⟩,⟨Compact54Packed.unpack [23182800,56735188], by decide +kernel⟩,⟨Compact54Packed.unpack [23047641,6402521,56735192], by decide +kernel⟩,⟨Compact54Packed.unpack [73511388,39955937], by decide +kernel⟩,⟨Compact54Packed.unpack [73511392,6402532], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [56735204,23179752], by decide +kernel⟩,⟨Compact54Packed.unpack [39959016,4401698285,4351565293,22980077], by decide +kernel⟩,⟨Compact54Packed.unpack [23112173,73510380], by decide +kernel⟩,⟨Compact54Packed.unpack [6406636,73510384], by decide +kernel⟩,⟨Compact54Packed.unpack [6406640,23045621,6400501,39955956], by decide +kernel⟩,⟨Compact54Packed.unpack [39959028,39954936], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [56735224,39624189,39821821], by decide +kernel⟩,⟨Compact54Packed.unpack [23176701,73509372], by decide +kernel⟩,⟨Compact54Packed.unpack [23182844,56732160], by decide +kernel⟩,⟨Compact54Packed.unpack [39959040,39953924], by decide +kernel⟩,⟨Compact54Packed.unpack [73511428], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 129 33 8 = true := by decide +kernel
private theorem i41 : checks ts 129 41 8 = true := by decide +kernel
private theorem rows : checks ts 129 33 16 = true := checks_join i33 (i41)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 13 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .two7 12
private def p0 : List P := [⟨Compact54Packed.unpack [52518490161,26009899293,21715463453,26010751321,21598547289,8696409465], by decide +kernel⟩,⟨Compact54Packed.unpack [8696871289,13007884693,8713183637,8713645461,4351506837,56541589], by decide +kernel⟩,⟨Compact54Packed.unpack [4351703461,56738213,12991435189,8696799669,4351503797,56538549], by decide +kernel⟩,⟨Compact54Packed.unpack [23050677,23182773,6406580,6406584,23116221,6405564], by decide +kernel⟩,⟨Compact54Packed.unpack [6406588,23182784,4334857669,39892421,6404549], by decide +kernel⟩,⟨Compact54Packed.unpack [23182788,39958984,6404556], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [23182796,12991828433,8646664657,22916561,23048657], by decide +kernel⟩,⟨Compact54Packed.unpack [6403537,39958992,23180756], by decide +kernel⟩,⟨Compact54Packed.unpack [23182804,23047641,23179737,23180760], by decide +kernel⟩,⟨Compact54Packed.unpack [23182808,56735196], by decide +kernel⟩,⟨Compact54Packed.unpack [4334723553,39758305,39955937,39956960], by decide +kernel⟩,⟨Compact54Packed.unpack [23182816,56734180], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [6406628,73511400], by decide +kernel⟩,⟨Compact54Packed.unpack [4401500653,4401830381,4351697389,56732141,23178732], by decide +kernel⟩,⟨Compact54Packed.unpack [56735212,23178736], by decide +kernel⟩,⟨Compact54Packed.unpack [56735216,23178740], by decide +kernel⟩,⟨Compact54Packed.unpack [56735220,23178744], by decide +kernel⟩,⟨Compact54Packed.unpack [56735224,39756285,39953917], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [90286588], by decide +kernel⟩,⟨Compact54Packed.unpack [6406652,73509376], by decide +kernel⟩,⟨Compact54Packed.unpack [23182848,56732164], by decide +kernel⟩,⟨Compact54Packed.unpack [39959044], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 129 36 8 = true := by decide +kernel
private theorem i44 : checks ts 129 44 5 = true := by decide +kernel
private theorem rows : checks ts 129 36 13 = true := checks_join i36 (i44)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 14 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo7

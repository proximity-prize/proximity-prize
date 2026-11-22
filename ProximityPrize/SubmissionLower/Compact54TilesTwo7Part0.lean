/- Modified from public PR657. Expanded the packed receipt notation. -/
import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top1
private abbrev P := PaidBatch .two7 1
private def p0 : List P := [⟨Compact54Packed.unpack [47784135685,43420892181,95434532901,47500233865,43472993417,21728070857], by decide +kernel⟩,⟨Compact54Packed.unpack [21728208073,21728464137,21728666889,43474697481,47770724617,43206547721], by decide +kernel⟩,⟨Compact54Packed.unpack [21728857417,21729060169,21731842377,17437143369,21729250697,21729518985], by decide +kernel⟩,⟨Compact54Packed.unpack [43207179657,21731568009,21732229513,21598149001,17303515529,8712985001], by decide +kernel⟩,⟨Compact54Packed.unpack [8713315753,8713646505,4418747817,21729643977,21729977801,21730770377], by decide +kernel⟩,⟨Compact54Packed.unpack [17436267977,21732354505,21598470601,8713443785,8713774537,4351570377], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [56539593,22986185,23052745,23117265,23183825,4318081497], by decide +kernel⟩,⟨Compact54Packed.unpack [23116249,6405593,6406616,23182812,22983137], by decide +kernel⟩,⟨Compact54Packed.unpack [23115233,6404577,23182816,23181796], by decide +kernel⟩,⟨Compact54Packed.unpack [6406628,8713044457,8713440745,8646531561,4351698409,56667625], by decide +kernel⟩,⟨Compact54Packed.unpack [23114217,6403561,39959016,6403564], by decide +kernel⟩,⟨Compact54Packed.unpack [39959020,6402545,23180784], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [23182832,56734196], by decide +kernel⟩,⟨Compact54Packed.unpack [6406644,4351498745,56533497,22980089,23112185,6401529], by decide +kernel⟩,⟨Compact54Packed.unpack [73511416,6401532], by decide +kernel⟩,⟨Compact54Packed.unpack [73511420,23111169], by decide +kernel⟩,⟨Compact54Packed.unpack [6400513,73510400], by decide +kernel⟩,⟨Compact54Packed.unpack [6406656,73509380], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [23182852], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 129 3 8 = true := by decide +kernel
private theorem i11 : checks ts 129 11 8 = true := by decide +kernel
private theorem i19 : checks ts 129 19 8 = true := by decide +kernel
private theorem i27 : checks ts 129 27 8 = true := by decide +kernel
private theorem i35 : checks ts 129 35 8 = true := by decide +kernel
private theorem i43 : checks ts 129 43 6 = true := by decide +kernel
private theorem rows : checks ts 129 3 46 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 3 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two7 2
private def p0 : List P := [⟨Compact54Packed.unpack [90719197193,86827823145,43473246345,43473192073,43475015945,43474961673], by decide +kernel⟩,⟨Compact54Packed.unpack [43475759369,38911712521,17436941641,17437339977,21729253769,17434489225], by decide +kernel⟩,⟨Compact54Packed.unpack [43207443849,21731897737,17437329801,17437924745,17303712137,8713777577], by decide +kernel⟩,⟨Compact54Packed.unpack [4351507881,4318084537,23051713,23118273,21729647049,17434948041], by decide +kernel⟩,⟨Compact54Packed.unpack [21731100105,17436663241,21732749769,17303570889,8713706953,4418808265], by decide +kernel⟩,⟨Compact54Packed.unpack [4351701449,56736201,23117257,6406601,6406604,6405585], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [6406608,23182804,23048665,23180761,6404568], by decide +kernel⟩,⟨Compact54Packed.unpack [23182808,39959004,23179745], by decide +kernel⟩,⟨Compact54Packed.unpack [56735200,23180772], by decide +kernel⟩,⟨Compact54Packed.unpack [23182820,8713439721,4418606569,4351565289,56534505], by decide +kernel⟩,⟨Compact54Packed.unpack [22981097,23113193,6402537,39957992], by decide +kernel⟩,⟨Compact54Packed.unpack [6406632,73511404], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [23112177,6401521,56734192], by decide +kernel⟩,⟨Compact54Packed.unpack [6406640,73510388], by decide +kernel⟩,⟨Compact54Packed.unpack [6406644,4318076409,56731129,6400505,23178744], by decide +kernel⟩,⟨Compact54Packed.unpack [56735224,23177724], by decide +kernel⟩,⟨Compact54Packed.unpack [73511420,22912513], by decide +kernel⟩,⟨Compact54Packed.unpack [23044609,73509376], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [23182848,56732164], by decide +kernel⟩,⟨Compact54Packed.unpack [39959044], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 129 6 8 = true := by decide +kernel
private theorem i14 : checks ts 129 14 8 = true := by decide +kernel
private theorem i22 : checks ts 129 22 8 = true := by decide +kernel
private theorem i30 : checks ts 129 30 8 = true := by decide +kernel
private theorem i38 : checks ts 129 38 8 = true := by decide +kernel
private theorem i46 : checks ts 129 46 3 = true := by decide +kernel
private theorem rows : checks ts 129 6 43 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 4 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two7 3
private def p0 : List P := [⟨Compact54Packed.unpack [82128217101,82549896233,39177757837,39178226829,39179199757,39179865357], by decide +kernel⟩,⟨Compact54Packed.unpack [39180793101,38912040205,17437138253,17437602125,39163864461,38912281997], by decide +kernel⟩,⟨Compact54Packed.unpack [17436865933,17437526413,17303379341,8713515405,4418616717,8713379245], by decide +kernel⟩,⟨Compact54Packed.unpack [4418480557,8646603181,4318084525,22986165,23118261,4351635901], by decide +kernel⟩,⟨Compact54Packed.unpack [56670653,23117245,23183805,6405573,6406596,6405576], by decide +kernel⟩,⟨Compact54Packed.unpack [6406600,17419226573,17420018125,17420809677,8713177549,4418278861], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [8646532557,4351633869,22983117,23115213,6404557,6405580], by decide +kernel⟩,⟨Compact54Packed.unpack [6406604,39958992,23114197,6403541], by decide +kernel⟩,⟨Compact54Packed.unpack [39958996,39957976], by decide +kernel⟩,⟨Compact54Packed.unpack [6406616,4351434205,56468957,22915549,23047645,23179741], by decide +kernel⟩,⟨Compact54Packed.unpack [56735196,23180768], by decide +kernel⟩,⟨Compact54Packed.unpack [23182816,23046629,23178725,23179748], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [39959012,39956968], by decide +kernel⟩,⟨Compact54Packed.unpack [23182824,8696728045,4401894893,4351696365,56665581], by decide +kernel⟩,⟨Compact54Packed.unpack [23177709,73510380], by decide +kernel⟩,⟨Compact54Packed.unpack [6406636,73510384], by decide +kernel⟩,⟨Compact54Packed.unpack [6406640,73509364], by decide +kernel⟩,⟨Compact54Packed.unpack [23182836,56732152], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [39959032,39755261,39887357,6399485], by decide +kernel⟩,⟨Compact54Packed.unpack [90286588], by decide +kernel⟩,⟨Compact54Packed.unpack [6406652,73508352], by decide +kernel⟩,⟨Compact54Packed.unpack [39959040,39953924], by decide +kernel⟩,⟨Compact54Packed.unpack [73511428], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 129 9 8 = true := by decide +kernel
private theorem i17 : checks ts 129 17 8 = true := by decide +kernel
private theorem i25 : checks ts 129 25 8 = true := by decide +kernel
private theorem i33 : checks ts 129 33 8 = true := by decide +kernel
private theorem i41 : checks ts 129 41 8 = true := by decide +kernel
private theorem rows : checks ts 129 9 40 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 5 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .two7 4
private def p0 : List P := [⟨Compact54Packed.unpack [77832925201,73942989869,39161114769,34866485393,39179333901,34884901133], by decide +kernel⟩,⟨Compact54Packed.unpack [34885827853,34617073933,17437335885,13142635853,39163998605,34617252237], by decide +kernel⟩,⟨Compact54Packed.unpack [17437130125,13142561165,17303576973,12941571469,4351374749,4351573405], by decide +kernel⟩,⟨Compact54Packed.unpack [8713576877,4418743725,4351636909,4318150061,23051701,23183797], by decide +kernel⟩,⟨Compact54Packed.unpack [22984125,23050685,23182781,6406588,6406592,23049669], by decide +kernel⟩,⟨Compact54Packed.unpack [23181765,23182788,23182792,17419688397], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [13125184973,17303371213,12941431245,4351435213,56469965,4318145997], by decide +kernel⟩,⟨Compact54Packed.unpack [23180749,39958988,23181776], by decide +kernel⟩,⟨Compact54Packed.unpack [6406608,23047637,23179733,39957972], by decide +kernel⟩,⟨Compact54Packed.unpack [6406612,56735192,4351103453], by decide +kernel⟩,⟨Compact54Packed.unpack [4351367645,4351631837,56666589,23113181,23179740], by decide +kernel⟩,⟨Compact54Packed.unpack [39959004,39956960], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [23182816,6401509,39956964], by decide +kernel⟩,⟨Compact54Packed.unpack [23182820,56733160], by decide +kernel⟩,⟨Compact54Packed.unpack [23182824,8696266221,4401433069,4401762797,4402026989], by decide +kernel⟩,⟨Compact54Packed.unpack [22913517,23045613,6400493,39955948], by decide +kernel⟩,⟨Compact54Packed.unpack [39959020,39954928], by decide +kernel⟩,⟨Compact54Packed.unpack [56735216,23044597,23176693], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [90286580], by decide +kernel⟩,⟨Compact54Packed.unpack [6406644,73509368], by decide +kernel⟩,⟨Compact54Packed.unpack [23182840,39952893,39953916], by decide +kernel⟩,⟨Compact54Packed.unpack [73511420,6399488], by decide +kernel⟩,⟨Compact54Packed.unpack [90286592], by decide +kernel⟩,⟨Compact54Packed.unpack [6406656,73508356], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [39959044], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 129 12 8 = true := by decide +kernel
private theorem i20 : checks ts 129 20 8 = true := by decide +kernel
private theorem i28 : checks ts 129 28 8 = true := by decide +kernel
private theorem i36 : checks ts 129 36 8 = true := by decide +kernel
private theorem i44 : checks ts 129 44 5 = true := by decide +kernel
private theorem rows : checks ts 129 12 37 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 6 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two7 5
private def p0 : List P := [⟨Compact54Packed.unpack [69765184533,69664931885,34867330321,30573027601,34869182737,30322173201], by decide +kernel⟩,⟨Compact54Packed.unpack [13125526865,13125924177,34868706701,30322155917,17437327757,13142693261], by decide +kernel⟩,⟨Compact54Packed.unpack [13008545165,12941637005,4351440285,4351704477,4351174061,4351438253], by decide +kernel⟩,⟨Compact54Packed.unpack [4351702445,23051693,23118253,23117237,6406581,6406584], by decide +kernel⟩,⟨Compact54Packed.unpack [4351370685,4351634877,22984125,23116221,6405565,6406588], by decide +kernel⟩,⟨Compact54Packed.unpack [23182784,23115205,6404549,23182788], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [39958984,13124657613,13125317069,17303503309], by decide +kernel⟩,⟨Compact54Packed.unpack [4351038925,4351303117,4351632845,22982093,23114189,6403533], by decide +kernel⟩,⟨Compact54Packed.unpack [39958988,39957968], by decide +kernel⟩,⟨Compact54Packed.unpack [6406608,23047637,6402517,39957972], by decide +kernel⟩,⟨Compact54Packed.unpack [6406612,73511384], by decide +kernel⟩,⟨Compact54Packed.unpack [4351235549,4351565277,4318143965,23178717,23179740], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [39959004,39956960], by decide +kernel⟩,⟨Compact54Packed.unpack [23182816,22980069,23177701,23178724], by decide +kernel⟩,⟨Compact54Packed.unpack [56735204,23178728], by decide +kernel⟩,⟨Compact54Packed.unpack [56735208,8696398317,4401630701], by decide +kernel⟩,⟨Compact54Packed.unpack [4401894893,4318076397,23111149,6400493,23178732], by decide +kernel⟩,⟨Compact54Packed.unpack [56735212,23177712], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [73511408,22912501], by decide +kernel⟩,⟨Compact54Packed.unpack [23044597,23176693,56732148], by decide +kernel⟩,⟨Compact54Packed.unpack [39959028,39954936], by decide +kernel⟩,⟨Compact54Packed.unpack [56735224,39820797,23175677], by decide +kernel⟩,⟨Compact54Packed.unpack [90285564], by decide +kernel⟩,⟨Compact54Packed.unpack [23182844,56731136], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [56735232,23175684], by decide +kernel⟩,⟨Compact54Packed.unpack [90286596], by decide +kernel⟩,⟨Compact54Packed.unpack [6406660], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 129 15 8 = true := by decide +kernel
private theorem i23 : checks ts 129 23 8 = true := by decide +kernel
private theorem i31 : checks ts 129 31 8 = true := by decide +kernel
private theorem i39 : checks ts 129 39 8 = true := by decide +kernel
private theorem i47 : checks ts 129 47 2 = true := by decide +kernel
private theorem rows : checks ts 129 15 34 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 7 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .two7 6
private def p0 : List P := [⟨Compact54Packed.unpack [64930727961,60536293425,64933021845,60638529685,30572300561,30573226257], by decide +kernel⟩,⟨Compact54Packed.unpack [30321576209,26027141393,30305716561,25893448017,12991441265,8696674673], by decide +kernel⟩,⟨Compact54Packed.unpack [30573611405,30322420109,13007686029,13008214413,13008742797,8646605197], by decide +kernel⟩,⟨Compact54Packed.unpack [4351637917,56607133,13008079277,13008673197,4351371693,4351570349], by decide +kernel⟩,⟨Compact54Packed.unpack [22985133,23051693,23183789,23050677,23182773,6406580], by decide +kernel⟩,⟨Compact54Packed.unpack [6406584,4351568317,4318147005,23181757,23182780], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [23182784,23048645,23180741,23181764], by decide +kernel⟩,⟨Compact54Packed.unpack [6406596,39958984,13124921805,13125646797], by decide +kernel⟩,⟨Compact54Packed.unpack [13008472525,4351171021,4351500749,4318079437,23114189,6403532], by decide +kernel⟩,⟨Compact54Packed.unpack [39958988,39957968], by decide +kernel⟩,⟨Compact54Packed.unpack [6406608,22981077,23113173,6402517,23180756], by decide +kernel⟩,⟨Compact54Packed.unpack [23182804,56734168], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [6406616,4351367645,4351697373,23046621,23178717,6402524], by decide +kernel⟩,⟨Compact54Packed.unpack [56735196,23179744], by decide +kernel⟩,⟨Compact54Packed.unpack [39959008,23177701,23178724], by decide +kernel⟩,⟨Compact54Packed.unpack [56735204,23178728], by decide +kernel⟩,⟨Compact54Packed.unpack [56735208,4401433069,4401762797], by decide +kernel⟩,⟨Compact54Packed.unpack [4351564269,22979053,23111149,39954924], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [56735212,23177712], by decide +kernel⟩,⟨Compact54Packed.unpack [73511408,23044597], by decide +kernel⟩,⟨Compact54Packed.unpack [6399477,73509364], by decide +kernel⟩,⟨Compact54Packed.unpack [23182836,56731128], by decide +kernel⟩,⟨Compact54Packed.unpack [56735224,39688701,39820797], by decide +kernel⟩,⟨Compact54Packed.unpack [23175677,73508348], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [39959036,39953920], by decide +kernel⟩,⟨Compact54Packed.unpack [73511424,6398468], by decide +kernel⟩,⟨Compact54Packed.unpack [90285572], by decide +kernel⟩,⟨Compact54Packed.unpack [23182852], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 129 18 8 = true := by decide +kernel
private theorem i26 : checks ts 129 26 8 = true := by decide +kernel
private theorem i34 : checks ts 129 34 8 = true := by decide +kernel
private theorem i42 : checks ts 129 42 7 = true := by decide +kernel
private theorem rows : checks ts 129 18 31 = true := checks_join i18 (checks_join i26 (checks_join i34 (i42)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 8 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two7 7
private def p0 : List P := [⟨Compact54Packed.unpack [56340665373,56258104369,56342697113,56343563417,56092087573,26026544405], by decide +kernel⟩,⟨Compact54Packed.unpack [26027272469,26008900949,26009825621,26010684757,25893579093,12991572341], by decide +kernel⟩,⟨Compact54Packed.unpack [8696805749,26009556369,26010546577,13007883665,8713117073,12941437329], by decide +kernel⟩,⟨Compact54Packed.unpack [4351506833,56476049,4351175073,4351439265,4351703457,56738209], by decide +kernel⟩,⟨Compact54Packed.unpack [12991434161,8696733105,4401899953,4351701425,23050673,23182769], by decide +kernel⟩,⟨Compact54Packed.unpack [6406576,6406580,23116217,23182776,6405564], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [6406588,39825857,39957953,6404545,23182784], by decide +kernel⟩,⟨Compact54Packed.unpack [39958980,39958984], by decide +kernel⟩,⟨Compact54Packed.unpack [26010146253,25893499341,13008604621,8646598093,4318144973,23114189], by decide +kernel⟩,⟨Compact54Packed.unpack [56735180,23180752], by decide +kernel⟩,⟨Compact54Packed.unpack [23182800,22981077,23113173,6402517,6403540], by decide +kernel⟩,⟨Compact54Packed.unpack [39958996,39956952], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [23182808,4351565277,56534493,23046621,23178717], by decide +kernel⟩,⟨Compact54Packed.unpack [73511388,6402528], by decide +kernel⟩,⟨Compact54Packed.unpack [56735200,23177701,6401508], by decide +kernel⟩,⟨Compact54Packed.unpack [73511396,6401512], by decide +kernel⟩,⟨Compact54Packed.unpack [73511400,12991033837], by decide +kernel⟩,⟨Compact54Packed.unpack [8696398317,4401565165,4401894893,4318076397,56731117,6400493], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [90287596], by decide +kernel⟩,⟨Compact54Packed.unpack [90286576], by decide +kernel⟩,⟨Compact54Packed.unpack [6406640,22912501,23044597,39954932], by decide +kernel⟩,⟨Compact54Packed.unpack [56735220,23177720], by decide +kernel⟩,⟨Compact54Packed.unpack [73511416,39820797], by decide +kernel⟩,⟨Compact54Packed.unpack [39952893,73508348], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [39959036,39953920], by decide +kernel⟩,⟨Compact54Packed.unpack [73511424,6399492], by decide +kernel⟩,⟨Compact54Packed.unpack [90286596], by decide +kernel⟩,⟨Compact54Packed.unpack [6406660], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 129 21 8 = true := by decide +kernel
private theorem i29 : checks ts 129 29 8 = true := by decide +kernel
private theorem i37 : checks ts 129 37 8 = true := by decide +kernel
private theorem i45 : checks ts 129 45 4 = true := by decide +kernel
private theorem rows : checks ts 129 21 28 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 9 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

end Compact50PriceTableTwo7

import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54TilesTwo7widePart9

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7wide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top11
private abbrev P := PaidBatch .two7wide 11
private def p0 : List P := [⟨Compact54Packed.unpack [30539088941,30490534969,30541841569,30306641057,13110191325,12992689373], by decide +kernel⟩,⟨Compact54Packed.unpack [4402754809,4403150073,13126763797,13009523989,12942812437,4352816405], by decide +kernel⟩,⟨Compact54Packed.unpack [24165653,24297749,24296733,7651613,7651616,4352484645], by decide +kernel⟩,⟨Compact54Packed.unpack [4352879909,24163621,24361253,7650597,7651620,7650600], by decide +kernel⟩,⟨Compact54Packed.unpack [7651624,24360237,7649581,24427820,7649584], by decide +kernel⟩,⟨Compact54Packed.unpack [24427824,4402615605,4403010869,4352812341,24161589], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [24359221,7648565,41204020,7648568], by decide +kernel⟩,⟨Compact54Packed.unpack [41204024,24292669,7647549,7648572], by decide +kernel⟩,⟨Compact54Packed.unpack [41204028,41201984], by decide +kernel⟩,⟨Compact54Packed.unpack [24427840,40936773,41134405,7646533,7647556], by decide +kernel⟩,⟨Compact54Packed.unpack [57980228,24423752], by decide +kernel⟩,⟨Compact54Packed.unpack [57980232,24423756], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [57980236,12993135953,4403139921], by decide +kernel⟩,⟨Compact54Packed.unpack [4319321425,24356177,57977168], by decide +kernel⟩,⟨Compact54Packed.unpack [41204048,41199956], by decide +kernel⟩,⟨Compact54Packed.unpack [57980244,24091993,24289625], by decide +kernel⟩,⟨Compact54Packed.unpack [7644505,74754392], by decide +kernel⟩,⟨Compact54Packed.unpack [24427864,57976156], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [57980252,41131361,7577953], by decide +kernel⟩,⟨Compact54Packed.unpack [91530592], by decide +kernel⟩,⟨Compact54Packed.unpack [24427872,7577956,41198948], by decide +kernel⟩,⟨Compact54Packed.unpack [74756452,7577960], by decide +kernel⟩,⟨Compact54Packed.unpack [91530600], by decide +kernel⟩,⟨Compact54Packed.unpack [24427880,4402808173,4352675181,24024429,24287597], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [24354156,57976172], by decide +kernel⟩,⟨Compact54Packed.unpack [57980268,24354160], by decide +kernel⟩,⟨Compact54Packed.unpack [91530608], by decide +kernel⟩,⟨Compact54Packed.unpack [24427888,24221045,7575925,7576948,7643508], by decide +kernel⟩,⟨Compact54Packed.unpack [91530612], by decide +kernel⟩,⟨Compact54Packed.unpack [24427892,24353144,24420728], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [91531640], by decide +kernel⟩,⟨Compact54Packed.unpack [7651704,40734077,40997245,24352125,24353148], by decide +kernel⟩,⟨Compact54Packed.unpack [91529596], by decide +kernel⟩,⟨Compact54Packed.unpack [41204092,24353152,7643520], by decide +kernel⟩,⟨Compact54Packed.unpack [91530624], by decide +kernel⟩,⟨Compact54Packed.unpack [24427904,41129348,7643524], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [91530628], by decide +kernel⟩,⟨Compact54Packed.unpack [24427908,4352738697,24087945,24351113,7574920], by decide +kernel⟩,⟨Compact54Packed.unpack [24353160,57975176], by decide +kernel⟩,⟨Compact54Packed.unpack [74756488,7574924], by decide +kernel⟩,⟨Compact54Packed.unpack [24353164,57975180], by decide +kernel⟩,⟨Compact54Packed.unpack [74756492,24219025], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [57905552,24420752], by decide +kernel⟩,⟨Compact54Packed.unpack [91531664], by decide +kernel⟩,⟨Compact54Packed.unpack [7651728,57905556,7643540], by decide +kernel⟩,⟨Compact54Packed.unpack [91530644], by decide +kernel⟩,⟨Compact54Packed.unpack [24427924,40732057,40995225,7507353,7573912], by decide +kernel⟩,⟨Compact54Packed.unpack [41129368,41197976], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [91532696], by decide +kernel⟩,⟨Compact54Packed.unpack [74681756,7643548], by decide +kernel⟩,⟨Compact54Packed.unpack [91530652], by decide +kernel⟩,⟨Compact54Packed.unpack [24427932,57904544], by decide +kernel⟩,⟨Compact54Packed.unpack [7576992,74752416], by decide +kernel⟩,⟨Compact54Packed.unpack [57980320,24085925,24349093], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [74681764,7643556], by decide +kernel⟩,⟨Compact54Packed.unpack [91530660], by decide +kernel⟩,⟨Compact54Packed.unpack [24427940,57904552], by decide +kernel⟩,⟨Compact54Packed.unpack [91528616], by decide +kernel⟩,⟨Compact54Packed.unpack [57980328,24217005,7571884], by decide +kernel⟩,⟨Compact54Packed.unpack [57904556,24419756], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [91530668], by decide +kernel⟩,⟨Compact54Packed.unpack [24427948,57903536], by decide +kernel⟩,⟨Compact54Packed.unpack [7575984,74751408], by decide +kernel⟩,⟨Compact54Packed.unpack [74756528,24348085], by decide +kernel⟩,⟨Compact54Packed.unpack [74680756,7642548], by decide +kernel⟩,⟨Compact54Packed.unpack [91529652], by decide +kernel⟩]
private def p11 : List P := [⟨Compact54Packed.unpack [41204148,41126328], by decide +kernel⟩,⟨Compact54Packed.unpack [24352184,57974200], by decide +kernel⟩,⟨Compact54Packed.unpack [91532728], by decide +kernel⟩,⟨Compact54Packed.unpack [91456956], by decide +kernel⟩,⟨Compact54Packed.unpack [91528636], by decide +kernel⟩,⟨Compact54Packed.unpack [57980348,24348096], by decide +kernel⟩]
private def p12 : List P := [⟨Compact54Packed.unpack [57904576,24419776], by decide +kernel⟩,⟨Compact54Packed.unpack [91530688], by decide +kernel⟩,⟨Compact54Packed.unpack [24427968,57902532], by decide +kernel⟩,⟨Compact54Packed.unpack [24352196,57974212], by decide +kernel⟩,⟨Compact54Packed.unpack [91532740], by decide +kernel⟩,⟨Compact54Packed.unpack [91456968], by decide +kernel⟩]
private def p13 : List P := [⟨Compact54Packed.unpack [91528648], by decide +kernel⟩,⟨Compact54Packed.unpack [57980360,24348108], by decide +kernel⟩,⟨Compact54Packed.unpack [57904588,24419788], by decide +kernel⟩,⟨Compact54Packed.unpack [91530700], by decide +kernel⟩,⟨Compact54Packed.unpack [24427980,57902544], by decide +kernel⟩,⟨Compact54Packed.unpack [24352208,57974224], by decide +kernel⟩]
private def p14 : List P := [⟨Compact54Packed.unpack [91532752], by decide +kernel⟩,⟨Compact54Packed.unpack [91456980], by decide +kernel⟩,⟨Compact54Packed.unpack [91528660], by decide +kernel⟩,⟨Compact54Packed.unpack [57980372,24348120], by decide +kernel⟩,⟨Compact54Packed.unpack [41127384,41195992], by decide +kernel⟩,⟨Compact54Packed.unpack [91530712], by decide +kernel⟩]
private def p15 : List P := [⟨Compact54Packed.unpack [24427992,57902556], by decide +kernel⟩,⟨Compact54Packed.unpack [7575004,74750428], by decide +kernel⟩,⟨Compact54Packed.unpack [91532764], by decide +kernel⟩,⟨Compact54Packed.unpack [74679776,7641568], by decide +kernel⟩,⟨Compact54Packed.unpack [91528672], by decide +kernel⟩,⟨Compact54Packed.unpack [57980384,24348132], by decide +kernel⟩]
private def p16 : List P := [⟨Compact54Packed.unpack [41127396,41196004], by decide +kernel⟩,⟨Compact54Packed.unpack [91530724], by decide +kernel⟩,⟨Compact54Packed.unpack [24428004,57902568], by decide +kernel⟩,⟨Compact54Packed.unpack [7575016,74750440], by decide +kernel⟩,⟨Compact54Packed.unpack [91532776], by decide +kernel⟩,⟨Compact54Packed.unpack [74679788,7641580], by decide +kernel⟩]
private def p17 : List P := [⟨Compact54Packed.unpack [91528684], by decide +kernel⟩,⟨Compact54Packed.unpack [57980396,24348144], by decide +kernel⟩,⟨Compact54Packed.unpack [41127408,41196016], by decide +kernel⟩,⟨Compact54Packed.unpack [91530736], by decide +kernel⟩,⟨Compact54Packed.unpack [24428016,57902580], by decide +kernel⟩,⟨Compact54Packed.unpack [7575028,74750452], by decide +kernel⟩]
private def p18 : List P := [⟨Compact54Packed.unpack [91532788], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10 ++ p11 ++ p12 ++ p13 ++ p14 ++ p15 ++ p16 ++ p17 ++ p18
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 125 33 8 = true := by decide +kernel
private theorem i41 : checks ts 125 41 8 = true := by decide +kernel
private theorem rows : checks ts 125 33 16 = true := checks_join i33 (i41)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 13 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

end Compact50PriceTableTwo7wide

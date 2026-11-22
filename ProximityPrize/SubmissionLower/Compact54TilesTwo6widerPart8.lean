/- Modified from public PR657. Expanded the packed receipt notation. -/
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

namespace Top9
private abbrev P := PaidBatch .two6wider 9
private def p0 : List P := [⟨Compact54Packed.unpack [47702633509,43342797877,47469063317,43175156885,21681564877,21682488525], by decide +kernel⟩,⟨Compact54Packed.unpack [21683412173,17389040845,21699456257,21700576513,8697519361,8698046721], by decide +kernel⟩,⟨Compact54Packed.unpack [8698508545,4353081601,41271569,41469201,8698174749,8648108317], by decide +kernel⟩,⟨Compact54Packed.unpack [4319524125,58309917,24756509,7980316,7980320,24425765], by decide +kernel⟩,⟨Compact54Packed.unpack [24557861,24756516,24756520,4336232749], by decide +kernel⟩,⟨Compact54Packed.unpack [41267501,41465133,24754477,41532716], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [41532720,41531700], by decide +kernel⟩,⟨Compact54Packed.unpack [7980340,21700570425,8697578809,8698171705,8648170809,4319652153], by decide +kernel⟩,⟨Compact54Packed.unpack [24686905,7910712,58308920], by decide +kernel⟩,⟨Compact54Packed.unpack [7910716,58308924,24488257], by decide +kernel⟩,⟨Compact54Packed.unpack [24685889,7909696,58307904], by decide +kernel⟩,⟨Compact54Packed.unpack [7980352,7909700,58307908], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [7980356,4336295241,41329993,24684873,24685896], by decide +kernel⟩,⟨Compact54Packed.unpack [75085128,7908684], by decide +kernel⟩,⟨Compact54Packed.unpack [7909708,75085132], by decide +kernel⟩,⟨Compact54Packed.unpack [41462096,41530704], by decide +kernel⟩,⟨Compact54Packed.unpack [24756560,8698103125,4352807253,57842005,24354133], by decide +kernel⟩,⟨Compact54Packed.unpack [24551765,7906645,41462100,7976276], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [58308948,24683864], by decide +kernel⟩,⟨Compact54Packed.unpack [24685912,58307928], by decide +kernel⟩,⟨Compact54Packed.unpack [7980376,24485213,24682845,41461084], by decide +kernel⟩,⟨Compact54Packed.unpack [91861340], by decide +kernel⟩,⟨Compact54Packed.unpack [41461088,41529696], by decide +kernel⟩,⟨Compact54Packed.unpack [41532768,4336292197,41326949,24681829], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [58237284,24752484], by decide +kernel⟩,⟨Compact54Packed.unpack [58308964,24682856], by decide +kernel⟩,⟨Compact54Packed.unpack [24684904,58306920], by decide +kernel⟩,⟨Compact54Packed.unpack [24756584,58236268], by decide +kernel⟩,⟨Compact54Packed.unpack [7908716,75084140], by decide +kernel⟩,⟨Compact54Packed.unpack [7980396,8697245041,8697969009,8648099185,4319646065,24680817], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [75013488,7975280], by decide +kernel⟩,⟨Compact54Packed.unpack [75085168,7904628], by decide +kernel⟩,⟨Compact54Packed.unpack [41460084,41528692], by decide +kernel⟩,⟨Compact54Packed.unpack [58308980,24416633,24614265], by decide +kernel⟩,⟨Compact54Packed.unpack [75012472,7974264], by decide +kernel⟩,⟨Compact54Packed.unpack [91861368], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [75012476,7974268], by decide +kernel⟩,⟨Compact54Packed.unpack [91861372], by decide +kernel⟩,⟨Compact54Packed.unpack [4336092545,41192833,41390465,7902593,24680832], by decide +kernel⟩,⟨Compact54Packed.unpack [41460096,41528704], by decide +kernel⟩,⟨Compact54Packed.unpack [58308992,24679812], by decide +kernel⟩,⟨Compact54Packed.unpack [58236292,24751492], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [75085188,7902600], by decide +kernel⟩,⟨Compact54Packed.unpack [75012488,7974280], by decide +kernel⟩,⟨Compact54Packed.unpack [91861384], by decide +kernel⟩,⟨Compact54Packed.unpack [8697703821,8698493325,4353197453,58232205,7901581,7902604], by decide +kernel⟩,⟨Compact54Packed.unpack [75012492,7974284], by decide +kernel⟩,⟨Compact54Packed.unpack [91861388], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [91787664], by decide +kernel⟩,⟨Compact54Packed.unpack [91859344], by decide +kernel⟩,⟨Compact54Packed.unpack [24756624,58233236], by decide +kernel⟩,⟨Compact54Packed.unpack [24682900,58304916], by decide +kernel⟩,⟨Compact54Packed.unpack [58309012,24678808], by decide +kernel⟩,⟨Compact54Packed.unpack [58235288,24750488], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [91861400], by decide +kernel⟩,⟨Compact54Packed.unpack [41190813,41453981,58232220], by decide +kernel⟩,⟨Compact54Packed.unpack [41459100,41527708], by decide +kernel⟩,⟨Compact54Packed.unpack [75085212,7900576], by decide +kernel⟩,⟨Compact54Packed.unpack [91787680], by decide +kernel⟩,⟨Compact54Packed.unpack [91859360], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [24756640,58232228], by decide +kernel⟩,⟨Compact54Packed.unpack [24681892,58303908], by decide +kernel⟩,⟨Compact54Packed.unpack [75085220,8698162601], by decide +kernel⟩,⟨Compact54Packed.unpack [4352932265,57967017,24544681,41453992], by decide +kernel⟩,⟨Compact54Packed.unpack [58234280,24749480], by decide +kernel⟩,⟨Compact54Packed.unpack [91860392], by decide +kernel⟩]
private def p11 : List P := [⟨Compact54Packed.unpack [7980456,75008428], by decide +kernel⟩,⟨Compact54Packed.unpack [24681900,58303916], by decide +kernel⟩,⟨Compact54Packed.unpack [75085228,24675761], by decide +kernel⟩,⟨Compact54Packed.unpack [91785648], by decide +kernel⟩,⟨Compact54Packed.unpack [7905712,75081136], by decide +kernel⟩,⟨Compact54Packed.unpack [58309040,24676788], by decide +kernel⟩]
private def p12 : List P := [⟨Compact54Packed.unpack [75010484,7972276], by decide +kernel⟩,⟨Compact54Packed.unpack [91859380], by decide +kernel⟩,⟨Compact54Packed.unpack [24756660,4336351673,41386425,24675768], by decide +kernel⟩,⟨Compact54Packed.unpack [91786680], by decide +kernel⟩,⟨Compact54Packed.unpack [91858360], by decide +kernel⟩,⟨Compact54Packed.unpack [41532856,41452988], by decide +kernel⟩]
private def p13 : List P := [⟨Compact54Packed.unpack [58233276,24748476], by decide +kernel⟩,⟨Compact54Packed.unpack [91859388], by decide +kernel⟩,⟨Compact54Packed.unpack [24756668,58230208], by decide +kernel⟩,⟨Compact54Packed.unpack [41457088,41525696], by decide +kernel⟩,⟨Compact54Packed.unpack [91860416], by decide +kernel⟩,⟨Compact54Packed.unpack [7980480,8631250373,41056709,41319877,7897541,7898564], by decide +kernel⟩]
private def p14 : List P := [⟨Compact54Packed.unpack [91785668], by decide +kernel⟩,⟨Compact54Packed.unpack [91857348], by decide +kernel⟩,⟨Compact54Packed.unpack [58309060,24674760], by decide +kernel⟩,⟨Compact54Packed.unpack [91785672], by decide +kernel⟩,⟨Compact54Packed.unpack [91857352], by decide +kernel⟩,⟨Compact54Packed.unpack [58309064,24674764], by decide +kernel⟩]
private def p15 : List P := [⟨Compact54Packed.unpack [91785676], by decide +kernel⟩,⟨Compact54Packed.unpack [91857356], by decide +kernel⟩,⟨Compact54Packed.unpack [58309068,4335889873,40990161], by decide +kernel⟩,⟨Compact54Packed.unpack [41253329,24673745,58229200], by decide +kernel⟩,⟨Compact54Packed.unpack [41456080,41524688], by decide +kernel⟩,⟨Compact54Packed.unpack [91859408], by decide +kernel⟩]
private def p16 : List P := [⟨Compact54Packed.unpack [24756688,58229204], by decide +kernel⟩,⟨Compact54Packed.unpack [41456084,41524692], by decide +kernel⟩,⟨Compact54Packed.unpack [91859412], by decide +kernel⟩,⟨Compact54Packed.unpack [24756692,58228184], by decide +kernel⟩,⟨Compact54Packed.unpack [58232280,24747480], by decide +kernel⟩,⟨Compact54Packed.unpack [91858392], by decide +kernel⟩]
private def p17 : List P := [⟨Compact54Packed.unpack [41532888], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10 ++ p11 ++ p12 ++ p13 ++ p14 ++ p15 ++ p16 ++ p17
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 118 27 8 = true := by decide +kernel
private theorem i35 : checks ts 118 35 8 = true := by decide +kernel
private theorem i43 : checks ts 118 43 7 = true := by decide +kernel
private theorem rows : checks ts 118 27 23 = true := checks_join i27 (checks_join i35 (i43))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 11 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

end Compact50PriceTableTwo6wider

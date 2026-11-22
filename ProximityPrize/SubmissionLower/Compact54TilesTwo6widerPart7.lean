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

namespace Top8
private abbrev P := PaidBatch .two6wider 8
private def p0 : List P := [⟨Compact54Packed.unpack [51997401121,51916346421,51764027537,51765351569,25993306313,21699067081], by decide +kernel⟩,⟨Compact54Packed.unpack [25995285705,21582688457,8697655525,8698117349,25994420481,21700312321], by decide +kernel⟩,⟨Compact54Packed.unpack [12992550145,8697914625,8698376449,8648178945,4336434449,41469201], by decide +kernel⟩,⟨Compact54Packed.unpack [12993205533,8647976221,4353143069,58177821,24624413,24756509], by decide +kernel⟩,⟨Compact54Packed.unpack [7980316,7980320,7912741,24756516,7978280], by decide +kernel⟩,⟨Compact54Packed.unpack [24756520,4336166189,41200941,41333037,24687917], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [7977261,41532716,24754480], by decide +kernel⟩,⟨Compact54Packed.unpack [24756528,7910708,41531700], by decide +kernel⟩,⟨Compact54Packed.unpack [7980340,25995534649,8697249081,8697907513,4403139897,4403535161], by decide +kernel⟩,⟨Compact54Packed.unpack [4319585593,24554809,7909689,7910712,24754488], by decide +kernel⟩,⟨Compact54Packed.unpack [24756536,24686908,24754492], by decide +kernel⟩,⟨Compact54Packed.unpack [24756540,24356161,24553793,7908673,7909696], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [75085120,7908676], by decide +kernel⟩,⟨Compact54Packed.unpack [7909700,75085124], by decide +kernel⟩,⟨Compact54Packed.unpack [41461065,7907657,24685896,24753480], by decide +kernel⟩,⟨Compact54Packed.unpack [41532744,41462092], by decide +kernel⟩,⟨Compact54Packed.unpack [75085132,7907664], by decide +kernel⟩,⟨Compact54Packed.unpack [24685904,58307920], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [7980368,8697773397,8698497365,4353135957,24419669,24617301], by decide +kernel⟩,⟨Compact54Packed.unpack [58238292,24753492], by decide +kernel⟩,⟨Compact54Packed.unpack [41532756,41461080], by decide +kernel⟩,⟨Compact54Packed.unpack [7909720,75085144], by decide +kernel⟩,⟨Compact54Packed.unpack [24616285,58237276,7975260], by decide +kernel⟩,⟨Compact54Packed.unpack [75085148,7905632], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [41461088,41529696], by decide +kernel⟩,⟨Compact54Packed.unpack [41532768,41194853,41392485,7904613], by decide +kernel⟩,⟨Compact54Packed.unpack [58237284,24752484], by decide +kernel⟩,⟨Compact54Packed.unpack [58308964,24681832], by decide +kernel⟩,⟨Compact54Packed.unpack [41461096,41529704], by decide +kernel⟩,⟨Compact54Packed.unpack [41532776,41459052], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [24684908,58306924], by decide +kernel⟩,⟨Compact54Packed.unpack [24756588,12992143729,8697639281,8698363249,4353001841], by decide +kernel⟩,⟨Compact54Packed.unpack [58036593,24548721,58235248], by decide +kernel⟩,⟨Compact54Packed.unpack [24684912,58306928], by decide +kernel⟩,⟨Compact54Packed.unpack [24756592,58235252], by decide +kernel⟩,⟨Compact54Packed.unpack [7907700,75083124], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [24756596,7902585,41458040], by decide +kernel⟩,⟨Compact54Packed.unpack [24683896,58305912], by decide +kernel⟩,⟨Compact54Packed.unpack [41532792,41457020], by decide +kernel⟩,⟨Compact54Packed.unpack [41460092,41528700], by decide +kernel⟩,⟨Compact54Packed.unpack [58308988,41060737,41258369], by decide +kernel⟩,⟨Compact54Packed.unpack [24678785,75011456], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [7907712,75083136], by decide +kernel⟩,⟨Compact54Packed.unpack [24756608,58234244], by decide +kernel⟩,⟨Compact54Packed.unpack [24683908,58305924], by decide +kernel⟩,⟨Compact54Packed.unpack [41532804,41456008], by decide +kernel⟩,⟨Compact54Packed.unpack [58236296,24751496], by decide +kernel⟩,⟨Compact54Packed.unpack [75085192,12992602509], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [8698098061,4352802189,57836941,24414605,24677773,7901580], by decide +kernel⟩,⟨Compact54Packed.unpack [91788684], by decide +kernel⟩,⟨Compact54Packed.unpack [91860364], by decide +kernel⟩,⟨Compact54Packed.unpack [7980428,75010448], by decide +kernel⟩,⟨Compact54Packed.unpack [7906704,75082128], by decide +kernel⟩,⟨Compact54Packed.unpack [41532816,24545685,24677780], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [75011476,7973268], by decide +kernel⟩,⟨Compact54Packed.unpack [91860372], by decide +kernel⟩,⟨Compact54Packed.unpack [7980436,75009432], by decide +kernel⟩,⟨Compact54Packed.unpack [24682904,58304920], by decide +kernel⟩,⟨Compact54Packed.unpack [58309016,4336287133,41321885], by decide +kernel⟩,⟨Compact54Packed.unpack [7834013,75009436], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [24682908,58304924], by decide +kernel⟩,⟨Compact54Packed.unpack [58309020,24676768], by decide +kernel⟩,⟨Compact54Packed.unpack [91787680], by decide +kernel⟩,⟨Compact54Packed.unpack [91859360], by decide +kernel⟩,⟨Compact54Packed.unpack [24756640,58231204], by decide +kernel⟩,⟨Compact54Packed.unpack [41458084,41526692], by decide +kernel⟩]
private def p11 : List P := [⟨Compact54Packed.unpack [91861412], by decide +kernel⟩,⟨Compact54Packed.unpack [12993061289,8648028585,4319641001,24675753,24676776], by decide +kernel⟩,⟨Compact54Packed.unpack [75010472,7972264], by decide +kernel⟩,⟨Compact54Packed.unpack [91859368], by decide +kernel⟩,⟨Compact54Packed.unpack [24756648,58231212], by decide +kernel⟩,⟨Compact54Packed.unpack [41458092,41526700], by decide +kernel⟩]
private def p12 : List P := [⟨Compact54Packed.unpack [91861420], by decide +kernel⟩,⟨Compact54Packed.unpack [24280497,24543665,58230192], by decide +kernel⟩,⟨Compact54Packed.unpack [58234288,24749488], by decide +kernel⟩,⟨Compact54Packed.unpack [91860400], by decide +kernel⟩,⟨Compact54Packed.unpack [7980464,75007412], by decide +kernel⟩,⟨Compact54Packed.unpack [41458100,41526708], by decide +kernel⟩]
private def p13 : List P := [⟨Compact54Packed.unpack [91861428], by decide +kernel⟩,⟨Compact54Packed.unpack [4335956409,40991161,41254329,24674745,24675768], by decide +kernel⟩,⟨Compact54Packed.unpack [91786680], by decide +kernel⟩,⟨Compact54Packed.unpack [91858360], by decide +kernel⟩,⟨Compact54Packed.unpack [41532856,41452988], by decide +kernel⟩,⟨Compact54Packed.unpack [58233276,24748476], by decide +kernel⟩]
private def p14 : List P := [⟨Compact54Packed.unpack [91859388], by decide +kernel⟩,⟨Compact54Packed.unpack [24756668,58229184], by decide +kernel⟩,⟨Compact54Packed.unpack [58233280,24748480], by decide +kernel⟩,⟨Compact54Packed.unpack [91859392], by decide +kernel⟩,⟨Compact54Packed.unpack [24756672,4385563077,4386089413,4336153029,41187781], by decide +kernel⟩,⟨Compact54Packed.unpack [41450949,75006404], by decide +kernel⟩]
private def p15 : List P := [⟨Compact54Packed.unpack [41457092,41525700], by decide +kernel⟩,⟨Compact54Packed.unpack [91860420], by decide +kernel⟩,⟨Compact54Packed.unpack [7980484,75006408], by decide +kernel⟩,⟨Compact54Packed.unpack [41457096,41525704], by decide +kernel⟩,⟨Compact54Packed.unpack [91860424], by decide +kernel⟩,⟨Compact54Packed.unpack [7980488,75006412], by decide +kernel⟩]
private def p16 : List P := [⟨Compact54Packed.unpack [41457100,41525708], by decide +kernel⟩,⟨Compact54Packed.unpack [91860428], by decide +kernel⟩,⟨Compact54Packed.unpack [7980492,4336349649,41384401,41450960], by decide +kernel⟩,⟨Compact54Packed.unpack [75008464,7970256], by decide +kernel⟩,⟨Compact54Packed.unpack [91857360], by decide +kernel⟩,⟨Compact54Packed.unpack [58309072,24673748], by decide +kernel⟩]
private def p17 : List P := [⟨Compact54Packed.unpack [91784660], by decide +kernel⟩,⟨Compact54Packed.unpack [91856340], by decide +kernel⟩,⟨Compact54Packed.unpack [75085268,7896536], by decide +kernel⟩,⟨Compact54Packed.unpack [91783640], by decide +kernel⟩,⟨Compact54Packed.unpack [7903704,75079128], by decide +kernel⟩,⟨Compact54Packed.unpack [91861464], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10 ++ p11 ++ p12 ++ p13 ++ p14 ++ p15 ++ p16 ++ p17
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 118 24 8 = true := by decide +kernel
private theorem i32 : checks ts 118 32 8 = true := by decide +kernel
private theorem i40 : checks ts 118 40 8 = true := by decide +kernel
private theorem i48 : checks ts 118 48 2 = true := by decide +kernel
private theorem rows : checks ts 118 24 26 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 10 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

end Compact50PriceTableTwo6wider

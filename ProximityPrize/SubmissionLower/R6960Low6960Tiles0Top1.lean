import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass0

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def priceBatch0 : P :=
  ⟨unpack [2197883909, 671158281, 4496364553, 4395703309, 25988244493, 73502703641], by decide +kernel⟩
private def priceBatch1 : P :=
  ⟨unpack [83958825, 8892194857, 73688188977, 369169469, 151066685, 4865662017], by decide +kernel⟩
private def priceBatch2 : P :=
  ⟨unpack [22381997125, 22299856969, 10033305701, 18707850357, 31056741521, 47817516177], by decide +kernel⟩
private def priceBatch3 : P :=
  ⟨unpack [27415090329, 35803828397, 43304785109, 38959628501, 26510583069, 26225508637], by decide +kernel⟩
private def priceBatch4 : P :=
  ⟨unpack [39730821409, 17367351585, 17317090593, 21762907437, 21645538605, 8660047173], by decide +kernel⟩
private def priceBatch5 : P :=
  ⟨unpack [4566409541, 4415409489, 8760636761, 8710373721, 4348302681, 8777489753], by decide +kernel⟩
private def priceBatch6 : P :=
  ⟨unpack [36558185, 3004777, 3004781, 53333361, 36557169, 3004784], by decide +kernel⟩
private def priceBatch7 : P :=
  ⟨unpack [13105864053, 8743857525, 3003764, 3004788, 4365074809, 53332345], by decide +kernel⟩
private def priceBatch8 : P :=
  ⟨unpack [3003768, 3004792, 3002748, 3003772, 3004796, 30705017217], by decide +kernel⟩
private def priceBatch9 : P :=
  ⟨unpack [3001729, 3002752, 3003776, 3004800, 4381849989, 3001732], by decide +kernel⟩
private def priceBatch10 : P :=
  ⟨unpack [3002756, 3003780, 3004804, 3000713, 3001736, 3002760], by decide +kernel⟩
private def priceBatch11 : P :=
  ⟨unpack [3003784, 3004808, 4348370313, 3073417, 17635705229, 8911558029], by decide +kernel⟩
private def priceBatch12 : P :=
  ⟨unpack [53330317, 19776909, 3000717, 3001740, 3002764, 3003788], by decide +kernel⟩
private def priceBatch13 : P :=
  ⟨unpack [3004812, 3073420, 3000720, 3001744, 3002768, 3003792], by decide +kernel⟩
private def priceBatch14 : P :=
  ⟨unpack [3004816, 3073424, 2999701, 3000724, 3001748, 3002772], by decide +kernel⟩
private def priceBatch15 : P :=
  ⟨unpack [3003796, 3004820, 3073428, 2999704, 3000728, 3001752], by decide +kernel⟩
private def priceBatch16 : P :=
  ⟨unpack [3002776, 3003800, 3004824, 19848601, 3072408, 3073432], by decide +kernel⟩
private def priceBatch17 : P :=
  ⟨unpack [4398558621, 120436125, 86882717, 53329309, 2998685, 2999708], by decide +kernel⟩
private def priceBatch18 : P :=
  ⟨unpack [3000732, 3001756, 3002780, 3003804, 3004828, 3072412], by decide +kernel⟩
private def priceBatch19 : P :=
  ⟨unpack [3073436, 2998689, 2999712, 3000736, 3001760, 3002784], by decide +kernel⟩
private def priceBatch20 : P :=
  ⟨unpack [3003808, 3004832, 3071392, 3072416, 3073440, 2998692], by decide +kernel⟩
private def priceBatch21 : P :=
  ⟨unpack [2999716, 3000740, 3001764, 3002788, 3003812, 3070372], by decide +kernel⟩
private def priceBatch22 : P :=
  ⟨unpack [3071396, 3072420, 3073444, 2998696, 2999720, 3000744], by decide +kernel⟩
private def priceBatch23 : P :=
  ⟨unpack [3001768, 3002792, 3003816, 3070376, 3071400, 3072424], by decide +kernel⟩
private def priceBatch24 : P :=
  ⟨unpack [3073448, 8727077293, 2997677, 2998700, 2999724, 3000748], by decide +kernel⟩
private def priceBatch25 : P :=
  ⟨unpack [3001772, 3002796, 3003820, 3070380, 3071404, 3072428], by decide +kernel⟩
private def priceBatch26 : P :=
  ⟨unpack [3073452, 2997680, 2998704, 2999728, 3000752, 3001776], by decide +kernel⟩
private def priceBatch27 : P :=
  ⟨unpack [3002800, 3003824, 3070384, 3071408, 3072432, 3073456], by decide +kernel⟩
private def priceBatch28 : P :=
  ⟨unpack [19773877, 2997684, 2998708, 2999732, 3000756, 3001780], by decide +kernel⟩
private def priceBatch29 : P :=
  ⟨unpack [3002804, 3003828, 3070388, 3071412, 3072436, 3073460], by decide +kernel⟩
private def priceBatch30 : P :=
  ⟨unpack [103591353, 86880697, 2997688, 2998712, 2999736, 3000760], by decide +kernel⟩
private def priceBatch31 : P :=
  ⟨unpack [3001784, 3002808, 3003832, 3070392, 3071416, 3072440], by decide +kernel⟩
private def priceBatch32 : P :=
  ⟨unpack [3073464, 36550077, 2996668, 2997692, 2998716, 2999740], by decide +kernel⟩
private def priceBatch33 : P :=
  ⟨unpack [3000764, 3001788, 3002812, 3069372, 3070396, 3071420], by decide +kernel⟩
private def priceBatch34 : P :=
  ⟨unpack [3072444, 3073468, 2996672, 2997696, 2998720, 2999744], by decide +kernel⟩
private def priceBatch35 : P :=
  ⟨unpack [3000768, 3001792, 3002816, 3069376, 3070400, 3071424], by decide +kernel⟩
private def priceBatch36 : P :=
  ⟨unpack [3072448, 3073472, 2996676, 2997700, 2998724, 2999748], by decide +kernel⟩
private def priceBatch37 : P :=
  ⟨unpack [3000772, 3001796, 3002820, 3069380, 3070404, 3071428], by decide +kernel⟩
private def priceBatch38 : P :=
  ⟨unpack [3072452, 3073476, 2995657, 2996680, 2997704, 2998728], by decide +kernel⟩
private def priceBatch39 : P :=
  ⟨unpack [2999752, 3000776, 3001800, 3002824, 3069384, 3070408], by decide +kernel⟩
private def priceBatch40 : P :=
  ⟨unpack [3071432, 3072456, 3073480, 2995660, 2996684, 2997708], by decide +kernel⟩
private def priceBatch41 : P :=
  ⟨unpack [2998732, 2999756, 3000780, 3001804, 3002828, 3069388], by decide +kernel⟩
private def priceBatch42 : P :=
  ⟨unpack [3070412, 3071436, 3072460, 3073484, 4415332817, 86813137], by decide +kernel⟩
private def priceBatch43 : P :=
  ⟨unpack [19771857, 2995664, 2996688, 2997712, 2998736, 2999760], by decide +kernel⟩
private def priceBatch44 : P :=
  ⟨unpack [3000784, 3001808, 3002832, 3069392, 3070416, 3071440], by decide +kernel⟩
private def priceBatch45 : P :=
  ⟨unpack [3072464, 3073488, 70102485, 2995668, 2996692, 2997716], by decide +kernel⟩
private def priceBatch46 : P :=
  ⟨unpack [2998740, 2999764, 3000788, 3001812, 3068372, 3069396], by decide +kernel⟩
private def priceBatch47 : P :=
  ⟨unpack [3070420, 3071444, 3072468, 3073492, 2994649, 2995672], by decide +kernel⟩
private def priceBatch48 : P :=
  ⟨unpack [2996696, 2997720, 2998744, 2999768, 3000792, 3001816], by decide +kernel⟩
private def priceBatch49 : P :=
  ⟨unpack [3068376, 3069400, 3070424, 3071448, 3072472, 3073496], by decide +kernel⟩
private def priceBatch50 : P :=
  ⟨unpack [4583101917, 4448886237, 2994652, 2995676, 2996700, 2997724], by decide +kernel⟩
private def priceBatch51 : P :=
  ⟨unpack [2998748, 2999772, 3000796, 3001820, 3068380, 3069404], by decide +kernel⟩
private def priceBatch52 : P :=
  ⟨unpack [3070428, 3071452, 3072476, 3073500, 2994656, 2995680], by decide +kernel⟩
private def priceBatch53 : P :=
  ⟨unpack [2996704, 2997728, 2998752, 2999776, 3000800, 3001824], by decide +kernel⟩
private def priceBatch54 : P :=
  ⟨unpack [3068384, 3069408, 3070432, 3071456, 3072480, 3073504], by decide +kernel⟩
private def priceBatch55 : P :=
  ⟨unpack [68973835749, 2994660, 2995684, 2996708, 2997732, 2998756], by decide +kernel⟩
private def priceBatch56 : P :=
  ⟨unpack [2999780, 3000804, 3001828, 3068388, 3069412, 3070436], by decide +kernel⟩
private def priceBatch57 : P :=
  ⟨unpack [3071460, 3072484, 3073508, 70101481, 19770857, 2994664], by decide +kernel⟩
private def priceBatch58 : P :=
  ⟨unpack [2995688, 2996712, 2997736, 2998760, 2999784, 3000808], by decide +kernel⟩
private def priceBatch59 : P :=
  ⟨unpack [3001832, 3068392, 3069416, 3070440, 3071464, 3072488], by decide +kernel⟩
private def priceBatch60 : P :=
  ⟨unpack [3073512, 2994668, 2995692, 2996716, 2997740, 2998764], by decide +kernel⟩
private def priceBatch61 : P :=
  ⟨unpack [2999788, 3000812, 3067372, 3068396, 3069420, 3070444], by decide +kernel⟩
private def priceBatch62 : P :=
  ⟨unpack [3071468, 3072492, 3073516, 103654897, 2993648, 2994672], by decide +kernel⟩
private def priceBatch63 : P :=
  ⟨unpack [2995696, 2996720, 2997744, 2998768, 2999792, 3000816], by decide +kernel⟩
private def priceBatch64 : P :=
  ⟨unpack [3067376, 3068400, 3069424, 3070448, 3071472, 3072496], by decide +kernel⟩
private def priceBatch65 : P :=
  ⟨unpack [3073520, 2993652, 2994676, 2995700, 2996724, 2997748], by decide +kernel⟩
private def priceBatch66 : P :=
  ⟨unpack [2998772, 2999796, 3000820, 3067380, 3068404, 3069428], by decide +kernel⟩
private def priceBatch67 : P :=
  ⟨unpack [3070452, 3071476, 3072500, 3073524, 2993656, 2994680], by decide +kernel⟩
private def priceBatch68 : P :=
  ⟨unpack [2995704, 2996728, 2997752, 2998776, 2999800, 3000824], by decide +kernel⟩
private def priceBatch69 : P :=
  ⟨unpack [3067384, 3068408, 3069432, 3070456, 3071480, 3072504], by decide +kernel⟩
private def priceBatch70 : P :=
  ⟨unpack [3073528, 21628748285, 19769853, 2993660, 2994684, 2995708], by decide +kernel⟩
private def priceBatch71 : P :=
  ⟨unpack [2996732, 2997756, 2998780, 2999804, 3000828, 3067388], by decide +kernel⟩
private def priceBatch72 : P :=
  ⟨unpack [3068412, 3069436, 3070460, 3071484, 3072508, 3073532], by decide +kernel⟩
private def priceBatch73 : P :=
  ⟨unpack [2993664, 2994688, 2995712, 2996736, 2997760, 2998784], by decide +kernel⟩
private def priceBatch74 : P :=
  ⟨unpack [2999808, 3066368, 3067392, 3068416, 3069440, 3070464], by decide +kernel⟩
private def priceBatch75 : P :=
  ⟨unpack [3071488, 3072512, 3073536, 120364549, 120431109, 2992645], by decide +kernel⟩
private def priceBatch76 : P :=
  ⟨unpack [2993668, 2994692, 2995716, 2996740, 2997764, 2998788], by decide +kernel⟩
private def priceBatch77 : P :=
  ⟨unpack [2999812, 3066372, 3067396, 3068420, 3069444, 3070468], by decide +kernel⟩
private def priceBatch78 : P :=
  ⟨unpack [3071492, 3072516, 3073540, 86002635273, 2992648, 2993672], by decide +kernel⟩
private def priceBatch79 : P :=
  ⟨unpack [2994696, 2995720, 2996744, 2997768, 2998792, 2999816], by decide +kernel⟩
private def priceBatch80 : P :=
  ⟨unpack [3066376, 3067400, 3068424, 3069448, 3070472, 3071496], by decide +kernel⟩
private def priceBatch81 : P :=
  ⟨unpack [3072520, 3073544, 36546061, 2992652, 2993676, 2994700], by decide +kernel⟩
private def priceBatch82 : P :=
  ⟨unpack [2995724, 2996748, 2997772, 2998796, 2999820, 3066380], by decide +kernel⟩
private def priceBatch83 : P :=
  ⟨unpack [3067404, 3068428, 3069452, 3070476, 3071500, 3072524], by decide +kernel⟩
private def priceBatch84 : P :=
  ⟨unpack [3073548, 2992656, 2993680, 2994704, 2995728, 2996752], by decide +kernel⟩
private def priceBatch85 : P :=
  ⟨unpack [2997776, 2998800, 2999824, 3066384, 3067408, 3068432], by decide +kernel⟩
private def priceBatch86 : P :=
  ⟨unpack [3069456, 3070480, 3071504, 3072528, 3073552, 85952302613], by decide +kernel⟩
private def priceBatch87 : P :=
  ⟨unpack [2992660, 2993684, 2994708, 2995732, 2996756, 2997780], by decide +kernel⟩
private def priceBatch88 : P :=
  ⟨unpack [2998804, 3065364, 3066388, 3067412, 3068436, 3069460], by decide +kernel⟩
private def priceBatch89 : P :=
  ⟨unpack [3070484, 3071508, 3072532, 3073556, 2991641, 2992664], by decide +kernel⟩
private def priceBatch90 : P :=
  ⟨unpack [2993688, 2994712, 2995736, 2996760, 2997784, 2998808], by decide +kernel⟩
private def priceBatch91 : P :=
  ⟨unpack [3065368, 3066392, 3067416, 3068440, 3069464, 3070488], by decide +kernel⟩
private def priceBatch92 : P :=
  ⟨unpack [3071512, 3072536, 3073560, 30084463133, 2991645, 2992668], by decide +kernel⟩
private def priceBatch93 : P :=
  ⟨unpack [2993692, 2994716, 2995740, 2996764, 2997788, 2998812], by decide +kernel⟩
private def priceBatch94 : P :=
  ⟨unpack [3065372, 3066396, 3067420, 3068444, 3069468, 3070492], by decide +kernel⟩
private def priceBatch95 : P :=
  ⟨unpack [3071516, 3072540, 3073564, 2991648, 2992672, 2993696], by decide +kernel⟩
private def priceBatch96 : P :=
  ⟨unpack [2994720, 2995744, 2996768, 2997792, 2998816, 3065376], by decide +kernel⟩
private def priceBatch97 : P :=
  ⟨unpack [3066400, 3067424, 3068448, 3069472, 3070496, 3071520], by decide +kernel⟩
private def priceBatch98 : P :=
  ⟨unpack [3072544, 3073568], by decide +kernel⟩
private def batches : List P := [priceBatch0, priceBatch1, priceBatch2, priceBatch3, priceBatch4, priceBatch5, priceBatch6, priceBatch7, priceBatch8, priceBatch9, priceBatch10, priceBatch11, priceBatch12, priceBatch13, priceBatch14, priceBatch15, priceBatch16, priceBatch17, priceBatch18, priceBatch19, priceBatch20, priceBatch21, priceBatch22, priceBatch23, priceBatch24, priceBatch25, priceBatch26, priceBatch27, priceBatch28, priceBatch29, priceBatch30, priceBatch31, priceBatch32, priceBatch33, priceBatch34, priceBatch35, priceBatch36, priceBatch37, priceBatch38, priceBatch39, priceBatch40, priceBatch41, priceBatch42, priceBatch43, priceBatch44, priceBatch45, priceBatch46, priceBatch47, priceBatch48, priceBatch49, priceBatch50, priceBatch51, priceBatch52, priceBatch53, priceBatch54, priceBatch55, priceBatch56, priceBatch57, priceBatch58, priceBatch59, priceBatch60, priceBatch61, priceBatch62, priceBatch63, priceBatch64, priceBatch65, priceBatch66, priceBatch67, priceBatch68, priceBatch69, priceBatch70, priceBatch71, priceBatch72, priceBatch73, priceBatch74, priceBatch75, priceBatch76, priceBatch77, priceBatch78, priceBatch79, priceBatch80, priceBatch81, priceBatch82, priceBatch83, priceBatch84, priceBatch85, priceBatch86, priceBatch87, priceBatch88, priceBatch89, priceBatch90, priceBatch91, priceBatch92, priceBatch93, priceBatch94, priceBatch95, priceBatch96, priceBatch97, priceBatch98]
private theorem i3 : checks (tilesOf batches) 136 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 136 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 136 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤57) :
    Covered orders a ∨ Low6960Gate.Gated ((0 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

end Low6960Allocation.Group0

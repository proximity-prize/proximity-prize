import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top4
private def b0 : PaidBatch .empty 4 := ⟨[
  .rectangle 4 12 66 17 14,
  .rectangle 6 18 129 22 31,
  .rectangle 8 23 68 32 28], by decide +kernel⟩
private def b1 : PaidBatch .empty 4 := ⟨[
  .rectangle 11 33 70 43 34,
  .rectangle 15 44 70 53 37,
  .rectangle 67 12 129 17 27], by decide +kernel⟩
private def b2 : PaidBatch .empty 4 := ⟨[
  .rectangle 69 23 129 27 37,
  .rectangle 69 28 129 32 43,
  .rectangle 71 49 85 53 41], by decide +kernel⟩
private def b3 : PaidBatch .empty 4 := ⟨[
  .rectangle 71 33 100 38 39,
  .rectangle 71 39 100 43 42,
  .rectangle 71 44 100 48 46], by decide +kernel⟩
private def b4 : PaidBatch .empty 4 := ⟨[
  .rectangle 86 49 100 51 46,
  .rectangle 86 52 100 53 46,
  .rectangle 101 52 104 53 48], by decide +kernel⟩
private def b5 : PaidBatch .empty 4 := ⟨[
  .rectangle 101 44 108 46 46,
  .rectangle 101 47 108 48 46,
  .rectangle 101 49 108 50 48], by decide +kernel⟩
private def b6 : PaidBatch .empty 4 := ⟨[
  .rectangle 101 51 108 51 48,
  .rectangle 101 39 115 41 44,
  .rectangle 101 42 115 43 45], by decide +kernel⟩
private def b7 : PaidBatch .empty 4 := ⟨[
  .rectangle 101 33 129 35 43,
  .rectangle 101 36 129 38 46,
  .rectangle 105 52 108 52 48], by decide +kernel⟩
private def b8 : PaidBatch .empty 4 := ⟨[
  .rectangle 105 53 108 53 49,
  .rectangle 109 51 109 51 48,
  .point 109 52 45], by decide +kernel⟩
private def b9 : PaidBatch .empty 4 := ⟨[
  .point 109 53 46,
  .rectangle 109 50 110 50 48,
  .rectangle 109 49 112 49 48], by decide +kernel⟩
private def b10 : PaidBatch .empty 4 := ⟨[
  .rectangle 109 44 115 45 47,
  .rectangle 109 46 115 46 47,
  .rectangle 109 47 115 47 47], by decide +kernel⟩
private def b11 : PaidBatch .empty 4 := ⟨[
  .rectangle 109 48 115 48 48,
  .point 110 51 45,
  .rectangle 110 52 110 52 49], by decide +kernel⟩
private def b12 : PaidBatch .empty 4 := ⟨[
  .point 110 53 47,
  .rectangle 111 50 111 50 48,
  .point 111 51 45], by decide +kernel⟩
private def b13 : PaidBatch .empty 4 := ⟨[
  .point 111 52 46,
  .point 111 53 47,
  .point 112 50 45], by decide +kernel⟩
private def b14 : PaidBatch .empty 4 := ⟨[
  .point 112 51 46,
  .point 112 52 47,
  .point 112 53 47], by decide +kernel⟩
private def b15 : PaidBatch .empty 4 := ⟨[
  .rectangle 113 49 113 49 48,
  .point 113 50 46,
  .point 113 51 46], by decide +kernel⟩
private def b16 : PaidBatch .empty 4 := ⟨[
  .point 113 52 47,
  .point 113 53 48,
  .point 114 49 45], by decide +kernel⟩
private def b17 : PaidBatch .empty 4 := ⟨[
  .point 114 50 46,
  .point 114 51 47,
  .point 114 52 48], by decide +kernel⟩
private def b18 : PaidBatch .empty 4 := ⟨[
  .point 114 53 48,
  .point 115 49 46,
  .point 115 50 46], by decide +kernel⟩
private def b19 : PaidBatch .empty 4 := ⟨[
  .point 115 51 47,
  .point 115 52 48,
  .point 115 53 49], by decide +kernel⟩
private def b20 : PaidBatch .empty 4 := ⟨[
  .point 116 48 45,
  .point 116 49 46,
  .point 116 50 47], by decide +kernel⟩
private def b21 : PaidBatch .empty 4 := ⟨[
  .point 116 51 48,
  .point 116 52 48,
  .point 116 53 49], by decide +kernel⟩
private def b22 : PaidBatch .empty 4 := ⟨[
  .rectangle 116 47 117 47 48,
  .rectangle 116 46 119 46 48,
  .rectangle 116 42 122 43 48], by decide +kernel⟩
private def b23 : PaidBatch .empty 4 := ⟨[
  .rectangle 116 44 122 44 48,
  .rectangle 116 45 122 45 48,
  .rectangle 116 39 129 40 47], by decide +kernel⟩
private def b24 : PaidBatch .empty 4 := ⟨[
  .rectangle 116 41 129 41 47,
  .point 117 48 46,
  .point 117 49 46], by decide +kernel⟩
private def b25 : PaidBatch .empty 4 := ⟨[
  .point 117 50 47,
  .point 117 51 48,
  .point 117 52 49], by decide +kernel⟩
private def b26 : PaidBatch .empty 4 := ⟨[
  .shared 117 53 37 ⟨.tilted, 1, 1, false, 158710529502896768⟩,
  .point 118 47 45,
  .point 118 48 46], by decide +kernel⟩
private def b27 : PaidBatch .empty 4 := ⟨[
  .point 118 49 47,
  .point 118 50 48,
  .point 118 51 49], by decide +kernel⟩
private def b28 : PaidBatch .empty 4 := ⟨[
  .point 118 52 49,
  .shared 118 53 38 ⟨.tilted, 1, 1, false, 160116939561904973⟩,
  .point 119 47 45], by decide +kernel⟩
private def b29 : PaidBatch .empty 4 := ⟨[
  .point 119 48 46,
  .point 119 49 47,
  .point 119 50 48], by decide +kernel⟩
private def b30 : PaidBatch .empty 4 := ⟨[
  .point 119 51 49,
  .shared 119 52 37 ⟨.tilted, 1, 1, false, 156039422684705996⟩,
  .shared 119 53 38 ⟨.tilted, 1, 1, false, 161523349620913178⟩], by decide +kernel⟩
private def b31 : PaidBatch .empty 4 := ⟨[
  .point 120 46 45,
  .point 120 47 46,
  .point 120 48 47], by decide +kernel⟩
private def b32 : PaidBatch .empty 4 := ⟨[
  .point 120 49 48,
  .shared 120 50 32 ⟨.tilted, 1, 2, true, 168201544818977356⟩,
  .point 120 51 49], by decide +kernel⟩
private def b33 : PaidBatch .empty 4 := ⟨[
  .shared 120 52 38 ⟨.tilted, 1, 1, false, 157393842442592396⟩,
  .shared 120 53 39 ⟨.tilted, 1, 1, false, 162929759679921383⟩,
  .point 121 46 45], by decide +kernel⟩
private def b34 : PaidBatch .empty 4 := ⟨[
  .point 121 47 46,
  .point 121 48 47,
  .point 121 49 48], by decide +kernel⟩
private def b35 : PaidBatch .empty 4 := ⟨[
  .shared 121 50 32 ⟨.tilted, 1, 2, true, 169678290415346724⟩,
  .shared 121 51 33 ⟨.tilted, 1, 2, true, 176196225562567118⟩,
  .shared 121 52 38 ⟨.tilted, 1, 1, false, 158748262200478796⟩], by decide +kernel⟩
private def b36 : PaidBatch .empty 4 := ⟨[
  .shared 121 53 39 ⟨.tilted, 1, 1, false, 164336169738929588⟩,
  .point 122 46 46,
  .point 122 47 47], by decide +kernel⟩
private def b37 : PaidBatch .empty 4 := ⟨[
  .point 122 48 48,
  .shared 122 49 32 ⟨.tilted, 1, 2, true, 164668234489909176⟩,
  .point 122 50 49], by decide +kernel⟩
private def b38 : PaidBatch .empty 4 := ⟨[
  .shared 122 51 38 ⟨.tilted, 1, 1, false, 154533458158891464⟩,
  .shared 122 52 39 ⟨.tilted, 1, 1, false, 160102681958365196⟩,
  .shared 122 53 40 ⟨.tilted, 1, 1, false, 165742579797937793⟩], by decide +kernel⟩
private def b39 : PaidBatch .empty 4 := ⟨[
  .point 123 45 45,
  .point 123 46 46,
  .point 123 47 47], by decide +kernel⟩
private def b40 : PaidBatch .empty 4 := ⟨[
  .point 123 48 48,
  .shared 123 49 32 ⟨.tilted, 1, 2, true, 166084066478592292⟩,
  .shared 123 50 33 ⟨.tilted, 1, 2, true, 172631781608085460⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 4 := ⟨[
  .shared 123 51 38 ⟨.tilted, 1, 1, false, 155836849409293053⟩,
  .shared 123 52 39 ⟨.tilted, 1, 1, false, 161457101716251596⟩,
  .shared 123 53 40 ⟨.tilted, 1, 1, false, 167148989856945998⟩], by decide +kernel⟩
private def b42 : PaidBatch .empty 4 := ⟨[
  .rectangle 123 44 124 44 48,
  .rectangle 123 43 126 43 48,
  .rectangle 123 42 129 42 48], by decide +kernel⟩
private def b43 : PaidBatch .empty 4 := ⟨[
  .point 124 45 46,
  .point 124 46 47,
  .point 124 47 47], by decide +kernel⟩
private def b44 : PaidBatch .empty 4 := ⟨[
  .point 124 48 48,
  .shared 124 49 33 ⟨.tilted, 1, 2, true, 167499898467275408⟩,
  .shared 124 50 34 ⟨.tilted, 1, 2, true, 174108527204454828⟩], by decide +kernel⟩
private def b45 : PaidBatch .empty 4 := ⟨[
  .shared 124 51 39 ⟨.tilted, 1, 1, false, 157140240659694642⟩,
  .shared 124 52 40 ⟨.tilted, 1, 1, false, 162811521474137996⟩,
  .shared 124 53 41 ⟨.tilted, 1, 1, false, 168555399915954203⟩], by decide +kernel⟩
private def b46 : PaidBatch .empty 4 := ⟨[
  .point 125 44 45,
  .point 125 45 46,
  .point 125 46 47], by decide +kernel⟩
private def b47 : PaidBatch .empty 4 := ⟨[
  .point 125 47 48,
  .shared 125 48 32 ⟨.tilted, 0, 2, true, 162345288497530536⟩,
  .shared 125 49 33 ⟨.tilted, 0, 2, true, 168915730455958524⟩], by decide +kernel⟩
private def b48 : PaidBatch .empty 4 := ⟨[
  .shared 125 50 34 ⟨.tilted, 1, 2, true, 175585272800824196⟩,
  .shared 125 51 39 ⟨.tilted, 1, 1, false, 158443631910096231⟩,
  .shared 125 52 40 ⟨.tilted, 1, 1, false, 164165941232024396⟩], by decide +kernel⟩
private def b49 : PaidBatch .empty 4 := ⟨[
  .shared 125 53 41 ⟨.tilted, 1, 1, false, 169961809974962408⟩,
  .point 126 44 45,
  .point 126 45 46], by decide +kernel⟩
private def b50 : PaidBatch .empty 4 := ⟨[
  .point 126 46 47,
  .point 126 47 48,
  .shared 126 48 33 ⟨.tilted, 0, 2, true, 163701489270043392⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 4 := ⟨[
  .shared 126 49 34 ⟨.tilted, 0, 2, true, 170331562444641640⟩,
  .shared 126 50 35 ⟨.tilted, 1, 2, true, 177062018397193564⟩,
  .shared 126 51 40 ⟨.tilted, 1, 1, false, 159747023160497820⟩], by decide +kernel⟩
private def b52 : PaidBatch .empty 4 := ⟨[
  .shared 126 52 41 ⟨.tilted, 1, 1, false, 165520360989910796⟩,
  .shared 126 53 42 ⟨.tilted, 1, 1, false, 171368220033970613⟩,
  .point 127 43 45], by decide +kernel⟩
private def b53 : PaidBatch .empty 4 := ⟨[
  .point 127 44 46,
  .point 127 45 47,
  .point 127 46 48], by decide +kernel⟩
private def b54 : PaidBatch .empty 4 := ⟨[
  .shared 127 47 36 ⟨.tilted, 0, 1, false, 138536632955256431⟩,
  .shared 127 48 33 ⟨.tilted, 0, 2, true, 165057690042556248⟩,
  .shared 127 49 34 ⟨.tilted, 0, 2, true, 171747394433324756⟩], by decide +kernel⟩
private def b55 : PaidBatch .empty 4 := ⟨[
  .shared 127 50 36 ⟨.tilted, 1, 2, true, 178538763993562932⟩,
  .shared 127 51 40 ⟨.tilted, 1, 1, false, 161050414410899409⟩,
  .shared 127 52 41 ⟨.tilted, 1, 1, false, 166874780747797196⟩], by decide +kernel⟩
private def b56 : PaidBatch .empty 4 := ⟨[
  .shared 127 53 42 ⟨.tilted, 1, 1, false, 172774630092978818⟩,
  .point 128 43 45,
  .point 128 44 46], by decide +kernel⟩
private def b57 : PaidBatch .empty 4 := ⟨[
  .point 128 45 47,
  .point 128 46 48,
  .shared 128 47 37 ⟨.tilted, 0, 1, false, 139645528112088716⟩], by decide +kernel⟩
private def b58 : PaidBatch .empty 4 := ⟨[
  .shared 128 48 34 ⟨.tilted, 0, 2, true, 166413890815069104⟩,
  .shared 128 49 35 ⟨.tilted, 0, 2, true, 173163226422007872⟩,
  .shared 128 50 36 ⟨.tilted, 0, 2, true, 180015509589932300⟩], by decide +kernel⟩
private def b59 : PaidBatch .empty 4 := ⟨[
  .shared 128 51 41 ⟨.tilted, 1, 1, false, 162353805661300998⟩,
  .shared 128 52 42 ⟨.tilted, 1, 1, false, 168229200505683596⟩,
  .shared 128 53 43 ⟨.tilted, 1, 1, false, 174181040151987023⟩], by decide +kernel⟩
private def b60 : PaidBatch .empty 4 := ⟨[
  .point 129 43 45,
  .point 129 44 47,
  .point 129 45 48], by decide +kernel⟩
private def b61 : PaidBatch .empty 4 := ⟨[
  .shared 129 46 36 ⟨.tilted, 0, 1, false, 135236673251675072⟩,
  .shared 129 47 37 ⟨.tilted, 0, 1, false, 140754423268921001⟩,
  .shared 129 48 34 ⟨.tilted, 0, 2, true, 167770091587581960⟩], by decide +kernel⟩
private def b62 : PaidBatch .empty 4 := ⟨[
  .shared 129 49 36 ⟨.tilted, 0, 2, true, 174579058410690988⟩,
  .shared 129 50 37 ⟨.tilted, 0, 2, true, 181492255186301668⟩,
  .shared 129 51 41 ⟨.tilted, 1, 1, false, 163657196911702587⟩], by decide +kernel⟩
private def b63 : PaidBatch .empty 4 := ⟨[
  .shared 129 52 42 ⟨.tilted, 1, 1, false, 169583620263569996⟩,
  .shared 129 53 43 ⟨.tilted, 1, 1, false, 175587450210995228⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 4) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 129 12 2 = true := by decide +kernel
private theorem i14 : checks tiles 129 14 2 = true := by decide +kernel
private theorem i16 : checks tiles 129 16 2 = true := by decide +kernel
private theorem i18 : checks tiles 129 18 2 = true := by decide +kernel
private theorem i20 : checks tiles 129 20 2 = true := by decide +kernel
private theorem i22 : checks tiles 129 22 2 = true := by decide +kernel
private theorem i24 : checks tiles 129 24 2 = true := by decide +kernel
private theorem i26 : checks tiles 129 26 2 = true := by decide +kernel
private theorem i28 : checks tiles 129 28 2 = true := by decide +kernel
private theorem i30 : checks tiles 129 30 2 = true := by decide +kernel
private theorem i32 : checks tiles 129 32 2 = true := by decide +kernel
private theorem i34 : checks tiles 129 34 2 = true := by decide +kernel
private theorem i36 : checks tiles 129 36 2 = true := by decide +kernel
private theorem i38 : checks tiles 129 38 2 = true := by decide +kernel
private theorem i40 : checks tiles 129 40 2 = true := by decide +kernel
private theorem i42 : checks tiles 129 42 2 = true := by decide +kernel
private theorem i44 : checks tiles 129 44 2 = true := by decide +kernel
private theorem i46 : checks tiles 129 46 2 = true := by decide +kernel
private theorem i48 : checks tiles 129 48 2 = true := by decide +kernel
private theorem i50 : checks tiles 129 50 2 = true := by decide +kernel
private theorem i52 : checks tiles 129 52 2 = true := by decide +kernel
def receipt : Certificate .empty 4 := ⟨batches, checks_join i12 (checks_join i14 (checks_join i16 (checks_join i18 (checks_join i20 (checks_join i22 (checks_join i24 (checks_join i26 (checks_join i28 (checks_join i30 (checks_join i32 (checks_join i34 (checks_join i36 (checks_join i38 (checks_join i40 (checks_join i42 (checks_join i44 (checks_join i46 (checks_join i48 (checks_join i50 i52)))))))))))))))))))⟩
end Top4


end Low53At2389PriceTableEmpty4

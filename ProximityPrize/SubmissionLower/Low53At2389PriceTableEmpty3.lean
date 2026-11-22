import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top3
private def b0 : PaidBatch .empty 3 := ⟨[
  .rectangle 3 9 34 14 7,
  .rectangle 5 15 67 20 16,
  .rectangle 7 21 68 31 28], by decide +kernel⟩
private def b1 : PaidBatch .empty 3 := ⟨[
  .rectangle 11 32 70 42 33,
  .rectangle 15 43 70 53 36,
  .rectangle 35 9 66 14 13], by decide +kernel⟩
private def b2 : PaidBatch .empty 3 := ⟨[
  .rectangle 67 9 129 14 25,
  .rectangle 68 15 129 20 31,
  .rectangle 69 21 129 26 37], by decide +kernel⟩
private def b3 : PaidBatch .empty 3 := ⟨[
  .rectangle 69 27 129 31 41,
  .rectangle 71 32 100 37 38,
  .rectangle 71 38 100 42 40], by decide +kernel⟩
private def b4 : PaidBatch .empty 3 := ⟨[
  .rectangle 71 43 100 48 45,
  .rectangle 71 49 100 53 47,
  .rectangle 101 52 104 53 47], by decide +kernel⟩
private def b5 : PaidBatch .empty 3 := ⟨[
  .rectangle 101 46 108 48 46,
  .rectangle 101 49 108 51 48,
  .rectangle 101 38 115 42 46], by decide +kernel⟩
private def b6 : PaidBatch .empty 3 := ⟨[
  .rectangle 101 43 115 45 47,
  .rectangle 101 32 129 34 41,
  .rectangle 101 35 129 37 45], by decide +kernel⟩
private def b7 : PaidBatch .empty 3 := ⟨[
  .rectangle 105 52 108 52 47,
  .rectangle 105 53 108 53 48,
  .rectangle 109 52 110 52 48], by decide +kernel⟩
private def b8 : PaidBatch .empty 3 := ⟨[
  .rectangle 109 53 110 53 49,
  .rectangle 109 50 112 50 47,
  .rectangle 109 51 112 51 48], by decide +kernel⟩
private def b9 : PaidBatch .empty 3 := ⟨[
  .rectangle 109 46 115 47 47,
  .rectangle 109 48 115 48 47,
  .rectangle 109 49 115 49 48], by decide +kernel⟩
private def b10 : PaidBatch .empty 3 := ⟨[
  .rectangle 111 53 111 53 49,
  .rectangle 111 52 112 52 49,
  .point 112 53 46], by decide +kernel⟩
private def b11 : PaidBatch .empty 3 := ⟨[
  .point 113 51 45,
  .rectangle 113 52 113 52 49,
  .point 113 53 46], by decide +kernel⟩
private def b12 : PaidBatch .empty 3 := ⟨[
  .rectangle 113 50 114 50 48,
  .point 114 51 45,
  .point 114 52 46], by decide +kernel⟩
private def b13 : PaidBatch .empty 3 := ⟨[
  .point 114 53 47,
  .point 115 50 45,
  .point 115 51 46], by decide +kernel⟩
private def b14 : PaidBatch .empty 3 := ⟨[
  .point 115 52 47,
  .point 115 53 47,
  .rectangle 116 49 116 49 48], by decide +kernel⟩
private def b15 : PaidBatch .empty 3 := ⟨[
  .point 116 50 45,
  .point 116 51 46,
  .point 116 52 47], by decide +kernel⟩
private def b16 : PaidBatch .empty 3 := ⟨[
  .point 116 53 48,
  .rectangle 116 48 117 48 48,
  .rectangle 116 47 119 47 48], by decide +kernel⟩
private def b17 : PaidBatch .empty 3 := ⟨[
  .rectangle 116 41 122 42 46,
  .rectangle 116 43 122 44 48,
  .rectangle 116 45 122 45 47], by decide +kernel⟩
private def b18 : PaidBatch .empty 3 := ⟨[
  .rectangle 116 46 122 46 48,
  .rectangle 116 38 129 39 45,
  .rectangle 116 40 129 40 45], by decide +kernel⟩
private def b19 : PaidBatch .empty 3 := ⟨[
  .point 117 49 45,
  .point 117 50 46,
  .point 117 51 47], by decide +kernel⟩
private def b20 : PaidBatch .empty 3 := ⟨[
  .point 117 52 47,
  .point 117 53 48,
  .rectangle 118 48 118 48 48], by decide +kernel⟩
private def b21 : PaidBatch .empty 3 := ⟨[
  .point 118 49 46,
  .point 118 50 46,
  .point 118 51 47], by decide +kernel⟩
private def b22 : PaidBatch .empty 3 := ⟨[
  .point 118 52 48,
  .point 118 53 49,
  .point 119 48 45], by decide +kernel⟩
private def b23 : PaidBatch .empty 3 := ⟨[
  .point 119 49 46,
  .point 119 50 47,
  .point 119 51 48], by decide +kernel⟩
private def b24 : PaidBatch .empty 3 := ⟨[
  .point 119 52 48,
  .point 119 53 49,
  .rectangle 120 47 120 47 48], by decide +kernel⟩
private def b25 : PaidBatch .empty 3 := ⟨[
  .point 120 48 46,
  .point 120 49 46,
  .point 120 50 47], by decide +kernel⟩
private def b26 : PaidBatch .empty 3 := ⟨[
  .point 120 51 48,
  .point 120 52 49,
  .shared 120 53 36 ⟨.tilted, 1, 1, false, 151800651051685252⟩], by decide +kernel⟩
private def b27 : PaidBatch .empty 3 := ⟨[
  .point 121 47 45,
  .point 121 48 46,
  .point 121 49 47], by decide +kernel⟩
private def b28 : PaidBatch .empty 3 := ⟨[
  .point 121 50 48,
  .point 121 51 48,
  .point 121 52 49], by decide +kernel⟩
private def b29 : PaidBatch .empty 3 := ⟨[
  .shared 121 53 37 ⟨.tilted, 1, 1, false, 153166826080082200⟩,
  .point 122 47 45,
  .point 122 48 46], by decide +kernel⟩
private def b30 : PaidBatch .empty 3 := ⟨[
  .point 122 49 47,
  .point 122 50 48,
  .point 122 51 49], by decide +kernel⟩
private def b31 : PaidBatch .empty 3 := ⟨[
  .shared 122 52 37 ⟨.tilted, 1, 1, false, 149311536907821006⟩,
  .shared 122 53 37 ⟨.tilted, 1, 1, false, 154533001108479148⟩,
  .point 123 46 45], by decide +kernel⟩
private def b32 : PaidBatch .empty 3 := ⟨[
  .point 123 47 46,
  .point 123 48 47,
  .point 123 49 48], by decide +kernel⟩
private def b33 : PaidBatch .empty 3 := ⟨[
  .point 123 50 48,
  .point 123 51 49,
  .shared 123 52 37 ⟨.tilted, 1, 1, false, 150626683428733143⟩], by decide +kernel⟩
private def b34 : PaidBatch .empty 3 := ⟨[
  .shared 123 53 38 ⟨.tilted, 1, 1, false, 155899176136876096⟩,
  .rectangle 123 45 124 45 48,
  .rectangle 123 44 126 44 48], by decide +kernel⟩
private def b35 : PaidBatch .empty 3 := ⟨[
  .rectangle 123 41 129 41 46,
  .rectangle 123 42 129 42 47,
  .rectangle 123 43 129 43 48], by decide +kernel⟩
private def b36 : PaidBatch .empty 3 := ⟨[
  .point 124 46 45,
  .point 124 47 46,
  .point 124 48 47], by decide +kernel⟩
private def b37 : PaidBatch .empty 3 := ⟨[
  .point 124 49 48,
  .point 124 50 49,
  .shared 124 51 37 ⟨.tilted, 1, 1, false, 146683532610173415⟩], by decide +kernel⟩
private def b38 : PaidBatch .empty 3 := ⟨[
  .shared 124 52 38 ⟨.tilted, 1, 1, false, 151941829949645280⟩,
  .shared 124 53 38 ⟨.tilted, 1, 1, false, 157265351165273044⟩,
  .point 125 45 45], by decide +kernel⟩
private def b39 : PaidBatch .empty 3 := ⟨[
  .point 125 46 46,
  .point 125 47 47,
  .point 125 48 48], by decide +kernel⟩
private def b40 : PaidBatch .empty 3 := ⟨[
  .point 125 49 48,
  .point 125 50 49,
  .shared 125 51 37 ⟨.tilted, 1, 1, false, 147948612417237735⟩], by decide +kernel⟩
private def b41 : PaidBatch .empty 3 := ⟨[
  .shared 125 52 38 ⟨.tilted, 1, 1, false, 153256976470557417⟩,
  .shared 125 53 39 ⟨.tilted, 1, 1, false, 158631526193669992⟩,
  .point 126 45 45], by decide +kernel⟩
private def b42 : PaidBatch .empty 3 := ⟨[
  .point 126 46 46,
  .point 126 47 47,
  .point 126 48 48], by decide +kernel⟩
private def b43 : PaidBatch .empty 3 := ⟨[
  .shared 126 49 36 ⟨.tilted, 0, 1, false, 138704043842078682⟩,
  .shared 126 50 37 ⟨.tilted, 1, 1, false, 143923851611019934⟩,
  .shared 126 51 38 ⟨.tilted, 1, 1, false, 149213692224302055⟩], by decide +kernel⟩
private def b44 : PaidBatch .empty 3 := ⟨[
  .shared 126 52 39 ⟨.tilted, 1, 1, false, 154572122991469554⟩,
  .shared 126 53 39 ⟨.tilted, 1, 1, false, 159997701222066940⟩,
  .point 127 44 45], by decide +kernel⟩
private def b45 : PaidBatch .empty 3 := ⟨[
  .point 127 45 46,
  .point 127 46 47,
  .point 127 47 48], by decide +kernel⟩
private def b46 : PaidBatch .empty 3 := ⟨[
  .point 127 48 48,
  .point 127 49 49,
  .shared 127 50 37 ⟨.tilted, 1, 1, false, 145139826497873431⟩], by decide +kernel⟩
private def b47 : PaidBatch .empty 3 := ⟨[
  .shared 127 51 38 ⟨.tilted, 1, 1, false, 150478772031366375⟩,
  .shared 127 52 39 ⟨.tilted, 1, 1, false, 155887269512381691⟩,
  .shared 127 53 40 ⟨.tilted, 1, 1, false, 161363876250463888⟩], by decide +kernel⟩
private def b48 : PaidBatch .empty 3 := ⟨[
  .point 128 44 45,
  .point 128 45 46,
  .point 128 46 47], by decide +kernel⟩
private def b49 : PaidBatch .empty 3 := ⟨[
  .point 128 47 48,
  .shared 128 48 36 ⟨.tilted, 0, 1, false, 135797012462619456⟩,
  .shared 128 49 37 ⟨.tilted, 0, 1, false, 141039707362638018⟩], by decide +kernel⟩
private def b50 : PaidBatch .empty 3 := ⟨[
  .shared 128 50 38 ⟨.tilted, 0, 1, false, 146355801384726928⟩,
  .shared 128 51 39 ⟨.tilted, 1, 1, false, 151743851838430695⟩,
  .shared 128 52 40 ⟨.tilted, 1, 1, false, 157202416033293828⟩], by decide +kernel⟩
private def b51 : PaidBatch .empty 3 := ⟨[
  .shared 128 53 40 ⟨.tilted, 1, 1, false, 162730051278860836⟩,
  .point 129 44 45,
  .point 129 45 46], by decide +kernel⟩
private def b52 : PaidBatch .empty 3 := ⟨[
  .point 129 46 47,
  .point 129 47 48,
  .shared 129 48 36 ⟨.tilted, 0, 1, false, 136917662889962289⟩], by decide +kernel⟩
private def b53 : PaidBatch .empty 3 := ⟨[
  .shared 129 49 37 ⟨.tilted, 0, 1, false, 142207539122917686⟩,
  .shared 129 50 38 ⟨.tilted, 0, 1, false, 147571776271580425⟩,
  .shared 129 51 39 ⟨.tilted, 1, 1, false, 153008931645495015⟩], by decide +kernel⟩
private def b54 : PaidBatch .empty 3 := ⟨[
  .shared 129 52 40 ⟨.tilted, 1, 1, false, 158517562554205965⟩,
  .shared 129 53 41 ⟨.tilted, 1, 1, false, 164096226307257784⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 3) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 129 9 2 = true := by decide +kernel
private theorem i11 : checks tiles 129 11 2 = true := by decide +kernel
private theorem i13 : checks tiles 129 13 2 = true := by decide +kernel
private theorem i15 : checks tiles 129 15 2 = true := by decide +kernel
private theorem i17 : checks tiles 129 17 2 = true := by decide +kernel
private theorem i19 : checks tiles 129 19 2 = true := by decide +kernel
private theorem i21 : checks tiles 129 21 2 = true := by decide +kernel
private theorem i23 : checks tiles 129 23 2 = true := by decide +kernel
private theorem i25 : checks tiles 129 25 2 = true := by decide +kernel
private theorem i27 : checks tiles 129 27 2 = true := by decide +kernel
private theorem i29 : checks tiles 129 29 2 = true := by decide +kernel
private theorem i31 : checks tiles 129 31 2 = true := by decide +kernel
private theorem i33 : checks tiles 129 33 2 = true := by decide +kernel
private theorem i35 : checks tiles 129 35 2 = true := by decide +kernel
private theorem i37 : checks tiles 129 37 2 = true := by decide +kernel
private theorem i39 : checks tiles 129 39 2 = true := by decide +kernel
private theorem i41 : checks tiles 129 41 2 = true := by decide +kernel
private theorem i43 : checks tiles 129 43 2 = true := by decide +kernel
private theorem i45 : checks tiles 129 45 2 = true := by decide +kernel
private theorem i47 : checks tiles 129 47 2 = true := by decide +kernel
private theorem i49 : checks tiles 129 49 2 = true := by decide +kernel
private theorem i51 : checks tiles 129 51 2 = true := by decide +kernel
private theorem i53 : checks tiles 129 53 1 = true := by decide +kernel
def receipt : Certificate .empty 3 := ⟨batches, checks_join i9 (checks_join i11 (checks_join i13 (checks_join i15 (checks_join i17 (checks_join i19 (checks_join i21 (checks_join i23 (checks_join i25 (checks_join i27 (checks_join i29 (checks_join i31 (checks_join i33 (checks_join i35 (checks_join i37 (checks_join i39 (checks_join i41 (checks_join i43 (checks_join i45 (checks_join i47 (checks_join i49 (checks_join i51 i53)))))))))))))))))))))⟩
end Top3


end Low53At2389PriceTableEmpty3

import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty1
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .empty 1 := ⟨[
  .rectangle 1 3 129 3 1,
  .rectangle 2 5 17 6 1,
  .rectangle 2 4 65 4 1], by decide +kernel⟩
private def b1 : PaidBatch .empty 1 := ⟨[
  .rectangle 3 7 10 9 1,
  .rectangle 4 10 66 15 13,
  .rectangle 6 16 67 28 27], by decide +kernel⟩
private def b2 : PaidBatch .empty 1 := ⟨[
  .rectangle 10 29 69 41 30,
  .rectangle 11 7 18 9 2,
  .rectangle 14 42 69 53 31], by decide +kernel⟩
private def b3 : PaidBatch .empty 1 := ⟨[
  .rectangle 18 5 33 5 1,
  .rectangle 18 6 33 6 2,
  .rectangle 19 7 34 9 4], by decide +kernel⟩
private def b4 : PaidBatch .empty 1 := ⟨[
  .rectangle 34 5 65 6 3,
  .rectangle 35 7 66 9 7,
  .rectangle 66 4 129 4 2], by decide +kernel⟩
private def b5 : PaidBatch .empty 1 := ⟨[
  .rectangle 66 5 129 6 6,
  .rectangle 67 7 129 9 13,
  .rectangle 67 10 129 15 25], by decide +kernel⟩
private def b6 : PaidBatch .empty 1 := ⟨[
  .rectangle 68 16 129 22 34,
  .rectangle 68 23 129 28 38,
  .rectangle 70 29 99 35 34], by decide +kernel⟩
private def b7 : PaidBatch .empty 1 := ⟨[
  .rectangle 70 36 99 41 37,
  .rectangle 70 42 99 47 40,
  .rectangle 70 48 99 53 44], by decide +kernel⟩
private def b8 : PaidBatch .empty 1 := ⟨[
  .rectangle 100 51 107 53 45,
  .rectangle 100 42 114 44 42,
  .rectangle 100 45 114 47 45], by decide +kernel⟩
private def b9 : PaidBatch .empty 1 := ⟨[
  .rectangle 100 48 114 50 47,
  .rectangle 100 29 129 32 39,
  .rectangle 100 33 129 35 41], by decide +kernel⟩
private def b10 : PaidBatch .empty 1 := ⟨[
  .rectangle 100 36 129 38 43,
  .rectangle 100 39 129 41 46,
  .rectangle 108 51 114 52 47], by decide +kernel⟩
private def b11 : PaidBatch .empty 1 := ⟨[
  .rectangle 108 53 114 53 47,
  .rectangle 115 48 118 49 47,
  .rectangle 115 50 118 50 47], by decide +kernel⟩
private def b12 : PaidBatch .empty 1 := ⟨[
  .rectangle 115 51 118 51 47,
  .rectangle 115 52 118 52 48,
  .rectangle 115 53 118 53 49], by decide +kernel⟩
private def b13 : PaidBatch .empty 1 := ⟨[
  .rectangle 115 42 122 44 46,
  .rectangle 115 45 122 47 48,
  .rectangle 119 53 119 53 49], by decide +kernel⟩
private def b14 : PaidBatch .empty 1 := ⟨[
  .rectangle 119 50 120 50 48,
  .rectangle 119 52 120 52 49,
  .rectangle 119 48 122 48 47], by decide +kernel⟩
private def b15 : PaidBatch .empty 1 := ⟨[
  .rectangle 119 49 122 49 48,
  .rectangle 119 51 122 51 49,
  .point 120 53 31], by decide +kernel⟩
private def b16 : PaidBatch .empty 1 := ⟨[
  .rectangle 121 50 121 50 48,
  .point 121 52 31,
  .point 121 53 32], by decide +kernel⟩
private def b17 : PaidBatch .empty 1 := ⟨[
  .rectangle 122 50 122 50 49,
  .point 122 52 32,
  .point 122 53 32], by decide +kernel⟩
private def b18 : PaidBatch .empty 1 := ⟨[
  .rectangle 123 49 123 49 48,
  .point 123 51 31,
  .point 123 52 32], by decide +kernel⟩
private def b19 : PaidBatch .empty 1 := ⟨[
  .point 123 53 32,
  .rectangle 123 48 124 48 48,
  .rectangle 123 50 124 50 49], by decide +kernel⟩
private def b20 : PaidBatch .empty 1 := ⟨[
  .rectangle 123 47 126 47 48,
  .rectangle 123 42 129 43 47,
  .rectangle 123 44 129 44 47], by decide +kernel⟩
private def b21 : PaidBatch .empty 1 := ⟨[
  .rectangle 123 45 129 45 47,
  .rectangle 123 46 129 46 48,
  .point 124 49 31], by decide +kernel⟩
private def b22 : PaidBatch .empty 1 := ⟨[
  .point 124 51 32,
  .point 124 52 32,
  .point 124 53 33], by decide +kernel⟩
private def b23 : PaidBatch .empty 1 := ⟨[
  .rectangle 125 48 125 48 48,
  .point 125 49 31,
  .point 125 50 31], by decide +kernel⟩
private def b24 : PaidBatch .empty 1 := ⟨[
  .point 125 51 32,
  .point 125 52 32,
  .point 125 53 33], by decide +kernel⟩
private def b25 : PaidBatch .empty 1 := ⟨[
  .point 126 48 31,
  .point 126 49 31,
  .point 126 50 32], by decide +kernel⟩
private def b26 : PaidBatch .empty 1 := ⟨[
  .point 126 51 32,
  .point 126 52 33,
  .point 126 53 33], by decide +kernel⟩
private def b27 : PaidBatch .empty 1 := ⟨[
  .rectangle 127 47 127 47 48,
  .point 127 48 31,
  .point 127 49 31], by decide +kernel⟩
private def b28 : PaidBatch .empty 1 := ⟨[
  .point 127 50 32,
  .point 127 51 33,
  .point 127 52 33], by decide +kernel⟩
private def b29 : PaidBatch .empty 1 := ⟨[
  .point 127 53 34,
  .point 128 47 31,
  .point 128 48 31], by decide +kernel⟩
private def b30 : PaidBatch .empty 1 := ⟨[
  .point 128 49 32,
  .point 128 50 32,
  .point 128 51 33], by decide +kernel⟩
private def b31 : PaidBatch .empty 1 := ⟨[
  .point 128 52 33,
  .point 128 53 34,
  .point 129 47 31], by decide +kernel⟩
private def b32 : PaidBatch .empty 1 := ⟨[
  .point 129 48 32,
  .point 129 49 32,
  .point 129 50 33], by decide +kernel⟩
private def b33 : PaidBatch .empty 1 := ⟨[
  .point 129 51 33,
  .point 129 52 34,
  .point 129 53 34], by decide +kernel⟩
private def batches : List (PaidBatch .empty 1) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 129 3 3 = true := by decide +kernel
private theorem i6 : checks tiles 129 6 3 = true := by decide +kernel
private theorem i9 : checks tiles 129 9 3 = true := by decide +kernel
private theorem i12 : checks tiles 129 12 3 = true := by decide +kernel
private theorem i15 : checks tiles 129 15 3 = true := by decide +kernel
private theorem i18 : checks tiles 129 18 3 = true := by decide +kernel
private theorem i21 : checks tiles 129 21 3 = true := by decide +kernel
private theorem i24 : checks tiles 129 24 3 = true := by decide +kernel
private theorem i27 : checks tiles 129 27 3 = true := by decide +kernel
private theorem i30 : checks tiles 129 30 3 = true := by decide +kernel
private theorem i33 : checks tiles 129 33 3 = true := by decide +kernel
private theorem i36 : checks tiles 129 36 3 = true := by decide +kernel
private theorem i39 : checks tiles 129 39 3 = true := by decide +kernel
private theorem i42 : checks tiles 129 42 3 = true := by decide +kernel
private theorem i45 : checks tiles 129 45 3 = true := by decide +kernel
private theorem i48 : checks tiles 129 48 3 = true := by decide +kernel
private theorem i51 : checks tiles 129 51 3 = true := by decide +kernel
def receipt : Certificate .empty 1 := ⟨batches, checks_join i3 (checks_join i6 (checks_join i9 (checks_join i12 (checks_join i15 (checks_join i18 (checks_join i21 (checks_join i24 (checks_join i27 (checks_join i30 (checks_join i33 (checks_join i36 (checks_join i39 (checks_join i42 (checks_join i45 (checks_join i48 i51)))))))))))))))⟩
end Top1


end Low53At2389PriceTableEmpty1

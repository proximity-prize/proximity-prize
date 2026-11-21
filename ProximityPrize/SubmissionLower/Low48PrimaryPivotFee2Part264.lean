import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part240

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s264 : directSlab w2 264 = 87539266408 := by decide +kernel
private theorem s265 : directSlab w2 265 = 87105033130 := by decide +kernel
private theorem s266 : directSlab w2 266 = 86670879008 := by decide +kernel
private theorem s267 : directSlab w2 267 = 86236410136 := by decide +kernel
private theorem s268 : directSlab w2 268 = 85802030880 := by decide +kernel
private theorem s269 : directSlab w2 269 = 85367345130 := by decide +kernel
private theorem s270 : directSlab w2 270 = 84932761124 := by decide +kernel
private theorem s271 : directSlab w2 271 = 84497879222 := by decide +kernel
private theorem s272 : directSlab w2 272 = 84063110244 := by decide +kernel
private theorem s273 : directSlab w2 273 = 83628053620 := by decide +kernel
private theorem s274 : directSlab w2 274 = 83193121460 := by decide +kernel
private theorem s275 : directSlab w2 275 = 82757910938 := by decide +kernel
private theorem s276 : directSlab w2 276 = 82322838088 := by decide +kernel
private theorem s277 : directSlab w2 277 = 81887496504 := by decide +kernel
private theorem s278 : directSlab w2 278 = 81452304852 := by decide +kernel
private theorem s279 : directSlab w2 279 = 81016855744 := by decide +kernel
private theorem s280 : directSlab w2 280 = 80581569188 := by decide +kernel
private theorem s281 : directSlab w2 281 = 80146035490 := by decide +kernel
private theorem s282 : directSlab w2 282 = 79710678632 := by decide +kernel
private theorem s283 : directSlab w2 283 = 79275085288 := by decide +kernel
private theorem s284 : directSlab w2 284 = 78839682124 := by decide +kernel
private theorem s285 : directSlab w2 285 = 78404054782 := by decide +kernel
private theorem s286 : directSlab w2 286 = 77968631320 := by decide +kernel
private theorem s287 : directSlab w2 287 = 77532995022 := by decide +kernel

theorem fee2Part264 : affineFeeChunk w2 264 24 = 1980932028334 :=
  affineFeeCertified_eq w2 264 [87539266408, 87105033130, 86670879008, 86236410136, 85802030880, 85367345130, 84932761124, 84497879222, 84063110244, 83628053620, 83193121460, 82757910938, 82322838088, 81887496504, 81452304852, 81016855744, 80581569188, 80146035490, 79710678632, 79275085288, 78839682124, 78404054782, 77968631320, 77532995022]
    ⟨s264, s265, s266, s267, s268, s269, s270, s271, s272, s273, s274, s275, s276, s277, s278, s279, s280, s281, s282, s283, s284, s285, s286, s287, True.intro⟩

end Low48PrimaryPivot

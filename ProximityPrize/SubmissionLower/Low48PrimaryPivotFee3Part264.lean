import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part240

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s264 : directSlab w3 264 = 14107697830 := by decide +kernel
private theorem s265 : directSlab w3 265 = 14021891968 := by decide +kernel
private theorem s266 : directSlab w3 266 = 13936354276 := by decide +kernel
private theorem s267 : directSlab w3 267 = 13850981590 := by decide +kernel
private theorem s268 : directSlab w3 268 = 13765878042 := by decide +kernel
private theorem s269 : directSlab w3 269 = 13680941220 := by decide +kernel
private theorem s270 : directSlab w3 270 = 13596274378 := by decide +kernel
private theorem s271 : directSlab w3 271 = 13511775728 := by decide +kernel
private theorem s272 : directSlab w3 272 = 13427548274 := by decide +kernel
private theorem s273 : directSlab w3 273 = 13343490348 := by decide +kernel
private theorem s274 : directSlab w3 274 = 13259704578 := by decide +kernel
private theorem s275 : directSlab w3 275 = 13176090050 := by decide +kernel
private theorem s276 : directSlab w3 276 = 13092748504 := by decide +kernel
private theorem s277 : directSlab w3 277 = 13009579660 := by decide +kernel
private theorem s278 : directSlab w3 278 = 12926685006 := by decide +kernel
private theorem s279 : directSlab w3 279 = 12843964374 := by decide +kernel
private theorem s280 : directSlab w3 280 = 12761518886 := by decide +kernel
private theorem s281 : directSlab w3 281 = 12679249126 := by decide +kernel
private theorem s282 : directSlab w3 282 = 12597255322 := by decide +kernel
private theorem s283 : directSlab w3 283 = 12515438698 := by decide +kernel
private theorem s284 : directSlab w3 284 = 12433899230 := by decide +kernel
private theorem s285 : directSlab w3 285 = 12352538248 := by decide +kernel
private theorem s286 : directSlab w3 286 = 12271455368 := by decide +kernel
private theorem s287 : directSlab w3 287 = 12190552674 := by decide +kernel

theorem fee3Part264 : affineFeeChunk w3 264 24 = 315353513378 :=
  affineFeeCertified_eq w3 264 [14107697830, 14021891968, 13936354276, 13850981590, 13765878042, 13680941220, 13596274378, 13511775728, 13427548274, 13343490348, 13259704578, 13176090050, 13092748504, 13009579660, 12926685006, 12843964374, 12761518886, 12679249126, 12597255322, 12515438698, 12433899230, 12352538248, 12271455368, 12190552674]
    ⟨s264, s265, s266, s267, s268, s269, s270, s271, s272, s273, s274, s275, s276, s277, s278, s279, s280, s281, s282, s283, s284, s285, s286, s287, True.intro⟩

end Low48PrimaryPivot

import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part408

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s432 : directSlab w3 432 = 3293886502 := by decide +kernel
private theorem s433 : directSlab w3 433 = 3250551954 := by decide +kernel
private theorem s434 : directSlab w3 434 = 3207412328 := by decide +kernel
private theorem s435 : directSlab w3 435 = 3164376024 := by decide +kernel
private theorem s436 : directSlab w3 436 = 3121535330 := by decide +kernel
private theorem s437 : directSlab w3 437 = 3078798272 := by decide +kernel
private theorem s438 : directSlab w3 438 = 3036258146 := by decide +kernel
private theorem s439 : directSlab w3 439 = 2993822584 := by decide +kernel
private theorem s440 : directSlab w3 440 = 2951585910 := by decide +kernel
private theorem s441 : directSlab w3 441 = 2909455346 := by decide +kernel
private theorem s442 : directSlab w3 442 = 2867526260 := by decide +kernel
private theorem s443 : directSlab w3 443 = 2825705446 := by decide +kernel
private theorem s444 : directSlab w3 444 = 2784089332 := by decide +kernel
private theorem s445 : directSlab w3 445 = 2742584248 := by decide +kernel
private theorem s446 : directSlab w3 446 = 2701287604 := by decide +kernel
private theorem s447 : directSlab w3 447 = 2660105116 := by decide +kernel
private theorem s448 : directSlab w3 448 = 2619135126 := by decide +kernel
private theorem s449 : directSlab w3 449 = 2578282710 := by decide +kernel
private theorem s450 : directSlab w3 450 = 2537647160 := by decide +kernel
private theorem s451 : directSlab w3 451 = 2497132894 := by decide +kernel
private theorem s452 : directSlab w3 452 = 2456840172 := by decide +kernel
private theorem s453 : directSlab w3 453 = 2416672738 := by decide +kernel
private theorem s454 : directSlab w3 454 = 2376731834 := by decide +kernel
private theorem s455 : directSlab w3 455 = 2336920514 := by decide +kernel

theorem fee3Part432 : affineFeeChunk w3 432 24 = 67408343550 :=
  affineFeeCertified_eq w3 432 [3293886502, 3250551954, 3207412328, 3164376024, 3121535330, 3078798272, 3036258146, 2993822584, 2951585910, 2909455346, 2867526260, 2825705446, 2784089332, 2742584248, 2701287604, 2660105116, 2619135126, 2578282710, 2537647160, 2497132894, 2456840172, 2416672738, 2376731834, 2336920514]
    ⟨s432, s433, s434, s435, s436, s437, s438, s439, s440, s441, s442, s443, s444, s445, s446, s447, s448, s449, s450, s451, s452, s453, s454, s455, True.intro⟩

end Low48PrimaryPivot

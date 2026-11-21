import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part384

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s408 : directSlab w3 408 = 4382283676 := by decide +kernel
private theorem s409 : directSlab w3 409 = 4334702646 := by decide +kernel
private theorem s410 : directSlab w3 410 = 4287385000 := by decide +kernel
private theorem s411 : directSlab w3 411 = 4240242398 := by decide +kernel
private theorem s412 : directSlab w3 412 = 4193356676 := by decide +kernel
private theorem s413 : directSlab w3 413 = 4146639172 := by decide +kernel
private theorem s414 : directSlab w3 414 = 4100171798 := by decide +kernel
private theorem s415 : directSlab w3 415 = 4053865298 := by decide +kernel
private theorem s416 : directSlab w3 416 = 4007802188 := by decide +kernel
private theorem s417 : directSlab w3 417 = 3961892362 := by decide +kernel
private theorem s418 : directSlab w3 418 = 3916218910 := by decide +kernel
private theorem s419 : directSlab w3 419 = 3870691754 := by decide +kernel
private theorem s420 : directSlab w3 420 = 3825394648 := by decide +kernel
private theorem s421 : directSlab w3 421 = 3780237356 := by decide +kernel
private theorem s422 : directSlab w3 422 = 3735280120 := by decide +kernel
private theorem s423 : directSlab w3 423 = 3690433674 := by decide +kernel
private theorem s424 : directSlab w3 424 = 3645785308 := by decide +kernel
private theorem s425 : directSlab w3 425 = 3601245756 := by decide +kernel
private theorem s426 : directSlab w3 426 = 3556902984 := by decide +kernel
private theorem s427 : directSlab w3 427 = 3512667458 := by decide +kernel
private theorem s428 : directSlab w3 428 = 3468628340 := by decide +kernel
private theorem s429 : directSlab w3 429 = 3424695306 := by decide +kernel
private theorem s430 : directSlab w3 430 = 3380957718 := by decide +kernel
private theorem s431 : directSlab w3 431 = 3337324676 := by decide +kernel

theorem fee3Part408 : affineFeeChunk w3 408 24 = 92454805222 :=
  affineFeeCertified_eq w3 408 [4382283676, 4334702646, 4287385000, 4240242398, 4193356676, 4146639172, 4100171798, 4053865298, 4007802188, 3961892362, 3916218910, 3870691754, 3825394648, 3780237356, 3735280120, 3690433674, 3645785308, 3601245756, 3556902984, 3512667458, 3468628340, 3424695306, 3380957718, 3337324676]
    ⟨s408, s409, s410, s411, s412, s413, s414, s415, s416, s417, s418, s419, s420, s421, s422, s423, s424, s425, s426, s427, s428, s429, s430, s431, True.intro⟩

end Low48PrimaryPivot

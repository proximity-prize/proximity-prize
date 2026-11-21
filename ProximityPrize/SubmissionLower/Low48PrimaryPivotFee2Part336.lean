import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part312

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s336 : directSlab w2 336 = 56351845734 := by decide +kernel
private theorem s337 : directSlab w2 337 = 55926421204 := by decide +kernel
private theorem s338 : directSlab w2 338 = 55501675376 := by decide +kernel
private theorem s339 : directSlab w2 339 = 55077123604 := by decide +kernel
private theorem s340 : directSlab w2 340 = 54653272600 := by decide +kernel
private theorem s341 : directSlab w2 341 = 54229635074 := by decide +kernel
private theorem s342 : directSlab w2 342 = 53806722286 := by decide +kernel
private theorem s343 : directSlab w2 343 = 53384043000 := by decide +kernel
private theorem s344 : directSlab w2 344 = 52962111708 := by decide +kernel
private theorem s345 : directSlab w2 345 = 52540435854 := by decide +kernel
private theorem s346 : directSlab w2 346 = 52119531844 := by decide +kernel
private theorem s347 : directSlab w2 347 = 51698904502 := by decide +kernel
private theorem s348 : directSlab w2 348 = 51279074758 := by decide +kernel
private theorem s349 : directSlab w2 349 = 50859543514 := by decide +kernel
private theorem s350 : directSlab w2 350 = 50440834908 := by decide +kernel
private theorem s351 : directSlab w2 351 = 50022448546 := by decide +kernel
private theorem s352 : directSlab w2 352 = 49604910456 := by decide +kernel
private theorem s353 : directSlab w2 353 = 49187717648 := by decide +kernel
private theorem s354 : directSlab w2 354 = 48771400650 := by decide +kernel
private theorem s355 : directSlab w2 355 = 48355452574 := by decide +kernel
private theorem s356 : directSlab w2 356 = 47940407132 := by decide +kernel
private theorem s357 : directSlab w2 357 = 47525756164 := by decide +kernel
private theorem s358 : directSlab w2 358 = 47112035248 := by decide +kernel
private theorem s359 : directSlab w2 359 = 46698733652 := by decide +kernel

theorem fee2Part336 : affineFeeChunk w2 336 24 = 1236050038036 :=
  affineFeeCertified_eq w2 336 [56351845734, 55926421204, 55501675376, 55077123604, 54653272600, 54229635074, 53806722286, 53384043000, 52962111708, 52540435854, 52119531844, 51698904502, 51279074758, 50859543514, 50440834908, 50022448546, 49604910456, 49187717648, 48771400650, 48355452574, 47940407132, 47525756164, 47112035248, 46698733652]
    ⟨s336, s337, s338, s339, s340, s341, s342, s343, s344, s345, s346, s347, s348, s349, s350, s351, s352, s353, s354, s355, s356, s357, s358, s359, True.intro⟩

end Low48PrimaryPivot

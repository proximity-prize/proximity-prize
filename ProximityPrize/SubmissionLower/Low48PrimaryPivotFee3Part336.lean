import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part312

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s336 : directSlab w3 336 = 8522883702 := by decide +kernel
private theorem s337 : directSlab w3 337 = 8454884856 := by decide +kernel
private theorem s338 : directSlab w3 338 = 8387219152 := by decide +kernel
private theorem s339 : directSlab w3 339 = 8319802182 := by decide +kernel
private theorem s340 : directSlab w3 340 = 8252720576 := by decide +kernel
private theorem s341 : directSlab w3 341 = 8185890504 := by decide +kernel
private theorem s342 : directSlab w3 342 = 8119397774 := by decide +kernel
private theorem s343 : directSlab w3 343 = 8053158860 := by decide +kernel
private theorem s344 : directSlab w3 344 = 7987259274 := by decide +kernel
private theorem s345 : directSlab w3 345 = 7921615518 := by decide +kernel
private theorem s346 : directSlab w3 346 = 7856312584 := by decide +kernel
private theorem s347 : directSlab w3 347 = 7791267478 := by decide +kernel
private theorem s348 : directSlab w3 348 = 7726564444 := by decide +kernel
private theorem s349 : directSlab w3 349 = 7662120718 := by decide +kernel
private theorem s350 : directSlab w3 350 = 7598020324 := by decide +kernel
private theorem s351 : directSlab w3 351 = 7534180448 := by decide +kernel
private theorem s352 : directSlab w3 352 = 7470684672 := by decide +kernel
private theorem s353 : directSlab w3 353 = 7407450610 := by decide +kernel
private theorem s354 : directSlab w3 354 = 7344561170 := by decide +kernel
private theorem s355 : directSlab w3 355 = 7281934122 := by decide +kernel
private theorem s356 : directSlab w3 356 = 7219652228 := by decide +kernel
private theorem s357 : directSlab w3 357 = 7157633136 := by decide +kernel
private theorem s358 : directSlab w3 358 = 7095959238 := by decide +kernel
private theorem s359 : directSlab w3 359 = 7034548534 := by decide +kernel

theorem fee3Part336 : affineFeeChunk w3 336 24 = 186385722104 :=
  affineFeeCertified_eq w3 336 [8522883702, 8454884856, 8387219152, 8319802182, 8252720576, 8185890504, 8119397774, 8053158860, 7987259274, 7921615518, 7856312584, 7791267478, 7726564444, 7662120718, 7598020324, 7534180448, 7470684672, 7407450610, 7344561170, 7281934122, 7219652228, 7157633136, 7095959238, 7034548534]
    ⟨s336, s337, s338, s339, s340, s341, s342, s343, s344, s345, s346, s347, s348, s349, s350, s351, s352, s353, s354, s355, s356, s357, s358, s359, True.intro⟩

end Low48PrimaryPivot

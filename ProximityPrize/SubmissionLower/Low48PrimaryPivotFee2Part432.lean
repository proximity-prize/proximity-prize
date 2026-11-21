import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part408

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s432 : directSlab w2 432 = 19324721056 := by decide +kernel
private theorem s433 : directSlab w2 433 = 19000736096 := by decide +kernel
private theorem s434 : directSlab w2 434 = 18679705506 := by decide +kernel
private theorem s435 : directSlab w2 435 = 18361028752 := by decide +kernel
private theorem s436 : directSlab w2 436 = 18045325862 := by decide +kernel
private theorem s437 : directSlab w2 437 = 17731996140 := by decide +kernel
private theorem s438 : directSlab w2 438 = 17421659452 := by decide +kernel
private theorem s439 : directSlab w2 439 = 17113714940 := by decide +kernel
private theorem s440 : directSlab w2 440 = 16808782308 := by decide +kernel
private theorem s441 : directSlab w2 441 = 16506260536 := by decide +kernel
private theorem s442 : directSlab w2 442 = 16206769166 := by decide +kernel
private theorem s443 : directSlab w2 443 = 15909707016 := by decide +kernel
private theorem s444 : directSlab w2 444 = 15615692800 := by decide +kernel
private theorem s445 : directSlab w2 445 = 15324118536 := by decide +kernel
private theorem s446 : directSlab w2 446 = 15035594212 := by decide +kernel
private theorem s447 : directSlab w2 447 = 14749509840 := by decide +kernel
private theorem s448 : directSlab w2 448 = 14466475408 := by decide +kernel
private theorem s449 : directSlab w2 449 = 14185880928 := by decide +kernel
private theorem s450 : directSlab w2 450 = 13908336388 := by decide +kernel
private theorem s451 : directSlab w2 451 = 13633231800 := by decide +kernel
private theorem s452 : directSlab w2 452 = 13361177152 := by decide +kernel
private theorem s453 : directSlab w2 453 = 13091562456 := by decide +kernel
private theorem s454 : directSlab w2 454 = 12824997700 := by decide +kernel
private theorem s455 : directSlab w2 455 = 12560872896 := by decide +kernel

theorem fee2Part432 : affineFeeChunk w2 432 24 = 379867856946 :=
  affineFeeCertified_eq w2 432 [19324721056, 19000736096, 18679705506, 18361028752, 18045325862, 17731996140, 17421659452, 17113714940, 16808782308, 16506260536, 16206769166, 15909707016, 15615692800, 15324118536, 15035594212, 14749509840, 14466475408, 14185880928, 13908336388, 13633231800, 13361177152, 13091562456, 12824997700, 12560872896]
    ⟨s432, s433, s434, s435, s436, s437, s438, s439, s440, s441, s442, s443, s444, s445, s446, s447, s448, s449, s450, s451, s452, s453, s454, s455, True.intro⟩

end Low48PrimaryPivot

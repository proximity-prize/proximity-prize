import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part480

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s504 : directSlab w2 504 = 2988941200 := by decide +kernel
private theorem s505 : directSlab w2 505 = 2862063696 := by decide +kernel
private theorem s506 : directSlab w2 506 = 2738236132 := by decide +kernel
private theorem s507 : directSlab w2 507 = 2616848520 := by decide +kernel
private theorem s508 : directSlab w2 508 = 2498510848 := by decide +kernel
private theorem s509 : directSlab w2 509 = 2382613128 := by decide +kernel
private theorem s510 : directSlab w2 510 = 2269765348 := by decide +kernel
private theorem s511 : directSlab w2 511 = 2159357520 := by decide +kernel
private theorem s512 : directSlab w2 512 = 2051999632 := by decide +kernel
private theorem s513 : directSlab w2 513 = 1947081696 := by decide +kernel
private theorem s514 : directSlab w2 514 = 1845213700 := by decide +kernel
private theorem s515 : directSlab w2 515 = 1745785656 := by decide +kernel
private theorem s516 : directSlab w2 516 = 1649407552 := by decide +kernel
private theorem s517 : directSlab w2 517 = 1555469400 := by decide +kernel
private theorem s518 : directSlab w2 518 = 1464581188 := by decide +kernel
private theorem s519 : directSlab w2 519 = 1376132928 := by decide +kernel
private theorem s520 : directSlab w2 520 = 1290734608 := by decide +kernel
private theorem s521 : directSlab w2 521 = 1207776240 := by decide +kernel
private theorem s522 : directSlab w2 522 = 1127867812 := by decide +kernel
private theorem s523 : directSlab w2 523 = 1050399336 := by decide +kernel
private theorem s524 : directSlab w2 524 = 975980800 := by decide +kernel
private theorem s525 : directSlab w2 525 = 904002216 := by decide +kernel
private theorem s526 : directSlab w2 526 = 835073572 := by decide +kernel
private theorem s527 : directSlab w2 527 = 768584880 := by decide +kernel

theorem fee2Part504 : affineFeeChunk w2 504 24 = 42312427608 :=
  affineFeeCertified_eq w2 504 [2988941200, 2862063696, 2738236132, 2616848520, 2498510848, 2382613128, 2269765348, 2159357520, 2051999632, 1947081696, 1845213700, 1745785656, 1649407552, 1555469400, 1464581188, 1376132928, 1290734608, 1207776240, 1127867812, 1050399336, 975980800, 904002216, 835073572, 768584880]
    ⟨s504, s505, s506, s507, s508, s509, s510, s511, s512, s513, s514, s515, s516, s517, s518, s519, s520, s521, s522, s523, s524, s525, s526, s527, True.intro⟩

end Low48PrimaryPivot

import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part24

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s48 : directSlab w3 48 = 36561366610 := by decide +kernel
private theorem s49 : directSlab w3 49 = 36444735508 := by decide +kernel
private theorem s50 : directSlab w3 50 = 36328251194 := by decide +kernel
private theorem s51 : directSlab w3 51 = 36211756392 := by decide +kernel
private theorem s52 : directSlab w3 52 = 36095409438 := by decide +kernel
private theorem s53 : directSlab w3 53 = 35979053808 := by decide +kernel
private theorem s54 : directSlab w3 54 = 35862847082 := by decide +kernel
private theorem s55 : directSlab w3 55 = 35746633242 := by decide +kernel
private theorem s56 : directSlab w3 56 = 35630569616 := by decide +kernel
private theorem s57 : directSlab w3 57 = 35514500436 := by decide +kernel
private theorem s58 : directSlab w3 58 = 35398582530 := by decide +kernel
private theorem s59 : directSlab w3 59 = 35282660882 := by decide +kernel
private theorem s60 : directSlab w3 60 = 35166891566 := by decide +kernel
private theorem s61 : directSlab w3 61 = 35051120070 := by decide +kernel
private theorem s62 : directSlab w3 62 = 34935502218 := by decide +kernel
private theorem s63 : directSlab w3 63 = 34819883746 := by decide +kernel
private theorem s64 : directSlab w3 64 = 34704419978 := by decide +kernel
private theorem s65 : directSlab w3 65 = 34588957404 := by decide +kernel
private theorem s66 : directSlab w3 66 = 34473650592 := by decide +kernel
private theorem s67 : directSlab w3 67 = 34358346538 := by decide +kernel
private theorem s68 : directSlab w3 68 = 34243199558 := by decide +kernel
private theorem s69 : directSlab w3 69 = 34128056896 := by decide +kernel
private theorem s70 : directSlab w3 70 = 34013072370 := by decide +kernel
private theorem s71 : directSlab w3 71 = 33898093976 := by decide +kernel

theorem fee3Part48 : affineFeeChunk w3 48 24 = 845437561650 :=
  affineFeeCertified_eq w3 48 [36561366610, 36444735508, 36328251194, 36211756392, 36095409438, 35979053808, 35862847082, 35746633242, 35630569616, 35514500436, 35398582530, 35282660882, 35166891566, 35051120070, 34935502218, 34819883746, 34704419978, 34588957404, 34473650592, 34358346538, 34243199558, 34128056896, 34013072370, 33898093976]
    ⟨s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, True.intro⟩

end Low48PrimaryPivot

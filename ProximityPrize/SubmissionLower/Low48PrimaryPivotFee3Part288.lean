import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part264

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s288 : directSlab w3 288 = 12109928878 := by decide +kernel
private theorem s289 : directSlab w3 289 = 12029486712 := by decide +kernel
private theorem s290 : directSlab w3 290 = 11949324638 := by decide +kernel
private theorem s291 : directSlab w3 291 = 11869345484 := by decide +kernel
private theorem s292 : directSlab w3 292 = 11789647362 := by decide +kernel
private theorem s293 : directSlab w3 293 = 11710133852 := by decide +kernel
private theorem s294 : directSlab w3 294 = 11630902154 := by decide +kernel
private theorem s295 : directSlab w3 295 = 11551856506 := by decide +kernel
private theorem s296 : directSlab w3 296 = 11473093856 := by decide +kernel
private theorem s297 : directSlab w3 297 = 11394518532 := by decide +kernel
private theorem s298 : directSlab w3 298 = 11316227138 := by decide +kernel
private theorem s299 : directSlab w3 299 = 11238124754 := by decide +kernel
private theorem s300 : directSlab w3 300 = 11160307066 := by decide +kernel
private theorem s301 : directSlab w3 301 = 11082679818 := by decide +kernel
private theorem s302 : directSlab w3 302 = 11005338446 := by decide +kernel
private theorem s303 : directSlab w3 303 = 10928188774 := by decide +kernel
private theorem s304 : directSlab w3 304 = 10851325902 := by decide +kernel
private theorem s305 : directSlab w3 305 = 10774656408 := by decide +kernel
private theorem s306 : directSlab w3 306 = 10698274464 := by decide +kernel
private theorem s307 : directSlab w3 307 = 10622087322 := by decide +kernel
private theorem s308 : directSlab w3 308 = 10546188902 := by decide +kernel
private theorem s309 : directSlab w3 309 = 10470486528 := by decide +kernel
private theorem s310 : directSlab w3 310 = 10395073794 := by decide +kernel
private theorem s311 : directSlab w3 311 = 10319858776 := by decide +kernel

theorem fee3Part288 : affineFeeChunk w3 288 24 = 268917056066 :=
  affineFeeCertified_eq w3 288 [12109928878, 12029486712, 11949324638, 11869345484, 11789647362, 11710133852, 11630902154, 11551856506, 11473093856, 11394518532, 11316227138, 11238124754, 11160307066, 11082679818, 11005338446, 10928188774, 10851325902, 10774656408, 10698274464, 10622087322, 10546188902, 10470486528, 10395073794, 10319858776]
    ⟨s288, s289, s290, s291, s292, s293, s294, s295, s296, s297, s298, s299, s300, s301, s302, s303, s304, s305, s306, s307, s308, s309, s310, s311, True.intro⟩

end Low48PrimaryPivot

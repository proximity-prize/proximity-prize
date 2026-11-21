import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part192

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s216 : directSlab w3 216 = 18466833084 := by decide +kernel
private theorem s217 : directSlab w3 217 = 18371404176 := by decide +kernel
private theorem s218 : directSlab w3 218 = 18276218174 := by decide +kernel
private theorem s219 : directSlab w3 219 = 18181159926 := by decide +kernel
private theorem s220 : directSlab w3 220 = 18086345610 := by decide +kernel
private theorem s221 : directSlab w3 221 = 17991660826 := by decide +kernel
private theorem s222 : directSlab w3 222 = 17897220938 := by decide +kernel
private theorem s223 : directSlab w3 223 = 17802912106 := by decide +kernel
private theorem s224 : directSlab w3 224 = 17708849442 := by decide +kernel
private theorem s225 : directSlab w3 225 = 17614919292 := by decide +kernel
private theorem s226 : directSlab w3 226 = 17521236328 := by decide +kernel
private theorem s227 : directSlab w3 227 = 17427687650 := by decide +kernel
private theorem s228 : directSlab w3 228 = 17334387106 := by decide +kernel
private theorem s229 : directSlab w3 229 = 17241222364 := by decide +kernel
private theorem s230 : directSlab w3 230 = 17148307022 := by decide +kernel
private theorem s231 : directSlab w3 231 = 17055528924 := by decide +kernel
private theorem s232 : directSlab w3 232 = 16963001238 := by decide +kernel
private theorem s233 : directSlab w3 233 = 16870612560 := by decide +kernel
private theorem s234 : directSlab w3 234 = 16778475226 := by decide +kernel
private theorem s235 : directSlab w3 235 = 16686478410 := by decide +kernel
private theorem s236 : directSlab w3 236 = 16594734196 := by decide +kernel
private theorem s237 : directSlab w3 237 = 16503131928 := by decide +kernel
private theorem s238 : directSlab w3 238 = 16411783266 := by decide +kernel
private theorem s239 : directSlab w3 239 = 16320578306 := by decide +kernel

theorem fee3Part216 : affineFeeChunk w3 216 24 = 417254688098 :=
  affineFeeCertified_eq w3 216 [18466833084, 18371404176, 18276218174, 18181159926, 18086345610, 17991660826, 17897220938, 17802912106, 17708849442, 17614919292, 17521236328, 17427687650, 17334387106, 17241222364, 17148307022, 17055528924, 16963001238, 16870612560, 16778475226, 16686478410, 16594734196, 16503131928, 16411783266, 16320578306]
    ⟨s216, s217, s218, s219, s220, s221, s222, s223, s224, s225, s226, s227, s228, s229, s230, s231, s232, s233, s234, s235, s236, s237, s238, s239, True.intro⟩

end Low48PrimaryPivot

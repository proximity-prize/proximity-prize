import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part192

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s216 : directSlab w2 216 = 108164088816 := by decide +kernel
private theorem s217 : directSlab w2 217 = 107739569454 := by decide +kernel
private theorem s218 : directSlab w2 218 = 107314975764 := by decide +kernel
private theorem s219 : directSlab w2 219 = 106889961504 := by decide +kernel
private theorem s220 : directSlab w2 220 = 106464874556 := by decide +kernel
private theorem s221 : directSlab w2 221 = 106039367030 := by decide +kernel
private theorem s222 : directSlab w2 222 = 105613790354 := by decide +kernel
private theorem s223 : directSlab w2 223 = 105187793532 := by decide +kernel
private theorem s224 : directSlab w2 224 = 104761730154 := by decide +kernel
private theorem s225 : directSlab w2 225 = 104335248696 := by decide +kernel
private theorem s226 : directSlab w2 226 = 103908703618 := by decide +kernel
private theorem s227 : directSlab w2 227 = 103481741542 := by decide +kernel
private theorem s228 : directSlab w2 228 = 103054720432 := by decide +kernel
private theorem s229 : directSlab w2 229 = 102627283732 := by decide +kernel
private theorem s230 : directSlab w2 230 = 102199791620 := by decide +kernel
private theorem s231 : directSlab w2 231 = 101771886964 := by decide +kernel
private theorem s232 : directSlab w2 232 = 101343930876 := by decide +kernel
private theorem s233 : directSlab w2 233 = 100915564326 := by decide +kernel
private theorem s234 : directSlab w2 234 = 100487151992 := by decide +kernel
private theorem s235 : directSlab w2 235 = 100058331620 := by decide +kernel
private theorem s236 : directSlab w2 236 = 99629470164 := by decide +kernel
private theorem s237 : directSlab w2 237 = 99200204746 := by decide +kernel
private theorem s238 : directSlab w2 238 = 98770903304 := by decide +kernel
private theorem s239 : directSlab w2 239 = 98341201010 := by decide +kernel

theorem fee2Part216 : affineFeeChunk w2 216 24 = 2478302285806 :=
  affineFeeCertified_eq w2 216 [108164088816, 107739569454, 107314975764, 106889961504, 106464874556, 106039367030, 105613790354, 105187793532, 104761730154, 104335248696, 103908703618, 103481741542, 103054720432, 102627283732, 102199791620, 101771886964, 101343930876, 100915564326, 100487151992, 100058331620, 99629470164, 99200204746, 98770903304, 98341201010]
    ⟨s216, s217, s218, s219, s220, s221, s222, s223, s224, s225, s226, s227, s228, s229, s230, s231, s232, s233, s234, s235, s236, s237, s238, s239, True.intro⟩

end Low48PrimaryPivot

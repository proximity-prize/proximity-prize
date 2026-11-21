import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part216

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s240 : directSlab w3 240 = 16229627870 := by decide +kernel
private theorem s241 : directSlab w3 241 = 16138822638 := by decide +kernel
private theorem s242 : directSlab w3 242 = 16048273182 := by decide +kernel
private theorem s243 : directSlab w3 243 = 15957870342 := by decide +kernel
private theorem s244 : directSlab w3 244 = 15867724274 := by decide +kernel
private theorem s245 : directSlab w3 245 = 15777726572 := by decide +kernel
private theorem s246 : directSlab w3 246 = 15687986544 := by decide +kernel
private theorem s247 : directSlab w3 247 = 15598396378 := by decide +kernel
private theorem s248 : directSlab w3 248 = 15509065130 := by decide +kernel
private theorem s249 : directSlab w3 249 = 15419885140 := by decide +kernel
private theorem s250 : directSlab w3 250 = 15330965058 := by decide +kernel
private theorem s251 : directSlab w3 251 = 15242197976 := by decide +kernel
private theorem s252 : directSlab w3 252 = 15153691690 := by decide +kernel
private theorem s253 : directSlab w3 253 = 15065339892 := by decide +kernel
private theorem s254 : directSlab w3 254 = 14977250126 := by decide +kernel
private theorem s255 : directSlab w3 255 = 14889316230 := by decide +kernel
private theorem s256 : directSlab w3 256 = 14801645348 := by decide +kernel
private theorem s257 : directSlab w3 257 = 14714132072 := by decide +kernel
private theorem s258 : directSlab w3 258 = 14626882682 := by decide +kernel
private theorem s259 : directSlab w3 259 = 14539792378 := by decide +kernel
private theorem s260 : directSlab w3 260 = 14452967190 := by decide +kernel
private theorem s261 : directSlab w3 261 = 14366302454 := by decide +kernel
private theorem s262 : directSlab w3 262 = 14279903810 := by decide +kernel
private theorem s263 : directSlab w3 263 = 14193667346 := by decide +kernel

theorem fee3Part240 : affineFeeChunk w3 240 24 = 364869432322 :=
  affineFeeCertified_eq w3 240 [16229627870, 16138822638, 16048273182, 15957870342, 15867724274, 15777726572, 15687986544, 15598396378, 15509065130, 15419885140, 15330965058, 15242197976, 15153691690, 15065339892, 14977250126, 14889316230, 14801645348, 14714132072, 14626882682, 14539792378, 14452967190, 14366302454, 14279903810, 14193667346]
    ⟨s240, s241, s242, s243, s244, s245, s246, s247, s248, s249, s250, s251, s252, s253, s254, s255, s256, s257, s258, s259, s260, s261, s262, s263, True.intro⟩

end Low48PrimaryPivot

import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part288

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s312 : directSlab w2 312 = 66665653648 := by decide +kernel
private theorem s313 : directSlab w2 313 = 66232584678 := by decide +kernel
private theorem s314 : directSlab w2 314 = 65799955728 := by decide +kernel
private theorem s315 : directSlab w2 315 = 65367315292 := by decide +kernel
private theorem s316 : directSlab w2 316 = 64935133976 := by decide +kernel
private theorem s317 : directSlab w2 317 = 64502957662 := by decide +kernel
private theorem s318 : directSlab w2 318 = 64071261236 := by decide +kernel
private theorem s319 : directSlab w2 319 = 63639586642 := by decide +kernel
private theorem s320 : directSlab w2 320 = 63208411756 := by decide +kernel
private theorem s321 : directSlab w2 321 = 62777277184 := by decide +kernel
private theorem s322 : directSlab w2 322 = 62346662500 := by decide +kernel
private theorem s323 : directSlab w2 323 = 61916105646 := by decide +kernel
private theorem s324 : directSlab w2 324 = 61486090528 := by decide +kernel
private theorem s325 : directSlab w2 325 = 61056151100 := by decide +kernel
private theorem s326 : directSlab w2 326 = 60626774308 := by decide +kernel
private theorem s327 : directSlab w2 327 = 60197492716 := by decide +kernel
private theorem s328 : directSlab w2 328 = 59768795020 := by decide +kernel
private theorem s329 : directSlab w2 329 = 59340211070 := by decide +kernel
private theorem s330 : directSlab w2 330 = 58912233944 := by decide +kernel
private theorem s331 : directSlab w2 331 = 58484389452 := by decide +kernel
private theorem s332 : directSlab w2 332 = 58057173764 := by decide +kernel
private theorem s333 : directSlab w2 333 = 57630111250 := by decide +kernel
private theorem s334 : directSlab w2 334 = 57203699880 := by decide +kernel
private theorem s335 : directSlab w2 335 = 56777444192 := by decide +kernel

theorem fee2Part312 : affineFeeChunk w2 312 24 = 1481003473172 :=
  affineFeeCertified_eq w2 312 [66665653648, 66232584678, 65799955728, 65367315292, 64935133976, 64502957662, 64071261236, 63639586642, 63208411756, 62777277184, 62346662500, 61916105646, 61486090528, 61056151100, 60626774308, 60197492716, 59768795020, 59340211070, 58912233944, 58484389452, 58057173764, 57630111250, 57203699880, 56777444192]
    ⟨s312, s313, s314, s315, s316, s317, s318, s319, s320, s321, s322, s323, s324, s325, s326, s327, s328, s329, s330, s331, s332, s333, s334, s335, True.intro⟩

end Low48PrimaryPivot

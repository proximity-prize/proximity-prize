import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part264

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s288 : directSlab w2 288 = 77097577972 := by decide +kernel
private theorem s289 : directSlab w2 289 = 76661959772 := by decide +kernel
private theorem s290 : directSlab w2 290 = 76226575240 := by decide +kernel
private theorem s291 : directSlab w2 291 = 75791002894 := by decide +kernel
private theorem s292 : directSlab w2 292 = 75355678996 := by decide +kernel
private theorem s293 : directSlab w2 293 = 74920179656 := by decide +kernel
private theorem s294 : directSlab w2 294 = 74484945212 := by decide +kernel
private theorem s295 : directSlab w2 295 = 74049548040 := by decide +kernel
private theorem s296 : directSlab w2 296 = 73614431264 := by decide +kernel
private theorem s297 : directSlab w2 297 = 73179166126 := by decide +kernel
private theorem s298 : directSlab w2 298 = 72744197244 := by decide +kernel
private theorem s299 : directSlab w2 299 = 72309093400 := by decide +kernel
private theorem s300 : directSlab w2 300 = 71874303340 := by decide +kernel
private theorem s301 : directSlab w2 301 = 71439392062 := by decide +kernel
private theorem s302 : directSlab w2 302 = 71004811148 := by decide +kernel
private theorem s303 : directSlab w2 303 = 70570124410 := by decide +kernel
private theorem s304 : directSlab w2 304 = 70135784976 := by decide +kernel
private theorem s305 : directSlab w2 305 = 69701354148 := by decide +kernel
private theorem s306 : directSlab w2 306 = 69267289232 := by decide +kernel
private theorem s307 : directSlab w2 307 = 68833147694 := by decide +kernel
private theorem s308 : directSlab w2 308 = 68399389728 := by decide +kernel
private theorem s309 : directSlab w2 309 = 67965571564 := by decide +kernel
private theorem s310 : directSlab w2 310 = 67532154992 := by decide +kernel
private theorem s311 : directSlab w2 311 = 67098693680 := by decide +kernel

theorem fee2Part288 : affineFeeChunk w2 288 24 = 1730256372790 :=
  affineFeeCertified_eq w2 288 [77097577972, 76661959772, 76226575240, 75791002894, 75355678996, 74920179656, 74484945212, 74049548040, 73614431264, 73179166126, 72744197244, 72309093400, 71874303340, 71439392062, 71004811148, 70570124410, 70135784976, 69701354148, 69267289232, 68833147694, 68399389728, 67965571564, 67532154992, 67098693680]
    ⟨s288, s289, s290, s291, s292, s293, s294, s295, s296, s297, s298, s299, s300, s301, s302, s303, s304, s305, s306, s307, s308, s309, s310, s311, True.intro⟩

end Low48PrimaryPivot

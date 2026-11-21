import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part456

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s480 : directSlab w2 480 = 6853825168 := by decide +kernel
private theorem s481 : directSlab w2 481 = 6661068960 := by decide +kernel
private theorem s482 : directSlab w2 482 = 6471362692 := by decide +kernel
private theorem s483 : directSlab w2 483 = 6284096376 := by decide +kernel
private theorem s484 : directSlab w2 484 = 6099880000 := by decide +kernel
private theorem s485 : directSlab w2 485 = 5918103576 := by decide +kernel
private theorem s486 : directSlab w2 486 = 5739377092 := by decide +kernel
private theorem s487 : directSlab w2 487 = 5563090560 := by decide +kernel
private theorem s488 : directSlab w2 488 = 5389853968 := by decide +kernel
private theorem s489 : directSlab w2 489 = 5219057328 := by decide +kernel
private theorem s490 : directSlab w2 490 = 5051310628 := by decide +kernel
private theorem s491 : directSlab w2 491 = 4886003880 := by decide +kernel
private theorem s492 : directSlab w2 492 = 4723747072 := by decide +kernel
private theorem s493 : directSlab w2 493 = 4563930216 := by decide +kernel
private theorem s494 : directSlab w2 494 = 4407163300 := by decide +kernel
private theorem s495 : directSlab w2 495 = 4252836336 := by decide +kernel
private theorem s496 : directSlab w2 496 = 4101559312 := by decide +kernel
private theorem s497 : directSlab w2 497 = 3952722240 := by decide +kernel
private theorem s498 : directSlab w2 498 = 3806935108 := by decide +kernel
private theorem s499 : directSlab w2 499 = 3663587928 := by decide +kernel
private theorem s500 : directSlab w2 500 = 3523290688 := by decide +kernel
private theorem s501 : directSlab w2 501 = 3385433400 := by decide +kernel
private theorem s502 : directSlab w2 502 = 3250626052 := by decide +kernel
private theorem s503 : directSlab w2 503 = 3118258656 := by decide +kernel

theorem fee2Part480 : affineFeeChunk w2 480 24 = 116887120536 :=
  affineFeeCertified_eq w2 480 [6853825168, 6661068960, 6471362692, 6284096376, 6099880000, 5918103576, 5739377092, 5563090560, 5389853968, 5219057328, 5051310628, 4886003880, 4723747072, 4563930216, 4407163300, 4252836336, 4101559312, 3952722240, 3806935108, 3663587928, 3523290688, 3385433400, 3250626052, 3118258656]
    ⟨s480, s481, s482, s483, s484, s485, s486, s487, s488, s489, s490, s491, s492, s493, s494, s495, s496, s497, s498, s499, s500, s501, s502, s503, True.intro⟩

end Low48PrimaryPivot

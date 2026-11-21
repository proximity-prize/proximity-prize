import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part336

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s360 : directSlab w3 360 = 6973482820 := by decide +kernel
private theorem s361 : directSlab w3 361 = 6912680176 := by decide +kernel
private theorem s362 : directSlab w3 362 = 6852222328 := by decide +kernel
private theorem s363 : directSlab w3 363 = 6792027156 := by decide +kernel
private theorem s364 : directSlab w3 364 = 6732176092 := by decide +kernel
private theorem s365 : directSlab w3 365 = 6672587296 := by decide +kernel
private theorem s366 : directSlab w3 366 = 6613341676 := by decide +kernel
private theorem s367 : directSlab w3 367 = 6554357398 := by decide +kernel
private theorem s368 : directSlab w3 368 = 6495715374 := by decide +kernel
private theorem s369 : directSlab w3 369 = 6437333496 := by decide +kernel
private theorem s370 : directSlab w3 370 = 6379292458 := by decide +kernel
private theorem s371 : directSlab w3 371 = 6321510354 := by decide +kernel
private theorem s372 : directSlab w3 372 = 6264067432 := by decide +kernel
private theorem s373 : directSlab w3 373 = 6206881716 := by decide +kernel
private theorem s374 : directSlab w3 374 = 6150033532 := by decide +kernel
private theorem s375 : directSlab w3 375 = 6093440556 := by decide +kernel
private theorem s376 : directSlab w3 376 = 6037182970 := by decide +kernel
private theorem s377 : directSlab w3 377 = 5981178580 := by decide +kernel
private theorem s378 : directSlab w3 378 = 5925507194 := by decide +kernel
private theorem s379 : directSlab w3 379 = 5870086472 := by decide +kernel
private theorem s380 : directSlab w3 380 = 5814996378 := by decide +kernel
private theorem s381 : directSlab w3 381 = 5760154148 := by decide +kernel
private theorem s382 : directSlab w3 382 = 5705639678 := by decide +kernel
private theorem s383 : directSlab w3 383 = 5651370256 := by decide +kernel

theorem fee3Part360 : affineFeeChunk w3 360 24 = 151197265536 :=
  affineFeeCertified_eq w3 360 [6973482820, 6912680176, 6852222328, 6792027156, 6732176092, 6672587296, 6613341676, 6554357398, 6495715374, 6437333496, 6379292458, 6321510354, 6264067432, 6206881716, 6150033532, 6093440556, 6037182970, 5981178580, 5925507194, 5870086472, 5814996378, 5760154148, 5705639678, 5651370256]
    ⟨s360, s361, s362, s363, s364, s365, s366, s367, s368, s369, s370, s371, s372, s373, s374, s375, s376, s377, s378, s379, s380, s381, s382, s383, True.intro⟩

end Low48PrimaryPivot

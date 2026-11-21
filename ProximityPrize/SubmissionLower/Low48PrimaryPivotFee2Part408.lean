import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part384

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s408 : directSlab w2 408 = 27609239238 := by decide +kernel
private theorem s409 : directSlab w2 409 = 27250454464 := by decide +kernel
private theorem s410 : directSlab w2 410 = 26893533128 := by decide +kernel
private theorem s411 : directSlab w2 411 = 26537900416 := by decide +kernel
private theorem s412 : directSlab w2 412 = 26184174616 := by decide +kernel
private theorem s413 : directSlab w2 413 = 25831778558 := by decide +kernel
private theorem s414 : directSlab w2 414 = 25481334790 := by decide +kernel
private theorem s415 : directSlab w2 415 = 25132262484 := by decide +kernel
private theorem s416 : directSlab w2 416 = 24785187132 := by decide +kernel
private theorem s417 : directSlab w2 417 = 24439526852 := by decide +kernel
private theorem s418 : directSlab w2 418 = 24095908568 := by decide +kernel
private theorem s419 : directSlab w2 419 = 23753747640 := by decide +kernel
private theorem s420 : directSlab w2 420 = 23413674718 := by decide +kernel
private theorem s421 : directSlab w2 421 = 23058692156 := by decide +kernel
private theorem s422 : directSlab w2 422 = 22706540196 := by decide +kernel
private theorem s423 : directSlab w2 423 = 22356619276 := by decide +kernel
private theorem s424 : directSlab w2 424 = 22009550396 := by decide +kernel
private theorem s425 : directSlab w2 425 = 21664733832 := by decide +kernel
private theorem s426 : directSlab w2 426 = 21322790422 := by decide +kernel
private theorem s427 : directSlab w2 427 = 20983120280 := by decide +kernel
private theorem s428 : directSlab w2 428 = 20646344082 := by decide +kernel
private theorem s429 : directSlab w2 429 = 20311861780 := by decide +kernel
private theorem s430 : directSlab w2 430 = 19980293888 := by decide +kernel
private theorem s431 : directSlab w2 431 = 19651040196 := by decide +kernel

theorem fee2Part408 : affineFeeChunk w2 408 24 = 566100309108 :=
  affineFeeCertified_eq w2 408 [27609239238, 27250454464, 26893533128, 26537900416, 26184174616, 25831778558, 25481334790, 25132262484, 24785187132, 24439526852, 24095908568, 23753747640, 23413674718, 23058692156, 22706540196, 22356619276, 22009550396, 21664733832, 21322790422, 20983120280, 20646344082, 20311861780, 19980293888, 19651040196]
    ⟨s408, s409, s410, s411, s412, s413, s414, s415, s416, s417, s418, s419, s420, s421, s422, s423, s424, s425, s426, s427, s428, s429, s430, s431, True.intro⟩

end Low48PrimaryPivot

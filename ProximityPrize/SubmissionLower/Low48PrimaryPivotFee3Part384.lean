import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part360

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s384 : directSlab w3 384 = 5597425480 := by decide +kernel
private theorem s385 : directSlab w3 385 = 5543722420 := by decide +kernel
private theorem s386 : directSlab w3 386 = 5490340902 := by decide +kernel
private theorem s387 : directSlab w3 387 = 5437197498 := by decide +kernel
private theorem s388 : directSlab w3 388 = 5384372040 := by decide +kernel
private theorem s389 : directSlab w3 389 = 5331781078 := by decide +kernel
private theorem s390 : directSlab w3 390 = 5279504222 := by decide +kernel
private theorem s391 : directSlab w3 391 = 5227457726 := by decide +kernel
private theorem s392 : directSlab w3 392 = 5175721506 := by decide +kernel
private theorem s393 : directSlab w3 393 = 5124211242 := by decide +kernel
private theorem s394 : directSlab w3 394 = 5073006930 := by decide +kernel
private theorem s395 : directSlab w3 395 = 5022024154 := by decide +kernel
private theorem s396 : directSlab w3 396 = 4971342762 := by decide +kernel
private theorem s397 : directSlab w3 397 = 4920877970 := by decide +kernel
private theorem s398 : directSlab w3 398 = 4870710004 := by decide +kernel
private theorem s399 : directSlab w3 399 = 4820753430 := by decide +kernel
private theorem s400 : directSlab w3 400 = 4771088632 := by decide +kernel
private theorem s401 : directSlab w3 401 = 4721630004 := by decide +kernel
private theorem s402 : directSlab w3 402 = 4672457858 := by decide +kernel
private theorem s403 : directSlab w3 403 = 4623486142 := by decide +kernel
private theorem s404 : directSlab w3 404 = 4574795622 := by decide +kernel
private theorem s405 : directSlab w3 405 = 4526299524 := by decide +kernel
private theorem s406 : directSlab w3 406 = 4478078844 := by decide +kernel
private theorem s407 : directSlab w3 407 = 4430046562 := by decide +kernel

theorem fee3Part384 : affineFeeChunk w3 384 24 = 120068332552 :=
  affineFeeCertified_eq w3 384 [5597425480, 5543722420, 5490340902, 5437197498, 5384372040, 5331781078, 5279504222, 5227457726, 5175721506, 5124211242, 5073006930, 5022024154, 4971342762, 4920877970, 4870710004, 4820753430, 4771088632, 4721630004, 4672457858, 4623486142, 4574795622, 4526299524, 4478078844, 4430046562]
    ⟨s384, s385, s386, s387, s388, s389, s390, s391, s392, s393, s394, s395, s396, s397, s398, s399, s400, s401, s402, s403, s404, s405, s406, s407, True.intro⟩

end Low48PrimaryPivot

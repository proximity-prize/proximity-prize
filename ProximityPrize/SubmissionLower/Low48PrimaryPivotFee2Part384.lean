import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part360

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s384 : directSlab w2 384 = 36633621670 := by decide +kernel
private theorem s385 : directSlab w2 385 = 36243247804 := by decide +kernel
private theorem s386 : directSlab w2 386 = 35854256832 := by decide +kernel
private theorem s387 : directSlab w2 387 = 35466102844 := by decide +kernel
private theorem s388 : directSlab w2 388 = 35079368088 := by decide +kernel
private theorem s389 : directSlab w2 389 = 34693504202 := by decide +kernel
private theorem s390 : directSlab w2 390 = 34309097790 := by decide +kernel
private theorem s391 : directSlab w2 391 = 33925596736 := by decide +kernel
private theorem s392 : directSlab w2 392 = 33543590684 := by decide +kernel
private theorem s393 : directSlab w2 393 = 33162526390 := by decide +kernel
private theorem s394 : directSlab w2 394 = 32782995220 := by decide +kernel
private theorem s395 : directSlab w2 395 = 32404441502 := by decide +kernel
private theorem s396 : directSlab w2 396 = 32027460934 := by decide +kernel
private theorem s397 : directSlab w2 397 = 31651494114 := by decide +kernel
private theorem s398 : directSlab w2 398 = 31277139756 := by decide +kernel
private theorem s399 : directSlab w2 399 = 30903837354 := by decide +kernel
private theorem s400 : directSlab w2 400 = 30532187320 := by decide +kernel
private theorem s401 : directSlab w2 401 = 30161626744 := by decide +kernel
private theorem s402 : directSlab w2 402 = 29792760346 := by decide +kernel
private theorem s403 : directSlab w2 403 = 29425021510 := by decide +kernel
private theorem s404 : directSlab w2 404 = 29059017948 := by decide +kernel
private theorem s405 : directSlab w2 405 = 28694181964 := by decide +kernel
private theorem s406 : directSlab w2 406 = 28331122944 := by decide +kernel
private theorem s407 : directSlab w2 407 = 27969270812 := by decide +kernel

theorem fee2Part384 : affineFeeChunk w2 384 24 = 773923471508 :=
  affineFeeCertified_eq w2 384 [36633621670, 36243247804, 35854256832, 35466102844, 35079368088, 34693504202, 34309097790, 33925596736, 33543590684, 33162526390, 32782995220, 32404441502, 32027460934, 31651494114, 31277139756, 30903837354, 30532187320, 30161626744, 29792760346, 29425021510, 29059017948, 28694181964, 28331122944, 27969270812]
    ⟨s384, s385, s386, s387, s388, s389, s390, s391, s392, s393, s394, s395, s396, s397, s398, s399, s400, s401, s402, s403, s404, s405, s406, s407, True.intro⟩

end Low48PrimaryPivot

import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part432

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s456 : directSlab w2 456 = 12299798032 := by decide +kernel
private theorem s457 : directSlab w2 457 = 12041163120 := by decide +kernel
private theorem s458 : directSlab w2 458 = 11785578148 := by decide +kernel
private theorem s459 : directSlab w2 459 = 11532433128 := by decide +kernel
private theorem s460 : directSlab w2 460 = 11282338048 := by decide +kernel
private theorem s461 : directSlab w2 461 = 11034682920 := by decide +kernel
private theorem s462 : directSlab w2 462 = 10790077732 := by decide +kernel
private theorem s463 : directSlab w2 463 = 10547912496 := by decide +kernel
private theorem s464 : directSlab w2 464 = 10308797200 := by decide +kernel
private theorem s465 : directSlab w2 465 = 10072121856 := by decide +kernel
private theorem s466 : directSlab w2 466 = 9838496452 := by decide +kernel
private theorem s467 : directSlab w2 467 = 9607311000 := by decide +kernel
private theorem s468 : directSlab w2 468 = 9379175488 := by decide +kernel
private theorem s469 : directSlab w2 469 = 9153479928 := by decide +kernel
private theorem s470 : directSlab w2 470 = 8930834308 := by decide +kernel
private theorem s471 : directSlab w2 471 = 8710628640 := by decide +kernel
private theorem s472 : directSlab w2 472 = 8493472912 := by decide +kernel
private theorem s473 : directSlab w2 473 = 8278757136 := by decide +kernel
private theorem s474 : directSlab w2 474 = 8067091300 := by decide +kernel
private theorem s475 : directSlab w2 475 = 7857865416 := by decide +kernel
private theorem s476 : directSlab w2 476 = 7651689472 := by decide +kernel
private theorem s477 : directSlab w2 477 = 7447953480 := by decide +kernel
private theorem s478 : directSlab w2 478 = 7247267428 := by decide +kernel
private theorem s479 : directSlab w2 479 = 7049021328 := by decide +kernel

theorem fee2Part456 : affineFeeChunk w2 456 24 = 229407946968 :=
  affineFeeCertified_eq w2 456 [12299798032, 12041163120, 11785578148, 11532433128, 11282338048, 11034682920, 10790077732, 10547912496, 10308797200, 10072121856, 9838496452, 9607311000, 9379175488, 9153479928, 8930834308, 8710628640, 8493472912, 8278757136, 8067091300, 7857865416, 7651689472, 7447953480, 7247267428, 7049021328]
    ⟨s456, s457, s458, s459, s460, s461, s462, s463, s464, s465, s466, s467, s468, s469, s470, s471, s472, s473, s474, s475, s476, s477, s478, s479, True.intro⟩

end Low48PrimaryPivot

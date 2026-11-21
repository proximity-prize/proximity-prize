import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part480

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s504 : directSlab w3 504 = 677432230 := by decide +kernel
private theorem s505 : directSlab w3 505 = 651302144 := by decide +kernel
private theorem s506 : directSlab w3 506 = 625636914 := by decide +kernel
private theorem s507 : directSlab w3 507 = 600315670 := by decide +kernel
private theorem s508 : directSlab w3 508 = 575472628 := by decide +kernel
private theorem s509 : directSlab w3 509 = 550985768 := by decide +kernel
private theorem s510 : directSlab w3 510 = 526990766 := by decide +kernel
private theorem s511 : directSlab w3 511 = 503364434 := by decide +kernel
private theorem s512 : directSlab w3 512 = 480243926 := by decide +kernel
private theorem s513 : directSlab w3 513 = 457504870 := by decide +kernel
private theorem s514 : directSlab w3 514 = 435285914 := by decide +kernel
private theorem s515 : directSlab w3 515 = 413461484 := by decide +kernel
private theorem s516 : directSlab w3 516 = 392171740 := by decide +kernel
private theorem s517 : directSlab w3 517 = 371289890 := by decide +kernel
private theorem s518 : directSlab w3 518 = 350957622 := by decide +kernel
private theorem s519 : directSlab w3 519 = 331046908 := by decide +kernel
private theorem s520 : directSlab w3 520 = 311700982 := by decide +kernel
private theorem s521 : directSlab w3 521 = 292790564 := by decide +kernel
private theorem s522 : directSlab w3 522 = 274460450 := by decide +kernel
private theorem s523 : directSlab w3 523 = 256580090 := by decide +kernel
private theorem s524 : directSlab w3 524 = 239295860 := by decide +kernel
private theorem s525 : directSlab w3 525 = 222475922 := by decide +kernel
private theorem s526 : directSlab w3 526 = 206268242 := by decide +kernel
private theorem s527 : directSlab w3 527 = 190539672 := by decide +kernel

theorem fee3Part504 : affineFeeChunk w3 504 24 = 9937574690 :=
  affineFeeCertified_eq w3 504 [677432230, 651302144, 625636914, 600315670, 575472628, 550985768, 526990766, 503364434, 480243926, 457504870, 435285914, 413461484, 392171740, 371289890, 350957622, 331046908, 311700982, 292790564, 274460450, 256580090, 239295860, 222475922, 206268242, 190539672]
    ⟨s504, s505, s506, s507, s508, s509, s510, s511, s512, s513, s514, s515, s516, s517, s518, s519, s520, s521, s522, s523, s524, s525, s526, s527, True.intro⟩

end Low48PrimaryPivot

import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part504

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s528 : directSlab w2 528 = 705146128 := by decide +kernel
private theorem s529 : directSlab w2 529 = 644147328 := by decide +kernel
private theorem s530 : directSlab w2 530 = 586198468 := by decide +kernel
private theorem s531 : directSlab w2 531 = 530689560 := by decide +kernel
private theorem s532 : directSlab w2 532 = 478230592 := by decide +kernel
private theorem s533 : directSlab w2 533 = 428211576 := by decide +kernel
private theorem s534 : directSlab w2 534 = 381242500 := by decide +kernel
private theorem s535 : directSlab w2 535 = 336713376 := by decide +kernel
private theorem s536 : directSlab w2 536 = 295234192 := by decide +kernel
private theorem s537 : directSlab w2 537 = 256194960 := by decide +kernel
private theorem s538 : directSlab w2 538 = 220205668 := by decide +kernel
private theorem s539 : directSlab w2 539 = 186656328 := by decide +kernel
private theorem s540 : directSlab w2 540 = 156156928 := by decide +kernel
private theorem s541 : directSlab w2 541 = 128097480 := by decide +kernel
private theorem s542 : directSlab w2 542 = 103087972 := by decide +kernel
private theorem s543 : directSlab w2 543 = 80518416 := by decide +kernel
private theorem s544 : directSlab w2 544 = 60998800 := by decide +kernel
private theorem s545 : directSlab w2 545 = 43919136 := by decide +kernel
private theorem s546 : directSlab w2 546 = 29889412 := by decide +kernel
private theorem s547 : directSlab w2 547 = 18299640 := by decide +kernel
private theorem s548 : directSlab w2 548 = 9759808 := by decide +kernel
private theorem s549 : directSlab w2 549 = 3659928 := by decide +kernel
private theorem s550 : directSlab w2 550 = 609988 := by decide +kernel

theorem fee2Part528 : affineFeeChunk w2 528 23 = 5683868184 :=
  affineFeeCertified_eq w2 528 [705146128, 644147328, 586198468, 530689560, 478230592, 428211576, 381242500, 336713376, 295234192, 256194960, 220205668, 186656328, 156156928, 128097480, 103087972, 80518416, 60998800, 43919136, 29889412, 18299640, 9759808, 3659928, 609988]
    ⟨s528, s529, s530, s531, s532, s533, s534, s535, s536, s537, s538, s539, s540, s541, s542, s543, s544, s545, s546, s547, s548, s549, s550, True.intro⟩

end Low48PrimaryPivot

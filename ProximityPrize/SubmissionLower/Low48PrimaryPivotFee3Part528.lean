import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part504

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s528 : directSlab w3 528 = 175439788 := by decide +kernel
private theorem s529 : directSlab w3 529 = 160834118 := by decide +kernel
private theorem s530 : directSlab w3 530 = 146873866 := by decide +kernel
private theorem s531 : directSlab w3 531 = 133423230 := by decide +kernel
private theorem s532 : directSlab w3 532 = 120635062 := by decide +kernel
private theorem s533 : directSlab w3 533 = 108372212 := by decide +kernel
private theorem s534 : directSlab w3 534 = 96789198 := by decide +kernel
private theorem s535 : directSlab w3 535 = 85747504 := by decide +kernel
private theorem s536 : directSlab w3 536 = 75403330 := by decide +kernel
private theorem s537 : directSlab w3 537 = 65616790 := by decide +kernel
private theorem s538 : directSlab w3 538 = 56545678 := by decide +kernel
private theorem s539 : directSlab w3 539 = 48048768 := by decide +kernel
private theorem s540 : directSlab w3 540 = 40285768 := by decide +kernel
private theorem s541 : directSlab w3 541 = 33114194 := by decide +kernel
private theorem s542 : directSlab w3 542 = 26695562 := by decide +kernel
private theorem s543 : directSlab w3 543 = 20886052 := by decide +kernel
private theorem s544 : directSlab w3 544 = 15847448 := by decide +kernel
private theorem s545 : directSlab w3 545 = 11428962 := by decide +kernel
private theorem s546 : directSlab w3 546 = 7789720 := by decide +kernel
private theorem s547 : directSlab w3 547 = 4776942 := by decide +kernel
private theorem s548 : directSlab w3 548 = 2551190 := by decide +kernel
private theorem s549 : directSlab w3 549 = 958108 := by decide +kernel
private theorem s550 : directSlab w3 550 = 159686 := by decide +kernel

theorem fee3Part528 : affineFeeChunk w3 528 23 = 1438223176 :=
  affineFeeCertified_eq w3 528 [175439788, 160834118, 146873866, 133423230, 120635062, 108372212, 96789198, 85747504, 75403330, 65616790, 56545678, 48048768, 40285768, 33114194, 26695562, 20886052, 15847448, 11428962, 7789720, 4776942, 2551190, 958108, 159686]
    ⟨s528, s529, s530, s531, s532, s533, s534, s535, s536, s537, s538, s539, s540, s541, s542, s543, s544, s545, s546, s547, s548, s549, s550, True.intro⟩

end Low48PrimaryPivot

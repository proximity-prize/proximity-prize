import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part456

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s480 : directSlab w3 480 = 1409132854 := by decide +kernel
private theorem s481 : directSlab w3 481 = 1375069764 := by decide +kernel
private theorem s482 : directSlab w3 482 = 1341335528 := by decide +kernel
private theorem s483 : directSlab w3 483 = 1307821744 := by decide +kernel
private theorem s484 : directSlab w3 484 = 1274646444 := by decide +kernel
private theorem s485 : directSlab w3 485 = 1241700282 := by decide +kernel
private theorem s486 : directSlab w3 486 = 1209102544 := by decide +kernel
private theorem s487 : directSlab w3 487 = 1176742922 := by decide +kernel
private theorem s488 : directSlab w3 488 = 1144741974 := by decide +kernel
private theorem s489 : directSlab w3 489 = 1112988412 := by decide +kernel
private theorem s490 : directSlab w3 490 = 1081604084 := by decide +kernel
private theorem s491 : directSlab w3 491 = 1050476704 := by decide +kernel
private theorem s492 : directSlab w3 492 = 1019729428 := by decide +kernel
private theorem s493 : directSlab w3 493 = 989248956 := by decide +kernel
private theorem s494 : directSlab w3 494 = 959159766 := by decide +kernel
private theorem s495 : directSlab w3 495 = 929347528 := by decide +kernel
private theorem s496 : directSlab w3 496 = 899938060 := by decide +kernel
private theorem s497 : directSlab w3 497 = 870815986 := by decide +kernel
private theorem s498 : directSlab w3 498 = 842108480 := by decide +kernel
private theorem s499 : directSlab w3 499 = 813699100 := by decide +kernel
private theorem s500 : directSlab w3 500 = 785716396 := by decide +kernel
private theorem s501 : directSlab w3 501 = 758042844 := by decide +kernel
private theorem s502 : directSlab w3 502 = 730808386 := by decide +kernel
private theorem s503 : directSlab w3 503 = 703894398 := by decide +kernel

theorem fee3Part480 : affineFeeChunk w3 480 24 = 25027872584 :=
  affineFeeCertified_eq w3 480 [1409132854, 1375069764, 1341335528, 1307821744, 1274646444, 1241700282, 1209102544, 1176742922, 1144741974, 1112988412, 1081604084, 1050476704, 1019729428, 989248956, 959159766, 929347528, 899938060, 870815986, 842108480, 813699100, 785716396, 758042844, 730808386, 703894398]
    ⟨s480, s481, s482, s483, s484, s485, s486, s487, s488, s489, s490, s491, s492, s493, s494, s495, s496, s497, s498, s499, s500, s501, s502, s503, True.intro⟩

end Low48PrimaryPivot

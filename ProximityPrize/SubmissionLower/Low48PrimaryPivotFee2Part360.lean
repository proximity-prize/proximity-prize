import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part336

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s360 : directSlab w2 360 = 46286391430 := by decide +kernel
private theorem s361 : directSlab w2 361 = 45874493976 := by decide +kernel
private theorem s362 : directSlab w2 362 = 45463584504 := by decide +kernel
private theorem s363 : directSlab w2 363 = 45053147160 := by decide +kernel
private theorem s364 : directSlab w2 364 = 44643727000 := by decide +kernel
private theorem s365 : directSlab w2 365 = 44234805622 := by decide +kernel
private theorem s366 : directSlab w2 366 = 43826932534 := by decide +kernel
private theorem s367 : directSlab w2 367 = 43419585484 := by decide +kernel
private theorem s368 : directSlab w2 368 = 43013317116 := by decide +kernel
private theorem s369 : directSlab w2 369 = 42607603954 := by decide +kernel
private theorem s370 : directSlab w2 370 = 42203000460 := by decide +kernel
private theorem s371 : directSlab w2 371 = 41798980634 := by decide +kernel
private theorem s372 : directSlab w2 372 = 41396103366 := by decide +kernel
private theorem s373 : directSlab w2 373 = 40993838830 := by decide +kernel
private theorem s374 : directSlab w2 374 = 40592749028 := by decide +kernel
private theorem s375 : directSlab w2 375 = 40192302934 := by decide +kernel
private theorem s376 : directSlab w2 376 = 39793064344 := by decide +kernel
private theorem s377 : directSlab w2 377 = 39394499732 := by decide +kernel
private theorem s378 : directSlab w2 378 = 38997177298 := by decide +kernel
private theorem s379 : directSlab w2 379 = 38600559714 := by decide +kernel
private theorem s380 : directSlab w2 380 = 38205218268 := by decide +kernel
private theorem s381 : directSlab w2 381 = 37810614456 := by decide +kernel
private theorem s382 : directSlab w2 382 = 37417321336 := by decide +kernel
private theorem s383 : directSlab w2 383 = 37024797928 := by decide +kernel

theorem fee2Part360 : affineFeeChunk w2 360 24 = 998843817108 :=
  affineFeeCertified_eq w2 360 [46286391430, 45874493976, 45463584504, 45053147160, 44643727000, 44234805622, 43826932534, 43419585484, 43013317116, 42607603954, 42203000460, 41798980634, 41396103366, 40993838830, 40592749028, 40192302934, 39793064344, 39394499732, 38997177298, 38600559714, 38205218268, 37810614456, 37417321336, 37024797928]
    ⟨s360, s361, s362, s363, s364, s365, s366, s367, s368, s369, s370, s371, s372, s373, s374, s375, s376, s377, s378, s379, s380, s381, s382, s383, True.intro⟩

end Low48PrimaryPivot

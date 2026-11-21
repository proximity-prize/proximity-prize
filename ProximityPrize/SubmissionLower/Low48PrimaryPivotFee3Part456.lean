import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part432

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s456 : directSlab w3 456 = 2297341020 := by decide +kernel
private theorem s457 : directSlab w3 457 = 2257895700 := by decide +kernel
private theorem s458 : directSlab w3 458 = 2218687812 := by decide +kernel
private theorem s459 : directSlab w3 459 = 2179618978 := by decide +kernel
private theorem s460 : directSlab w3 460 = 2140793492 := by decide +kernel
private theorem s461 : directSlab w3 461 = 2102112234 := by decide +kernel
private theorem s462 : directSlab w3 462 = 2063680550 := by decide +kernel
private theorem s463 : directSlab w3 463 = 2025398560 := by decide +kernel
private theorem s464 : directSlab w3 464 = 1987372678 := by decide +kernel
private theorem s465 : directSlab w3 465 = 1949502250 := by decide +kernel
private theorem s466 : directSlab w3 466 = 1911894774 := by decide +kernel
private theorem s467 : directSlab w3 467 = 1874448804 := by decide +kernel
private theorem s468 : directSlab w3 468 = 1837272940 := by decide +kernel
private theorem s469 : directSlab w3 469 = 1800264926 := by decide +kernel
private theorem s470 : directSlab w3 470 = 1763534482 := by decide +kernel
private theorem s471 : directSlab w3 471 = 1726978524 := by decide +kernel
private theorem s472 : directSlab w3 472 = 1690707910 := by decide +kernel
private theorem s473 : directSlab w3 473 = 1654618712 := by decide +kernel
private theorem s474 : directSlab w3 474 = 1618822940 := by decide +kernel
private theorem s475 : directSlab w3 475 = 1583215806 := by decide +kernel
private theorem s476 : directSlab w3 476 = 1547910490 := by decide +kernel
private theorem s477 : directSlab w3 477 = 1512801328 := by decide +kernel
private theorem s478 : directSlab w3 478 = 1478002686 := by decide +kernel
private theorem s479 : directSlab w3 479 = 1443408004 := by decide +kernel

theorem fee3Part456 : affineFeeChunk w3 456 24 = 44666285600 :=
  affineFeeCertified_eq w3 456 [2297341020, 2257895700, 2218687812, 2179618978, 2140793492, 2102112234, 2063680550, 2025398560, 1987372678, 1949502250, 1911894774, 1874448804, 1837272940, 1800264926, 1763534482, 1726978524, 1690707910, 1654618712, 1618822940, 1583215806, 1547910490, 1512801328, 1478002686, 1443408004]
    ⟨s456, s457, s458, s459, s460, s461, s462, s463, s464, s465, s466, s467, s468, s469, s470, s471, s472, s473, s474, s475, s476, s477, s478, s479, True.intro⟩

end Low48PrimaryPivot

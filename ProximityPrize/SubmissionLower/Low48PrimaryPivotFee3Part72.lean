import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part48

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s72 : directSlab w3 72 = 33783274778 := by decide +kernel
private theorem s73 : directSlab w3 73 = 33668463276 := by decide +kernel
private theorem s74 : directSlab w3 74 = 33553812282 := by decide +kernel
private theorem s75 : directSlab w3 75 = 33439170546 := by decide +kernel
private theorem s76 : directSlab w3 76 = 33324690380 := by decide +kernel
private theorem s77 : directSlab w3 77 = 33210221288 := by decide +kernel
private theorem s78 : directSlab w3 78 = 33095914826 := by decide +kernel
private theorem s79 : directSlab w3 79 = 32981621002 := by decide +kernel
private theorem s80 : directSlab w3 80 = 32867491122 := by decide +kernel
private theorem s81 : directSlab w3 81 = 32753375442 := by decide +kernel
private theorem s82 : directSlab w3 82 = 32639424770 := by decide +kernel
private theorem s83 : directSlab w3 83 = 32525490114 := by decide +kernel
private theorem s84 : directSlab w3 84 = 32411721526 := by decide +kernel
private theorem s85 : directSlab w3 85 = 32297970520 := by decide +kernel
private theorem s86 : directSlab w3 86 = 32184386896 := by decide +kernel
private theorem s87 : directSlab w3 87 = 32070822418 := by decide +kernel
private theorem s88 : directSlab w3 88 = 31957426386 := by decide +kernel
private theorem s89 : directSlab w3 89 = 31844051316 := by decide +kernel
private theorem s90 : directSlab w3 90 = 31730845754 := by decide +kernel
private theorem s91 : directSlab w3 91 = 31617662720 := by decide +kernel
private theorem s92 : directSlab w3 92 = 31504650510 := by decide +kernel
private theorem s93 : directSlab w3 93 = 31391662392 := by decide +kernel
private theorem s94 : directSlab w3 94 = 31278846162 := by decide +kernel
private theorem s95 : directSlab w3 95 = 31166055842 := by decide +kernel

theorem fee3Part72 : affineFeeChunk w3 72 24 = 779299052268 :=
  affineFeeCertified_eq w3 72 [33783274778, 33668463276, 33553812282, 33439170546, 33324690380, 33210221288, 33095914826, 32981621002, 32867491122, 32753375442, 32639424770, 32525490114, 32411721526, 32297970520, 32184386896, 32070822418, 31957426386, 31844051316, 31730845754, 31617662720, 31504650510, 31391662392, 31278846162, 31166055842]
    ⟨s72, s73, s74, s75, s76, s77, s78, s79, s80, s81, s82, s83, s84, s85, s86, s87, s88, s89, s90, s91, s92, s93, s94, s95, True.intro⟩

end Low48PrimaryPivot

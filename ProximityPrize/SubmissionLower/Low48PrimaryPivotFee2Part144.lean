import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part120

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s144 : directSlab w2 144 = 138264142344 := by decide +kernel
private theorem s145 : directSlab w2 145 = 137847837074 := by decide +kernel
private theorem s146 : directSlab w2 146 = 137431753766 := by decide +kernel
private theorem s147 : directSlab w2 147 = 137015599942 := by decide +kernel
private theorem s148 : directSlab w2 148 = 136599657764 := by decide +kernel
private theorem s149 : directSlab w2 149 = 136183633352 := by decide +kernel
private theorem s150 : directSlab w2 150 = 135767811500 := by decide +kernel
private theorem s151 : directSlab w2 151 = 135351895598 := by decide +kernel
private theorem s152 : directSlab w2 152 = 134936171782 := by decide +kernel
private theorem s153 : directSlab w2 153 = 134520343314 := by decide +kernel
private theorem s154 : directSlab w2 154 = 134104696378 := by decide +kernel
private theorem s155 : directSlab w2 155 = 133688932782 := by decide +kernel
private theorem s156 : directSlab w2 156 = 133273341394 := by decide +kernel
private theorem s157 : directSlab w2 157 = 132857621242 := by decide +kernel
private theorem s158 : directSlab w2 158 = 132442062586 := by decide +kernel
private theorem s159 : directSlab w2 159 = 132026364274 := by decide +kernel
private theorem s160 : directSlab w2 160 = 131610816666 := by decide +kernel
private theorem s161 : directSlab w2 161 = 131195117106 := by decide +kernel
private theorem s162 : directSlab w2 162 = 130779558688 := by decide +kernel
private theorem s163 : directSlab w2 163 = 130363835924 := by decide +kernel
private theorem s164 : directSlab w2 164 = 129948243352 := by decide +kernel
private theorem s165 : directSlab w2 165 = 129532475254 := by decide +kernel
private theorem s166 : directSlab w2 166 = 129116826318 := by decide +kernel
private theorem s167 : directSlab w2 167 = 128700989270 := by decide +kernel

theorem fee2Part144 : affineFeeChunk w2 144 24 = 3203559727670 :=
  affineFeeCertified_eq w2 144 [138264142344, 137847837074, 137431753766, 137015599942, 136599657764, 136183633352, 135767811500, 135351895598, 134936171782, 134520343314, 134104696378, 133688932782, 133273341394, 132857621242, 132442062586, 132026364274, 131610816666, 131195117106, 130779558688, 130363835924, 129948243352, 129532475254, 129116826318, 128700989270]
    ⟨s144, s145, s146, s147, s148, s149, s150, s151, s152, s153, s154, s155, s156, s157, s158, s159, s160, s161, s162, s163, s164, s165, s166, s167, True.intro⟩

end Low48PrimaryPivot

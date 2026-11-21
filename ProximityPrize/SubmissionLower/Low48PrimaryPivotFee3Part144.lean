import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part120

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s144 : directSlab w3 144 = 25777189874 := by decide +kernel
private theorem s145 : directSlab w3 145 = 25670252916 := by decide +kernel
private theorem s146 : directSlab w3 146 = 25563517856 := by decide +kernel
private theorem s147 : directSlab w3 147 = 25456851522 := by decide +kernel
private theorem s148 : directSlab w3 148 = 25350388158 := by decide +kernel
private theorem s149 : directSlab w3 149 = 25243995344 := by decide +kernel
private theorem s150 : directSlab w3 150 = 25137806570 := by decide +kernel
private theorem s151 : directSlab w3 151 = 25031689920 := by decide +kernel
private theorem s152 : directSlab w3 152 = 24925778634 := by decide +kernel
private theorem s153 : directSlab w3 153 = 24819941044 := by decide +kernel
private theorem s154 : directSlab w3 154 = 24714309890 := by decide +kernel
private theorem s155 : directSlab w3 155 = 24608754258 := by decide +kernel
private theorem s156 : directSlab w3 156 = 24503406132 := by decide +kernel
private theorem s157 : directSlab w3 157 = 24398135104 := by decide +kernel
private theorem s158 : directSlab w3 158 = 24293072906 := by decide +kernel
private theorem s159 : directSlab w3 159 = 24188089378 := by decide +kernel
private theorem s160 : directSlab w3 160 = 24083315754 := by decide +kernel
private theorem s161 : directSlab w3 161 = 23978622626 := by decide +kernel
private theorem s162 : directSlab w3 162 = 23874140474 := by decide +kernel
private theorem s163 : directSlab w3 163 = 23769740394 := by decide +kernel
private theorem s164 : directSlab w3 164 = 23665552614 := by decide +kernel
private theorem s165 : directSlab w3 165 = 23561448480 := by decide +kernel
private theorem s166 : directSlab w3 166 = 23457557720 := by decide +kernel
private theorem s167 : directSlab w3 167 = 23353752434 := by decide +kernel

theorem fee3Part144 : affineFeeChunk w3 144 24 = 589427310002 :=
  affineFeeCertified_eq w3 144 [25777189874, 25670252916, 25563517856, 25456851522, 25350388158, 25243995344, 25137806570, 25031689920, 24925778634, 24819941044, 24714309890, 24608754258, 24503406132, 24398135104, 24293072906, 24188089378, 24083315754, 23978622626, 23874140474, 23769740394, 23665552614, 23561448480, 23457557720, 23353752434]
    ⟨s144, s145, s146, s147, s148, s149, s150, s151, s152, s153, s154, s155, s156, s157, s158, s159, s160, s161, s162, s163, s164, s165, s166, s167, True.intro⟩

end Low48PrimaryPivot

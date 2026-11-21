import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part144

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s168 : directSlab w3 168 = 23250161594 := by decide +kernel
private theorem s169 : directSlab w3 169 = 23146657804 := by decide +kernel
private theorem s170 : directSlab w3 170 = 23043369786 := by decide +kernel
private theorem s171 : directSlab w3 171 = 22940170392 := by decide +kernel
private theorem s172 : directSlab w3 172 = 22837187846 := by decide +kernel
private theorem s173 : directSlab w3 173 = 22734295752 := by decide +kernel
private theorem s174 : directSlab w3 174 = 22631621578 := by decide +kernel
private theorem s175 : directSlab w3 175 = 22529039434 := by decide +kernel
private theorem s176 : directSlab w3 176 = 22426676536 := by decide +kernel
private theorem s177 : directSlab w3 177 = 22324407244 := by decide +kernel
private theorem s178 : directSlab w3 178 = 22222358274 := by decide +kernel
private theorem s179 : directSlab w3 179 = 22120404738 := by decide +kernel
private theorem s180 : directSlab w3 180 = 22018672594 := by decide +kernel
private theorem s181 : directSlab w3 181 = 21917037458 := by decide +kernel
private theorem s182 : directSlab w3 182 = 21815625038 := by decide +kernel
private theorem s183 : directSlab w3 183 = 21714311190 := by decide +kernel
private theorem s184 : directSlab w3 184 = 21613221126 := by decide +kernel
private theorem s185 : directSlab w3 185 = 21512231456 := by decide +kernel
private theorem s186 : directSlab w3 186 = 21411466624 := by decide +kernel
private theorem s187 : directSlab w3 187 = 21310803754 := by decide +kernel
private theorem s188 : directSlab w3 188 = 21210367038 := by decide +kernel
private theorem s189 : directSlab w3 189 = 21110033832 := by decide +kernel
private theorem s190 : directSlab w3 190 = 21009927842 := by decide +kernel
private theorem s191 : directSlab w3 191 = 20909927176 := by decide +kernel

theorem fee3Part168 : affineFeeChunk w3 168 24 = 529759976106 :=
  affineFeeCertified_eq w3 168 [23250161594, 23146657804, 23043369786, 22940170392, 22837187846, 22734295752, 22631621578, 22529039434, 22426676536, 22324407244, 22222358274, 22120404738, 22018672594, 21917037458, 21815625038, 21714311190, 21613221126, 21512231456, 21411466624, 21310803754, 21210367038, 21110033832, 21009927842, 20909927176]
    ⟨s168, s169, s170, s171, s172, s173, s174, s175, s176, s177, s178, s179, s180, s181, s182, s183, s184, s185, s186, s187, s188, s189, s190, s191, True.intro⟩

end Low48PrimaryPivot

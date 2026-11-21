import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part168

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s192 : directSlab w2 192 = 118277889094 := by decide +kernel
private theorem s193 : directSlab w2 193 = 117859009672 := by decide +kernel
private theorem s194 : directSlab w2 194 = 117440092804 := by decide +kernel
private theorem s195 : directSlab w2 195 = 117020807596 := by decide +kernel
private theorem s196 : directSlab w2 196 = 116601472624 := by decide +kernel
private theorem s197 : directSlab w2 197 = 116181755432 := by decide +kernel
private theorem s198 : directSlab w2 198 = 115761980218 := by decide +kernel
private theorem s199 : directSlab w2 199 = 115341814902 := by decide +kernel
private theorem s200 : directSlab w2 200 = 114921586544 := by decide +kernel
private theorem s201 : directSlab w2 201 = 114500962902 := by decide +kernel
private theorem s202 : directSlab w2 202 = 114080271864 := by decide +kernel
private theorem s203 : directSlab w2 203 = 113659179700 := by decide +kernel
private theorem s204 : directSlab w2 204 = 113238017760 := by decide +kernel
private theorem s205 : directSlab w2 205 = 112816449502 := by decide +kernel
private theorem s206 : directSlab w2 206 = 112394808446 := by decide +kernel
private theorem s207 : directSlab w2 207 = 111972757836 := by decide +kernel
private theorem s208 : directSlab w2 208 = 111550632072 := by decide +kernel
private theorem s209 : directSlab w2 209 = 111128092860 := by decide +kernel
private theorem s210 : directSlab w2 210 = 110705478112 := by decide +kernel
private theorem s211 : directSlab w2 211 = 110282446670 := by decide +kernel
private theorem s212 : directSlab w2 212 = 109859338668 := by decide +kernel
private theorem s213 : directSlab w2 213 = 109435812684 := by decide +kernel
private theorem s214 : directSlab w2 214 = 109012209782 := by decide +kernel
private theorem s215 : directSlab w2 215 = 108588186950 := by decide +kernel

theorem fee2Part192 : affineFeeChunk w2 192 24 = 2722631054694 :=
  affineFeeCertified_eq w2 192 [118277889094, 117859009672, 117440092804, 117020807596, 116601472624, 116181755432, 115761980218, 115341814902, 114921586544, 114500962902, 114080271864, 113659179700, 113238017760, 112816449502, 112394808446, 111972757836, 111550632072, 111128092860, 110705478112, 110282446670, 109859338668, 109435812684, 109012209782, 108588186950]
    ⟨s192, s193, s194, s195, s196, s197, s198, s199, s200, s201, s202, s203, s204, s205, s206, s207, s208, s209, s210, s211, s212, s213, s214, s215, True.intro⟩

end Low48PrimaryPivot

import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part144

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s168 : directSlab w2 168 = 128285261584 := by decide +kernel
private theorem s169 : directSlab w2 169 = 127869333104 := by decide +kernel
private theorem s170 : directSlab w2 170 = 127453502798 := by decide +kernel
private theorem s171 : directSlab w2 171 = 127037460228 := by decide +kernel
private theorem s172 : directSlab w2 172 = 126621504564 := by decide +kernel
private theorem s173 : directSlab w2 173 = 126205323762 := by decide +kernel
private theorem s174 : directSlab w2 174 = 125789219828 := by decide +kernel
private theorem s175 : directSlab w2 175 = 125372877784 := by decide +kernel
private theorem s176 : directSlab w2 176 = 124956601182 := by decide +kernel
private theorem s177 : directSlab w2 177 = 124540074712 := by decide +kernel
private theorem s178 : directSlab w2 178 = 124123602176 := by decide +kernel
private theorem s179 : directSlab w2 179 = 123706866600 := by decide +kernel
private theorem s180 : directSlab w2 180 = 123290174668 := by decide +kernel
private theorem s181 : directSlab w2 181 = 122873206418 := by decide +kernel
private theorem s182 : directSlab w2 182 = 122456270124 := by decide +kernel
private theorem s183 : directSlab w2 183 = 122039045434 := by decide +kernel
private theorem s184 : directSlab w2 184 = 121621840922 := by decide +kernel
private theorem s185 : directSlab w2 185 = 121204334522 := by decide +kernel
private theorem s186 : directSlab w2 186 = 120786837740 := by decide +kernel
private theorem s187 : directSlab w2 187 = 120369025470 := by decide +kernel
private theorem s188 : directSlab w2 188 = 119951210860 := by decide +kernel
private theorem s189 : directSlab w2 189 = 119533068364 := by decide +kernel
private theorem s190 : directSlab w2 190 = 119114911480 := by decide +kernel
private theorem s191 : directSlab w2 191 = 118696412896 := by decide +kernel

theorem fee2Part168 : affineFeeChunk w2 168 24 = 2963897967220 :=
  affineFeeCertified_eq w2 168 [128285261584, 127869333104, 127453502798, 127037460228, 126621504564, 126205323762, 125789219828, 125372877784, 124956601182, 124540074712, 124123602176, 123706866600, 123290174668, 122873206418, 122456270124, 122039045434, 121621840922, 121204334522, 120786837740, 120369025470, 119951210860, 119533068364, 119114911480, 118696412896]
    ⟨s168, s169, s170, s171, s172, s173, s174, s175, s176, s177, s178, s179, s180, s181, s182, s183, s184, s185, s186, s187, s188, s189, s190, s191, True.intro⟩

end Low48PrimaryPivot

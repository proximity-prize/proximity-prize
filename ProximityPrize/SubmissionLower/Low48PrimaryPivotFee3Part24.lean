import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part0

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s24 : directSlab w3 24 = 39378077258 := by decide +kernel
private theorem s25 : directSlab w3 25 = 39260027644 := by decide +kernel
private theorem s26 : directSlab w3 26 = 39142111136 := by decide +kernel
private theorem s27 : directSlab w3 27 = 39024164434 := by decide +kernel
private theorem s28 : directSlab w3 28 = 38906351894 := by decide +kernel
private theorem s29 : directSlab w3 29 = 38788510968 := by decide +kernel
private theorem s30 : directSlab w3 30 = 38670805258 := by decide +kernel
private theorem s31 : directSlab w3 31 = 38553072720 := by decide +kernel
private theorem s32 : directSlab w3 32 = 38435476706 := by decide +kernel
private theorem s33 : directSlab w3 33 = 38317855420 := by decide +kernel
private theorem s34 : directSlab w3 34 = 38200371714 := by decide +kernel
private theorem s35 : directSlab w3 35 = 38082864546 := by decide +kernel
private theorem s36 : directSlab w3 36 = 37965496012 := by decide +kernel
private theorem s37 : directSlab w3 37 = 37848105576 := by decide +kernel
private theorem s38 : directSlab w3 38 = 37730855082 := by decide +kernel
private theorem s39 : directSlab w3 39 = 37613584242 := by decide +kernel
private theorem s40 : directSlab w3 40 = 37496454402 := by decide +kernel
private theorem s41 : directSlab w3 41 = 37379306026 := by decide +kernel
private theorem s42 : directSlab w3 42 = 37262299706 := by decide +kernel
private theorem s43 : directSlab w3 43 = 37145276410 := by decide +kernel
private theorem s44 : directSlab w3 44 = 37028396478 := by decide +kernel
private theorem s45 : directSlab w3 45 = 36911501128 := by decide +kernel
private theorem s46 : directSlab w3 46 = 36794750200 := by decide +kernel
private theorem s47 : directSlab w3 47 = 36677985666 := by decide +kernel

theorem fee3Part24 : affineFeeChunk w3 24 24 = 912613700626 :=
  affineFeeCertified_eq w3 24 [39378077258, 39260027644, 39142111136, 39024164434, 38906351894, 38788510968, 38670805258, 38553072720, 38435476706, 38317855420, 38200371714, 38082864546, 37965496012, 37848105576, 37730855082, 37613584242, 37496454402, 37379306026, 37262299706, 37145276410, 37028396478, 36911501128, 36794750200, 36677985666]
    ⟨s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, True.intro⟩

end Low48PrimaryPivot

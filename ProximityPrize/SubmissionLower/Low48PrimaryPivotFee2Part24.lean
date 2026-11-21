import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part0

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s24 : directSlab w2 24 = 190450709452 := by decide +kernel
private theorem s25 : directSlab w2 25 = 189979697382 := by decide +kernel
private theorem s26 : directSlab w2 26 = 189509656344 := by decide +kernel
private theorem s27 : directSlab w2 27 = 189040345232 := by decide +kernel
private theorem s28 : directSlab w2 28 = 188572000190 := by decide +kernel
private theorem s29 : directSlab w2 29 = 188104379826 := by decide +kernel
private theorem s30 : directSlab w2 30 = 187637721638 := by decide +kernel
private theorem s31 : directSlab w2 31 = 187171782610 := by decide +kernel
private theorem s32 : directSlab w2 32 = 186706800314 := by decide +kernel
private theorem s33 : directSlab w2 33 = 186242532704 := by decide +kernel
private theorem s34 : directSlab w2 34 = 185779216138 := by decide +kernel
private theorem s35 : directSlab w2 35 = 185316608208 := by decide +kernel
private theorem s36 : directSlab w2 36 = 184854946702 := by decide +kernel
private theorem s37 : directSlab w2 37 = 184393987514 := by decide +kernel
private theorem s38 : directSlab w2 38 = 183933968580 := by decide +kernel
private theorem s39 : directSlab w2 39 = 183474646688 := by decide +kernel
private theorem s40 : directSlab w2 40 = 183016258636 := by decide +kernel
private theorem s41 : directSlab w2 41 = 182558560776 := by decide +kernel
private theorem s42 : directSlab w2 42 = 182101791410 := by decide +kernel
private theorem s43 : directSlab w2 43 = 181645705116 := by decide +kernel
private theorem s44 : directSlab w2 44 = 181190540420 := by decide +kernel
private theorem s45 : directSlab w2 45 = 180736052720 := by decide +kernel
private theorem s46 : directSlab w2 46 = 180282479478 := by decide +kernel
private theorem s47 : directSlab w2 47 = 179829575580 := by decide +kernel

theorem fee2Part24 : affineFeeChunk w2 24 24 = 4442529963658 :=
  affineFeeCertified_eq w2 24 [190450709452, 189979697382, 189509656344, 189040345232, 188572000190, 188104379826, 187637721638, 187171782610, 186706800314, 186242532704, 185779216138, 185316608208, 184854946702, 184393987514, 183933968580, 183474646688, 183016258636, 182558560776, 182101791410, 181645705116, 181190540420, 180736052720, 180282479478, 179829575580]
    ⟨s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, True.intro⟩

end Low48PrimaryPivot

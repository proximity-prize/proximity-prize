import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part24

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s48 : directSlab w2 48 = 179377580068 := by decide +kernel
private theorem s49 : directSlab w2 49 = 178926245980 := by decide +kernel
private theorem s50 : directSlab w2 50 = 178475812656 := by decide +kernel
private theorem s51 : directSlab w2 51 = 178026033878 := by decide +kernel
private theorem s52 : directSlab w2 52 = 177577147998 := by decide +kernel
private theorem s53 : directSlab w2 53 = 177128908212 := by decide +kernel
private theorem s54 : directSlab w2 54 = 176681554526 := by decide +kernel
private theorem s55 : directSlab w2 55 = 176234838212 := by decide +kernel
private theorem s56 : directSlab w2 56 = 175788999650 := by decide +kernel
private theorem s57 : directSlab w2 57 = 175343790782 := by decide +kernel
private theorem s58 : directSlab w2 58 = 174899451074 := by decide +kernel
private theorem s59 : directSlab w2 59 = 174455731806 := by decide +kernel
private theorem s60 : directSlab w2 60 = 174012874174 := by decide +kernel
private theorem s61 : directSlab w2 61 = 173570627460 := by decide +kernel
private theorem s62 : directSlab w2 62 = 173129233308 := by decide +kernel
private theorem s63 : directSlab w2 63 = 172688441594 := by decide +kernel
private theorem s64 : directSlab w2 64 = 172248493124 := by decide +kernel
private theorem s65 : directSlab w2 65 = 171809137038 := by decide +kernel
private theorem s66 : directSlab w2 66 = 171370615946 := by decide +kernel
private theorem s67 : directSlab w2 67 = 170932676914 := by decide +kernel
private theorem s68 : directSlab w2 68 = 170495563076 := by decide +kernel
private theorem s69 : directSlab w2 69 = 170059022018 := by decide +kernel
private theorem s70 : directSlab w2 70 = 169623296110 := by decide +kernel
private theorem s71 : directSlab w2 71 = 169188132126 := by decide +kernel

theorem fee2Part48 : affineFeeChunk w2 48 24 = 4182044207730 :=
  affineFeeCertified_eq w2 48 [179377580068, 178926245980, 178475812656, 178026033878, 177577147998, 177128908212, 176681554526, 176234838212, 175788999650, 175343790782, 174899451074, 174455731806, 174012874174, 173570627460, 173129233308, 172688441594, 172248493124, 171809137038, 171370615946, 170932676914, 170495563076, 170059022018, 169623296110, 169188132126]
    ⟨s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, True.intro⟩

end Low48PrimaryPivot

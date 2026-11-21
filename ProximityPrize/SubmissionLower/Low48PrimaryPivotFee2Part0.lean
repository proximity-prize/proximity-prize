import ProximityPrize.SubmissionLower.Low48PrimaryPivotFeeBase

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s0 : directSlab w2 0 = 202013767794 := by decide +kernel
private theorem s1 : directSlab w2 1 = 201521806472 := by decide +kernel
private theorem s2 : directSlab w2 2 = 201030851584 := by decide +kernel
private theorem s3 : directSlab w2 3 = 200540663546 := by decide +kernel
private theorem s4 : directSlab w2 4 = 200051479888 := by decide +kernel
private theorem s5 : directSlab w2 5 = 199563061038 := by decide +kernel
private theorem s6 : directSlab w2 6 = 199075645582 := by decide +kernel
private theorem s7 : directSlab w2 7 = 198588992622 := by decide +kernel
private theorem s8 : directSlab w2 8 = 198103340518 := by decide +kernel
private theorem s9 : directSlab w2 9 = 197618449642 := by decide +kernel
private theorem s10 : directSlab w2 10 = 197134556840 := by decide +kernel
private theorem s11 : directSlab w2 11 = 196651422422 := by decide +kernel
private theorem s12 : directSlab w2 12 = 196169284364 := by decide +kernel
private theorem s13 : directSlab w2 13 = 195687901576 := by decide +kernel
private theorem s14 : directSlab w2 14 = 195207511884 := by decide +kernel
private theorem s15 : directSlab w2 15 = 194727875390 := by decide +kernel
private theorem s16 : directSlab w2 16 = 194249228484 := by decide +kernel
private theorem s17 : directSlab w2 17 = 193771331130 := by decide +kernel
private theorem s18 : directSlab w2 18 = 193294420922 := by decide +kernel
private theorem s19 : directSlab w2 19 = 192818256350 := by decide +kernel
private theorem s20 : directSlab w2 20 = 192343074932 := by decide +kernel
private theorem s21 : directSlab w2 21 = 191868636278 := by decide +kernel
private theorem s22 : directSlab w2 22 = 191395176542 := by decide +kernel
private theorem s23 : directSlab w2 23 = 190922455122 := by decide +kernel

theorem fee2Part0 : affineFeeChunk w2 0 24 = 4714349190922 :=
  affineFeeCertified_eq w2 0 [202013767794, 201521806472, 201030851584, 200540663546, 200051479888, 199563061038, 199075645582, 198588992622, 198103340518, 197618449642, 197134556840, 196651422422, 196169284364, 195687901576, 195207511884, 194727875390, 194249228484, 193771331130, 193294420922, 192818256350, 192343074932, 191868636278, 191395176542, 190922455122]
    ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, True.intro⟩

end Low48PrimaryPivot

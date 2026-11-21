import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part96

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem s120 : directSlab w2 120 = 148290543856 := by decide +kernel
private theorem s121 : directSlab w2 121 = 147870839788 := by decide +kernel
private theorem s122 : directSlab w2 122 = 147451470046 := by decide +kernel
private theorem s123 : directSlab w2 123 = 147032157664 := by decide +kernel
private theorem s124 : directSlab w2 124 = 146613170244 := by decide +kernel
private theorem s125 : directSlab w2 125 = 146194229622 := by decide +kernel
private theorem s126 : directSlab w2 126 = 145775605828 := by decide +kernel
private theorem s127 : directSlab w2 127 = 145357018172 := by decide +kernel
private theorem s128 : directSlab w2 128 = 144938737822 := by decide +kernel
private theorem s129 : directSlab w2 129 = 144520484164 := by decide +kernel
private theorem s130 : directSlab w2 130 = 144102528210 := by decide +kernel
private theorem s131 : directSlab w2 131 = 143684588096 := by decide +kernel
private theorem s132 : directSlab w2 132 = 143266937314 := by decide +kernel
private theorem s133 : directSlab w2 133 = 142849291424 := by decide +kernel
private theorem s134 : directSlab w2 134 = 142431925106 := by decide +kernel
private theorem s135 : directSlab w2 135 = 142014553944 := by decide +kernel
private theorem s136 : directSlab w2 136 = 141597452514 := by decide +kernel
private theorem s137 : directSlab w2 137 = 141180335100 := by decide +kernel
private theorem s138 : directSlab w2 138 = 140763478808 := by decide +kernel
private theorem s139 : directSlab w2 139 = 140346595294 := by decide +kernel
private theorem s140 : directSlab w2 140 = 139929962904 := by decide +kernel
private theorem s141 : directSlab w2 141 = 139513293268 := by decide +kernel
private theorem s142 : directSlab w2 142 = 139096864678 := by decide +kernel
private theorem s143 : directSlab w2 143 = 138680387412 := by decide +kernel

theorem fee2Part120 : affineFeeChunk w2 120 24 = 3443502451278 :=
  affineFeeCertified_eq w2 120 [148290543856, 147870839788, 147451470046, 147032157664, 146613170244, 146194229622, 145775605828, 145357018172, 144938737822, 144520484164, 144102528210, 143684588096, 143266937314, 142849291424, 142431925106, 142014553944, 141597452514, 141180335100, 140763478808, 140346595294, 139929962904, 139513293268, 139096864678, 138680387412]
    ⟨s120, s121, s122, s123, s124, s125, s126, s127, s128, s129, s130, s131, s132, s133, s134, s135, s136, s137, s138, s139, s140, s141, s142, s143, True.intro⟩

end Low48PrimaryPivot

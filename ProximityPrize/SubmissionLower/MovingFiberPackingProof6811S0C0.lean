import ProximityPrize.SubmissionLower.MovingFiberPackingCheck6811
import ProximityPrize.SubmissionLower.MovingFiberPackingFast6811

namespace ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S0
open MovingFiberPackingCheck6811 MovingFiberPackingData6811.S0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem row1_1 : convolution own1.toList packed0.toList packed1.toList=true := by
  exact convolution_zero_right 172 _ _ (by decide +kernel) (by decide +kernel)
theorem row2_1 : convolution own1.toList packed1.toList packed2.toList=true := by decide +kernel
theorem row2_2 : convolution own2.toList packed0.toList packed2.toList=true := by
  exact convolution_zero_right 172 _ _ (by decide +kernel) (by decide +kernel)
theorem row3_1 : convolution own1.toList packed2.toList packed3.toList=true := by decide +kernel
theorem row3_2 : convolution own2.toList packed1.toList packed3.toList=true := by decide +kernel
theorem row3_3 : convolution own3.toList packed0.toList packed3.toList=true := by
  exact convolution_zero_right 172 _ _ (by decide +kernel) (by decide +kernel)
theorem row4_1 : convolution own1.toList packed3.toList packed4.toList=true := by decide +kernel
theorem row4_2 : convolution own2.toList packed2.toList packed4.toList=true := by decide +kernel
theorem row4_3 : convolution own3.toList packed1.toList packed4.toList=true := by decide +kernel
theorem row4_4 : convolution own4.toList packed0.toList packed4.toList=true := by
  exact convolution_zero_right 172 _ _ (by decide +kernel) (by decide +kernel)
theorem row5_1 : convolution own1.toList packed4.toList packed5.toList=true := by decide +kernel
theorem row5_2 : convolution own2.toList packed3.toList packed5.toList=true := by decide +kernel
theorem row5_3 : convolution own3.toList packed2.toList packed5.toList=true := by decide +kernel
theorem row5_4 : convolution own4.toList packed1.toList packed5.toList=true := by decide +kernel
theorem row5_5 : convolution own5.toList packed0.toList packed5.toList=true := by
  exact convolution_zero_right 172 _ _ (by decide +kernel) (by decide +kernel)
end ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S0

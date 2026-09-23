import ProximityPrize.SubmissionLower.MovingFiberPackingProof6811S6C7
import ProximityPrize.SubmissionLower.MovingFiberPackingFast6811

namespace ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S7
open MovingFiberPackingCheck6811 MovingFiberPackingData6811.S7
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem own1_le : shifted 0 own1.toList packed1.toList=true := by decide +kernel
theorem super1_0 : convolution packed0.toList packed1.toList packed1.toList=true := by
  exact convolution_zero 172 _ (by decide +kernel)
theorem own2_le : shifted 0 own2.toList packed2.toList=true := by decide +kernel
theorem super2_0 : convolution packed0.toList packed2.toList packed2.toList=true := by
  exact convolution_zero 172 _ (by decide +kernel)
theorem super2_1 : convolution packed1.toList packed1.toList packed2.toList=true := by decide +kernel
theorem own3_le : shifted 0 own3.toList packed3.toList=true := by decide +kernel
theorem super3_0 : convolution packed0.toList packed3.toList packed3.toList=true := by
  exact convolution_zero 172 _ (by decide +kernel)
theorem super3_1 : convolution packed1.toList packed2.toList packed3.toList=true := by decide +kernel
theorem own4_le : shifted 0 own4.toList packed4.toList=true := by decide +kernel
theorem super4_0 : convolution packed0.toList packed4.toList packed4.toList=true := by
  exact convolution_zero 172 _ (by decide +kernel)
theorem super4_1 : convolution packed1.toList packed3.toList packed4.toList=true := by decide +kernel
theorem super4_2 : convolution packed2.toList packed2.toList packed4.toList=true := by decide +kernel
theorem own5_le : shifted 0 own5.toList packed5.toList=true := by decide +kernel
theorem super5_0 : convolution packed0.toList packed5.toList packed5.toList=true := by
  exact convolution_zero 172 _ (by decide +kernel)
theorem super5_1 : convolution packed1.toList packed4.toList packed5.toList=true := by decide +kernel
theorem super5_2 : convolution packed2.toList packed3.toList packed5.toList=true := by decide +kernel
end ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S7

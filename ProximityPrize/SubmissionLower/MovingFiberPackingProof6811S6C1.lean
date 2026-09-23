import ProximityPrize.SubmissionLower.MovingFiberPackingProof6811S6C0
import ProximityPrize.SubmissionLower.MovingFiberPackingFast6811

namespace ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S6
open MovingFiberPackingCheck6811 MovingFiberPackingData6811.S6
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem own6_le : shifted 0 own6.toList packed6.toList=true := by decide +kernel
theorem super6_0 : convolution packed0.toList packed6.toList packed6.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super6_1 : convolution packed1.toList packed5.toList packed6.toList=true := by decide +kernel
theorem super6_2 : convolution packed2.toList packed4.toList packed6.toList=true := by decide +kernel
theorem super6_3 : convolution packed3.toList packed3.toList packed6.toList=true := by decide +kernel
theorem own7_le : shifted 0 own7.toList packed7.toList=true := by decide +kernel
theorem super7_0 : convolution packed0.toList packed7.toList packed7.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super7_1 : convolution packed1.toList packed6.toList packed7.toList=true := by decide +kernel
theorem super7_2 : convolution packed2.toList packed5.toList packed7.toList=true := by decide +kernel
theorem super7_3 : convolution packed3.toList packed4.toList packed7.toList=true := by decide +kernel
theorem own8_le : shifted 0 own8.toList packed8.toList=true := by decide +kernel
theorem super8_0 : convolution packed0.toList packed8.toList packed8.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super8_1 : convolution packed1.toList packed7.toList packed8.toList=true := by decide +kernel
theorem super8_2 : convolution packed2.toList packed6.toList packed8.toList=true := by decide +kernel
theorem super8_3 : convolution packed3.toList packed5.toList packed8.toList=true := by decide +kernel
theorem super8_4 : convolution packed4.toList packed4.toList packed8.toList=true := by decide +kernel
theorem own9_le : shifted 0 own9.toList packed9.toList=true := by decide +kernel
theorem super9_0 : convolution packed0.toList packed9.toList packed9.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super9_1 : convolution packed1.toList packed8.toList packed9.toList=true := by decide +kernel
theorem super9_2 : convolution packed2.toList packed7.toList packed9.toList=true := by decide +kernel
theorem super9_3 : convolution packed3.toList packed6.toList packed9.toList=true := by decide +kernel
theorem super9_4 : convolution packed4.toList packed5.toList packed9.toList=true := by decide +kernel
theorem own10_le : shifted 0 own10.toList packed10.toList=true := by decide +kernel
theorem super10_0 : convolution packed0.toList packed10.toList packed10.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super10_1 : convolution packed1.toList packed9.toList packed10.toList=true := by decide +kernel
theorem super10_2 : convolution packed2.toList packed8.toList packed10.toList=true := by decide +kernel
theorem super10_3 : convolution packed3.toList packed7.toList packed10.toList=true := by decide +kernel
theorem super10_4 : convolution packed4.toList packed6.toList packed10.toList=true := by decide +kernel
theorem super10_5 : convolution packed5.toList packed5.toList packed10.toList=true := by decide +kernel
end ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S6

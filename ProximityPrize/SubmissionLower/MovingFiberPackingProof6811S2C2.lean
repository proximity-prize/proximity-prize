import ProximityPrize.SubmissionLower.MovingFiberPackingProof6811S2C1
import ProximityPrize.SubmissionLower.MovingFiberPackingFast6811

namespace ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S2
open MovingFiberPackingCheck6811 MovingFiberPackingData6811.S2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem own11_le : shifted 0 own11.toList packed11.toList=true := by decide +kernel
theorem super11_0 : convolution packed0.toList packed11.toList packed11.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super11_1 : convolution packed1.toList packed10.toList packed11.toList=true := by decide +kernel
theorem super11_2 : convolution packed2.toList packed9.toList packed11.toList=true := by decide +kernel
theorem super11_3 : convolution packed3.toList packed8.toList packed11.toList=true := by decide +kernel
theorem super11_4 : convolution packed4.toList packed7.toList packed11.toList=true := by decide +kernel
theorem super11_5 : convolution packed5.toList packed6.toList packed11.toList=true := by decide +kernel
theorem own12_le : shifted 0 own12.toList packed12.toList=true := by decide +kernel
theorem super12_0 : convolution packed0.toList packed12.toList packed12.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super12_1 : convolution packed1.toList packed11.toList packed12.toList=true := by decide +kernel
theorem super12_2 : convolution packed2.toList packed10.toList packed12.toList=true := by decide +kernel
theorem super12_3 : convolution packed3.toList packed9.toList packed12.toList=true := by decide +kernel
theorem super12_4 : convolution packed4.toList packed8.toList packed12.toList=true := by decide +kernel
theorem super12_5 : convolution packed5.toList packed7.toList packed12.toList=true := by decide +kernel
theorem super12_6 : convolution packed6.toList packed6.toList packed12.toList=true := by decide +kernel
theorem own13_le : shifted 0 own13.toList packed13.toList=true := by decide +kernel
theorem super13_0 : convolution packed0.toList packed13.toList packed13.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super13_1 : convolution packed1.toList packed12.toList packed13.toList=true := by decide +kernel
theorem super13_2 : convolution packed2.toList packed11.toList packed13.toList=true := by decide +kernel
theorem super13_3 : convolution packed3.toList packed10.toList packed13.toList=true := by decide +kernel
theorem super13_4 : convolution packed4.toList packed9.toList packed13.toList=true := by decide +kernel
theorem super13_5 : convolution packed5.toList packed8.toList packed13.toList=true := by decide +kernel
theorem super13_6 : convolution packed6.toList packed7.toList packed13.toList=true := by decide +kernel
theorem own14_le : shifted 0 own14.toList packed14.toList=true := by decide +kernel
theorem super14_0 : convolution packed0.toList packed14.toList packed14.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super14_1 : convolution packed1.toList packed13.toList packed14.toList=true := by decide +kernel
theorem super14_2 : convolution packed2.toList packed12.toList packed14.toList=true := by decide +kernel
theorem super14_3 : convolution packed3.toList packed11.toList packed14.toList=true := by decide +kernel
theorem super14_4 : convolution packed4.toList packed10.toList packed14.toList=true := by decide +kernel
theorem super14_5 : convolution packed5.toList packed9.toList packed14.toList=true := by decide +kernel
theorem super14_6 : convolution packed6.toList packed8.toList packed14.toList=true := by decide +kernel
theorem super14_7 : convolution packed7.toList packed7.toList packed14.toList=true := by decide +kernel
theorem own15_le : shifted 0 own15.toList packed15.toList=true := by decide +kernel
theorem super15_0 : convolution packed0.toList packed15.toList packed15.toList=true := by
  exact convolution_zero 164 _ (by decide +kernel)
theorem super15_1 : convolution packed1.toList packed14.toList packed15.toList=true := by decide +kernel
theorem super15_2 : convolution packed2.toList packed13.toList packed15.toList=true := by decide +kernel
theorem super15_3 : convolution packed3.toList packed12.toList packed15.toList=true := by decide +kernel
theorem super15_4 : convolution packed4.toList packed11.toList packed15.toList=true := by decide +kernel
theorem super15_5 : convolution packed5.toList packed10.toList packed15.toList=true := by decide +kernel
theorem super15_6 : convolution packed6.toList packed9.toList packed15.toList=true := by decide +kernel
theorem super15_7 : convolution packed7.toList packed8.toList packed15.toList=true := by decide +kernel
end ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S2

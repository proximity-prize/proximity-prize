import ProximityPrize.SubmissionLower.MovingFiberPackingProof6811S5C6
import ProximityPrize.SubmissionLower.MovingFiberPackingFast6811

namespace ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S5
open MovingFiberPackingCheck6811 MovingFiberPackingData6811.S5
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem own36_le : shifted 0 own36.toList packed36.toList=true := by decide +kernel
theorem super36_0 : convolution packed0.toList packed36.toList packed36.toList=true := by
  exact convolution_zero 172 _ (by decide +kernel)
theorem super36_1 : convolution packed1.toList packed35.toList packed36.toList=true := by decide +kernel
theorem super36_2 : convolution packed2.toList packed34.toList packed36.toList=true := by decide +kernel
theorem super36_3 : convolution packed3.toList packed33.toList packed36.toList=true := by decide +kernel
theorem super36_4 : convolution packed4.toList packed32.toList packed36.toList=true := by decide +kernel
theorem super36_5 : convolution packed5.toList packed31.toList packed36.toList=true := by decide +kernel
theorem super36_6 : convolution packed6.toList packed30.toList packed36.toList=true := by decide +kernel
theorem super36_7 : convolution packed7.toList packed29.toList packed36.toList=true := by decide +kernel
theorem super36_8 : convolution packed8.toList packed28.toList packed36.toList=true := by decide +kernel
theorem super36_9 : convolution packed9.toList packed27.toList packed36.toList=true := by decide +kernel
theorem super36_10 : convolution packed10.toList packed26.toList packed36.toList=true := by decide +kernel
theorem super36_11 : convolution packed11.toList packed25.toList packed36.toList=true := by decide +kernel
theorem super36_12 : convolution packed12.toList packed24.toList packed36.toList=true := by decide +kernel
theorem super36_13 : convolution packed13.toList packed23.toList packed36.toList=true := by decide +kernel
theorem super36_14 : convolution packed14.toList packed22.toList packed36.toList=true := by decide +kernel
theorem super36_15 : convolution packed15.toList packed21.toList packed36.toList=true := by decide +kernel
theorem super36_16 : convolution packed16.toList packed20.toList packed36.toList=true := by decide +kernel
theorem super36_17 : convolution packed17.toList packed19.toList packed36.toList=true := by decide +kernel
theorem super36_18 : convolution packed18.toList packed18.toList packed36.toList=true := by decide +kernel
end ProximityPrize.SubmissionLower.MovingFiberPackingProof6811.S5

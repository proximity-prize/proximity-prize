import ProximityPrize.SubmissionLower.MovingFiberPackingProof6811S1C6
import ProximityPrize.SubmissionLower.MovingFiberPackingSemantics6811

namespace ProximityPrize.SubmissionLower.MovingFiberPackingSound6811.S1
open MovingFiberPackingCheck6811 MovingFiberPackingData6811.S1
open MovingFiberPackingProof6811.S1 MovingFiberPackingSemantics6811
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem own_size (r : Nat) (hr : 1≤r) (hR : r≤35) : (ownRow r).size=164-r := by
  interval_cases r <;> decide +kernel
theorem packed_size (r : Nat) (hR : r≤35) : (packedRow r).size=164-r := by
  interval_cases r <;> decide +kernel
theorem own_under (r : Nat) (hr : 1≤r) (hR : r≤35) : shifted 0 (ownRow r).toList (packedRow r).toList=true := by
  interval_cases r
  · simpa only [ownRow,packedRow] using own1_le
  · simpa only [ownRow,packedRow] using own2_le
  · simpa only [ownRow,packedRow] using own3_le
  · simpa only [ownRow,packedRow] using own4_le
  · simpa only [ownRow,packedRow] using own5_le
  · simpa only [ownRow,packedRow] using own6_le
  · simpa only [ownRow,packedRow] using own7_le
  · simpa only [ownRow,packedRow] using own8_le
  · simpa only [ownRow,packedRow] using own9_le
  · simpa only [ownRow,packedRow] using own10_le
  · simpa only [ownRow,packedRow] using own11_le
  · simpa only [ownRow,packedRow] using own12_le
  · simpa only [ownRow,packedRow] using own13_le
  · simpa only [ownRow,packedRow] using own14_le
  · simpa only [ownRow,packedRow] using own15_le
  · simpa only [ownRow,packedRow] using own16_le
  · simpa only [ownRow,packedRow] using own17_le
  · simpa only [ownRow,packedRow] using own18_le
  · simpa only [ownRow,packedRow] using own19_le
  · simpa only [ownRow,packedRow] using own20_le
  · simpa only [ownRow,packedRow] using own21_le
  · simpa only [ownRow,packedRow] using own22_le
  · simpa only [ownRow,packedRow] using own23_le
  · simpa only [ownRow,packedRow] using own24_le
  · simpa only [ownRow,packedRow] using own25_le
  · simpa only [ownRow,packedRow] using own26_le
  · simpa only [ownRow,packedRow] using own27_le
  · simpa only [ownRow,packedRow] using own28_le
  · simpa only [ownRow,packedRow] using own29_le
  · simpa only [ownRow,packedRow] using own30_le
  · simpa only [ownRow,packedRow] using own31_le
  · simpa only [ownRow,packedRow] using own32_le
  · simpa only [ownRow,packedRow] using own33_le
  · simpa only [ownRow,packedRow] using own34_le
  · simpa only [ownRow,packedRow] using own35_le
theorem all_checks (R r : Nat) (hrr : 2*r≤R) (hR : R≤35) :
    convolution (packedRow r).toList (packedRow (R-r)).toList (packedRow R).toList=true := by
  have hrmax : r≤R/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (by omega)
  interval_cases R
  · interval_cases r
    · decide +kernel
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super1_0
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super2_0
    · simpa only [packedRow,Nat.reduceSub] using super2_1
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super3_0
    · simpa only [packedRow,Nat.reduceSub] using super3_1
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super4_0
    · simpa only [packedRow,Nat.reduceSub] using super4_1
    · simpa only [packedRow,Nat.reduceSub] using super4_2
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super5_0
    · simpa only [packedRow,Nat.reduceSub] using super5_1
    · simpa only [packedRow,Nat.reduceSub] using super5_2
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super6_0
    · simpa only [packedRow,Nat.reduceSub] using super6_1
    · simpa only [packedRow,Nat.reduceSub] using super6_2
    · simpa only [packedRow,Nat.reduceSub] using super6_3
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super7_0
    · simpa only [packedRow,Nat.reduceSub] using super7_1
    · simpa only [packedRow,Nat.reduceSub] using super7_2
    · simpa only [packedRow,Nat.reduceSub] using super7_3
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super8_0
    · simpa only [packedRow,Nat.reduceSub] using super8_1
    · simpa only [packedRow,Nat.reduceSub] using super8_2
    · simpa only [packedRow,Nat.reduceSub] using super8_3
    · simpa only [packedRow,Nat.reduceSub] using super8_4
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super9_0
    · simpa only [packedRow,Nat.reduceSub] using super9_1
    · simpa only [packedRow,Nat.reduceSub] using super9_2
    · simpa only [packedRow,Nat.reduceSub] using super9_3
    · simpa only [packedRow,Nat.reduceSub] using super9_4
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super10_0
    · simpa only [packedRow,Nat.reduceSub] using super10_1
    · simpa only [packedRow,Nat.reduceSub] using super10_2
    · simpa only [packedRow,Nat.reduceSub] using super10_3
    · simpa only [packedRow,Nat.reduceSub] using super10_4
    · simpa only [packedRow,Nat.reduceSub] using super10_5
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super11_0
    · simpa only [packedRow,Nat.reduceSub] using super11_1
    · simpa only [packedRow,Nat.reduceSub] using super11_2
    · simpa only [packedRow,Nat.reduceSub] using super11_3
    · simpa only [packedRow,Nat.reduceSub] using super11_4
    · simpa only [packedRow,Nat.reduceSub] using super11_5
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super12_0
    · simpa only [packedRow,Nat.reduceSub] using super12_1
    · simpa only [packedRow,Nat.reduceSub] using super12_2
    · simpa only [packedRow,Nat.reduceSub] using super12_3
    · simpa only [packedRow,Nat.reduceSub] using super12_4
    · simpa only [packedRow,Nat.reduceSub] using super12_5
    · simpa only [packedRow,Nat.reduceSub] using super12_6
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super13_0
    · simpa only [packedRow,Nat.reduceSub] using super13_1
    · simpa only [packedRow,Nat.reduceSub] using super13_2
    · simpa only [packedRow,Nat.reduceSub] using super13_3
    · simpa only [packedRow,Nat.reduceSub] using super13_4
    · simpa only [packedRow,Nat.reduceSub] using super13_5
    · simpa only [packedRow,Nat.reduceSub] using super13_6
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super14_0
    · simpa only [packedRow,Nat.reduceSub] using super14_1
    · simpa only [packedRow,Nat.reduceSub] using super14_2
    · simpa only [packedRow,Nat.reduceSub] using super14_3
    · simpa only [packedRow,Nat.reduceSub] using super14_4
    · simpa only [packedRow,Nat.reduceSub] using super14_5
    · simpa only [packedRow,Nat.reduceSub] using super14_6
    · simpa only [packedRow,Nat.reduceSub] using super14_7
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super15_0
    · simpa only [packedRow,Nat.reduceSub] using super15_1
    · simpa only [packedRow,Nat.reduceSub] using super15_2
    · simpa only [packedRow,Nat.reduceSub] using super15_3
    · simpa only [packedRow,Nat.reduceSub] using super15_4
    · simpa only [packedRow,Nat.reduceSub] using super15_5
    · simpa only [packedRow,Nat.reduceSub] using super15_6
    · simpa only [packedRow,Nat.reduceSub] using super15_7
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super16_0
    · simpa only [packedRow,Nat.reduceSub] using super16_1
    · simpa only [packedRow,Nat.reduceSub] using super16_2
    · simpa only [packedRow,Nat.reduceSub] using super16_3
    · simpa only [packedRow,Nat.reduceSub] using super16_4
    · simpa only [packedRow,Nat.reduceSub] using super16_5
    · simpa only [packedRow,Nat.reduceSub] using super16_6
    · simpa only [packedRow,Nat.reduceSub] using super16_7
    · simpa only [packedRow,Nat.reduceSub] using super16_8
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super17_0
    · simpa only [packedRow,Nat.reduceSub] using super17_1
    · simpa only [packedRow,Nat.reduceSub] using super17_2
    · simpa only [packedRow,Nat.reduceSub] using super17_3
    · simpa only [packedRow,Nat.reduceSub] using super17_4
    · simpa only [packedRow,Nat.reduceSub] using super17_5
    · simpa only [packedRow,Nat.reduceSub] using super17_6
    · simpa only [packedRow,Nat.reduceSub] using super17_7
    · simpa only [packedRow,Nat.reduceSub] using super17_8
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super18_0
    · simpa only [packedRow,Nat.reduceSub] using super18_1
    · simpa only [packedRow,Nat.reduceSub] using super18_2
    · simpa only [packedRow,Nat.reduceSub] using super18_3
    · simpa only [packedRow,Nat.reduceSub] using super18_4
    · simpa only [packedRow,Nat.reduceSub] using super18_5
    · simpa only [packedRow,Nat.reduceSub] using super18_6
    · simpa only [packedRow,Nat.reduceSub] using super18_7
    · simpa only [packedRow,Nat.reduceSub] using super18_8
    · simpa only [packedRow,Nat.reduceSub] using super18_9
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super19_0
    · simpa only [packedRow,Nat.reduceSub] using super19_1
    · simpa only [packedRow,Nat.reduceSub] using super19_2
    · simpa only [packedRow,Nat.reduceSub] using super19_3
    · simpa only [packedRow,Nat.reduceSub] using super19_4
    · simpa only [packedRow,Nat.reduceSub] using super19_5
    · simpa only [packedRow,Nat.reduceSub] using super19_6
    · simpa only [packedRow,Nat.reduceSub] using super19_7
    · simpa only [packedRow,Nat.reduceSub] using super19_8
    · simpa only [packedRow,Nat.reduceSub] using super19_9
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super20_0
    · simpa only [packedRow,Nat.reduceSub] using super20_1
    · simpa only [packedRow,Nat.reduceSub] using super20_2
    · simpa only [packedRow,Nat.reduceSub] using super20_3
    · simpa only [packedRow,Nat.reduceSub] using super20_4
    · simpa only [packedRow,Nat.reduceSub] using super20_5
    · simpa only [packedRow,Nat.reduceSub] using super20_6
    · simpa only [packedRow,Nat.reduceSub] using super20_7
    · simpa only [packedRow,Nat.reduceSub] using super20_8
    · simpa only [packedRow,Nat.reduceSub] using super20_9
    · simpa only [packedRow,Nat.reduceSub] using super20_10
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super21_0
    · simpa only [packedRow,Nat.reduceSub] using super21_1
    · simpa only [packedRow,Nat.reduceSub] using super21_2
    · simpa only [packedRow,Nat.reduceSub] using super21_3
    · simpa only [packedRow,Nat.reduceSub] using super21_4
    · simpa only [packedRow,Nat.reduceSub] using super21_5
    · simpa only [packedRow,Nat.reduceSub] using super21_6
    · simpa only [packedRow,Nat.reduceSub] using super21_7
    · simpa only [packedRow,Nat.reduceSub] using super21_8
    · simpa only [packedRow,Nat.reduceSub] using super21_9
    · simpa only [packedRow,Nat.reduceSub] using super21_10
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super22_0
    · simpa only [packedRow,Nat.reduceSub] using super22_1
    · simpa only [packedRow,Nat.reduceSub] using super22_2
    · simpa only [packedRow,Nat.reduceSub] using super22_3
    · simpa only [packedRow,Nat.reduceSub] using super22_4
    · simpa only [packedRow,Nat.reduceSub] using super22_5
    · simpa only [packedRow,Nat.reduceSub] using super22_6
    · simpa only [packedRow,Nat.reduceSub] using super22_7
    · simpa only [packedRow,Nat.reduceSub] using super22_8
    · simpa only [packedRow,Nat.reduceSub] using super22_9
    · simpa only [packedRow,Nat.reduceSub] using super22_10
    · simpa only [packedRow,Nat.reduceSub] using super22_11
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super23_0
    · simpa only [packedRow,Nat.reduceSub] using super23_1
    · simpa only [packedRow,Nat.reduceSub] using super23_2
    · simpa only [packedRow,Nat.reduceSub] using super23_3
    · simpa only [packedRow,Nat.reduceSub] using super23_4
    · simpa only [packedRow,Nat.reduceSub] using super23_5
    · simpa only [packedRow,Nat.reduceSub] using super23_6
    · simpa only [packedRow,Nat.reduceSub] using super23_7
    · simpa only [packedRow,Nat.reduceSub] using super23_8
    · simpa only [packedRow,Nat.reduceSub] using super23_9
    · simpa only [packedRow,Nat.reduceSub] using super23_10
    · simpa only [packedRow,Nat.reduceSub] using super23_11
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super24_0
    · simpa only [packedRow,Nat.reduceSub] using super24_1
    · simpa only [packedRow,Nat.reduceSub] using super24_2
    · simpa only [packedRow,Nat.reduceSub] using super24_3
    · simpa only [packedRow,Nat.reduceSub] using super24_4
    · simpa only [packedRow,Nat.reduceSub] using super24_5
    · simpa only [packedRow,Nat.reduceSub] using super24_6
    · simpa only [packedRow,Nat.reduceSub] using super24_7
    · simpa only [packedRow,Nat.reduceSub] using super24_8
    · simpa only [packedRow,Nat.reduceSub] using super24_9
    · simpa only [packedRow,Nat.reduceSub] using super24_10
    · simpa only [packedRow,Nat.reduceSub] using super24_11
    · simpa only [packedRow,Nat.reduceSub] using super24_12
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super25_0
    · simpa only [packedRow,Nat.reduceSub] using super25_1
    · simpa only [packedRow,Nat.reduceSub] using super25_2
    · simpa only [packedRow,Nat.reduceSub] using super25_3
    · simpa only [packedRow,Nat.reduceSub] using super25_4
    · simpa only [packedRow,Nat.reduceSub] using super25_5
    · simpa only [packedRow,Nat.reduceSub] using super25_6
    · simpa only [packedRow,Nat.reduceSub] using super25_7
    · simpa only [packedRow,Nat.reduceSub] using super25_8
    · simpa only [packedRow,Nat.reduceSub] using super25_9
    · simpa only [packedRow,Nat.reduceSub] using super25_10
    · simpa only [packedRow,Nat.reduceSub] using super25_11
    · simpa only [packedRow,Nat.reduceSub] using super25_12
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super26_0
    · simpa only [packedRow,Nat.reduceSub] using super26_1
    · simpa only [packedRow,Nat.reduceSub] using super26_2
    · simpa only [packedRow,Nat.reduceSub] using super26_3
    · simpa only [packedRow,Nat.reduceSub] using super26_4
    · simpa only [packedRow,Nat.reduceSub] using super26_5
    · simpa only [packedRow,Nat.reduceSub] using super26_6
    · simpa only [packedRow,Nat.reduceSub] using super26_7
    · simpa only [packedRow,Nat.reduceSub] using super26_8
    · simpa only [packedRow,Nat.reduceSub] using super26_9
    · simpa only [packedRow,Nat.reduceSub] using super26_10
    · simpa only [packedRow,Nat.reduceSub] using super26_11
    · simpa only [packedRow,Nat.reduceSub] using super26_12
    · simpa only [packedRow,Nat.reduceSub] using super26_13
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super27_0
    · simpa only [packedRow,Nat.reduceSub] using super27_1
    · simpa only [packedRow,Nat.reduceSub] using super27_2
    · simpa only [packedRow,Nat.reduceSub] using super27_3
    · simpa only [packedRow,Nat.reduceSub] using super27_4
    · simpa only [packedRow,Nat.reduceSub] using super27_5
    · simpa only [packedRow,Nat.reduceSub] using super27_6
    · simpa only [packedRow,Nat.reduceSub] using super27_7
    · simpa only [packedRow,Nat.reduceSub] using super27_8
    · simpa only [packedRow,Nat.reduceSub] using super27_9
    · simpa only [packedRow,Nat.reduceSub] using super27_10
    · simpa only [packedRow,Nat.reduceSub] using super27_11
    · simpa only [packedRow,Nat.reduceSub] using super27_12
    · simpa only [packedRow,Nat.reduceSub] using super27_13
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super28_0
    · simpa only [packedRow,Nat.reduceSub] using super28_1
    · simpa only [packedRow,Nat.reduceSub] using super28_2
    · simpa only [packedRow,Nat.reduceSub] using super28_3
    · simpa only [packedRow,Nat.reduceSub] using super28_4
    · simpa only [packedRow,Nat.reduceSub] using super28_5
    · simpa only [packedRow,Nat.reduceSub] using super28_6
    · simpa only [packedRow,Nat.reduceSub] using super28_7
    · simpa only [packedRow,Nat.reduceSub] using super28_8
    · simpa only [packedRow,Nat.reduceSub] using super28_9
    · simpa only [packedRow,Nat.reduceSub] using super28_10
    · simpa only [packedRow,Nat.reduceSub] using super28_11
    · simpa only [packedRow,Nat.reduceSub] using super28_12
    · simpa only [packedRow,Nat.reduceSub] using super28_13
    · simpa only [packedRow,Nat.reduceSub] using super28_14
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super29_0
    · simpa only [packedRow,Nat.reduceSub] using super29_1
    · simpa only [packedRow,Nat.reduceSub] using super29_2
    · simpa only [packedRow,Nat.reduceSub] using super29_3
    · simpa only [packedRow,Nat.reduceSub] using super29_4
    · simpa only [packedRow,Nat.reduceSub] using super29_5
    · simpa only [packedRow,Nat.reduceSub] using super29_6
    · simpa only [packedRow,Nat.reduceSub] using super29_7
    · simpa only [packedRow,Nat.reduceSub] using super29_8
    · simpa only [packedRow,Nat.reduceSub] using super29_9
    · simpa only [packedRow,Nat.reduceSub] using super29_10
    · simpa only [packedRow,Nat.reduceSub] using super29_11
    · simpa only [packedRow,Nat.reduceSub] using super29_12
    · simpa only [packedRow,Nat.reduceSub] using super29_13
    · simpa only [packedRow,Nat.reduceSub] using super29_14
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super30_0
    · simpa only [packedRow,Nat.reduceSub] using super30_1
    · simpa only [packedRow,Nat.reduceSub] using super30_2
    · simpa only [packedRow,Nat.reduceSub] using super30_3
    · simpa only [packedRow,Nat.reduceSub] using super30_4
    · simpa only [packedRow,Nat.reduceSub] using super30_5
    · simpa only [packedRow,Nat.reduceSub] using super30_6
    · simpa only [packedRow,Nat.reduceSub] using super30_7
    · simpa only [packedRow,Nat.reduceSub] using super30_8
    · simpa only [packedRow,Nat.reduceSub] using super30_9
    · simpa only [packedRow,Nat.reduceSub] using super30_10
    · simpa only [packedRow,Nat.reduceSub] using super30_11
    · simpa only [packedRow,Nat.reduceSub] using super30_12
    · simpa only [packedRow,Nat.reduceSub] using super30_13
    · simpa only [packedRow,Nat.reduceSub] using super30_14
    · simpa only [packedRow,Nat.reduceSub] using super30_15
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super31_0
    · simpa only [packedRow,Nat.reduceSub] using super31_1
    · simpa only [packedRow,Nat.reduceSub] using super31_2
    · simpa only [packedRow,Nat.reduceSub] using super31_3
    · simpa only [packedRow,Nat.reduceSub] using super31_4
    · simpa only [packedRow,Nat.reduceSub] using super31_5
    · simpa only [packedRow,Nat.reduceSub] using super31_6
    · simpa only [packedRow,Nat.reduceSub] using super31_7
    · simpa only [packedRow,Nat.reduceSub] using super31_8
    · simpa only [packedRow,Nat.reduceSub] using super31_9
    · simpa only [packedRow,Nat.reduceSub] using super31_10
    · simpa only [packedRow,Nat.reduceSub] using super31_11
    · simpa only [packedRow,Nat.reduceSub] using super31_12
    · simpa only [packedRow,Nat.reduceSub] using super31_13
    · simpa only [packedRow,Nat.reduceSub] using super31_14
    · simpa only [packedRow,Nat.reduceSub] using super31_15
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super32_0
    · simpa only [packedRow,Nat.reduceSub] using super32_1
    · simpa only [packedRow,Nat.reduceSub] using super32_2
    · simpa only [packedRow,Nat.reduceSub] using super32_3
    · simpa only [packedRow,Nat.reduceSub] using super32_4
    · simpa only [packedRow,Nat.reduceSub] using super32_5
    · simpa only [packedRow,Nat.reduceSub] using super32_6
    · simpa only [packedRow,Nat.reduceSub] using super32_7
    · simpa only [packedRow,Nat.reduceSub] using super32_8
    · simpa only [packedRow,Nat.reduceSub] using super32_9
    · simpa only [packedRow,Nat.reduceSub] using super32_10
    · simpa only [packedRow,Nat.reduceSub] using super32_11
    · simpa only [packedRow,Nat.reduceSub] using super32_12
    · simpa only [packedRow,Nat.reduceSub] using super32_13
    · simpa only [packedRow,Nat.reduceSub] using super32_14
    · simpa only [packedRow,Nat.reduceSub] using super32_15
    · simpa only [packedRow,Nat.reduceSub] using super32_16
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super33_0
    · simpa only [packedRow,Nat.reduceSub] using super33_1
    · simpa only [packedRow,Nat.reduceSub] using super33_2
    · simpa only [packedRow,Nat.reduceSub] using super33_3
    · simpa only [packedRow,Nat.reduceSub] using super33_4
    · simpa only [packedRow,Nat.reduceSub] using super33_5
    · simpa only [packedRow,Nat.reduceSub] using super33_6
    · simpa only [packedRow,Nat.reduceSub] using super33_7
    · simpa only [packedRow,Nat.reduceSub] using super33_8
    · simpa only [packedRow,Nat.reduceSub] using super33_9
    · simpa only [packedRow,Nat.reduceSub] using super33_10
    · simpa only [packedRow,Nat.reduceSub] using super33_11
    · simpa only [packedRow,Nat.reduceSub] using super33_12
    · simpa only [packedRow,Nat.reduceSub] using super33_13
    · simpa only [packedRow,Nat.reduceSub] using super33_14
    · simpa only [packedRow,Nat.reduceSub] using super33_15
    · simpa only [packedRow,Nat.reduceSub] using super33_16
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super34_0
    · simpa only [packedRow,Nat.reduceSub] using super34_1
    · simpa only [packedRow,Nat.reduceSub] using super34_2
    · simpa only [packedRow,Nat.reduceSub] using super34_3
    · simpa only [packedRow,Nat.reduceSub] using super34_4
    · simpa only [packedRow,Nat.reduceSub] using super34_5
    · simpa only [packedRow,Nat.reduceSub] using super34_6
    · simpa only [packedRow,Nat.reduceSub] using super34_7
    · simpa only [packedRow,Nat.reduceSub] using super34_8
    · simpa only [packedRow,Nat.reduceSub] using super34_9
    · simpa only [packedRow,Nat.reduceSub] using super34_10
    · simpa only [packedRow,Nat.reduceSub] using super34_11
    · simpa only [packedRow,Nat.reduceSub] using super34_12
    · simpa only [packedRow,Nat.reduceSub] using super34_13
    · simpa only [packedRow,Nat.reduceSub] using super34_14
    · simpa only [packedRow,Nat.reduceSub] using super34_15
    · simpa only [packedRow,Nat.reduceSub] using super34_16
    · simpa only [packedRow,Nat.reduceSub] using super34_17
  · interval_cases r
    · simpa only [packedRow,Nat.reduceSub] using super35_0
    · simpa only [packedRow,Nat.reduceSub] using super35_1
    · simpa only [packedRow,Nat.reduceSub] using super35_2
    · simpa only [packedRow,Nat.reduceSub] using super35_3
    · simpa only [packedRow,Nat.reduceSub] using super35_4
    · simpa only [packedRow,Nat.reduceSub] using super35_5
    · simpa only [packedRow,Nat.reduceSub] using super35_6
    · simpa only [packedRow,Nat.reduceSub] using super35_7
    · simpa only [packedRow,Nat.reduceSub] using super35_8
    · simpa only [packedRow,Nat.reduceSub] using super35_9
    · simpa only [packedRow,Nat.reduceSub] using super35_10
    · simpa only [packedRow,Nat.reduceSub] using super35_11
    · simpa only [packedRow,Nat.reduceSub] using super35_12
    · simpa only [packedRow,Nat.reduceSub] using super35_13
    · simpa only [packedRow,Nat.reduceSub] using super35_14
    · simpa only [packedRow,Nat.reduceSub] using super35_15
    · simpa only [packedRow,Nat.reduceSub] using super35_16
    · simpa only [packedRow,Nat.reduceSub] using super35_17
theorem bellman : AffineFactorAggregate6808.BellmanRows 35 163 own packed :=
  symmetric_bellman ownRow packedRow own_size packed_size own_under all_checks
#print axioms bellman
end ProximityPrize.SubmissionLower.MovingFiberPackingSound6811.S1

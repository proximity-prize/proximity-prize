import ProximityPrize.SubmissionLower.ThresholdFastProof6802

/-! Per-R decidable checker scaffolds for the 6802 four-phase receipt. -/

section PackedLocator_LocatorPhase6802ThresholdR01Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR01Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData01.threshold 1 132 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 132,
    ThresholdAtOf LocatorPhase6802ReceiptRowData01.threshold 1 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR01Checked
end PackedLocator_LocatorPhase6802ThresholdR01Checked

section PackedLocator_LocatorPhase6802ThresholdR02Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR02Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData02.threshold 2 131 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 131,
    ThresholdAtOf LocatorPhase6802ReceiptRowData02.threshold 2 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR02Checked
end PackedLocator_LocatorPhase6802ThresholdR02Checked

section PackedLocator_LocatorPhase6802ThresholdR03Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR03Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData03.threshold 3 130 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 130,
    ThresholdAtOf LocatorPhase6802ReceiptRowData03.threshold 3 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR03Checked
end PackedLocator_LocatorPhase6802ThresholdR03Checked

section PackedLocator_LocatorPhase6802ThresholdR04Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR04Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData04.threshold 4 129 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 129,
    ThresholdAtOf LocatorPhase6802ReceiptRowData04.threshold 4 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR04Checked
end PackedLocator_LocatorPhase6802ThresholdR04Checked

section PackedLocator_LocatorPhase6802ThresholdR05Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR05Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData05.threshold 5 128 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 128,
    ThresholdAtOf LocatorPhase6802ReceiptRowData05.threshold 5 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR05Checked
end PackedLocator_LocatorPhase6802ThresholdR05Checked

section PackedLocator_LocatorPhase6802ThresholdR06Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR06Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData06.threshold 6 127 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 127,
    ThresholdAtOf LocatorPhase6802ReceiptRowData06.threshold 6 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR06Checked
end PackedLocator_LocatorPhase6802ThresholdR06Checked

section PackedLocator_LocatorPhase6802ThresholdR07Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR07Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData07.threshold 7 126 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 126,
    ThresholdAtOf LocatorPhase6802ReceiptRowData07.threshold 7 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR07Checked
end PackedLocator_LocatorPhase6802ThresholdR07Checked

section PackedLocator_LocatorPhase6802ThresholdR08Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR08Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData08.threshold 8 125 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 125,
    ThresholdAtOf LocatorPhase6802ReceiptRowData08.threshold 8 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR08Checked
end PackedLocator_LocatorPhase6802ThresholdR08Checked

section PackedLocator_LocatorPhase6802ThresholdR09Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR09Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData09.threshold 9 124 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 124,
    ThresholdAtOf LocatorPhase6802ReceiptRowData09.threshold 9 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR09Checked
end PackedLocator_LocatorPhase6802ThresholdR09Checked

section PackedLocator_LocatorPhase6802ThresholdR10Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR10Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData10.threshold 10 123 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 123,
    ThresholdAtOf LocatorPhase6802ReceiptRowData10.threshold 10 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR10Checked
end PackedLocator_LocatorPhase6802ThresholdR10Checked

section PackedLocator_LocatorPhase6802ThresholdR11Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR11Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData11.threshold 11 122 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 122,
    ThresholdAtOf LocatorPhase6802ReceiptRowData11.threshold 11 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR11Checked
end PackedLocator_LocatorPhase6802ThresholdR11Checked

section PackedLocator_LocatorPhase6802ThresholdR12Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR12Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData12.threshold 12 121 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 121,
    ThresholdAtOf LocatorPhase6802ReceiptRowData12.threshold 12 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR12Checked
end PackedLocator_LocatorPhase6802ThresholdR12Checked

section PackedLocator_LocatorPhase6802ThresholdR13Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR13Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData13.threshold 13 120 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 120,
    ThresholdAtOf LocatorPhase6802ReceiptRowData13.threshold 13 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR13Checked
end PackedLocator_LocatorPhase6802ThresholdR13Checked

section PackedLocator_LocatorPhase6802ThresholdR14Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR14Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData14.threshold 14 119 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 119,
    ThresholdAtOf LocatorPhase6802ReceiptRowData14.threshold 14 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR14Checked
end PackedLocator_LocatorPhase6802ThresholdR14Checked

section PackedLocator_LocatorPhase6802ThresholdR15Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR15Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData15.threshold 15 118 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 118,
    ThresholdAtOf LocatorPhase6802ReceiptRowData15.threshold 15 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR15Checked
end PackedLocator_LocatorPhase6802ThresholdR15Checked

section PackedLocator_LocatorPhase6802ThresholdR16Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR16Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData16.threshold 16 117 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 117,
    ThresholdAtOf LocatorPhase6802ReceiptRowData16.threshold 16 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR16Checked
end PackedLocator_LocatorPhase6802ThresholdR16Checked

section PackedLocator_LocatorPhase6802ThresholdR17Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR17Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData17.threshold 17 116 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 116,
    ThresholdAtOf LocatorPhase6802ReceiptRowData17.threshold 17 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR17Checked
end PackedLocator_LocatorPhase6802ThresholdR17Checked

section PackedLocator_LocatorPhase6802ThresholdR18Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR18Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData18.threshold 18 115 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 115,
    ThresholdAtOf LocatorPhase6802ReceiptRowData18.threshold 18 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR18Checked
end PackedLocator_LocatorPhase6802ThresholdR18Checked

section PackedLocator_LocatorPhase6802ThresholdR19Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR19Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData19.threshold 19 114 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 114,
    ThresholdAtOf LocatorPhase6802ReceiptRowData19.threshold 19 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR19Checked
end PackedLocator_LocatorPhase6802ThresholdR19Checked

section PackedLocator_LocatorPhase6802ThresholdR20Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR20Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData20.threshold 20 113 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 113,
    ThresholdAtOf LocatorPhase6802ReceiptRowData20.threshold 20 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR20Checked
end PackedLocator_LocatorPhase6802ThresholdR20Checked

section PackedLocator_LocatorPhase6802ThresholdR21Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR21Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData21.threshold 21 112 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 112,
    ThresholdAtOf LocatorPhase6802ReceiptRowData21.threshold 21 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR21Checked
end PackedLocator_LocatorPhase6802ThresholdR21Checked

section PackedLocator_LocatorPhase6802ThresholdR22Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR22Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData22.threshold 22 111 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 111,
    ThresholdAtOf LocatorPhase6802ReceiptRowData22.threshold 22 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR22Checked
end PackedLocator_LocatorPhase6802ThresholdR22Checked

section PackedLocator_LocatorPhase6802ThresholdR23Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR23Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData23.threshold 23 110 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 110,
    ThresholdAtOf LocatorPhase6802ReceiptRowData23.threshold 23 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR23Checked
end PackedLocator_LocatorPhase6802ThresholdR23Checked

section PackedLocator_LocatorPhase6802ThresholdR24Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR24Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData24.threshold 24 109 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 109,
    ThresholdAtOf LocatorPhase6802ReceiptRowData24.threshold 24 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR24Checked
end PackedLocator_LocatorPhase6802ThresholdR24Checked

section PackedLocator_LocatorPhase6802ThresholdR25Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR25Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData25.threshold 25 108 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 108,
    ThresholdAtOf LocatorPhase6802ReceiptRowData25.threshold 25 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR25Checked
end PackedLocator_LocatorPhase6802ThresholdR25Checked

section PackedLocator_LocatorPhase6802ThresholdR26Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR26Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData26.threshold 26 107 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 107,
    ThresholdAtOf LocatorPhase6802ReceiptRowData26.threshold 26 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR26Checked
end PackedLocator_LocatorPhase6802ThresholdR26Checked

section PackedLocator_LocatorPhase6802ThresholdR27Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR27Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData27.threshold 27 106 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 106,
    ThresholdAtOf LocatorPhase6802ReceiptRowData27.threshold 27 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR27Checked
end PackedLocator_LocatorPhase6802ThresholdR27Checked

section PackedLocator_LocatorPhase6802ThresholdR28Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR28Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData28.threshold 28 105 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 105,
    ThresholdAtOf LocatorPhase6802ReceiptRowData28.threshold 28 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR28Checked
end PackedLocator_LocatorPhase6802ThresholdR28Checked

section PackedLocator_LocatorPhase6802ThresholdR29Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR29Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6802ReceiptRowData29.threshold 29 104 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 104,
    ThresholdAtOf LocatorPhase6802ReceiptRowData29.threshold 29 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802ThresholdR29Checked
end PackedLocator_LocatorPhase6802ThresholdR29Checked

section PackedLocator_LocatorPhase6802PrefixCoreR01Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR01Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData01.prefixData
    LocatorPhase6802ReceiptRowData02.prefixData 1 131 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR01Checked
end PackedLocator_LocatorPhase6802PrefixCoreR01Checked

section PackedLocator_LocatorPhase6802PrefixCoreR02Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR02Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData02.prefixData
    LocatorPhase6802ReceiptRowData03.prefixData 2 130 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR02Checked
end PackedLocator_LocatorPhase6802PrefixCoreR02Checked

section PackedLocator_LocatorPhase6802PrefixCoreR03Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR03Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData03.prefixData
    LocatorPhase6802ReceiptRowData04.prefixData 3 129 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR03Checked
end PackedLocator_LocatorPhase6802PrefixCoreR03Checked

section PackedLocator_LocatorPhase6802PrefixCoreR04Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR04Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData04.prefixData
    LocatorPhase6802ReceiptRowData05.prefixData 4 128 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR04Checked
end PackedLocator_LocatorPhase6802PrefixCoreR04Checked

section PackedLocator_LocatorPhase6802PrefixCoreR05Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR05Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData05.prefixData
    LocatorPhase6802ReceiptRowData06.prefixData 5 127 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR05Checked
end PackedLocator_LocatorPhase6802PrefixCoreR05Checked

section PackedLocator_LocatorPhase6802PrefixCoreR06Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR06Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData06.prefixData
    LocatorPhase6802ReceiptRowData07.prefixData 6 126 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR06Checked
end PackedLocator_LocatorPhase6802PrefixCoreR06Checked

section PackedLocator_LocatorPhase6802PrefixCoreR07Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR07Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData07.prefixData
    LocatorPhase6802ReceiptRowData08.prefixData 7 125 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR07Checked
end PackedLocator_LocatorPhase6802PrefixCoreR07Checked

section PackedLocator_LocatorPhase6802PrefixCoreR08Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR08Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData08.prefixData
    LocatorPhase6802ReceiptRowData09.prefixData 8 124 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR08Checked
end PackedLocator_LocatorPhase6802PrefixCoreR08Checked

section PackedLocator_LocatorPhase6802PrefixCoreR09Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR09Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData09.prefixData
    LocatorPhase6802ReceiptRowData10.prefixData 9 123 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR09Checked
end PackedLocator_LocatorPhase6802PrefixCoreR09Checked

section PackedLocator_LocatorPhase6802PrefixCoreR10Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR10Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData10.prefixData
    LocatorPhase6802ReceiptRowData11.prefixData 10 122 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR10Checked
end PackedLocator_LocatorPhase6802PrefixCoreR10Checked

section PackedLocator_LocatorPhase6802PrefixCoreR11Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR11Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData11.prefixData
    LocatorPhase6802ReceiptRowData12.prefixData 11 121 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR11Checked
end PackedLocator_LocatorPhase6802PrefixCoreR11Checked

section PackedLocator_LocatorPhase6802PrefixCoreR12Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR12Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData12.prefixData
    LocatorPhase6802ReceiptRowData13.prefixData 12 120 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR12Checked
end PackedLocator_LocatorPhase6802PrefixCoreR12Checked

section PackedLocator_LocatorPhase6802PrefixCoreR13Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR13Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData13.prefixData
    LocatorPhase6802ReceiptRowData14.prefixData 13 119 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR13Checked
end PackedLocator_LocatorPhase6802PrefixCoreR13Checked

section PackedLocator_LocatorPhase6802PrefixCoreR14Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR14Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData14.prefixData
    LocatorPhase6802ReceiptRowData15.prefixData 14 118 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR14Checked
end PackedLocator_LocatorPhase6802PrefixCoreR14Checked

section PackedLocator_LocatorPhase6802PrefixCoreR15Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR15Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData15.prefixData
    LocatorPhase6802ReceiptRowData16.prefixData 15 117 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR15Checked
end PackedLocator_LocatorPhase6802PrefixCoreR15Checked

section PackedLocator_LocatorPhase6802PrefixCoreR16Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR16Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData16.prefixData
    LocatorPhase6802ReceiptRowData17.prefixData 16 116 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR16Checked
end PackedLocator_LocatorPhase6802PrefixCoreR16Checked

section PackedLocator_LocatorPhase6802PrefixCoreR17Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR17Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData17.prefixData
    LocatorPhase6802ReceiptRowData18.prefixData 17 115 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR17Checked
end PackedLocator_LocatorPhase6802PrefixCoreR17Checked

section PackedLocator_LocatorPhase6802PrefixCoreR18Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR18Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData18.prefixData
    LocatorPhase6802ReceiptRowData19.prefixData 18 114 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR18Checked
end PackedLocator_LocatorPhase6802PrefixCoreR18Checked

section PackedLocator_LocatorPhase6802PrefixCoreR19Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR19Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData19.prefixData
    LocatorPhase6802ReceiptRowData20.prefixData 19 113 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR19Checked
end PackedLocator_LocatorPhase6802PrefixCoreR19Checked

section PackedLocator_LocatorPhase6802PrefixCoreR20Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR20Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData20.prefixData
    LocatorPhase6802ReceiptRowData21.prefixData 20 112 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR20Checked
end PackedLocator_LocatorPhase6802PrefixCoreR20Checked

section PackedLocator_LocatorPhase6802PrefixCoreR21Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR21Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData21.prefixData
    LocatorPhase6802ReceiptRowData22.prefixData 21 111 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR21Checked
end PackedLocator_LocatorPhase6802PrefixCoreR21Checked

section PackedLocator_LocatorPhase6802PrefixCoreR22Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR22Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData22.prefixData
    LocatorPhase6802ReceiptRowData23.prefixData 22 110 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR22Checked
end PackedLocator_LocatorPhase6802PrefixCoreR22Checked

section PackedLocator_LocatorPhase6802PrefixCoreR23Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR23Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData23.prefixData
    LocatorPhase6802ReceiptRowData24.prefixData 23 109 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR23Checked
end PackedLocator_LocatorPhase6802PrefixCoreR23Checked

section PackedLocator_LocatorPhase6802PrefixCoreR24Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR24Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData24.prefixData
    LocatorPhase6802ReceiptRowData25.prefixData 24 108 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR24Checked
end PackedLocator_LocatorPhase6802PrefixCoreR24Checked

section PackedLocator_LocatorPhase6802PrefixCoreR25Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR25Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData25.prefixData
    LocatorPhase6802ReceiptRowData26.prefixData 25 107 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR25Checked
end PackedLocator_LocatorPhase6802PrefixCoreR25Checked

section PackedLocator_LocatorPhase6802PrefixCoreR26Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR26Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData26.prefixData
    LocatorPhase6802ReceiptRowData27.prefixData 26 106 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR26Checked
end PackedLocator_LocatorPhase6802PrefixCoreR26Checked

section PackedLocator_LocatorPhase6802PrefixCoreR27Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR27Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData27.prefixData
    LocatorPhase6802ReceiptRowData28.prefixData 27 105 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR27Checked
end PackedLocator_LocatorPhase6802PrefixCoreR27Checked

section PackedLocator_LocatorPhase6802PrefixCoreR28Checked
namespace ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR28Checked
open LocatorPhase6802Oracle LocatorPhase6802ReceiptCellCore ThresholdFastProof6802
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6802ReceiptRowData28.prefixData
    LocatorPhase6802ReceiptRowData29.prefixData 28 104 := by
  decide +kernel

#print axioms checked
end ProximityPrize.SubmissionLower.LocatorPhase6802PrefixCoreR28Checked
end PackedLocator_LocatorPhase6802PrefixCoreR28Checked

import ProximityPrize.SubmissionLower.PackedLocatorTailPart03

section PackedLocator_LocatorPhase6800ThresholdR25Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR25Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData25.threshold 25 103 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 103,
    ThresholdAtOf LocatorPhase6800ReceiptRowData25.threshold 25 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR25Checked
end PackedLocator_LocatorPhase6800ThresholdR25Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR09Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR09Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR09Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData09.prefixData
    LocatorPhase6800ReceiptRowData10.prefixData 9 118 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR09Checked
end PackedLocator_LocatorPhase6800PrefixCoreR09Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR21Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR21Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR21Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData21.prefixData
    LocatorPhase6800ReceiptRowData22.prefixData 21 106 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR21Checked
end PackedLocator_LocatorPhase6800PrefixCoreR21Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR02Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR02Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR02Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData02.threshold 2 126 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 126,
    ThresholdAtOf LocatorPhase6800ReceiptRowData02.threshold 2 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR02Checked
end PackedLocator_LocatorPhase6800ThresholdR02Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR14Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR14Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR14Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData14.threshold 14 114 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 114,
    ThresholdAtOf LocatorPhase6800ReceiptRowData14.threshold 14 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR14Checked
end PackedLocator_LocatorPhase6800ThresholdR14Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR26Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR26Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR26Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData26.threshold 26 102 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 102,
    ThresholdAtOf LocatorPhase6800ReceiptRowData26.threshold 26 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR26Checked
end PackedLocator_LocatorPhase6800ThresholdR26Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR10Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR10Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR10Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData10.prefixData
    LocatorPhase6800ReceiptRowData11.prefixData 10 117 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR10Checked
end PackedLocator_LocatorPhase6800PrefixCoreR10Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR22Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR22Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR22Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData22.prefixData
    LocatorPhase6800ReceiptRowData23.prefixData 22 105 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR22Checked
end PackedLocator_LocatorPhase6800PrefixCoreR22Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR03Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR03Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR03Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData03.threshold 3 125 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 125,
    ThresholdAtOf LocatorPhase6800ReceiptRowData03.threshold 3 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR03Checked
end PackedLocator_LocatorPhase6800ThresholdR03Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR15Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR15Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR15Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData15.threshold 15 113 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 113,
    ThresholdAtOf LocatorPhase6800ReceiptRowData15.threshold 15 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR15Checked
end PackedLocator_LocatorPhase6800ThresholdR15Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR27Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR27Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR27Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData27.threshold 27 101 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 101,
    ThresholdAtOf LocatorPhase6800ReceiptRowData27.threshold 27 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR27Checked
end PackedLocator_LocatorPhase6800ThresholdR27Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR11Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR11Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR11Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData11.prefixData
    LocatorPhase6800ReceiptRowData12.prefixData 11 116 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR11Checked
end PackedLocator_LocatorPhase6800PrefixCoreR11Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR23Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR23Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR23Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData23.prefixData
    LocatorPhase6800ReceiptRowData24.prefixData 23 104 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR23Checked
end PackedLocator_LocatorPhase6800PrefixCoreR23Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR04Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR04Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR04Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData04.threshold 4 124 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 124,
    ThresholdAtOf LocatorPhase6800ReceiptRowData04.threshold 4 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR04Checked
end PackedLocator_LocatorPhase6800ThresholdR04Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR16Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR16Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR16Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData16.threshold 16 112 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 112,
    ThresholdAtOf LocatorPhase6800ReceiptRowData16.threshold 16 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR16Checked
end PackedLocator_LocatorPhase6800ThresholdR16Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR28Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR28Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR28Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData28.threshold 28 100 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 100,
    ThresholdAtOf LocatorPhase6800ReceiptRowData28.threshold 28 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR28Checked
end PackedLocator_LocatorPhase6800ThresholdR28Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR12Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR12Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR12Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData12.prefixData
    LocatorPhase6800ReceiptRowData13.prefixData 12 115 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR12Checked
end PackedLocator_LocatorPhase6800PrefixCoreR12Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR24Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR24Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR24Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData24.prefixData
    LocatorPhase6800ReceiptRowData25.prefixData 24 103 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR24Checked
end PackedLocator_LocatorPhase6800PrefixCoreR24Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR05Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR05Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR05Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData05.threshold 5 123 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 123,
    ThresholdAtOf LocatorPhase6800ReceiptRowData05.threshold 5 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR05Checked
end PackedLocator_LocatorPhase6800ThresholdR05Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR17Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR17Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR17Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData17.threshold 17 111 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 111,
    ThresholdAtOf LocatorPhase6800ReceiptRowData17.threshold 17 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR17Checked
end PackedLocator_LocatorPhase6800ThresholdR17Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR01Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR01Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR01Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData01.prefixData
    LocatorPhase6800ReceiptRowData02.prefixData 1 126 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR01Checked
end PackedLocator_LocatorPhase6800PrefixCoreR01Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR13Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR13Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR13Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData13.prefixData
    LocatorPhase6800ReceiptRowData14.prefixData 13 114 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR13Checked
end PackedLocator_LocatorPhase6800PrefixCoreR13Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR25Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR25Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR25Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData25.prefixData
    LocatorPhase6800ReceiptRowData26.prefixData 25 102 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR25Checked
end PackedLocator_LocatorPhase6800PrefixCoreR25Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR06Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR06Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR06Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData06.threshold 6 122 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 122,
    ThresholdAtOf LocatorPhase6800ReceiptRowData06.threshold 6 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR06Checked
end PackedLocator_LocatorPhase6800ThresholdR06Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR18Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR18Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR18Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData18.threshold 18 110 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 110,
    ThresholdAtOf LocatorPhase6800ReceiptRowData18.threshold 18 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR18Checked
end PackedLocator_LocatorPhase6800ThresholdR18Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR02Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR02Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR02Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData02.prefixData
    LocatorPhase6800ReceiptRowData03.prefixData 2 125 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR02Checked
end PackedLocator_LocatorPhase6800PrefixCoreR02Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR14Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR14Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR14Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData14.prefixData
    LocatorPhase6800ReceiptRowData15.prefixData 14 113 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR14Checked
end PackedLocator_LocatorPhase6800PrefixCoreR14Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR26Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR26Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR26Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData26.prefixData
    LocatorPhase6800ReceiptRowData27.prefixData 26 101 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR26Checked
end PackedLocator_LocatorPhase6800PrefixCoreR26Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR07Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR07Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR07Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData07.threshold 7 121 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 121,
    ThresholdAtOf LocatorPhase6800ReceiptRowData07.threshold 7 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR07Checked
end PackedLocator_LocatorPhase6800ThresholdR07Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR19Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR19Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR19Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData19.threshold 19 109 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 109,
    ThresholdAtOf LocatorPhase6800ReceiptRowData19.threshold 19 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR19Checked
end PackedLocator_LocatorPhase6800ThresholdR19Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR03Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR03Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR03Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData03.prefixData
    LocatorPhase6800ReceiptRowData04.prefixData 3 124 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR03Checked
end PackedLocator_LocatorPhase6800PrefixCoreR03Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR15Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR15Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR15Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData15.prefixData
    LocatorPhase6800ReceiptRowData16.prefixData 15 112 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR15Checked
end PackedLocator_LocatorPhase6800PrefixCoreR15Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR27Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR27Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR27Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData27.prefixData
    LocatorPhase6800ReceiptRowData28.prefixData 27 100 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR27Checked
end PackedLocator_LocatorPhase6800PrefixCoreR27Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR08Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR08Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR08Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData08.threshold 8 120 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 120,
    ThresholdAtOf LocatorPhase6800ReceiptRowData08.threshold 8 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR08Checked
end PackedLocator_LocatorPhase6800ThresholdR08Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR20Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR20Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR20Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData20.threshold 20 108 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 108,
    ThresholdAtOf LocatorPhase6800ReceiptRowData20.threshold 20 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR20Checked
end PackedLocator_LocatorPhase6800ThresholdR20Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR04Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR04Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR04Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData04.prefixData
    LocatorPhase6800ReceiptRowData05.prefixData 4 123 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR04Checked
end PackedLocator_LocatorPhase6800PrefixCoreR04Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR16Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR16Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR16Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData16.prefixData
    LocatorPhase6800ReceiptRowData17.prefixData 16 111 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR16Checked
end PackedLocator_LocatorPhase6800PrefixCoreR16Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR09Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR09Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR09Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData09.threshold 9 119 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 119,
    ThresholdAtOf LocatorPhase6800ReceiptRowData09.threshold 9 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR09Checked
end PackedLocator_LocatorPhase6800ThresholdR09Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR21Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR21Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR21Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData21.threshold 21 107 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 107,
    ThresholdAtOf LocatorPhase6800ReceiptRowData21.threshold 21 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR21Checked
end PackedLocator_LocatorPhase6800ThresholdR21Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR05Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR05Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR05Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData05.prefixData
    LocatorPhase6800ReceiptRowData06.prefixData 5 122 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR05Checked
end PackedLocator_LocatorPhase6800PrefixCoreR05Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR17Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR17Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR17Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData17.prefixData
    LocatorPhase6800ReceiptRowData18.prefixData 17 110 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR17Checked
end PackedLocator_LocatorPhase6800PrefixCoreR17Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR10Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR10Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR10Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData10.threshold 10 118 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 118,
    ThresholdAtOf LocatorPhase6800ReceiptRowData10.threshold 10 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR10Checked
end PackedLocator_LocatorPhase6800ThresholdR10Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR22Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR22Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR22Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData22.threshold 22 106 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 106,
    ThresholdAtOf LocatorPhase6800ReceiptRowData22.threshold 22 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR22Checked
end PackedLocator_LocatorPhase6800ThresholdR22Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR06Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR06Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR06Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData06.prefixData
    LocatorPhase6800ReceiptRowData07.prefixData 6 121 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR06Checked
end PackedLocator_LocatorPhase6800PrefixCoreR06Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR18Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR18Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR18Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData18.prefixData
    LocatorPhase6800ReceiptRowData19.prefixData 18 109 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR18Checked
end PackedLocator_LocatorPhase6800PrefixCoreR18Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR11Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR11Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR11Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData11.threshold 11 117 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 117,
    ThresholdAtOf LocatorPhase6800ReceiptRowData11.threshold 11 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR11Checked
end PackedLocator_LocatorPhase6800ThresholdR11Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR23Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR23Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR23Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData23.threshold 23 105 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 105,
    ThresholdAtOf LocatorPhase6800ReceiptRowData23.threshold 23 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR23Checked
end PackedLocator_LocatorPhase6800ThresholdR23Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR07Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR07Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR07Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData07.prefixData
    LocatorPhase6800ReceiptRowData08.prefixData 7 120 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR07Checked
end PackedLocator_LocatorPhase6800PrefixCoreR07Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR19Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR19Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR19Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData19.prefixData
    LocatorPhase6800ReceiptRowData20.prefixData 19 108 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR19Checked
end PackedLocator_LocatorPhase6800PrefixCoreR19Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR12Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR12Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR12Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData12.threshold 12 116 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 116,
    ThresholdAtOf LocatorPhase6800ReceiptRowData12.threshold 12 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR12Checked
end PackedLocator_LocatorPhase6800ThresholdR12Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR24Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR24Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR24Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData24.threshold 24 104 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 104,
    ThresholdAtOf LocatorPhase6800ReceiptRowData24.threshold 24 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR24Checked
end PackedLocator_LocatorPhase6800ThresholdR24Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR08Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR08Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR08Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData08.prefixData
    LocatorPhase6800ReceiptRowData09.prefixData 8 119 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR08Checked
end PackedLocator_LocatorPhase6800PrefixCoreR08Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR20Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR20Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR20Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData20.prefixData
    LocatorPhase6800ReceiptRowData21.prefixData 20 107 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR20Checked
end PackedLocator_LocatorPhase6800PrefixCoreR20Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdCoreChecked. -/

import ProximityPrize.SubmissionLower.PackedLocatorTail2

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR01Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR01Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR01Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData01B.threshold 1 135 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 135,
    ThresholdAtOf LocatorPhase6800ReceiptRowData01B.threshold 1 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR01Checked
end PackedLocator_LocatorPhase6800ThresholdR01Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier194 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR13Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR13Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR13Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData13.threshold 13 123 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 123,
    ThresholdAtOf LocatorPhase6800ReceiptRowData13.threshold 13 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR13Checked
end PackedLocator_LocatorPhase6800ThresholdR13Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier195 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR25Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR25Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR25Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData25.threshold 25 111 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 111,
    ThresholdAtOf LocatorPhase6800ReceiptRowData25.threshold 25 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR25Checked
end PackedLocator_LocatorPhase6800ThresholdR25Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier196 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR09Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR09Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR09Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData09.prefixData
    LocatorPhase6800ReceiptRowData10.prefixData 9 126 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR09Checked
end PackedLocator_LocatorPhase6800PrefixCoreR09Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier197 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR21Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR21Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR21Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData21.prefixData
    LocatorPhase6800ReceiptRowData22.prefixData 21 114 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR21Checked
end PackedLocator_LocatorPhase6800PrefixCoreR21Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier198 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR02Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR02Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR02Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData02B.threshold 2 134 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 134,
    ThresholdAtOf LocatorPhase6800ReceiptRowData02B.threshold 2 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR02Checked
end PackedLocator_LocatorPhase6800ThresholdR02Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier199 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR14Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR14Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR14Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData14.threshold 14 122 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 122,
    ThresholdAtOf LocatorPhase6800ReceiptRowData14.threshold 14 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR14Checked
end PackedLocator_LocatorPhase6800ThresholdR14Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier200 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR26Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR26Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR26Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData26.threshold 26 110 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 110,
    ThresholdAtOf LocatorPhase6800ReceiptRowData26.threshold 26 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR26Checked
end PackedLocator_LocatorPhase6800ThresholdR26Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier201 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR10Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR10Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR10Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData10.prefixData
    LocatorPhase6800ReceiptRowData11.prefixData 10 125 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR10Checked
end PackedLocator_LocatorPhase6800PrefixCoreR10Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier202 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR22Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR22Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR22Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData22.prefixData
    LocatorPhase6800ReceiptRowData23.prefixData 22 113 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR22Checked
end PackedLocator_LocatorPhase6800PrefixCoreR22Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier203 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR03Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR03Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR03Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData03B.threshold 3 133 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 133,
    ThresholdAtOf LocatorPhase6800ReceiptRowData03B.threshold 3 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR03Checked
end PackedLocator_LocatorPhase6800ThresholdR03Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier204 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR15Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR15Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR15Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData15.threshold 15 121 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 121,
    ThresholdAtOf LocatorPhase6800ReceiptRowData15.threshold 15 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR15Checked
end PackedLocator_LocatorPhase6800ThresholdR15Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier205 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR27Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR27Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR27Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData27.threshold 27 109 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 109,
    ThresholdAtOf LocatorPhase6800ReceiptRowData27.threshold 27 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR27Checked
end PackedLocator_LocatorPhase6800ThresholdR27Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier206 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR11Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR11Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR11Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData11.prefixData
    LocatorPhase6800ReceiptRowData12.prefixData 11 124 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR11Checked
end PackedLocator_LocatorPhase6800PrefixCoreR11Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier207 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR23Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR23Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR23Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData23.prefixData
    LocatorPhase6800ReceiptRowData24.prefixData 23 112 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR23Checked
end PackedLocator_LocatorPhase6800PrefixCoreR23Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier208 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR04Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR04Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR04Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData04.threshold 4 132 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 132,
    ThresholdAtOf LocatorPhase6800ReceiptRowData04.threshold 4 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR04Checked
end PackedLocator_LocatorPhase6800ThresholdR04Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier209 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR16Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR16Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR16Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData16.threshold 16 120 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 120,
    ThresholdAtOf LocatorPhase6800ReceiptRowData16.threshold 16 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR16Checked
end PackedLocator_LocatorPhase6800ThresholdR16Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier210 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR28Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR28Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR28Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData28.threshold 28 108 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 108,
    ThresholdAtOf LocatorPhase6800ReceiptRowData28.threshold 28 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR28Checked
end PackedLocator_LocatorPhase6800ThresholdR28Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR29Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR29Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR29Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData29.threshold 29 107 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 107,
    ThresholdAtOf LocatorPhase6800ReceiptRowData29.threshold 29 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR29Checked
end PackedLocator_LocatorPhase6800ThresholdR29Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier211 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR12Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR12Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR12Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData12.prefixData
    LocatorPhase6800ReceiptRowData13.prefixData 12 123 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR12Checked
end PackedLocator_LocatorPhase6800PrefixCoreR12Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier212 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR24Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR24Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR24Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData24.prefixData
    LocatorPhase6800ReceiptRowData25.prefixData 24 111 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR24Checked
end PackedLocator_LocatorPhase6800PrefixCoreR24Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier213 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR05Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR05Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR05Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData05.threshold 5 131 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 131,
    ThresholdAtOf LocatorPhase6800ReceiptRowData05.threshold 5 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR05Checked
end PackedLocator_LocatorPhase6800ThresholdR05Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier214 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR17Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR17Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR17Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData17.threshold 17 119 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 119,
    ThresholdAtOf LocatorPhase6800ReceiptRowData17.threshold 17 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR17Checked
end PackedLocator_LocatorPhase6800ThresholdR17Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier215 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR01Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR01Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR01Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData01B.prefixData
    LocatorPhase6800ReceiptRowData02B.prefixData 1 134 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR01Checked
end PackedLocator_LocatorPhase6800PrefixCoreR01Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier216 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR13Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR13Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR13Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData13.prefixData
    LocatorPhase6800ReceiptRowData14.prefixData 13 122 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR13Checked
end PackedLocator_LocatorPhase6800PrefixCoreR13Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier217 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR25Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR25Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR25Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData25.prefixData
    LocatorPhase6800ReceiptRowData26.prefixData 25 110 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR25Checked
end PackedLocator_LocatorPhase6800PrefixCoreR25Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier218 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR06Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR06Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR06Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData06.threshold 6 130 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 130,
    ThresholdAtOf LocatorPhase6800ReceiptRowData06.threshold 6 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR06Checked
end PackedLocator_LocatorPhase6800ThresholdR06Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier219 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR18Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR18Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR18Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData18.threshold 18 118 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 118,
    ThresholdAtOf LocatorPhase6800ReceiptRowData18.threshold 18 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR18Checked
end PackedLocator_LocatorPhase6800ThresholdR18Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier220 : True := by trivial
end ProximityPrize.SubmissionLower

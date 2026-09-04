import ProximityPrize.SubmissionLower.PackedLocatorTail2

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR02Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR02Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR02Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData02B.prefixData
    LocatorPhase6800ReceiptRowData03B.prefixData 2 133 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR02Checked
end PackedLocator_LocatorPhase6800PrefixCoreR02Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier221 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR14Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR14Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR14Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData14.prefixData
    LocatorPhase6800ReceiptRowData15.prefixData 14 121 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR14Checked
end PackedLocator_LocatorPhase6800PrefixCoreR14Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier222 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR26Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR26Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR26Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData26.prefixData
    LocatorPhase6800ReceiptRowData27.prefixData 26 109 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR26Checked
end PackedLocator_LocatorPhase6800PrefixCoreR26Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier223 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR07Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR07Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR07Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData07.threshold 7 129 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 129,
    ThresholdAtOf LocatorPhase6800ReceiptRowData07.threshold 7 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR07Checked
end PackedLocator_LocatorPhase6800ThresholdR07Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier224 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR19Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR19Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR19Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData19.threshold 19 117 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 117,
    ThresholdAtOf LocatorPhase6800ReceiptRowData19.threshold 19 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR19Checked
end PackedLocator_LocatorPhase6800ThresholdR19Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier225 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR03Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR03Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR03Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData03B.prefixData
    LocatorPhase6800ReceiptRowData04.prefixData 3 132 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR03Checked
end PackedLocator_LocatorPhase6800PrefixCoreR03Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier226 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR15Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR15Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR15Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData15.prefixData
    LocatorPhase6800ReceiptRowData16.prefixData 15 120 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR15Checked
end PackedLocator_LocatorPhase6800PrefixCoreR15Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier227 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR27Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR27Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR27Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData27.prefixData
    LocatorPhase6800ReceiptRowData28.prefixData 27 108 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR27Checked
end PackedLocator_LocatorPhase6800PrefixCoreR27Checked

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR28Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR28Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR28Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData28.prefixData
    LocatorPhase6800ReceiptRowData29.prefixData 28 107 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR28Checked
end PackedLocator_LocatorPhase6800PrefixCoreR28Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier228 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR08Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR08Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR08Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData08.threshold 8 128 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 128,
    ThresholdAtOf LocatorPhase6800ReceiptRowData08.threshold 8 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR08Checked
end PackedLocator_LocatorPhase6800ThresholdR08Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier229 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR20Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR20Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR20Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData20.threshold 20 116 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 116,
    ThresholdAtOf LocatorPhase6800ReceiptRowData20.threshold 20 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR20Checked
end PackedLocator_LocatorPhase6800ThresholdR20Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier230 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR04Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR04Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR04Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData04.prefixData
    LocatorPhase6800ReceiptRowData05.prefixData 4 131 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR04Checked
end PackedLocator_LocatorPhase6800PrefixCoreR04Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier231 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR16Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR16Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR16Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData16.prefixData
    LocatorPhase6800ReceiptRowData17.prefixData 16 119 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR16Checked
end PackedLocator_LocatorPhase6800PrefixCoreR16Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier232 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR09Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR09Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR09Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData09.threshold 9 127 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 127,
    ThresholdAtOf LocatorPhase6800ReceiptRowData09.threshold 9 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR09Checked
end PackedLocator_LocatorPhase6800ThresholdR09Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier233 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR21Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR21Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR21Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData21.threshold 21 115 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 115,
    ThresholdAtOf LocatorPhase6800ReceiptRowData21.threshold 21 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR21Checked
end PackedLocator_LocatorPhase6800ThresholdR21Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier234 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR05Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR05Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR05Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData05.prefixData
    LocatorPhase6800ReceiptRowData06.prefixData 5 130 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR05Checked
end PackedLocator_LocatorPhase6800PrefixCoreR05Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier235 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR17Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR17Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR17Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData17.prefixData
    LocatorPhase6800ReceiptRowData18.prefixData 17 118 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR17Checked
end PackedLocator_LocatorPhase6800PrefixCoreR17Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier236 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR10Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR10Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR10Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData10.threshold 10 126 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 126,
    ThresholdAtOf LocatorPhase6800ReceiptRowData10.threshold 10 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR10Checked
end PackedLocator_LocatorPhase6800ThresholdR10Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier237 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR22Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR22Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR22Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData22.threshold 22 114 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 114,
    ThresholdAtOf LocatorPhase6800ReceiptRowData22.threshold 22 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR22Checked
end PackedLocator_LocatorPhase6800ThresholdR22Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier238 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR06Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR06Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR06Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData06.prefixData
    LocatorPhase6800ReceiptRowData07.prefixData 6 129 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR06Checked
end PackedLocator_LocatorPhase6800PrefixCoreR06Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier239 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR18Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR18Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR18Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData18.prefixData
    LocatorPhase6800ReceiptRowData19.prefixData 18 117 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR18Checked
end PackedLocator_LocatorPhase6800PrefixCoreR18Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier240 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR11Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR11Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR11Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData11.threshold 11 125 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 125,
    ThresholdAtOf LocatorPhase6800ReceiptRowData11.threshold 11 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR11Checked
end PackedLocator_LocatorPhase6800ThresholdR11Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier241 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR23Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR23Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR23Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData23.threshold 23 113 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 113,
    ThresholdAtOf LocatorPhase6800ReceiptRowData23.threshold 23 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR23Checked
end PackedLocator_LocatorPhase6800ThresholdR23Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier242 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR07Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR07Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR07Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData07.prefixData
    LocatorPhase6800ReceiptRowData08.prefixData 7 128 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR07Checked
end PackedLocator_LocatorPhase6800PrefixCoreR07Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier243 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR19Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR19Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR19Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData19.prefixData
    LocatorPhase6800ReceiptRowData20.prefixData 19 116 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR19Checked
end PackedLocator_LocatorPhase6800PrefixCoreR19Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier244 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR12Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR12Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR12Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData12.threshold 12 124 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 124,
    ThresholdAtOf LocatorPhase6800ReceiptRowData12.threshold 12 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR12Checked
end PackedLocator_LocatorPhase6800ThresholdR12Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier245 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR24Checked. -/
section PackedLocator_LocatorPhase6800ThresholdR24Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR24Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData24.threshold 24 112 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 112,
    ThresholdAtOf LocatorPhase6800ReceiptRowData24.threshold 24 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR24Checked
end PackedLocator_LocatorPhase6800ThresholdR24Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier246 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR08Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR08Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR08Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData08.prefixData
    LocatorPhase6800ReceiptRowData09.prefixData 8 127 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR08Checked
end PackedLocator_LocatorPhase6800PrefixCoreR08Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier247 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR20Checked. -/
section PackedLocator_LocatorPhase6800PrefixCoreR20Checked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR20Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checked : PrefixCoreRIndexedOf LocatorPhase6800ReceiptRowData20.prefixData
    LocatorPhase6800ReceiptRowData21.prefixData 20 115 := by
  decide +kernel

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800PrefixCoreR20Checked
end PackedLocator_LocatorPhase6800PrefixCoreR20Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier248 : True := by trivial
end ProximityPrize.SubmissionLower

import ProximityPrize.SubmissionLower.LocatorPhase6802PhaseRunChecked

/-! Assembly of the kernel-checked sparse 6802 C2 receipt. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6802Checked

open LocatorPhase6802Concrete LocatorPhase6802Oracle LocatorPhase6802Audit
open LocatorPhase6802ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

theorem thresholds : ThresholdsIndexed := by
  intro R hR hpos
  have hlt := List.mem_range.mp hR
  interval_cases R
  · exact LocatorPhase6802ThresholdR01Checked.checked
  · exact LocatorPhase6802ThresholdR02Checked.checked
  · exact LocatorPhase6802ThresholdR03Checked.checked
  · exact LocatorPhase6802ThresholdR04Checked.checked
  · exact LocatorPhase6802ThresholdR05Checked.checked
  · exact LocatorPhase6802ThresholdR06Checked.checked
  · exact LocatorPhase6802ThresholdR07Checked.checked
  · exact LocatorPhase6802ThresholdR08Checked.checked
  · exact LocatorPhase6802ThresholdR09Checked.checked
  · exact LocatorPhase6802ThresholdR10Checked.checked
  · exact LocatorPhase6802ThresholdR11Checked.checked
  · exact LocatorPhase6802ThresholdR12Checked.checked
  · exact LocatorPhase6802ThresholdR13Checked.checked
  · exact LocatorPhase6802ThresholdR14Checked.checked
  · exact LocatorPhase6802ThresholdR15Checked.checked
  · exact LocatorPhase6802ThresholdR16Checked.checked
  · exact LocatorPhase6802ThresholdR17Checked.checked
  · exact LocatorPhase6802ThresholdR18Checked.checked
  · exact LocatorPhase6802ThresholdR19Checked.checked
  · exact LocatorPhase6802ThresholdR20Checked.checked
  · exact LocatorPhase6802ThresholdR21Checked.checked
  · exact LocatorPhase6802ThresholdR22Checked.checked
  · exact LocatorPhase6802ThresholdR23Checked.checked
  · exact LocatorPhase6802ThresholdR24Checked.checked
  · exact LocatorPhase6802ThresholdR25Checked.checked
  · exact LocatorPhase6802ThresholdR26Checked.checked
  · exact LocatorPhase6802ThresholdR27Checked.checked
  · exact LocatorPhase6802ThresholdR28Checked.checked
  · exact LocatorPhase6802ThresholdR29Checked.checked

theorem core : PrefixCoreChecks := by
  intro R hR hpos
  have hlt := List.mem_range.mp hR
  interval_cases R
  · exact LocatorPhase6802PrefixCoreR01Checked.checked
  · exact LocatorPhase6802PrefixCoreR02Checked.checked
  · exact LocatorPhase6802PrefixCoreR03Checked.checked
  · exact LocatorPhase6802PrefixCoreR04Checked.checked
  · exact LocatorPhase6802PrefixCoreR05Checked.checked
  · exact LocatorPhase6802PrefixCoreR06Checked.checked
  · exact LocatorPhase6802PrefixCoreR07Checked.checked
  · exact LocatorPhase6802PrefixCoreR08Checked.checked
  · exact LocatorPhase6802PrefixCoreR09Checked.checked
  · exact LocatorPhase6802PrefixCoreR10Checked.checked
  · exact LocatorPhase6802PrefixCoreR11Checked.checked
  · exact LocatorPhase6802PrefixCoreR12Checked.checked
  · exact LocatorPhase6802PrefixCoreR13Checked.checked
  · exact LocatorPhase6802PrefixCoreR14Checked.checked
  · exact LocatorPhase6802PrefixCoreR15Checked.checked
  · exact LocatorPhase6802PrefixCoreR16Checked.checked
  · exact LocatorPhase6802PrefixCoreR17Checked.checked
  · exact LocatorPhase6802PrefixCoreR18Checked.checked
  · exact LocatorPhase6802PrefixCoreR19Checked.checked
  · exact LocatorPhase6802PrefixCoreR20Checked.checked
  · exact LocatorPhase6802PrefixCoreR21Checked.checked
  · exact LocatorPhase6802PrefixCoreR22Checked.checked
  · exact LocatorPhase6802PrefixCoreR23Checked.checked
  · exact LocatorPhase6802PrefixCoreR24Checked.checked
  · exact LocatorPhase6802PrefixCoreR25Checked.checked
  · exact LocatorPhase6802PrefixCoreR26Checked.checked
  · exact LocatorPhase6802PrefixCoreR27Checked.checked
  · exact LocatorPhase6802PrefixCoreR28Checked.checked

theorem states : PhaseStateChecks :=
  LocatorPhase6802PhaseRunChecked.states

theorem rRows :
    PrefixTableSound checkedBaseCap r1200Potential
      sourceR1200.Routeable rPrefix :=
  LocatorPhase6802Concrete.rRows thresholds states core

theorem cRows :
    PrefixTableSound afterR sourceCPotential sourceC.Routeable cPrefix :=
  LocatorPhase6802Concrete.cRows thresholds states core

theorem f500Rows :
    PrefixTableSound afterC split500Potential
      sourceSplit500.Routeable f500Prefix :=
  LocatorPhase6802Concrete.f500Rows thresholds states core

theorem s390Rows :
    PrefixTableSound afterF500 split390Potential
      sourceSplit390.Routeable s390Prefix :=
  LocatorPhase6802Concrete.s390Rows thresholds states core

end ProximityPrize.SubmissionLower.LocatorPhase6802Checked

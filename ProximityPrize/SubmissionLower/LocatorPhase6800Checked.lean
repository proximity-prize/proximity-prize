import ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdCoreChecked
import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked

/-! Assembly of the kernel-checked sparse 6800 receipt. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Checked

open LocatorPhase6800Concrete LocatorPhase6800Oracle LocatorPhase6800Audit

set_option maxRecDepth 100000

theorem thresholds : ThresholdsIndexed :=
  LocatorPhase6800ThresholdCoreChecked.thresholds

theorem core : PrefixCoreChecks :=
  LocatorPhase6800ThresholdCoreChecked.core

theorem states : PhaseStateChecks :=
  LocatorPhase6800PhaseRunChecked.states

theorem rRows :
    PrefixTableSound checkedBaseCap r1200Potential
      sourceR1200.Routeable rPrefix :=
  LocatorPhase6800Concrete.rRows thresholds states core

theorem cRows :
    PrefixTableSound afterR sourceCPotential sourceC.Routeable cPrefix :=
  LocatorPhase6800Concrete.cRows thresholds states core

theorem f500Rows :
    PrefixTableSound afterC split500Potential
      sourceSplit500.Routeable f500Prefix :=
  LocatorPhase6800Concrete.f500Rows thresholds states core

theorem s390Rows :
    PrefixTableSound afterF500 split390Potential
      sourceSplit390.Routeable s390Prefix :=
  LocatorPhase6800Concrete.s390Rows thresholds states core

end ProximityPrize.SubmissionLower.LocatorPhase6800Checked

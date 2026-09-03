import ProximityPrize.SubmissionLower.LocatorPhase6802Composition

namespace ProximityPrize.SubmissionLower.LocatorPhase6802Certificate

open RCN095 LocatorFactorAggregate
open LocatorPhase6802Oracle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The generated C2 receipt, assembled into the semantic four-phase
certificate consumed by the structural closure. -/
def certificate : LocatorPhase6802Composition.PhasePrefixCertificate where
  baseCap := LocatorPhase6802Concrete.checkedBaseCap
  rPrefix := LocatorPhase6802Concrete.rPrefix
  cPrefix := LocatorPhase6802Concrete.cPrefix
  f500Prefix := LocatorPhase6802Concrete.f500Prefix
  s390Prefix := LocatorPhase6802Concrete.s390Prefix
  baseSound := LocatorPhase6802Concrete.checkedBaseCap_sound
  rRows := LocatorPhase6802Checked.rRows
  cRows := by
    simpa [LocatorPhase6802Composition.afterR1200,
      LocatorPhase6802Concrete.afterR] using LocatorPhase6802Checked.cRows
  f500Rows := by
    simpa [LocatorPhase6802Composition.afterSourceC,
      LocatorPhase6802Composition.afterR1200,
      LocatorPhase6802Concrete.afterC,
      LocatorPhase6802Concrete.afterR] using LocatorPhase6802Checked.f500Rows
  s390Rows := by
    simpa [LocatorPhase6802Composition.afterSplit500,
      LocatorPhase6802Composition.afterSourceC,
      LocatorPhase6802Composition.afterR1200,
      LocatorPhase6802Concrete.afterF500,
      LocatorPhase6802Concrete.afterC,
      LocatorPhase6802Concrete.afterR] using LocatorPhase6802Checked.s390Rows
  joint := by
    intro p hslope hmiddle htotal
    have hjoint :=
      LocatorPhase6802Concrete.joint_le LocatorPhase6802Checked.thresholds
        LocatorPhase6802Checked.states p hslope hmiddle htotal
    have hallow : certifiedJointMaximum ≤ tightenedRegularAllowance := by
      norm_num [certifiedJointMaximum, tightenedRegularAllowance]
    have hrewritten :
        LocatorPhase6802Composition.afterSplit390
            LocatorPhase6802Concrete.checkedBaseCap
            LocatorPhase6802Concrete.rPrefix
            LocatorPhase6802Concrete.cPrefix
            LocatorPhase6802Concrete.f500Prefix
            LocatorPhase6802Concrete.s390Prefix p +
          initialAComplement p ≤ certifiedJointMaximum := by
      simpa [LocatorPhase6802Composition.afterSplit390,
        LocatorPhase6802Composition.afterSplit500,
        LocatorPhase6802Composition.afterSourceC,
        LocatorPhase6802Composition.afterR1200,
        LocatorPhase6802Concrete.afterS390,
        LocatorPhase6802Concrete.afterF500,
        LocatorPhase6802Concrete.afterC,
        LocatorPhase6802Concrete.afterR] using hjoint
    exact hrewritten.trans hallow

end ProximityPrize.SubmissionLower.LocatorPhase6802Certificate

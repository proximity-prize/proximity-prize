import ProximityPrize.SubmissionLower.LocatorPhase6800Checked
import ProximityPrize.SubmissionLower.LocatorPhase6800Composition

/-! Fully checked compact certificate consumed by the algebraic 6800 route. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Certificate

open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def certificate : LocatorPhase6800Composition.PhasePrefixCertificate where
  baseCap := LocatorPhase6800Concrete.checkedBaseCap
  rPrefix := LocatorPhase6800Concrete.rPrefix
  cPrefix := LocatorPhase6800Concrete.cPrefix
  f500Prefix := LocatorPhase6800Concrete.f500Prefix
  s390Prefix := LocatorPhase6800Concrete.s390Prefix
  baseSound := LocatorPhase6800Concrete.checkedBaseCap_sound
  rRows := LocatorPhase6800Checked.rRows
  cRows := by
    simpa [LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterR] using LocatorPhase6800Checked.cRows
  f500Rows := by
    simpa [LocatorPhase6800Composition.afterSourceC,
      LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterC,
      LocatorPhase6800Concrete.afterR] using LocatorPhase6800Checked.f500Rows
  s390Rows := by
    simpa [LocatorPhase6800Composition.afterSplit500,
      LocatorPhase6800Composition.afterSourceC,
      LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterF500,
      LocatorPhase6800Concrete.afterC,
      LocatorPhase6800Concrete.afterR] using LocatorPhase6800Checked.s390Rows
  joint := by
    intro p hslope hmiddle htotal
    simpa [LocatorPhase6800Composition.afterSplit390,
      LocatorPhase6800Composition.afterSplit500,
      LocatorPhase6800Composition.afterSourceC,
      LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterS390,
      LocatorPhase6800Concrete.afterF500,
      LocatorPhase6800Concrete.afterC,
      LocatorPhase6800Concrete.afterR,
      LocatorFixedConsumer.initialRegularCap,
      LocatorArithmetic.fixedRegularCap, certifiedJointMaximum] using
        LocatorPhase6800Concrete.joint_le LocatorPhase6800Checked.thresholds
          LocatorPhase6800Checked.states p hslope hmiddle htotal

end ProximityPrize.SubmissionLower.LocatorPhase6800Certificate

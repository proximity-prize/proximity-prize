import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTwoTailResidualGeneric6750Research
import ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research
import ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate6719Research
import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research
import ProximityPrize.SubmissionLower.ContactAnchoredDelayedTailProviderAdapter6750Research

 







namespace ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research

open ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch
open ContactMovingAgreementCertificate6719Research
open ContactMovingPositiveLedger6719Research
open ContactAnchoredDelayedTailProviderAdapter6750Research
open ContactTightSingularLedgerResearch
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research

set_option autoImplicit false
set_option maxHeartbeats 1000000

 
def cellA (t y : Nat) : Nat := t - y
def cellB (y r : Nat) : Nat := y - r - 1
def cellS (r : Nat) : Nat := r - 2

def cellSupport (t y r : Nat) := support (cellA t y) (cellB y r) (cellS r)

def cellFixedFlag (t y r : Nat) : FlagDegree :=
  surfaceFlag (cellA t y) (cellB y r) (cellS r)

def cellFirstTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag6750 (cellSupport t y r) (w + 1)

def cellSecondTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag6750 (cellSupport t y r) (w + 2)

def cellRegularCost (t y r : Nat) : Nat :=
  flagMixed (cellFixedFlag t y r) (cellFirstTail t y r)
    (cellSecondTail t y r)

def cellTightProfile (D t r : Nat) : TightParameters :=
  ⟨n, w, agreements, D, t, r⟩

def ordinaryReplacementCost (t y r : Nat) : Nat :=
  cellRegularCost t y r +
    (cellTightProfile profileA.weightedCap t r).countCap

def ordinaryDiagonalCost (t y r : Nat) : Nat :=
  upstreamCellCost t y r + ordinaryReplacementCost t y r

 

def firstDerivativeReplacementCost (t y r : Nat) : Nat :=
  cellRegularCost (t - 1) (y - 1) (r - 1) +
    (cellTightProfile
      (profileA.weightedCap - (w - 1)) (t - 1) (r - 1)).countCap

def firstDerivativeDiagonalCost (t y r : Nat) : Nat :=
  upstreamCellCost t y r + firstDerivativeReplacementCost t y r

 

theorem cell_cost_cross_checks :
    ordinaryDiagonalCost 1659 38 14 = 278157547351330244 ∧
    firstDerivativeDiagonalCost 1659 38 14 = 253234563860500286 ∧
    ordinaryDiagonalCost 1278 53 12 = 274979775394674415 ∧
    firstDerivativeDiagonalCost 1659 43 13 = 274769052670195672 := by
  norm_num [ordinaryDiagonalCost, firstDerivativeDiagonalCost,
    ordinaryReplacementCost, firstDerivativeReplacementCost,
    upstreamCellCost, residualCost6750, firstStage, secondStage,
    firstPivot, secondPivot,
    ContactRecursiveResidualStages6656Research.UnequalParameters.regularCountCap,
    ContactRecursiveResidualStages6656Research.UnequalParameters.regularNumerator,
    ContactRecursiveResidualStages6656Research.UnequalParameters.agreement,
    ContactRecursiveResidualStages6656Research.UnequalParameters.leftAgreement,
    ContactRecursiveResidualStages6656Research.UnequalParameters.rightAgreement,
    ContactRecursiveResidualStages6656Research.UnequalParameters.mixedCost,
    ContactRecursiveResidualStages6656Research.UnequalParameters.errors,
    ContactRecursiveResidualStages6656Research.UnequalParameters.gap,
    ContactTightSingularLedgerResearch.TightParameters.countCap,
    ContactTightSingularLedgerResearch.TightParameters.tightNumerator,
    ContactTightSingularLedgerResearch.TightParameters.coreNumerator,
    ContactTightSingularLedgerResearch.TightParameters.agreement,
    ContactTightSingularLedgerResearch.TightParameters.aggregateCost,
    ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
    ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
    ContactTightSingularLedgerResearch.TightParameters.kappa,
    ContactTightSingularLedgerResearch.TightParameters.errors,
    ContactTightSingularLedgerResearch.TightParameters.gap,
    ContactSingularLedger6600Research.dot, cellRegularCost, cellFixedFlag,
    cellFirstTail, cellSecondTail, cellSupport, cellA, cellB, cellS,
    cellTightProfile, reducedResidualAgreementFlag6750,
    reducedAgreementDirection6750,
    ContactMovingAgreementCertificate6719Research.support,
    ContactMovingPositiveLedger6719Research.surfaceFlag, flagMixed,
    profileA, profileB, profileC, Profile.weightedCap,
    n, w, agreements, errors, gap]

end ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research

#print axioms ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research.cell_cost_cross_checks

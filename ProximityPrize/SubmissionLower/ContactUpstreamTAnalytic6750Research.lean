import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research

 







namespace ProximityPrize.SubmissionLower.ContactUpstreamTAnalytic6750Research

open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch
open ContactSingularLedger6600Research

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

theorem residualCost6750_antitone_total
    {lt₁ lt₂ ly ls us : Nat} (h : lt₁ ≤ lt₂) :
    residualCost6750 lt₂ ly ls us ≤ residualCost6750 lt₁ ly ls us := by
  unfold residualCost6750 firstStage secondStage firstPivot secondPivot
  simp only [UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, UnequalParameters.errors,
    UnequalParameters.gap, TightParameters.countCap,
    TightParameters.tightNumerator, TightParameters.coreNumerator,
    TightParameters.agreement, TightParameters.aggregateCost,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.kappa, TightParameters.errors, TightParameters.gap,
    ContactSingularLedger6600Research.dot]
  gcongr

 
theorem upstreamCellCost_antitone_total
    {t₁ t₂ y r : Nat} (h : t₁ ≤ t₂) :
    upstreamCellCost t₂ y r ≤ upstreamCellCost t₁ y r := by
  unfold upstreamCellCost
  apply residualCost6750_antitone_total
  omega

end ProximityPrize.SubmissionLower.ContactUpstreamTAnalytic6750Research

#print axioms ProximityPrize.SubmissionLower.ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total

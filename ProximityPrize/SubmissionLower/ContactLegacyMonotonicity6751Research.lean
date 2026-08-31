import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research
import ProximityPrize.SubmissionLower.ContactMovingOuterBudget6719Research
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

namespace ProximityPrize.SubmissionLower.ContactLegacyMonotonicity6751Research

open ContactRouterCellCosts6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactTightSingularLedgerResearch
open ContactFlagBezout6543Research

set_option autoImplicit false

theorem tightCount_mono_total {D r t₁ t₂ : Nat} (ht : t₁ ≤ t₂) :
    (cellTightProfile D t₁ r).countCap ≤
      (cellTightProfile D t₂ r).countCap := by
  unfold cellTightProfile
  simp only [TightParameters.countCap, TightParameters.tightNumerator,
    TightParameters.coreNumerator, TightParameters.aggregateCost,
    TightParameters.agreement, TightParameters.implicitYCap,
    TightParameters.algebraicCap, TightParameters.kappa,
    TightParameters.errors, TightParameters.gap,
    ContactSingularLedger6600Research.dot]
  gcongr

theorem cellRegularCost_mono_total {t₁ t₂ y r : Nat} (ht : t₁ ≤ t₂) :
    cellRegularCost t₁ y r ≤ cellRegularCost t₂ y r := by
  unfold cellRegularCost cellFixedFlag cellFirstTail cellSecondTail
    cellSupport cellA cellB cellS
  simp only [ContactMovingAgreementCertificate6719Research.support,
    ContactAnchoredDelayedTailProviderAdapter6750Research.reducedResidualAgreementFlag6750,
    ContactAnchoredDelayedTailProviderAdapter6750Research.reducedAgreementDirection6750,
    ContactMovingOuterBudget6719Research.paddedCut,
    ContactMovingPositiveLedger6719Research.surfaceFlag,
    ContactMovingPositiveLedger6719Research.centreFlag,
    ContactMovingPositiveLedger6719Research.directionFlag,
    flagMixed, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  gcongr

end ProximityPrize.SubmissionLower.ContactLegacyMonotonicity6751Research

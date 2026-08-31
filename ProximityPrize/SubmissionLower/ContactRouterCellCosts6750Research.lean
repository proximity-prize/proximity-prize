import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTwoTailResidualGeneric6750Research
import ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research
import ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate6719Research
import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research
import ProximityPrize.SubmissionLower.ContactAnchoredDelayedTailProviderAdapter6750Research
import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research
import ProximityPrize.SubmissionLower.ContactFactoredFlagCount6676Research

 







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

def cellSharpTail (t y r : Nat) : FlagDegree :=
  ContactSharpTaylorFixedMeet6656Research.sharpResidualAgreementFlag
    (cellSupport t y r) (w + 1)

def cellSecondTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag6750 (cellSupport t y r) (w + 2)

def cellDirection (t y r : Nat) : FlagDegree :=
  directionFlag (cellA t y) (cellB y r) (cellS r)

def cellRational (t y r : Nat) : FlagDegree :=
  ⟨(w + 1) * cellA t y + (cellDirection t y r).zOnly,
    (w + 1) * cellB y r + (cellDirection t y r).yz + 1,
    (w + 1) * cellS r + (cellDirection t y r).all⟩

def cellHybridCoordinate (t y r : Nat) : FlagDegree :=
  cellRational t y r + ⟨0, (w + 1) / 2, 3 * ((w + 1) / 2)⟩

def cellMovingFiber (t y r : Nat) : FlagDegree :=
  fiberFlag (cellA t y) (cellB y r) (cellS r)

def cellMovingCut (t y r : Nat) : FlagDegree :=
  cellRational t y r + ⟨0, w + 1, 2 * (w + 1)⟩

def cellHybridCost (t y r : Nat) : Nat :=
  flagMixed (cellFixedFlag t y r) (cellSharpTail t y r)
      (cellHybridCoordinate t y r) +
    (w + 1) * flagMixed (cellFixedFlag t y r) (cellMovingFiber t y r)
      (cellMovingCut t y r)

def cellDelayedCost (t y r : Nat) : Nat :=
  flagMixed (cellFixedFlag t y r) (cellFirstTail t y r)
    (cellSecondTail t y r)

def cellRegularCost (t y r : Nat) : Nat :=
  if r + 2 ≤ y then cellHybridCost t y r else cellDelayedCost t y r

 
def cellTail1 (t y r : Nat) : FlagDegree :=
  if r + 2 ≤ y then cellSharpTail t y r else cellFirstTail t y r

def cellTail2 (t y r : Nat) : FlagDegree :=
  if r + 2 ≤ y then cellHybridCoordinate t y r else cellSecondTail t y r

def cellCostOf (f : FlagDegree) (t y r : Nat) : Nat :=
  if r + 2 ≤ y then
    flagMixed f (cellSharpTail t y r) (cellHybridCoordinate t y r) +
      (w + 1) * flagMixed f (cellMovingFiber t y r) (cellMovingCut t y r)
  else flagMixed f (cellFirstTail t y r) (cellSecondTail t y r)

theorem cellRegularCost_eq_cellCostOf (t y r : Nat) :
    cellRegularCost t y r = cellCostOf (cellFixedFlag t y r) t y r := by
  unfold cellRegularCost cellCostOf cellHybridCost cellDelayedCost
  split_ifs <;> rfl

theorem sum_cellCostOf_le_of_cumulative {J : Type*} [Fintype J]
    (f : J → FlagDegree) (p : FlagDegree) (t y r : Nat)
    (hs : (∑ i, (f i).all) ≤ p.all)
    (hm : (∑ i, ((f i).yz + (f i).all)) ≤ p.yz + p.all)
    (ht : (∑ i, ((f i).zOnly + (f i).yz + (f i).all)) ≤
      p.zOnly + p.yz + p.all) :
    (∑ i, cellCostOf (f i) t y r) ≤ cellCostOf p t y r := by
  unfold cellCostOf
  split_ifs
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add
      (ContactFactoredFlagCount6676Research.sum_flagMixed_le_of_cumulative
        f p _ _ hs hm ht)
      (Nat.mul_le_mul_left _
        (ContactFactoredFlagCount6676Research.sum_flagMixed_le_of_cumulative
          f p _ _ hs hm ht))
  · exact ContactFactoredFlagCount6676Research.sum_flagMixed_le_of_cumulative
      f p _ _ hs hm ht

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
    ordinaryDiagonalCost 1699 38 14 = 222417960708630885 ∧
    firstDerivativeDiagonalCost 1699 38 14 = 203087528617743222 ∧
    ordinaryDiagonalCost 1278 53 12 = 215898164627090063 ∧
    firstDerivativeDiagonalCost 1699 43 13 = 221103585327791131 := by
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
    cellHybridCost, cellDelayedCost, cellRational, cellHybridCoordinate,
    cellMovingFiber, cellMovingCut, cellDirection,
    ContactMovingPositiveLedger6719Research.directionFlag,
    ContactMovingPositiveLedger6719Research.fiberFlag,
    cellFirstTail, cellSharpTail, cellSecondTail, cellSupport,
    ContactSharpTaylorFixedMeet6656Research.sharpResidualAgreementFlag,
    ContactSharpTaylorFixedMeet6656Research.sharpAgreementDirection, cellA, cellB, cellS,
    cellTightProfile, reducedResidualAgreementFlag6750,
    reducedAgreementDirection6750,
    ContactMovingAgreementCertificate6719Research.support,
    ContactMovingPositiveLedger6719Research.surfaceFlag, flagMixed,
    profileA, profileB, profileC, Profile.weightedCap,
    n, w, agreements, errors, gap]

end ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research

#print axioms ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research.cell_cost_cross_checks

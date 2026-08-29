import ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger6720Research
import ProximityPrize.SubmissionLower.ContactMovingStageZero6719Research
import ProximityPrize.SubmissionLower.ContactReducedTaylorProfileResearch

/-! # Small normalization adapter for the reduced-moving terminal charge -/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedTerminalNormalize6720Research

open ContactFlagBezout6543Research ContactRobustFixedMeet6656Research
open ContactResidualSupportParametersResearch
open ContactReducedTaylorProfileResearch
open ContactMovingReducedPositiveLedger6720Research
open ContactMovingReducedFactorLedger6720Research
open ContactMovingAgreementCertificate6719Research

/-- Hide the large affine normalization proof from dependent outer-fiber elaboration. -/
theorem terminal_bound_of_raw (p : Profile) (support : ResidualSupportParameters)
    (a b s d : ℕ) (flag : FlagDegree) (lhs : ℕ)
    (h : lhs ≤
      p.degreeIncidence *
          (ContactMovingPositiveLedger6719Research.weightedMixed flag
              (reducedCut support d)
              (ContactMovingPositiveLedger6719Research.normalFlag a b s) +
            flagMixed flag
              (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
              (ContactMovingPositiveLedger6719Research.centreFlag a b s +
                d • ContactMovingPositiveLedger6719Research.surfaceFlag a b s)) +
        p.unitIncidence *
          ContactMovingPositiveLedger6719Research.weightedMixed flag
            (reducedCut support d)
            (ContactMovingPositiveLedger6719Research.centreFlag a b s) +
        (p.errors + 1) * p.gap *
          (flagMixed flag (reducedCut support d) unitZFlag +
            flagMixed flag (reducedCut support d) unitYZFlag)) :
    lhs ≤ d * factorDegreeCost p support a b s flag +
      factorUnitCost p support a b s flag :=
  h.trans_eq (terminal_affine p support a b s d flag)

/-- Normalize directly from the exact stage-zero ledger returned by component incidence. -/
theorem terminal_bound_of_stage_zero_raw
    (p : Profile) (support : ResidualSupportParameters)
    (a b s d : ℕ) (flag : FlagDegree) (lhs : ℕ)
    (h : lhs ≤
      p.degreeIncidence *
        ContactMovingStageZero6719Research.degreeCost a b s
          (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitAllFlag)
          (flagMixed flag
            (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
            (center a b s + d •
              ContactMovingPositiveLedger6719Research.surfaceFlag a b s)) +
      p.unitIncidence *
        ContactMovingStageZero6719Research.unitCost a b s
          (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitAllFlag) +
      (p.errors + 1) * p.gap *
        (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag +
          flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag)) :
    lhs ≤ d * factorDegreeCost p support a b s flag +
      factorUnitCost p support a b s flag := by
  change lhs ≤
    p.degreeIncidence *
        (ContactMovingPositiveLedger6719Research.weightedMixed flag
            (reducedResidualAgreementFlag support d)
            (ContactMovingPositiveLedger6719Research.normalFlag a b s) +
          flagMixed flag
            (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
            (ContactMovingPositiveLedger6719Research.centreFlag a b s +
              d • ContactMovingPositiveLedger6719Research.surfaceFlag a b s)) +
      p.unitIncidence *
        ContactMovingPositiveLedger6719Research.weightedMixed flag
          (reducedResidualAgreementFlag support d)
          (ContactMovingPositiveLedger6719Research.centreFlag a b s) +
      (p.errors + 1) * p.gap *
        (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag +
          flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag) at h
  have hcut : reducedResidualAgreementFlag support d = reducedCut support d :=
    (reducedCut_eq_residualFlag support d).symm
  rw [hcut] at h
  exact terminal_bound_of_raw p support a b s d flag lhs h

/-- Replace the terminal residual gap inside this small opaque adapter, rather
than rewriting a large dependent hypothesis in the outer-fiber theorem. -/
theorem terminal_bound_of_stage_zero_gap
    (p : Profile) (support : ResidualSupportParameters)
    (a b s d aD card : ℕ) (flag : FlagDegree)
    (hgap : aD - d = p.gap)
    (h : card * (aD - d) ≤
      p.degreeIncidence *
        ContactMovingStageZero6719Research.degreeCost a b s
          (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitAllFlag)
          (flagMixed flag
            (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
            (center a b s + d •
              ContactMovingPositiveLedger6719Research.surfaceFlag a b s)) +
      p.unitIncidence *
        ContactMovingStageZero6719Research.unitCost a b s
          (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitAllFlag) +
      (p.errors + 1) * (aD - d) *
        (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag +
          flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag)) :
    card * p.gap ≤ d * factorDegreeCost p support a b s flag +
      factorUnitCost p support a b s flag := by
  have h' : card * p.gap ≤
      p.degreeIncidence *
        ContactMovingStageZero6719Research.degreeCost a b s
          (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitAllFlag)
          (flagMixed flag
            (ContactMovingPositiveLedger6719Research.fiberFlag a b s)
            (center a b s + d •
              ContactMovingPositiveLedger6719Research.surfaceFlag a b s)) +
      p.unitIncidence *
        ContactMovingStageZero6719Research.unitCost a b s
          (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag)
          (flagMixed flag (reducedResidualAgreementFlag support d) unitAllFlag) +
      (p.errors + 1) * p.gap *
        (flagMixed flag (reducedResidualAgreementFlag support d) unitZFlag +
          flagMixed flag (reducedResidualAgreementFlag support d) unitYZFlag) := by
    simpa only [hgap] using h
  exact terminal_bound_of_stage_zero_raw p support a b s d flag
    (card * p.gap) h'

end ProximityPrize.SubmissionLower.ContactMovingReducedTerminalNormalize6720Research

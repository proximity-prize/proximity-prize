import ProximityPrize.SubmissionLower.ContactMovingReducedPositiveLedger
/-! # Factor ledger for reduced-static/moving-sharp cuts -/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger

open scoped Classical BigOperators
open ContactFlagBezout ContactRobustFixedMeet
open ContactGCDCumulativeFlags ContactResidualSupportParameters
open ContactOriginalRegularSeedCount ContactRegularFactorFlag
open ContactTranslation
open ContactMovingReducedPositiveLedger

noncomputable section
set_option maxHeartbeats 2000000

def factorDegreeCost (p : Profile) (support : ResidualSupportParameters)
    (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  p.degreeIncidence * degreeSlope support a b s flag +
    p.unitIncidence * unitSlope support a b s flag +
    (p.errors + 1) * p.gap * (zSlope support flag + yzSlope support flag)

def factorUnitCost (p : Profile) (_support : ResidualSupportParameters)
    (a b s : ℕ) (flag : FlagDegree) : ℕ :=
  p.degreeIncidence * degreeBase a b s flag +
    p.unitIncidence * unitBase a b s flag +
    (p.errors + 1) * p.gap * (zBase flag + yzBase flag)

theorem terminal_affine (p : Profile) (support : ResidualSupportParameters)
    (a b s d : ℕ) (flag : FlagDegree) :
    p.degreeIncidence *
        (ContactMovingPositiveLedger.weightedMixed flag
            (reducedCut support d)
            (ContactMovingPositiveLedger.normalFlag a b s) +
          flagMixed flag
            (ContactMovingPositiveLedger.fiberFlag a b s)
            (ContactMovingPositiveLedger.centreFlag a b s +
              d • ContactMovingPositiveLedger.surfaceFlag a b s)) +
      p.unitIncidence *
        ContactMovingPositiveLedger.weightedMixed flag
          (reducedCut support d)
          (ContactMovingPositiveLedger.centreFlag a b s) +
      (p.errors + 1) * p.gap *
        (flagMixed flag (reducedCut support d) unitZFlag +
          flagMixed flag (reducedCut support d) unitYZFlag) =
      d * factorDegreeCost p support a b s flag +
        factorUnitCost p support a b s flag := by
  rw [degree_affine, unit_affine, z_affine, yz_affine]
  simp only [factorDegreeCost, factorUnitCost]
  ring

variable {K : Type} [Field K]

end

end ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger

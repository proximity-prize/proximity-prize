import ProximityPrize.SubmissionLower.ContactSingularBranch
import ProximityPrize.SubmissionLower.ContactRobustFixedMeet
import ProximityPrize.SubmissionLower.ContactTightSingularLedger
namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies

open scoped Classical BigOperators
open ContactParameters
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactRegularFactorFlag
open ContactSingularBranch
open ContactPrimeSeedIncidence
open ContactRobustFixedMeet
open ContactTightSingularLedger

noncomputable section

set_option maxHeartbeats 6000000
set_option maxRecDepth 35000

variable {K : Type} [Field K]

def regularSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : ContactRegularFactorFlag.RegularIndex Q) : Finset K :=
  Gamma.filter (fun gamma ↦ RegularSolution F.1 (selected gamma) gamma)

theorem regularSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : ContactRegularFactorFlag.RegularIndex Q) :
    regularSeeds Q selected Gamma F ⊆ Gamma :=
  Finset.filter_subset _ _

end

end ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies

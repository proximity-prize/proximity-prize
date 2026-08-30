import ProximityPrize.SubmissionLower.ContactParameters
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag
namespace ProximityPrize.SubmissionLower.ContactRegularFactorFlag

open scoped BigOperators
open ContactParameters
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactGenericSurface
open ContactFlagBezout

noncomputable section

variable {K Omega : Type} [Field K] [Field Omega]

abbrev RegularIndex (Q : MvPolynomial (Fin 4) K) :=
  ↥(positiveRFactors Q)

end

end ProximityPrize.SubmissionLower.ContactRegularFactorFlag

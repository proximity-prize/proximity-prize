import ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies
import ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage

namespace ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage

open scoped Classical
open ContactParameters
open ContactSelectedSeedDecomposition ContactInterpolation ContactTranslation
open ContactGenericInitialPoint ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactFactorCaps
open ContactOriginalRegularSeedCount ContactOriginalRegularResidualStage
open ContactRegularFactorFlag ContactGlobalSelectedFamilies
open ContactIdentityResidualIteration ContactFlagBezout
open ContactResidualSupportParameters

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable {K Iota : Type} [Field K]

def regularGeometricResidualStageOfSupport
    (support : ResidualSupportParameters)
    {pchar errorCap degree : ℕ} [CharP K pchar]
    (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ degree)
    (hnoPencil : NoLargeSelectedPencil selected Gamma degree errorCap)
    (R : ContactRegularFactorFlag.RegularIndex Q)
    (hRirred : Irreducible R.1)
    (hRpos : 0 < R.1.degreeOf (2 : Fin 4))
    (hRsmall : R.1.degreeOf (2 : Fin 4) < pchar)
    (hRsupport : ResidualSupportData support R.1)
    (hdegreeChar : degree < pchar)
    (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) pchar := genericField_charP K pchar
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      x pchar errorCap (geometricFlag K g) degree support := by
  have hsub := regularSeeds_subset Q selected Gamma R
  exact geometricResidualStageOfSupport K support R.1 hRirred hRpos
    hRsmall hRsupport selected
    (regularSeeds Q selected Gamma R) nodes x u0 u1 hinj
    (fun gamma hgamma ↦ hdegree gamma (hsub hgamma))
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2.1)
    (fun gamma hgamma ↦ (Finset.mem_filter.mp hgamma).2.2)
    (noLargeSelectedPencil_mono selected Gamma _ degree errorCap hsub hnoPencil)
    hdegreeChar g

end

end ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage

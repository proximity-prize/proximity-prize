import ProximityPrize.SubmissionLower.Y6
import ProximityPrize.SubmissionLower.E5
namespace ProximityPrize.SubmissionLower.ContactFirstTailReducedCertificate6732Research
open ContactGenericSurface ContactTaylorNumerators ContactPrimeSeedIncidence
open ContactResidualSupportParametersResearch
open ContactFlagBezout6543Research
open ContactMovingAgreementCertificate6719Research
open ContactFirstTailCertificate6731Research
open ContactReducedTaylorNumerators6643Research
open ContactReducedTaylorProfileResearch
noncomputable section
variable {K Omega : Type} [Field K] [Field Omega]
def reducedGlobalTailCut (phi : Polynomial K →+* Omega)
   (support : ResidualSupportParameters) (F : MvPolynomial (Fin 4) K)
   (d : ℕ) : MvPolynomial (Fin 3) Omega :=
 surfaceMap phi
   (reducedAgreementNumerator F support.s d (tailSelector d) 0 0 0)
theorem globalTailCut_sub_reduced_dvd
   (phi : Polynomial K →+* Omega) (support : ResidualSupportParameters)
   (F : MvPolynomial (Fin 4) K) (d : ℕ) :
   surfaceMap phi F ∣ globalTailCut phi F d -
     reducedGlobalTailCut phi support F d := by
 change surfaceMap phi F ∣
   surfaceMap phi (agreementNumerator F d (tailSelector d) 0 0 0) -
     surfaceMap phi
       (reducedAgreementNumerator F support.s d (tailSelector d) 0 0 0)
 rw [← map_sub]
 exact map_dvd (surfaceMap phi)
   (agreementNumerator_sub_reduced_dvd F support.s d
     (tailSelector d) 0 0 0)
theorem reducedGlobalTailCut_in_flag
   (phi : Polynomial K →+* Omega) (support : ResidualSupportParameters)
   {F : MvPolynomial (Fin 4) K} (H : ResidualSupportData support F)
   (d : ℕ) :
   PolynomialInFlag (reducedResidualAgreementFlag support d)
     (reducedGlobalTailCut phi support F d) := by
 exact surfaceMap_reducedAgreement_in_flag phi support H d
   (tailSelector d) 0 0 0
end
end ProximityPrize.SubmissionLower.ContactFirstTailReducedCertificate6732Research

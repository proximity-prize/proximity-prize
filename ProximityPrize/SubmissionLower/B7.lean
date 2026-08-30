import ProximityPrize.SubmissionLower.Y6
import ProximityPrize.SubmissionLower.E5
namespace ProximityPrize.SubmissionLower.RCN089
open RCN136 RCN313 RCN238
open RCN275
open RCN095
open RCN198
open RCN086
open RCN262
open RCN263
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
end ProximityPrize.SubmissionLower.RCN089

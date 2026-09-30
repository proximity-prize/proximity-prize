import ProximityPrize.SubmissionLower.MovingSourceGenericField6814
import ProximityPrize.SubmissionLower.MovingSourceSaturation6814
namespace ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN135 RCN136 SecondJetCoefficients SecondJetClearedHelper
open MovingSourceClearing6814 MovingSourceGenericField6814 MovingSourceSaturation6814

variable (K : Type*) [Field K]
local notation "Omega" => GenericField K
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local instance : StrongNormalizationMonoid (Polynomial Poly3) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : NormalizedGCDMonoid (Polynomial Poly3) :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid _

def collectTarget (E : Type*) [Field E] :
    Polynomial (MvPolynomial (Fin 3) E) ≃ₐ[E] MvPolynomial (Fin 3) (Polynomial E) :=
  (MvPolynomial.finSuccEquiv E 3).symm.trans (RCN136.collectX E)

def genericTargetMap (E : Type*) [Field E] :
    Polynomial (MvPolynomial (Fin 3) E) →+* MvPolynomial (Fin 3) (GenericField E) :=
  (RCN136.surfaceMap (polynomialEmbedding E)).comp (MvPolynomial.finSuccEquiv E 3).symm.toRingHom

theorem genericTargetMap_injective (E : Type*) [Field E] :
    Function.Injective (genericTargetMap E) :=
  (RCN136.surfaceMap_injective (polynomialEmbedding E) (polynomialEmbedding_injective E)).comp
    (MvPolynomial.finSuccEquiv E 3).symm.injective

theorem genericTargetMap_relPrime (E : Type*) [Field E]
    (U V : Polynomial (MvPolynomial (Fin 3) E)) (hU : U≠0) (hrel : IsRelPrime U V) :
    IsRelPrime (genericTargetMap E U) (genericTargetMap E V) := by
  have hU' : collectTarget E U≠0 := by
    intro hz
    exact hU ((collectTarget E).injective (by simpa only [map_zero] using hz))
  exact generic_coefficient_map_relPrime E _ _ hU'
    (MovingSourceFlatBaseChange6814.isRelPrime_equiv (collectTarget E).toRingEquiv U V hrel)

theorem generic_coefficients_ne_zero (P : WholeSpaceCube6814.Poly (K := K)) (hP : P≠0) :
    coefficients (polynomialEmbedding K) P≠0 := by
  intro hz
  apply hP
  apply (asS (K := K)).injective
  apply Polynomial.map_injective (surfaceMap (polynomialEmbedding K))
    (surfaceMap_injective (polynomialEmbedding K) (polynomialEmbedding_injective K))
  simpa only [coefficients,map_zero,Polynomial.map_zero] using hz

end
end ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814

import ProximityPrize.SubmissionLower.ContactMovingFixedProfile
import ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage

namespace ProximityPrize.SubmissionLower.ContactMovingFixedStage

open scoped Classical
open ContactInterpolation ContactSelectedSeedDecomposition ContactFactorCaps
open ContactOriginalRegularSeedCount ContactOriginalRegularResidualStage
open ContactRegularFactorResidualStage ContactRegularFactorFlag
open ContactGenericInitialPoint ContactGlobalSelectedFamilies
open ContactIdentityResidualIteration ContactIdentityResidualGlobalFlag
open ContactResidualSupportParameters ContactFlagBezout
open ContactGCDCumulativeFlags ContactMovingFixedProfile
open ContactPrimeSeedIncidence ContactProperCutSeedCount

noncomputable section
set_option maxHeartbeats 3000000

variable {K I : Type} [Field K]

theorem fixedSupport_of_dvd
    (F Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hdiv : F ∣ Q)
    (Hsupport : ResidualSupportData ContactMovingParameters.fixedSupport Q) :
      ResidualSupportData ContactMovingParameters.fixedSupport F :=
  ⟨(weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans Hsupport.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights F Q hdiv hQ).trans Hsupport.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans Hsupport.total_weight⟩

def fixedGeometricStage
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K ContactMovingParameters.prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData ContactMovingParameters.fixedSupport Q)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ fixedProfile.w)
    (hnoPencil : NoLargeSelectedPencil selected Γ fixedProfile.w fixedProfile.errors)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) ContactMovingParameters.prime :=
      genericField_charP K ContactMovingParameters.prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g)
      x ContactMovingParameters.prime fixedProfile.errors
        (geometricCumulativeFlag K g) fixedProfile.w ContactMovingParameters.fixedSupport := by
  letI : CharP (GenericField K) ContactMovingParameters.prime :=
    genericField_charP K ContactMovingParameters.prime
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap fixedProfile.w
    fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < ContactMovingParameters.prime :=
    (degreeOf_R_le_of_mem_box R.1 fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap hRdata.2.2).trans_lt (by decide)
  have hsupport : ResidualSupportData ContactMovingParameters.fixedSupport R.1 :=
    fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport
  let S := regularGeometricResidualStageOfSupport ContactMovingParameters.fixedSupport
    Q selected Γ nodes x u0 u1
    hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall hsupport (by decide) g
  exact reflagResidualStage S (polynomialIn_surfaceCumulativeFlag g.1)

theorem geometric_flag_caps
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData ContactMovingParameters.fixedSupport Q)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    (geometricCumulativeFlag K g).all ≤ ContactMovingParameters.fixedSupport.s ∧
      (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤
        ContactMovingParameters.fixedSupport.ys ∧
      (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
        (geometricCumulativeFlag K g).all ≤ ContactMovingParameters.fixedSupport.total := by
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap fixedProfile.w
    fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  exact geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero
    (fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport) g

end
end ProximityPrize.SubmissionLower.ContactMovingFixedStage

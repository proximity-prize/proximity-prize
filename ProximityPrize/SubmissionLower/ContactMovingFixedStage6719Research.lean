import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingFixedProfile6719Research
import ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research

namespace ProximityPrize.SubmissionLower.ContactMovingFixedStage6719Research

open scoped Classical
open ContactInterpolation ContactSelectedSeedDecomposition ContactFactorCaps
open ContactOriginalRegularSeedCount ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorResidualStage6600Research ContactRegularFactorFlag6600Research
open ContactGenericInitialPoint ContactGlobalSelectedFamilies6600Research
open ContactIdentityResidualIterationResearch ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch ContactFlagBezout6543Research
open ContactGCDCumulativeFlagsResearch ContactMovingFixedProfile6719Research
open ContactPrimeSeedIncidence ContactProperCutSeedCount

noncomputable section
set_option maxHeartbeats 3000000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _

theorem fixedSupport_of_dvd
    (F Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hdiv : F ∣ Q)
    (Hsupport : ResidualSupportData fixedSupport Q) : ResidualSupportData fixedSupport F :=
  ⟨(weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans Hsupport.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights F Q hdiv hQ).trans Hsupport.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans Hsupport.total_weight⟩

/-- .
 -/
def fixedGeometricStage
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ fixedProfile.w)
    (hnoPencil : NoLargeSelectedPencil selected Γ fixedProfile.w fixedProfile.errors)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g)
      x prime fixedProfile.errors (geometricCumulativeFlag K g) fixedProfile.w fixedSupport := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap fixedProfile.w
    fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < prime :=
    (degreeOf_R_le_of_mem_box R.1 fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap hRdata.2.2).trans_lt (by decide)
  have hsupport : ResidualSupportData fixedSupport R.1 :=
    fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport
  let S := regularGeometricResidualStageOfSupport fixedSupport Q selected Γ nodes x u0 u1
    hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall hsupport (by decide) g
  exact reflagResidualStage S (polynomialIn_surfaceCumulativeFlag g.1)

theorem geometric_flag_caps
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    (geometricCumulativeFlag K g).all ≤ fixedSupport.s ∧
      (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ fixedSupport.ys ∧
      (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
        (geometricCumulativeFlag K g).all ≤ fixedSupport.total := by
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap fixedProfile.w
    fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  exact geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero
    (fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport) g

end

end ProximityPrize.SubmissionLower.ContactMovingFixedStage6719Research

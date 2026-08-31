import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTwoTailFixedProvider6732Research
import ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research
import ProximityPrize.SubmissionLower.ContactTwoTailStackedBoxTransport6733Research
import ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailFixedStage6733Research
open ProximityPrize.Benchmark
open scoped Classical
open ContactInterpolation ContactSelectedSeedDecomposition ContactFactorCaps
open ContactOriginalRegularSeedCount ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorResidualStage6600Research ContactRegularFactorFlag6600Research
open ContactGenericInitialPoint ContactGlobalSelectedFamilies6600Research
open ContactTaylorNumerators
open ContactIdentityResidualIterationResearch ContactResidualSupportParametersResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactGCDCumulativeFlagsResearch ContactPrimeSeedIncidence
open ContactProperCutSeedCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev fixedProfile:=
  ContactTwoTailFixedProvider6732Research.fixedProfile
abbrev fixedSupport:=
  ContactTwoTailFixedProvider6732Research.fixedSupport
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K ContactTwoTailParameters6733Research.prime:=by
  simpa [ContactTwoTailParameters6733Research.prime,
    ContactParameters6600Research.prime] using
      ContactFrozenAlignment6600Research.challenge_field_characteristic6600
theorem fixedSupport_of_dvd
    (F Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (hdiv:F∣Q)
    (Hsupport:ResidualSupportData fixedSupport Q):
    ResidualSupportData fixedSupport F:=
  ⟨(weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans
      Hsupport.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights F Q hdiv hQ).trans
      Hsupport.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans
      Hsupport.total_weight⟩
def fixedGeometricStage
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    (hbox:Q∈globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport:ResidualSupportData fixedSupport Q)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (u0 u1:I → K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ fixedProfile.w)
    (hnoPencil:NoLargeSelectedPencil selected Gamma
      fixedProfile.w fixedProfile.errors)
    (R:RegularIndex Q) (g:GeometricFactor K R.1):
    letI:CharP (GenericField K) ContactTwoTailParameters6733Research.prime:=
      genericField_charP K ContactTwoTailParameters6733Research.prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      IRSProfile.domain ContactTwoTailParameters6733Research.prime
      fixedProfile.errors (geometricCumulativeFlag K g) fixedProfile.w
      fixedSupport:=by
  letI:CharP (GenericField K) ContactTwoTailParameters6733Research.prime:=
    genericField_charP K ContactTwoTailParameters6733Research.prime
  have hRdata:=directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4) <
      ContactTwoTailParameters6733Research.prime:=
    (degreeOf_R_le_of_mem_box R.1 fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap hRdata.2.2).trans_lt
        (by decide)
  have hsupport:ResidualSupportData fixedSupport R.1:=
    fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1
      Hsupport
  let S:=regularGeometricResidualStageOfSupport fixedSupport Q selected Gamma
    (Finset.univ:Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn hdegree hnoPencil R
    hRdata.1 hRdata.2.1 hRsmall hsupport (by decide) g
  exact reflagResidualStage S (polynomialIn_surfaceCumulativeFlag g.1)
theorem geometric_flag_caps
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    (hbox:Q∈globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport:ResidualSupportData fixedSupport Q)
    (R:RegularIndex Q) (g:GeometricFactor K R.1):
    (geometricCumulativeFlag K g).all ≤ fixedSupport.s∧
      (geometricCumulativeFlag K g).yz+
        (geometricCumulativeFlag K g).all ≤ fixedSupport.ys∧
      (geometricCumulativeFlag K g).zOnly+
        (geometricCumulativeFlag K g).yz+
        (geometricCumulativeFlag K g).all ≤ fixedSupport.total:=by
  have hRdata:=directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  exact geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero
    (fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1
      Hsupport) g
end
end ProximityPrize.SubmissionLower.ContactTwoTailFixedStage6733Research

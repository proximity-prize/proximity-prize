import ProximityPrize.SubmissionLower.FB

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactTwoTailFixedProvider6735Research
open ContactResidualSupportParametersResearch
noncomputable section
def fixedProfile:ContactRobustFixedMeet6656Research.Profile:=
  ⟨262144,131071,181983,7825269,1394,12⟩
def fixedSupport:ResidualSupportParameters:=
  ContactMovingAgreementCertificate6719Research.support 1335 46 10
end
end ProximityPrize.SubmissionLower.ContactTwoTailFixedProvider6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedBoxTransport6735Research
open ProximityPrize.Benchmark
open ContactInterpolation ContactFactorCaps ContactRecursiveGCDResearch
open ContactTwoTailParameters6735Research
open ContactResidualSupportParametersResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
def fixedSupport:ResidualSupportParameters:=
  ⟨12,59,1394,by decide,by decide,by decide,by decide⟩
local instance:GCDMonoid GlobalPoly:=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
theorem gcd12_mem_meet_box
    (A B:GlobalPoly) (hA:A≠0) (hB:B≠0)
    (hboxA:A∈globalCoefficientBox IRSProfile.Field
      profileA.weightedCap w profileA.totalCap profileA.slopeCap)
    (hboxB:B∈globalCoefficientBox IRSProfile.Field
      profileB.weightedCap w profileB.totalCap profileB.slopeCap):
    gcd12 A B∈globalCoefficientBox IRSProfile.Field
      (43*agreements) w 1394 13:=by
  have hfromA:=mem_globalCoefficientBox_of_dvd (gcd12 A B) A
    profileA.weightedCap w profileA.totalCap profileA.slopeCap hA
    (gcd_dvd_left A B) hboxA
  have hfromB:=mem_globalCoefficientBox_of_dvd (gcd12 A B) B
    profileB.weightedCap w profileB.totalCap profileB.slopeCap hB
    (gcd_dvd_right A B) hboxB
  intro d hd
  exact ⟨(hfromB hd).1,(hfromA hd).2.1,(hfromA hd).2.2⟩
theorem gcd123_mem_meet_box
    (A B C:GlobalPoly) (hA:A≠0) (hC:C≠0)
    (hbox12:gcd12 A B∈globalCoefficientBox IRSProfile.Field
      (43*agreements) w 1394 13)
    (hboxC:C∈globalCoefficientBox IRSProfile.Field
      profileC.weightedCap w profileC.totalCap profileC.slopeCap):
    gcd123 A B C∈globalCoefficientBox IRSProfile.Field
      (43*agreements) w 1394 12:=by
  have h12:=ContactStackedBoxTransport6656Research.gcd12_ne_zero (B:=B) hA
  have hfrom12:=mem_globalCoefficientBox_of_dvd (gcd123 A B C) (gcd12 A B)
    (43*agreements) w 1394 13 h12 (gcd_dvd_left (gcd12 A B) C) hbox12
  have hfromC:=mem_globalCoefficientBox_of_dvd (gcd123 A B C) C
    profileC.weightedCap w profileC.totalCap profileC.slopeCap hC
    (gcd_dvd_right (gcd12 A B) C) hboxC
  intro d hd
  exact ⟨(hfrom12 hd).1,(hfromC hd).2.1,(hfrom12 hd).2.2⟩
theorem quotientA_mem_parent_box
    (A B:GlobalPoly) (hA:A≠0)
    (hboxA:A∈globalCoefficientBox IRSProfile.Field
      profileA.weightedCap w profileA.totalCap profileA.slopeCap):
    quotientA A B∈globalCoefficientBox IRSProfile.Field
      profileA.weightedCap w profileA.totalCap profileA.slopeCap:=
  mem_globalCoefficientBox_of_dvd (quotientA A B) A
    profileA.weightedCap w profileA.totalCap profileA.slopeCap hA
    (ContactStackedBoxTransport6656Research.quotientA_dvd_left A B) hboxA
theorem quotientB_mem_parent_box
    (A B:GlobalPoly) (hB:B≠0)
    (hboxB:B∈globalCoefficientBox IRSProfile.Field
      profileB.weightedCap w profileB.totalCap profileB.slopeCap):
    quotientB A B∈globalCoefficientBox IRSProfile.Field
      profileB.weightedCap w profileB.totalCap profileB.slopeCap:=
  mem_globalCoefficientBox_of_dvd (quotientB A B) B
    profileB.weightedCap w profileB.totalCap profileB.slopeCap hB
    (ContactStackedBoxTransport6656Research.quotientB_dvd_right A B) hboxB
theorem middleQuotient_mem_parent_box
    (A B C:GlobalPoly) (hA:A≠0)
    (hbox12:gcd12 A B∈globalCoefficientBox IRSProfile.Field
      (43*agreements) w 1394 13):
    middleQuotient A B C∈globalCoefficientBox IRSProfile.Field
      (43*agreements) w 1394 13:=
  mem_globalCoefficientBox_of_dvd (middleQuotient A B C) (gcd12 A B)
    (43*agreements) w 1394 13
    (ContactStackedBoxTransport6656Research.gcd12_ne_zero (B:=B) hA)
    (ContactStackedBoxTransport6656Research.middleQuotient_dvd_gcd12 A B C) hbox12
theorem quotientC_mem_parent_box
    (A B C:GlobalPoly) (hC:C≠0)
    (hboxC:C∈globalCoefficientBox IRSProfile.Field
      profileC.weightedCap w profileC.totalCap profileC.slopeCap):
    quotientC A B C∈globalCoefficientBox IRSProfile.Field
      profileC.weightedCap w profileC.totalCap profileC.slopeCap:=
  mem_globalCoefficientBox_of_dvd (quotientC A B C) C
    profileC.weightedCap w profileC.totalCap profileC.slopeCap hC
    (ContactStackedBoxTransport6656Research.quotientC_dvd_right A B C) hboxC
theorem gcd123_support_of_flagB
    (A B C:GlobalPoly) (hA:A≠0) (hB:B≠0) (hC:C≠0)
    (hboxA:A∈globalCoefficientBox IRSProfile.Field
      profileA.weightedCap w profileA.totalCap profileA.slopeCap)
    (hboxB:B∈globalCoefficientBox IRSProfile.Field
      profileB.weightedCap w profileB.totalCap profileB.slopeCap)
    (hboxC:C∈globalCoefficientBox IRSProfile.Field
      profileC.weightedCap w profileC.totalCap profileC.slopeCap)
    (hflagB:B∈ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field profileB.weightedCap w profileB.totalCap profileB.slopeCap):
    ResidualSupportData fixedSupport (gcd123 A B C):=by
  have hbox:=gcd123_mem_meet_box A B C hA hC
    (gcd12_mem_meet_box A B hA hB hboxA hboxB) hboxC
  refine ⟨?_,?_,?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights (gcd123 A B C) 12).mpr
    intro d hd
    have hb:=hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0*0+d 1*0+d 2*1+d 3*0 ≤ 12
    simpa using hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights (gcd123 A B C) 59).mpr
    intro d hd
    have hb:d 1+d 3 ≤ 1394∧d 2 ≤ 12∧
        d 0+131071*d 1+131070*d 2 < 43*agreements:=hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0*0+d 1*1+d 2*1+d 3*0 ≤ 59
    norm_num [ContactTwoTailParameters6735Research.agreements,
      ContactTwoTailParameters6735Research.n,
      ContactTwoTailParameters6735Research.errors,
      ContactTwoTailParameters6735Research.w] at hb ⊢
    omega
  · have hBtotal:wt residualTotalWeights B ≤ 1394:=by
      apply (weightedTotalDegree_le_iff residualTotalWeights B 1394).mpr
      intro d hd
      have hb:=hflagB hd
      rw [ContactFactorCaps.weight_fin4]
      change d 0*0+d 1*1+d 2*1+d 3*1 ≤ 1394
      simpa [profileB] using hb.1
    have hdiv:gcd123 A B C∣B:=
      (gcd_dvd_left (gcd12 A B) C).trans (gcd_dvd_right A B)
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (gcd123 A B C) B hdiv hB).trans hBtotal
end
end ProximityPrize.SubmissionLower.ContactTwoTailStackedBoxTransport6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactTwoTailFixedStage6735Research
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
  ContactTwoTailFixedProvider6735Research.fixedProfile
abbrev fixedSupport:=
  ContactTwoTailFixedProvider6735Research.fixedSupport
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K ContactTwoTailParameters6735Research.prime:=by
  simpa [ContactTwoTailParameters6735Research.prime,
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
    letI:CharP (GenericField K) ContactTwoTailParameters6735Research.prime:=
      genericField_charP K ContactTwoTailParameters6735Research.prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
      IRSProfile.domain ContactTwoTailParameters6735Research.prime
      fixedProfile.errors (geometricCumulativeFlag K g) fixedProfile.w
      fixedSupport:=by
  letI:CharP (GenericField K) ContactTwoTailParameters6735Research.prime:=
    genericField_charP K ContactTwoTailParameters6735Research.prime
  have hRdata:=directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRsmall:R.1.degreeOf (2:Fin 4) <
      ContactTwoTailParameters6735Research.prime:=
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
end ProximityPrize.SubmissionLower.ContactTwoTailFixedStage6735Research
end

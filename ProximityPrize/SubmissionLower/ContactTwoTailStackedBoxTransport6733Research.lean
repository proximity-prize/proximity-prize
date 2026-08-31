import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6656Research
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactResidualSupportParametersResearch
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedBoxTransport6733Research
open ProximityPrize.Benchmark
open ContactInterpolation ContactFactorCaps ContactRecursiveGCDResearch
open ContactTwoTailParameters6733Research
open ContactResidualSupportParametersResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
def fixedSupport:ResidualSupportParameters:=
  ⟨11,56,1242,by decide,by decide,by decide,by decide⟩
local instance:GCDMonoid GlobalPoly:=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
theorem gcd12_mem_meet_box
    (A B:GlobalPoly) (hA:A≠0) (hB:B≠0)
    (hboxA:A∈globalCoefficientBox IRSProfile.Field
      profileA.weightedCap w profileA.totalCap profileA.slopeCap)
    (hboxB:B∈globalCoefficientBox IRSProfile.Field
      profileB.weightedCap w profileB.totalCap profileB.slopeCap):
    gcd12 A B∈globalCoefficientBox IRSProfile.Field
      (41*agreements) w 1242 12:=by
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
      (41*agreements) w 1242 12)
    (hboxC:C∈globalCoefficientBox IRSProfile.Field
      profileC.weightedCap w profileC.totalCap profileC.slopeCap):
    gcd123 A B C∈globalCoefficientBox IRSProfile.Field
      (41*agreements) w 1242 11:=by
  have h12:=ContactStackedBoxTransport6656Research.gcd12_ne_zero (B:=B) hA
  have hfrom12:=mem_globalCoefficientBox_of_dvd (gcd123 A B C) (gcd12 A B)
    (41*agreements) w 1242 12 h12 (gcd_dvd_left (gcd12 A B) C) hbox12
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
      (41*agreements) w 1242 12):
    middleQuotient A B C∈globalCoefficientBox IRSProfile.Field
      (41*agreements) w 1242 12:=
  mem_globalCoefficientBox_of_dvd (middleQuotient A B C) (gcd12 A B)
    (41*agreements) w 1242 12
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
  · apply (weightedTotalDegree_le_iff residualSWeights (gcd123 A B C) 11).mpr
    intro d hd
    have hb:=hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0*0+d 1*0+d 2*1+d 3*0 ≤ 11
    simpa using hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights (gcd123 A B C) 56).mpr
    intro d hd
    have hb:d 1+d 3 ≤ 1242∧d 2 ≤ 11∧
        d 0+131071*d 1+131070*d 2 < 41*agreements:=hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0*0+d 1*1+d 2*1+d 3*0 ≤ 56
    norm_num [ContactTwoTailParameters6733Research.agreements,
      ContactTwoTailParameters6733Research.n,
      ContactTwoTailParameters6733Research.errors,
      ContactTwoTailParameters6733Research.w] at hb ⊢
    omega
  · have hBtotal:wt residualTotalWeights B ≤ 1242:=by
      apply (weightedTotalDegree_le_iff residualTotalWeights B 1242).mpr
      intro d hd
      have hb:=hflagB hd
      rw [ContactFactorCaps.weight_fin4]
      change d 0*0+d 1*1+d 2*1+d 3*1 ≤ 1242
      simpa [profileB] using hb.1
    have hdiv:gcd123 A B C∣B:=
      (gcd_dvd_left (gcd12 A B) C).trans (gcd_dvd_right A B)
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (gcd123 A B C) B hdiv hB).trans hBtotal
end
end ProximityPrize.SubmissionLower.ContactTwoTailStackedBoxTransport6733Research

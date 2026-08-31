import ProximityPrize.SubmissionLower.ContactFlagKernelUniversalityResearch
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedInterpolation6733Research
open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactTranslation ContactFlagKernelUniversalityResearch
open ContactTwoTailParameters6733Research ContactStackedGCDCover6670Research
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
theorem exists_universal_interpolants
    (u0 u1:IRSProfile.Index → IRSProfile.Field):
    ∃ QA QB QC:GlobalPoly,
      QA≠0∧QA∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileA.weightedCap w profileA.totalCap profileA.slopeCap∧
      QB≠0∧QB∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap∧
      QC≠0∧QC∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileC.weightedCap w profileC.totalCap profileC.slopeCap∧
      QB∈globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap∧
      ∀ gamma P (support:Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i∈support,P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
        specialization IRSProfile.Field P gamma QA=0∧
        specialization IRSProfile.Field P gamma QB=0∧
        specialization IRSProfile.Field P gamma QC=0:=by
  have hindex:Fintype.card IRSProfile.Index=n:=by
    norm_num [IRSProfile.Index,n]
  have hA:Fintype.card IRSProfile.Index*
      localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap <
      coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap:=by
    rw [hindex]
    exact interpolation_gateA_exact
  have hB:Fintype.card IRSProfile.Index*
      localRankBound profileB.multiplicity profileB.totalCap profileB.slopeCap <
      coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap:=by
    rw [hindex]
    exact interpolation_gateB_exact
  have hC:Fintype.card IRSProfile.Index*
      localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap <
      coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap:=by
    rw [hindex]
    exact interpolation_gateC_exact
  obtain ⟨thetaA,hnA,hkA⟩:=exists_nonzero_kernel_array
    IRSProfile.Field profileA.weightedCap w profileA.totalCap profileA.slopeCap
      profileA.multiplicity IRSProfile.domain u0 u1 hA
  obtain ⟨thetaB,hnB,hkB⟩:=exists_nonzero_kernel_array
    IRSProfile.Field profileB.weightedCap w profileB.totalCap profileB.slopeCap
      profileB.multiplicity IRSProfile.domain u0 u1 hB
  obtain ⟨thetaC,hnC,hkC⟩:=exists_nonzero_kernel_array
    IRSProfile.Field profileC.weightedCap w profileC.totalCap profileC.slopeCap
      profileC.multiplicity IRSProfile.domain u0 u1 hC
  have hDA:0 < profileA.weightedCap:=by decide
  have hDB:0 < profileB.weightedCap:=by decide
  have hDC:0 < profileC.weightedCap:=by decide
  have rA:=nonzero_kernel_member_universal IRSProfile.Field
    profileA.weightedCap w profileA.totalCap profileA.slopeCap profileA.multiplicity
    agreements IRSProfile.domain u0 u1 thetaA hnA (LinearMap.mem_ker.mpr hkA) hDA rfl
  have rB:=nonzero_kernel_member_universal IRSProfile.Field
    profileB.weightedCap w profileB.totalCap profileB.slopeCap profileB.multiplicity
    agreements IRSProfile.domain u0 u1 thetaB hnB (LinearMap.mem_ker.mpr hkB) hDB rfl
  have rC:=nonzero_kernel_member_universal IRSProfile.Field
    profileC.weightedCap w profileC.totalCap profileC.slopeCap profileC.multiplicity
    agreements IRSProfile.domain u0 u1 thetaC hnC (LinearMap.mem_ker.mpr hkC) hDC rfl
  let QA:=reconstruct IRSProfile.Field profileA.weightedCap w
    profileA.totalCap profileA.slopeCap thetaA
  let QB:=reconstruct IRSProfile.Field profileB.weightedCap w
    profileB.totalCap profileB.slopeCap thetaB
  let QC:=reconstruct IRSProfile.Field profileC.weightedCap w
    profileC.totalCap profileC.slopeCap thetaC
  refine ⟨QA,QB,QC,rA.1,
    flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rA.2.1,
    rB.1,flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rB.2.1,
    rC.1,flag_box_to_ordinary IRSProfile.Field _ w _ _ _ rC.2.1,
    rB.2.1,?_⟩
  intro gamma P support hP hcard hvalues
  exact ⟨rA.2.2 gamma P support hP hcard hvalues,
    rB.2.2 gamma P support hP hcard hvalues,
    rC.2.2 gamma P support hP hcard hvalues⟩
local instance:GCDMonoid GlobalPoly:=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
theorem exists_interpolants_with_recursive_cover
    (u0 u1:IRSProfile.Index → IRSProfile.Field):
    ∃ QA QB QC:GlobalPoly,
      QA≠0∧QA∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileA.weightedCap w profileA.totalCap profileA.slopeCap∧
      QB≠0∧QB∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap∧
      QC≠0∧QC∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
        profileC.weightedCap w profileC.totalCap profileC.slopeCap∧
      QB∈globalCoefficientBox IRSProfile.Field
        profileB.weightedCap w profileB.totalCap profileB.slopeCap∧
      ∀ gamma P (support:Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i∈support,P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
        RecursiveSpecializationBranch P gamma QA QB QC:=by
  obtain ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,hflagB,hall⟩:=
    exists_universal_interpolants u0 u1
  refine ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,hflagB,?_⟩
  intro gamma P support hP hcard hvalues
  obtain ⟨hA,hB,hC⟩:=hall gamma P support hP hcard hvalues
  exact recursive_branch_of_three_vanishings P gamma QA QB QC hA hB hC
end
end ProximityPrize.SubmissionLower.ContactTwoTailStackedInterpolation6733Research

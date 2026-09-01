import ProximityPrize.SubmissionLower.ContactTwoTailInterpolantA6733Research
import ProximityPrize.SubmissionLower.ContactTwoTailInterpolantB6733Research
import ProximityPrize.SubmissionLower.ContactTwoTailInterpolantC6733Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedInterpolation6733Research
open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactTranslation ContactFlagKernelUniversalityResearch
open ContactTwoTailParameters6733Research ContactStackedGCDCover6670Research
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
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
  obtain ⟨QA,hQA,hboxA,hallA⟩:=
    ContactTwoTailInterpolantA6733Research.exists_universal_interpolant u0 u1
  obtain ⟨QB,hQB,hboxB,hallB⟩:=
    ContactTwoTailInterpolantB6733Research.exists_universal_interpolant u0 u1
  obtain ⟨QC,hQC,hboxC,hallC⟩:=
    ContactTwoTailInterpolantC6733Research.exists_universal_interpolant u0 u1
  refine ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,hboxB,?_⟩
  intro gamma P support hP hcard hvalues
  exact ⟨hallA gamma P support hP hcard hvalues,
    hallB gamma P support hP hcard hvalues,
    hallC gamma P support hP hcard hvalues⟩
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

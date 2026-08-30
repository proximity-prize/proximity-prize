import ProximityPrize.SubmissionLower.P6
import ProximityPrize.SubmissionLower.Q5
namespace ProximityPrize.SubmissionLower.ContactTwoTailSelectedBound6734Research
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactAlignmentBridge
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCDResearch
open ContactStackedGCDCover6670Research ContactStackedSeedPartition6670Research
open ContactIdentityResidualGlobalFlagResearch ContactResidualSupportParametersResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactKernelCommonGCDResearch ContactKernelSelectedInterpolation6733Research
open ContactTwoTailParameters6734Research
open ContactTwoTailFixedSelectedGeneric6734Research
open ContactTwoTailRectangleStageBounds6734Research
open ContactTwoTailResidualGeneric6734Research
open ContactTwoTailResidualRectangles6734Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid GlobalPoly :=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
theorem selected_recursive_cover
   (U : Fin 2 → I → K) (seeds : Finset K)
   (A : K → Finset I) (selected : K → Polynomial K)
   (S : SelectedInterpolants (U 0) (U 1))
   (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
   (hcard : ∀ gamma ∈ seeds,
     Fintype.card I - errors ≤ (A gamma).card)
   (hvalues : ∀ gamma ∈ seeds, ∀ i ∈ A gamma,
     (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i) :
   ∀ gamma ∈ seeds,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC := by
 intro gamma hgamma
 have hv := S.universal_vanishing gamma (selected gamma) (A gamma)
   (hdegree gamma hgamma) (by
     have hh := hcard gamma hgamma
     norm_num [I, IRSProfile.Index, errors, n, agreements,
       ContactKernelSelectedInterpolation6733Research.agreements6733] at hh ⊢
     exact hh) (hvalues gamma hgamma)
 apply recursive_branch_of_three_vanishings
 exact hv.1
 exact hv.2.1
 exact hv.2.2
theorem selected_full_domain_agreement
   (U : Fin 2 → I → K) (seeds : Finset K)
   (A : K → Finset I) (selected : K → Polynomial K)
   (hcard : ∀ gamma ∈ seeds,
     Fintype.card I - errors ≤ (A gamma).card)
   (hvalues : ∀ gamma ∈ seeds, ∀ i ∈ A gamma,
     (selected gamma).eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i) :
   ∀ gamma ∈ seeds, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) =
         U 0 i + gamma * U 1 i)).card := by
 intro gamma hgamma
 have hsub : A gamma ⊆
     (Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) =
         U 0 i + gamma * U 1 i) := by
   intro i hi
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalues gamma hgamma i hi⟩
 have hsize := (hcard gamma hgamma).trans (Finset.card_le_card hsub)
 norm_num [I, IRSProfile.Index, errors, n, agreements] at hsize ⊢
 exact hsize
theorem selected_card_le_of_rectangle
   (a b s lt ly ls us : ℕ)
   (stageBound : FixedStageBound a b s)
   (validFirst : ResidualValidity (firstStage lt ly ls us) (firstPivot lt ls))
   (validSecond : ResidualValidity (secondStage lt ly ls us) (secondPivot lt ls))
   (hbudget : rectangleCost a b s lt ly ls us < mcaBudget)
   (hsSmall : s + 2 < prime)
   (hseedSmall : (2 * (s + 2) - 1) * (a + b + s + 3) < prime)
   (himplicitYSmall : (fixedTightProfile a b s).implicitYCap < prime)
   (hmixedSmall : 2 * (fixedTightProfile a b s).implicitYCap *
     (fixedTightProfile a b s).algebraicCap < prime)
   {u0 u1 : I → K} (S : SelectedInterpolants u0 u1)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (htotalUpper : wt residualTotalWeights S.G ≤ a + b + s + 3)
   (hysUpper : wt residualYSWeights S.G ≤ b + s + 3)
   (hsUpper : wt residualSWeights S.G ≤ s + 2)
   (htotalLower : lt ≤ wt residualTotalWeights S.G)
   (hysLower : ly ≤ wt residualYSWeights S.G)
   (hsLower : ls ≤ wt residualSWeights S.G)
   (hus : us = s + 2) :
   Gamma.card ≤ mcaBudget := by
 have hGeq : gcd123 S.QA S.QB S.QC = S.G := by
   simpa [gcd123, gcd12, S.H_eq] using S.G_eq.symm
 have hHcaps := (mem_flagGlobalCoefficientBox_iff S.H
   profileA.weightedCap w profileA.totalCap profileA.slopeCap
   (by norm_num [profileA, Profile.weightedCap, agreements, errors, n])).mp S.H_flagA
 have hHbox : S.H ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
     profileA.weightedCap w 1261 profileA.slopeCap := by
   apply (mem_flagGlobalCoefficientBox_iff S.H profileA.weightedCap w 1261
     profileA.slopeCap
     (by norm_num [profileA, Profile.weightedCap, agreements, errors, n])).mpr
   exact ⟨S.H_total_le, hHcaps.2.1, hHcaps.2.2⟩
 have hGcapsC := (mem_flagGlobalCoefficientBox_iff S.G
   profileC.weightedCap w profileC.totalCap profileC.slopeCap
   (by norm_num [profileC, Profile.weightedCap, agreements, errors, n])).mp S.G_flagC
 have hGflag : S.G ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
     (41 * agreements) w (a + b + s + 3) (s + 2) := by
   apply (mem_flagGlobalCoefficientBox_iff S.G (41 * agreements) w
     (a + b + s + 3) (s + 2) (by norm_num [agreements, errors, n])).mpr
   refine ⟨htotalUpper, hsUpper, ?_⟩
   simpa [profileC, Profile.weightedCap] using hGcapsC.2.2
 have hGbox : S.G ∈ globalCoefficientBox K
     (41 * agreements) w (a + b + s + 3) (s + 2) :=
   ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
     (K := K) (D := 41 * agreements) (w := w)
     (L := a + b + s + 3) (s := s + 2) S.G hGflag
 have hsupport : ResidualSupportData
     (ContactMovingAgreementCertificate6719Research.support a b s) S.G := by
   refine ⟨?_, ?_, ?_⟩
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using hsUpper
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using hysUpper
   · simpa only [ContactMovingAgreementCertificate6719Research.support] using htotalUpper
 let fixedDelta := fixedSeeds selected Gamma S.QA S.QB S.QC
 have hfixedSub : fixedDelta ⊆ Gamma := by
   simpa only [fixedDelta] using fixedSeeds_subset selected Gamma S.QA S.QB S.QC
 have hfixedSolution : ∀ gamma ∈ fixedDelta,
     specialization K (selected gamma) gamma S.G = 0 := by
   intro gamma hgamma
   have hv := fixedSeeds_vanish selected Gamma S.QA S.QB S.QC gamma hgamma
   simpa only [hGeq] using hv
 have hfixed := fixed_count_le a b s hsSmall stageBound hseedSmall
   himplicitYSmall hmixedSmall S.G S.G_ne hGbox hsupport selected fixedDelta u0 u1
   hfixedSolution
   (fun gamma hgamma => hdegree gamma (hfixedSub hgamma))
   (fun gamma hgamma => hagreement gamma (hfixedSub hgamma))
   (noLargeSelectedPencil_mono selected Gamma fixedDelta w errors hfixedSub hnoPencil)
 have hfirst := firstResidualCell_count_lt lt ly ls us validFirst
   S.QA S.QB S.QC S.QA_ne S.QB_ne S.QA_flag S.QB_flag
   (by simpa only [hGeq] using htotalLower)
   (by simpa only [hGeq] using hysLower)
   (by simpa only [hGeq] using hsLower)
   (by simpa only [hGeq, hus] using hsUpper)
   selected Gamma u0 u1 hcover hdegree hagreement hnoPencil
 have hsecond := secondResidualCell_count_lt lt ly ls us validSecond
   S.QA S.QB S.QC S.QA_ne S.QC_ne S.QC_flag (by
     have hh : gcd S.QA S.QB ∈
         ContactFlagInterpolation6641Research.globalCoefficientBox K
           profileA.weightedCap w 1261 profileA.slopeCap := by
       rw [← S.H_eq]
       exact hHbox
     simpa only [gcd12] using hh)
   (by simpa only [hGeq] using htotalLower)
   (by simpa only [hGeq] using hysLower)
   (by simpa only [hGeq] using hsLower)
   (by simpa only [hGeq, hus] using hsUpper)
   selected Gamma u0 u1 hcover hdegree hagreement hnoPencil
 have hpartition : Gamma.card =
     (firstResidualSeeds selected Gamma S.QA S.QB).card +
     (secondResidualSeeds selected Gamma S.QA S.QB S.QC).card +
     (fixedSeeds selected Gamma S.QA S.QB S.QC).card :=
   (partition_card selected Gamma S.QA S.QB S.QC).symm
 have hfixed' : (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
     fixedRegularCost a b s + (fixedTightProfile a b s).countCap := by
   simpa only [fixedDelta] using hfixed
 unfold rectangleCost at hbudget
 omega
def RectangleSideConditions (a b s : ℕ) : Prop :=
 s + 2 < prime ∧
 (2 * (s + 2) - 1) * (a + b + s + 3) < prime ∧
 (fixedTightProfile a b s).implicitYCap < prime ∧
 2 * (fixedTightProfile a b s).implicitYCap *
   (fixedTightProfile a b s).algebraicCap < prime
theorem rectangleSideConditions_of_profiles (a b s : ℕ)
   (h :
     (a = 1207 ∧ b = 41 ∧ s = 10) ∨
     (a = 1207 ∧ b = 42 ∧ s = 9) ∨
     (a = 1208 ∧ b = 40 ∧ s = 10) ∨
     (a = 1208 ∧ b = 41 ∧ s = 9) ∨
     (a = 1206 ∧ b = 41 ∧ s = 10) ∨
     (a = 1206 ∧ b = 42 ∧ s = 9) ∨
     (a = 1207 ∧ b = 40 ∧ s = 10) ∨
     (a = 1207 ∧ b = 41 ∧ s = 9) ∨
     (a = 1206 ∧ b = 43 ∧ s = 9) ∨
     (a = 1206 ∧ b = 44 ∧ s = 8) ∨
     (a = 1207 ∧ b = 43 ∧ s = 8) ∨
     (a = 1205 ∧ b = 43 ∧ s = 9) ∨
     (a = 1205 ∧ b = 44 ∧ s = 8) ∨
     (a = 1206 ∧ b = 43 ∧ s = 8)) :
   RectangleSideConditions a b s := by
 rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
   rcases h with ⟨rfl, rfl, rfl⟩ <;>
   norm_num [RectangleSideConditions,
     ContactTwoTailParameters6734Research.prime,
     ContactTwoTailParameters6734Research.n,
     ContactTwoTailParameters6734Research.w,
     ContactTwoTailParameters6734Research.errors,
     ContactTwoTailParameters6734Research.agreements,
     ContactTwoTailFixedSelectedGeneric6734Research.fixedTightProfile,
     ContactTightSingularLedgerResearch.TightParameters.errors,
     ContactTightSingularLedgerResearch.TightParameters.gap,
     ContactTightSingularLedgerResearch.TightParameters.kappa,
     ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
     ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
     ContactTightSingularLedgerResearch.TightParameters.agreement,
     ContactTightSingularLedgerResearch.TightParameters.aggregateCost,
     ContactTightSingularLedgerResearch.TightParameters.coreNumerator,
     ContactTightSingularLedgerResearch.TightParameters.tightNumerator,
     ContactTightSingularLedgerResearch.TightParameters.countCap]
theorem selected_card_le_of_certified_rectangle
   (a b s lt ly ls us : ℕ)
   (stageBound : FixedStageBound a b s)
   (validFirst : ResidualValidity (firstStage lt ly ls us) (firstPivot lt ls))
   (validSecond : ResidualValidity (secondStage lt ly ls us) (secondPivot lt ls))
   (hbudget : rectangleCost a b s lt ly ls us < mcaBudget)
   (hside : RectangleSideConditions a b s)
   {u0 u1 : I → K} (S : SelectedInterpolants u0 u1)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma S.QA S.QB S.QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (htotalUpper : wt residualTotalWeights S.G ≤ a + b + s + 3)
   (hysUpper : wt residualYSWeights S.G ≤ b + s + 3)
   (hsUpper : wt residualSWeights S.G ≤ s + 2)
   (htotalLower : lt ≤ wt residualTotalWeights S.G)
   (hysLower : ly ≤ wt residualYSWeights S.G)
   (hsLower : ls ≤ wt residualSWeights S.G)
   (hus : us = s + 2) :
   Gamma.card ≤ mcaBudget :=
 selected_card_le_of_rectangle a b s lt ly ls us stageBound validFirst validSecond
   hbudget hside.1 hside.2.1 hside.2.2.1 hside.2.2.2 S selected Gamma hcover
   hdegree hagreement hnoPencil htotalUpper hysUpper hsUpper htotalLower hysLower
   hsLower hus
theorem selectedNoLargePencilBound6734 :
   SelectedNoLargePencilBound IRSProfile.domain 131071 errors mcaBudget := by
 intro U seeds A selected hdegreeRaw hcardRaw hvalues hnoRaw
 have hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w := by
   simpa [w] using hdegreeRaw
 have hcard : ∀ gamma ∈ seeds,
     Fintype.card I - errors ≤ (A gamma).card := by
   simpa [errors] using hcardRaw
 have hagreement := selected_full_domain_agreement U seeds A selected hcard hvalues
 have hno : NoLargeSelectedPencil selected seeds w errors := by
   intro P0 P1 hP0 hP1
   have hh := hnoRaw P0 P1 (by simpa [w] using hP0) (by simpa [w] using hP1)
   convert hh using 1
   · apply congrArg Finset.card
     ext gamma
     simp [pencilSeeds]
 let S : SelectedInterpolants (U 0) (U 1) :=
   Classical.choice (exists_selected_interpolants (U 0) (U 1))
 have hcover := selected_recursive_cover U seeds A selected S hdegree hcard hvalues
 have hGcapsC := (mem_flagGlobalCoefficientBox_iff S.G
   profileC.weightedCap w profileC.totalCap profileC.slopeCap
   (by norm_num [profileC, Profile.weightedCap, agreements, errors, n])).mp S.G_flagC
 have hs12 : wt residualSWeights S.G ≤ 12 := by
   simpa [profileC] using hGcapsC.2.1
 have ht1261 : wt residualTotalWeights S.G ≤ 1261 := S.G_total_le
 have hy55 : wt residualYSWeights S.G ≤ 55 := S.G_ys_le
 rcases S.G_corner with hys54 | hs11
 · have htSplit : wt residualTotalWeights S.G = 1261 ∨
       wt residualTotalWeights S.G ≤ 1260 := by omega
   have hySplit : wt residualYSWeights S.G = 54 ∨
       wt residualYSWeights S.G ≤ 53 := by omega
   have hsSplit : wt residualSWeights S.G = 12 ∨
       wt residualSWeights S.G ≤ 11 := by omega
   rcases htSplit with htHigh | htLow
   · rcases hySplit with hyHigh | hyLow
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_certified_rectangle 1207 41 10 1260 53 11 12
           stageBoundYS111 firstValidYS111 secondValidYS111 budgetYS111
           (rectangleSideConditions_of_profiles 1207 41 10 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
       · refine selected_card_le_of_certified_rectangle 1207 42 9 1260 53 0 11
           stageBoundYS110 firstValidYS110 secondValidYS110 budgetYS110
           (rectangleSideConditions_of_profiles 1207 42 9 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_certified_rectangle 1208 40 10 1260 0 11 12
           stageBoundYS101 firstValidYS101 secondValidYS101 budgetYS101
           (rectangleSideConditions_of_profiles 1208 40 10 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
       · refine selected_card_le_of_certified_rectangle 1208 41 9 1260 0 0 11
           stageBoundYS100 firstValidYS100 secondValidYS100 budgetYS100
           (rectangleSideConditions_of_profiles 1208 41 9 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
   · rcases hySplit with hyHigh | hyLow
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_certified_rectangle 1206 41 10 0 53 11 12
           stageBoundYS011 firstValidYS011 secondValidYS011 budgetYS011
           (rectangleSideConditions_of_profiles 1206 41 10 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
       · refine selected_card_le_of_certified_rectangle 1206 42 9 0 53 0 11
           stageBoundYS010 firstValidYS010 secondValidYS010 budgetYS010
           (rectangleSideConditions_of_profiles 1206 42 9 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_certified_rectangle 1207 40 10 0 0 11 12
           stageBoundYS001 firstValidYS001 secondValidYS001 budgetYS001
           (rectangleSideConditions_of_profiles 1207 40 10 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
       · refine selected_card_le_of_certified_rectangle 1207 41 9 0 0 0 11
           stageBoundYS000 firstValidYS000 secondValidYS000 budgetYS000
           (rectangleSideConditions_of_profiles 1207 41 9 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
 · have htSplit : wt residualTotalWeights S.G = 1261 ∨
       wt residualTotalWeights S.G ≤ 1260 := by omega
   have hySplit : wt residualYSWeights S.G = 55 ∨
       wt residualYSWeights S.G ≤ 54 := by omega
   have hsSplit : wt residualSWeights S.G = 11 ∨
       wt residualSWeights S.G ≤ 10 := by omega
   rcases htSplit with htHigh | htLow
   · rcases hySplit with hyHigh | hyLow
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_certified_rectangle 1206 43 9 1260 54 10 11
           stageBoundS111 firstValidS111 secondValidS111 budgetS111
           (rectangleSideConditions_of_profiles 1206 43 9 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
       · refine selected_card_le_of_certified_rectangle 1206 44 8 1260 54 0 10
           stageBoundS110 firstValidS110 secondValidS110 budgetS110
           (rectangleSideConditions_of_profiles 1206 44 8 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_certified_rectangle 1207 42 9 1260 0 10 11
           stageBoundS101 firstValidS101 secondValidS101 budgetS101
           (rectangleSideConditions_of_profiles 1207 42 9 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
       · refine selected_card_le_of_certified_rectangle 1207 43 8 1260 0 0 10
           stageBoundS100 firstValidS100 secondValidS100 budgetS100
           (rectangleSideConditions_of_profiles 1207 43 8 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
   · rcases hySplit with hyHigh | hyLow
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_certified_rectangle 1205 43 9 0 54 10 11
           stageBoundS011 firstValidS011 secondValidS011 budgetS011
           (rectangleSideConditions_of_profiles 1205 43 9 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
       · refine selected_card_le_of_certified_rectangle 1205 44 8 0 54 0 10
           stageBoundS010 firstValidS010 secondValidS010 budgetS010
           (rectangleSideConditions_of_profiles 1205 44 8 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
     · rcases hsSplit with hsHigh | hsLow
       · refine selected_card_le_of_certified_rectangle 1206 42 9 0 0 10 11
           stageBoundS001 firstValidS001 secondValidS001 budgetS001
           (rectangleSideConditions_of_profiles 1206 42 9 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
       · refine selected_card_le_of_certified_rectangle 1206 43 8 0 0 0 10
           stageBoundS000 firstValidS000 secondValidS000 budgetS000
           (rectangleSideConditions_of_profiles 1206 43 8 (by simp))
           S selected seeds hcover hdegree hagreement hno ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> omega
end
end ProximityPrize.SubmissionLower.ContactTwoTailSelectedBound6734Research

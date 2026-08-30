import ProximityPrize.SubmissionLower.GH
import ProximityPrize.SubmissionLower.GI
import ProximityPrize.SubmissionLower.L4
import ProximityPrize.SubmissionLower.AL
namespace ProximityPrize.SubmissionLower.ContactTwoTailResidualGeneric6734Research
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCDResearch
open ContactStackedGCDCover6670Research ContactStackedSeedPartition6670Research
open ContactTightSingularLedgerResearch ContactSingularLedger6600Research
open ContactSingularBranch6600Research ContactAsymmetricResidualStageResearch
open ContactRecursiveResidualStages6656Research
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactKernelCommonGCDResearch
open ContactTwoTailParameters6734Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev Poly4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid Poly4 := UniqueFactorizationMonoid.toGCDMonoid Poly4
local instance : CharP K prime := by
 simpa [prime, ContactParameters6600Research.prime] using
   ContactFrozenAlignment6600Research.challenge_field_characteristic6600
def firstStage (lt ly ls us : ℕ) : UnequalParameters :=
 ⟨n, w, agreements,
   (profileB.weightedCap - 1) / w, profileB.slopeCap - ls,
     profileB.totalCap - lt,
   (profileA.weightedCap - (w * ly - us) - 1) / w,
     profileA.slopeCap - ls, profileA.totalCap - lt⟩
def firstPivot (lt ls : ℕ) : TightParameters :=
 ⟨n, w, agreements, profileB.weightedCap,
   profileB.totalCap - lt, profileB.slopeCap - ls⟩
def secondStage (lt ly ls us : ℕ) : UnequalParameters :=
 ⟨n, w, agreements,
   (profileA.weightedCap - 1) / w, profileA.slopeCap - ls, 1261 - lt,
   (profileC.weightedCap - (w * ly - us) - 1) / w,
     profileC.slopeCap - ls, profileC.totalCap - lt⟩
def secondPivot (lt ls : ℕ) : TightParameters :=
 ⟨n, w, agreements, profileA.weightedCap, 1261 - lt,
   profileA.slopeCap - ls⟩
structure ResidualValidity (P : UnequalParameters) (S : TightParameters) : Prop where
 P_n : P.n = n
 S_n : S.n = n
 w_eq : P.w = S.w
 a_eq : P.a = S.a
 s_one : 1 ≤ S.s
 s_small : S.s < prime
 w_one : 1 ≤ S.w
 w_small : S.w < prime
 kD : S.w < S.kappa * S.D
 algebraic_pos : 1 ≤ S.algebraicCap
 implicit_small : S.implicitYCap < prime
 algebraic_small : S.algebraicCap < prime
 mixed_small : 2 * S.implicitYCap * S.algebraicCap < prime
 wa : S.w < S.a
 an : S.a ≤ S.n
 gap_pos : 0 < P.gap
 gap_eq : S.gap = P.gap
 qY : (S.D - 1) / S.w ≤ P.leftY
 qR : S.s ≤ P.leftR
 qZ : S.L ≤ P.leftZ
 leftR_pos : 1 ≤ P.leftR
 leftY_small : P.leftY < prime
 leftR_small : P.leftR < prime
 leftZ_small : P.leftZ < prime
 mixedY_small : P.mixedCost.y < prime
 mixedR_small : P.mixedCost.r < prime
 mixedZ_small : P.mixedCost.z < prime
theorem residual_count_lt
   (P : UnequalParameters) (S : TightParameters) (valid : ResidualValidity P S)
   (Q T : Poly4) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
   (hQbox : Q ∈ globalCoefficientBox K S.D S.w S.L S.s)
   (hTcaps : T.degreeOf 1 ≤ P.rightY ∧ T.degreeOf 2 ≤ P.rightR ∧
     T.degreeOf 3 ≤ P.rightZ)
   (selected : K → Polynomial K) (Delta : Finset K)
   (u0 u1 : I → K)
   (hQsolution : ∀ gamma ∈ Delta,
     specialization K (selected gamma) gamma Q = 0)
   (hTsolution : ∀ gamma ∈ Delta,
     specialization K (selected gamma) gamma T = 0)
   (hdegree : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ S.w)
   (hagreement : ∀ gamma ∈ Delta, S.a ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Delta S.w S.errors) :
   Delta.card < P.regularCountCap + S.countCap + 1 := by
 apply ContactStackedResidualCells6656Research.asymmetric_stage_count_lt_of_regular_factors
   P S Q T hQ prime valid.s_one valid.s_small valid.w_one valid.w_small valid.kD
   valid.algebraic_pos valid.implicit_small valid.algebraic_small valid.mixed_small
   valid.wa valid.an hQbox valid.gap_pos valid.gap_eq valid.qY valid.qR valid.qZ
   selected Delta (Finset.univ : Finset I) IRSProfile.domain u0 u1
   IRSProfile.domain.injective.injOn
   (by rw [valid.S_n]; norm_num [I, IRSProfile.Index, n])
   hdegree hQsolution hTsolution hagreement hnoPencil
 exact all_regularPairSeeds_bound P Q T hQ hrel S.D S.w S.L S.s prime hQbox
   valid.w_one valid.qY valid.qR valid.qZ hTcaps.1 hTcaps.2.1 hTcaps.2.2
   valid.leftR_pos valid.leftY_small valid.leftR_small valid.leftZ_small
   valid.mixedY_small valid.mixedR_small valid.mixedZ_small selected Delta
   (Finset.univ : Finset I) IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
   (by rw [valid.P_n]; norm_num [I, IRSProfile.Index, n])
   (by rw [valid.w_eq]; exact valid.w_one)
   (by rw [valid.w_eq]; exact valid.w_small)
   (by rw [valid.w_eq, valid.a_eq]; exact valid.wa)
   (by
     rw [valid.a_eq, valid.P_n]
     have hh := valid.an
     rw [valid.S_n] at hh
     exact hh)
   (by rw [valid.w_eq]; exact hdegree)
   (by rw [valid.a_eq]; exact hagreement)
   (by
     have herr : P.errors = S.errors := by
       simp only [UnequalParameters.errors, TightParameters.errors,
         valid.P_n, valid.S_n, valid.a_eq]
     simpa only [valid.w_eq, herr] using hnoPencil)
theorem gcd_contact_lower
   (G : Poly4) (ly us : ℕ)
   (hgy : ly ≤ wt residualYSWeights G)
   (hgs : wt residualSWeights G ≤ us) :
   w * ly - us ≤ wt (contactWeights w) G := by
 have h := residualYS_mul_le_contact_add_slope G w (by norm_num [w])
 have hlow : w * ly ≤ w * wt residualYSWeights G :=
   Nat.mul_le_mul_left w hgy
 omega
theorem firstResidualCell_count_lt
   (lt ly ls us : ℕ)
   (valid : ResidualValidity (firstStage lt ly ls us) (firstPivot lt ls))
   (QA QB QC : Poly4) (hQA : QA ≠ 0) (hQB : QB ≠ 0)
   (hboxA : QA ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
     profileA.weightedCap w profileA.totalCap profileA.slopeCap)
   (hboxB : QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
     profileB.weightedCap w profileB.totalCap profileB.slopeCap)
   (hgt : lt ≤ wt residualTotalWeights (gcd123 QA QB QC))
   (hgy : ly ≤ wt residualYSWeights (gcd123 QA QB QC))
   (hgs : ls ≤ wt residualSWeights (gcd123 QA QB QC))
   (hgsUpper : wt residualSWeights (gcd123 QA QB QC) ≤ us)
   (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
   (firstResidualSeeds selected Gamma QA QB).card <
     (firstStage lt ly ls us).regularCountCap + (firstPivot lt ls).countCap + 1 := by
 let Delta := firstResidualSeeds selected Gamma QA QB
 let H := gcd12 QA QB
 let G := gcd123 QA QB QC
 let Q := quotientB QA QB
 let T := quotientA QA QB
 have hH : H ≠ 0 := ContactStackedBoxTransport6656Research.gcd12_ne_zero hQA
 have hG : G ≠ 0 := ContactStackedBoxTransport6656Research.gcd123_ne_zero hQA
 have hQ : Q ≠ 0 := ContactStackedResidualCells6656Research.quotientB_ne_zero QA QB hQB
 have hT : T ≠ 0 := by
   intro hz
   apply hQA
   rw [a_eq_gcd12_mul_quotientA QA QB]
   simpa only [T, hz, mul_zero]
 have hGdivH : G ∣ H := by
   dsimp only [G, H]
   exact gcd_dvd_left (gcd12 QA QB) QC
 have htotalH : lt ≤ wt residualTotalWeights H := hgt.trans
   (weightedTotalDegree_le_of_dvd residualTotalWeights G H hGdivH hH)
 have hslopeH : ls ≤ wt residualSWeights H := hgs.trans
   (weightedTotalDegree_le_of_dvd residualSWeights G H hGdivH hH)
 have hcontactH : w * ly - us ≤ wt (contactWeights w) H :=
   (gcd_contact_lower G ly us hgy hgsUpper).trans
     (weightedTotalDegree_le_of_dvd (contactWeights w) G H hGdivH hH)
 have hQeq : QB = H * Q := by
   exact b_eq_gcd12_mul_quotientB QA QB
 have hTeq : QA = H * T := by
   exact a_eq_gcd12_mul_quotientA QA QB
 have hQflag := quotient_mem_flagGlobalCoefficientBox_of_mul_eq
   QB H Q profileB.weightedCap w profileB.totalCap profileB.slopeCap
   0 lt ls hQB hH hQ hboxB hQeq (by omega) htotalH hslopeH
 have hTflag := quotient_mem_flagGlobalCoefficientBox_of_mul_eq
   QA H T profileA.weightedCap w profileA.totalCap profileA.slopeCap
   (w * ly - us) lt ls hQA hH hT hboxA hTeq hcontactH htotalH hslopeH
 have hQbox : Q ∈ globalCoefficientBox K (firstPivot lt ls).D
     (firstPivot lt ls).w (firstPivot lt ls).L (firstPivot lt ls).s := by
   apply ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
   simpa [firstPivot] using hQflag
 have hTbox : T ∈ globalCoefficientBox K
     (profileA.weightedCap - (w * ly - us)) w (profileA.totalCap - lt)
     (profileA.slopeCap - ls) :=
   ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
     (K := K) (D := profileA.weightedCap - (w * ly - us)) (w := w)
     (L := profileA.totalCap - lt) (s := profileA.slopeCap - ls) T hTflag
 have hTraw := degree_bounds_of_mem_box T
   (profileA.weightedCap - (w * ly - us)) w (profileA.totalCap - lt)
   (profileA.slopeCap - ls) (by norm_num [w]) hTbox
 have hTcaps : T.degreeOf 1 ≤ (firstStage lt ly ls us).rightY ∧
     T.degreeOf 2 ≤ (firstStage lt ly ls us).rightR ∧
     T.degreeOf 3 ≤ (firstStage lt ly ls us).rightZ := by
   simpa only [firstStage] using hTraw
 have hsub : Delta ⊆ Gamma := by
   simpa only [Delta] using firstResidualSeeds_subset selected Gamma QA QB
 have hsolutions := firstResidualSeeds_quotient_vanish selected Gamma
   QA QB QC hcover
 have hQD : ∀ gamma ∈ Delta, specialization K (selected gamma) gamma Q = 0 :=
   fun gamma hgamma => (hsolutions gamma hgamma).2
 have hTD : ∀ gamma ∈ Delta, specialization K (selected gamma) gamma T = 0 :=
   fun gamma hgamma => (hsolutions gamma hgamma).1
 have hrel : IsRelPrime Q T := (firstQuotients_isRelPrime hQA).symm
 have hdD : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ (firstPivot lt ls).w := by
   intro gamma hgamma
   simpa [firstPivot] using hdegree gamma (hsub hgamma)
 have haD : ∀ gamma ∈ Delta, (firstPivot lt ls).a ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card := by
   intro gamma hgamma
   simpa [firstPivot] using hagreement gamma (hsub hgamma)
 have hnD : NoLargeSelectedPencil selected Delta (firstPivot lt ls).w
     (firstPivot lt ls).errors := by
   simpa [firstPivot, TightParameters.errors, errors, agreements, n, w] using
     noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
 simpa only [Delta] using residual_count_lt (firstStage lt ly ls us)
   (firstPivot lt ls) valid Q T hQ hrel hQbox hTcaps selected Delta u0 u1
   hQD hTD hdD haD hnD
theorem secondResidualCell_count_lt
   (lt ly ls us : ℕ)
   (valid : ResidualValidity (secondStage lt ly ls us) (secondPivot lt ls))
   (QA QB QC : Poly4) (hQA : QA ≠ 0) (hQC : QC ≠ 0)
   (hboxC : QC ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
     profileC.weightedCap w profileC.totalCap profileC.slopeCap)
   (hboxH : gcd12 QA QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
     profileA.weightedCap w 1261 profileA.slopeCap)
   (hgt : lt ≤ wt residualTotalWeights (gcd123 QA QB QC))
   (hgy : ly ≤ wt residualYSWeights (gcd123 QA QB QC))
   (hgs : ls ≤ wt residualSWeights (gcd123 QA QB QC))
   (hgsUpper : wt residualSWeights (gcd123 QA QB QC) ≤ us)
   (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
   (hcover : ∀ gamma ∈ Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
   (secondResidualSeeds selected Gamma QA QB QC).card <
     (secondStage lt ly ls us).regularCountCap + (secondPivot lt ls).countCap + 1 := by
 let Delta := secondResidualSeeds selected Gamma QA QB QC
 let H := gcd12 QA QB
 let G := gcd123 QA QB QC
 let Q := middleQuotient QA QB QC
 let T := quotientC QA QB QC
 have hH : H ≠ 0 := ContactStackedBoxTransport6656Research.gcd12_ne_zero hQA
 have hG : G ≠ 0 := ContactStackedBoxTransport6656Research.gcd123_ne_zero hQA
 have hQ : Q ≠ 0 :=
   ContactStackedResidualCells6656Research.middleQuotient_ne_zero QA QB QC hQA
 have hT : T ≠ 0 := by
   intro hz
   apply hQC
   rw [c_eq_gcd123_mul_quotientC QA QB QC]
   simpa only [T, hz, mul_zero]
 have hcontactG := gcd_contact_lower G ly us hgy hgsUpper
 have hQeq : H = G * Q := by
   exact gcd12_eq_gcd123_mul_middleQuotient QA QB QC
 have hTeq : QC = G * T := by
   exact c_eq_gcd123_mul_quotientC QA QB QC
 have hQflag := quotient_mem_flagGlobalCoefficientBox_of_mul_eq
   H G Q profileA.weightedCap w 1261 profileA.slopeCap 0 lt ls
   hH hG hQ hboxH hQeq (by omega)
   hgt hgs
 have hTflag := quotient_mem_flagGlobalCoefficientBox_of_mul_eq
   QC G T profileC.weightedCap w profileC.totalCap profileC.slopeCap
   (w * ly - us) lt ls hQC hG hT hboxC hTeq hcontactG hgt hgs
 have hQbox : Q ∈ globalCoefficientBox K (secondPivot lt ls).D
     (secondPivot lt ls).w (secondPivot lt ls).L (secondPivot lt ls).s := by
   apply ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
   simpa [secondPivot] using hQflag
 have hTbox : T ∈ globalCoefficientBox K
     (profileC.weightedCap - (w * ly - us)) w (profileC.totalCap - lt)
     (profileC.slopeCap - ls) :=
   ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
     (K := K) (D := profileC.weightedCap - (w * ly - us)) (w := w)
     (L := profileC.totalCap - lt) (s := profileC.slopeCap - ls) T hTflag
 have hTraw := degree_bounds_of_mem_box T
   (profileC.weightedCap - (w * ly - us)) w (profileC.totalCap - lt)
   (profileC.slopeCap - ls) (by norm_num [w]) hTbox
 have hTcaps : T.degreeOf 1 ≤ (secondStage lt ly ls us).rightY ∧
     T.degreeOf 2 ≤ (secondStage lt ly ls us).rightR ∧
     T.degreeOf 3 ≤ (secondStage lt ly ls us).rightZ := by
   simpa only [secondStage] using hTraw
 have hsub : Delta ⊆ Gamma := by
   simpa only [Delta] using secondResidualSeeds_subset selected Gamma QA QB QC
 have hsolutions := secondResidualSeeds_quotient_vanish selected Gamma
   QA QB QC hcover
 have hQD : ∀ gamma ∈ Delta, specialization K (selected gamma) gamma Q = 0 :=
   fun gamma hgamma => (hsolutions gamma hgamma).1
 have hTD : ∀ gamma ∈ Delta, specialization K (selected gamma) gamma T = 0 :=
   fun gamma hgamma => (hsolutions gamma hgamma).2
 have hrel : IsRelPrime Q T := secondQuotients_isRelPrime hQA
 have hdD : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ (secondPivot lt ls).w := by
   intro gamma hgamma
   simpa [secondPivot] using hdegree gamma (hsub hgamma)
 have haD : ∀ gamma ∈ Delta, (secondPivot lt ls).a ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card := by
   intro gamma hgamma
   simpa [secondPivot] using hagreement gamma (hsub hgamma)
 have hnD : NoLargeSelectedPencil selected Delta (secondPivot lt ls).w
     (secondPivot lt ls).errors := by
   simpa [secondPivot, TightParameters.errors, errors, agreements, n, w] using
     noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
 simpa only [Delta] using residual_count_lt (secondStage lt ly ls us)
   (secondPivot lt ls) valid Q T hQ hrel hQbox hTcaps selected Delta u0 u1
   hQD hTD hdD haD hnD
end
end ProximityPrize.SubmissionLower.ContactTwoTailResidualGeneric6734Research

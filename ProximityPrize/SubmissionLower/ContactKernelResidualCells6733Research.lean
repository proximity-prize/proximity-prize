import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactKernelCommonGCDResearch
import ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactExceptionalSeedCount
namespace ProximityPrize.SubmissionLower.ContactKernelResidualCells6733Research
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactRecursiveGCDResearch ContactPrimeSeedIncidence
open ContactProperCutSeedCount ContactParameters6600Research
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch ContactSingularLedger6600Research
open ContactAsymmetricResidualStageResearch
open ContactStackedGCDCover6670Research ContactStackedSeedPartition6670Research
open ContactKernelCommonGCDResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
def n : ℕ := 262144
def w : ℕ := 131071
def a : ℕ := 182052
def errors : ℕ := n - a
def gap : ℕ := a - w
def prime : ℕ := 2130706433
def paddedSlope (s : ℕ) : ℕ := max 1 s
def residualParameters
    (leftY rightY qTotal qSlope tTotal tSlope : ℕ) : UnequalParameters :=
  ⟨n,w,a,leftY,paddedSlope qSlope,qTotal,
    rightY,tSlope,tTotal⟩
def singularParameters (D qTotal qSlope : ℕ) : TightParameters :=
  ⟨n,w,a,D,qTotal,paddedSlope qSlope⟩
structure StageGates (P : UnequalParameters) (S : TightParameters) : Prop where
  singularSlopePositive : 1 ≤ S.s
  singularSlopeSmall : S.s < prime
  singularWeightPositive : 1 ≤ S.w
  singularWeightSmall : S.w < prime
  singularWeightedGate : S.w < S.kappa * S.D
  singularAlgebraicPositive : 1 ≤ S.algebraicCap
  singularImplicitSmall : S.implicitYCap < prime
  singularAlgebraicSmall : S.algebraicCap < prime
  singularMixedSmall : 2 * S.implicitYCap * S.algebraicCap < prime
  singularAgreement : S.w < S.a
  singularLength : S.a ≤ S.n
  carrierY : (S.D - 1) / S.w ≤ P.leftY
  carrierR : S.s ≤ P.leftR
  carrierZ : S.L ≤ P.leftZ
  leftYSmall : P.leftY < prime
  leftRSmall : P.leftR < prime
  leftZSmall : P.leftZ < prime
  mixedYSmall : P.mixedCost.y < prime
  mixedRSmall : P.mixedCost.r < prime
  mixedZSmall : P.mixedCost.z < prime
  regularWeightPositive : 1 ≤ P.w
  regularWeightSmall : P.w < prime
  regularAgreement : P.w < P.a
  regularLength : P.a ≤ P.n
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
abbrev Poly := MvPolynomial (Fin 4) IRSProfile.Field
local instance : GCDMonoid Poly :=
  UniqueFactorizationMonoid.toGCDMonoid Poly
local instance : CharP IRSProfile.Field prime := by
  simpa [prime,ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
theorem quotient_flag_box_keep_contact
    (F H Q : Poly) (D L s hTotal hSlope : ℕ)
    (hF : F ≠ 0) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hbox : F ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field D w L s)
    (heq : F = H * Q)
    (htotal : hTotal = wt residualTotalWeights H)
    (hslope : hSlope = wt residualSWeights H) :
    Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field D w (L - hTotal) (s - hSlope) := by
  simpa [w,htotal,hslope] using
    quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      F H Q D w L s 0 hTotal hSlope hF hH hQ hbox heq
      (Nat.zero_le _) (by simp [htotal]) (by simp [hslope])
theorem tight_flag_box_of_dvd
    (H F : Poly) (D L s : ℕ) (hF : F ≠ 0) (hdiv : H ∣ F)
    (hbox : F ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field D w L s) :
    H ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field D w (wt residualTotalWeights H)
        (wt residualSWeights H) := by
  have hparent := mem_flagGlobalCoefficientBox_of_dvd H F D w L s hF hdiv hbox
  have hD : 0 < D := by
    rcases MvPolynomial.support_nonempty.mpr hF with ⟨d,hd⟩
    have := (hbox hd).2.2
    omega
  have hc :=
    (mem_flagGlobalCoefficientBox_iff H D w L s hD).mp hparent
  apply (mem_flagGlobalCoefficientBox_iff H D w
    (wt residualTotalWeights H) (wt residualSWeights H) hD).mpr
  exact ⟨le_rfl,le_rfl,hc.2.2⟩
theorem pad_ordinary_slope
    (Q : Poly) (D L s : ℕ)
    (hbox : Q ∈ ContactInterpolation.globalCoefficientBox
      IRSProfile.Field D w L s) :
    Q ∈ ContactInterpolation.globalCoefficientBox
      IRSProfile.Field D w L (paddedSlope s) := by
  intro d hd
  have h := hbox hd
  exact ⟨h.1,h.2.1.trans (le_max_right 1 s),h.2.2⟩
theorem dynamic_stage_count_lt
    (P : UnequalParameters) (S : TightParameters)
    (Q T : Poly) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (hQbox : Q ∈ ContactInterpolation.globalCoefficientBox
      IRSProfile.Field S.D S.w S.L S.s)
    (hTY : T.degreeOf 1 ≤ P.rightY)
    (hTR : T.degreeOf 2 ≤ P.rightR)
    (hTZ : T.degreeOf 3 ≤ P.rightZ)
    (hgates : StageGates P S)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hdegree : ∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ w)
    (hQsolution : ∀ gamma ∈ Gamma,
      specialization IRSProfile.Field (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Gamma,
      specialization IRSProfile.Field (selected gamma) gamma T = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hshapeP : P.n = n ∧ P.w = w ∧ P.a = a)
    (hshapeS : S.n = n ∧ S.w = w ∧ S.a = a) :
    Gamma.card < P.regularCountCap + S.countCap + 1 := by
  have hdegreeS : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ S.w := by
    intro gamma hgamma
    simpa [hshapeS.1,hshapeS.2.1] using hdegree gamma hgamma
  have hagreementS : ∀ gamma ∈ Gamma,
      S.a ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    simpa [hshapeS.2.2] using hagreement gamma hgamma
  have hnoPencilS : NoLargeSelectedPencil selected Gamma S.w S.errors := by
    simpa [hshapeS.1,hshapeS.2.1,hshapeS.2.2,
      TightParameters.errors,errors,n,a,w] using hnoPencil
  have hregular := all_regularPairSeeds_bound P Q T hQ hrel
    S.D S.w S.L S.s prime hQbox hgates.singularWeightPositive
    hgates.carrierY hgates.carrierR hgates.carrierZ hTY hTR hTZ
    (hgates.singularSlopePositive.trans hgates.carrierR)
    hgates.leftYSmall hgates.leftRSmall
    hgates.leftZSmall hgates.mixedYSmall hgates.mixedRSmall
    hgates.mixedZSmall selected Gamma
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by simpa [hshapeP.1] using
      (show (Finset.univ : Finset IRSProfile.Index).card = n by
        norm_num [IRSProfile.Index,n]))
    hgates.regularWeightPositive hgates.regularWeightSmall
    hgates.regularAgreement hgates.regularLength
    (by simpa [hshapeP.2.1] using hdegree)
    (by simpa [hshapeP.2.2] using hagreement)
    (by simpa [hshapeP.1,hshapeP.2.1,hshapeP.2.2,
      UnequalParameters.errors,errors,n,a,w] using hnoPencil)
  exact
    ContactStackedResidualCells6656Research.asymmetric_stage_count_lt_of_regular_factors
      P S Q T hQ prime hgates.singularSlopePositive
      hgates.singularSlopeSmall hgates.singularWeightPositive
      hgates.singularWeightSmall hgates.singularWeightedGate
      hgates.singularAlgebraicPositive hgates.singularImplicitSmall
      hgates.singularAlgebraicSmall hgates.singularMixedSmall
      hgates.singularAgreement hgates.singularLength hQbox
      (by simpa [hshapeP.1,hshapeP.2.1,hshapeP.2.2,
        UnequalParameters.gap,n,w,a] using
          (show 0 < gap by norm_num [gap,n,w,a]))
      (by simp [hshapeP.2.1,hshapeP.2.2,hshapeS.2.1,hshapeS.2.2,
        UnequalParameters.gap,TightParameters.gap])
      hgates.carrierY hgates.carrierR hgates.carrierZ selected Gamma
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by simpa [hshapeS.1] using
        (show (Finset.univ : Finset IRSProfile.Index).card = n by
          norm_num [IRSProfile.Index,n]))
      hdegreeS hQsolution hTsolution hagreementS hnoPencilS hregular
def firstQTotal (QA QB : Poly) : ℕ :=
  1242 - wt residualTotalWeights (gcd12 QA QB)
def firstQSlope (QA QB : Poly) : ℕ :=
  25 - wt residualSWeights (gcd12 QA QB)
def firstTTotal (QA QB : Poly) : ℕ :=
  1003041 - wt residualTotalWeights (gcd12 QA QB)
def firstTSlope (QA QB : Poly) : ℕ :=
  12 - wt residualSWeights (gcd12 QA QB)
def firstStage (QA QB : Poly) : UnequalParameters :=
  residualParameters 112 56 (firstQTotal QA QB) (firstQSlope QA QB)
    (firstTTotal QA QB) (firstTSlope QA QB)
def firstSingular (QA QB : Poly) : TightParameters :=
  singularParameters 14746212 (firstQTotal QA QB) (firstQSlope QA QB)
def firstCeiling (QA QB : Poly) : ℕ :=
  if firstQTotal QA QB = 0 then 1
  else (firstStage QA QB).regularCountCap + (firstSingular QA QB).countCap + 1
theorem firstResidualCell_count_lt
    (QA QB QC : Poly) (hQA : QA ≠ 0) (hQB : QB ≠ 0)
    (hflagA : QA ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 7464132 w 1003041 12)
    (hflagB : QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 14746212 w 1242 25)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hcover : ∀ gamma ∈ Gamma,
      RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
    (hdegree : ∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hgates : firstQTotal QA QB ≠ 0 →
      StageGates (firstStage QA QB) (firstSingular QA QB)) :
    (firstResidualSeeds selected Gamma QA QB).card < firstCeiling QA QB := by
  let Delta := firstResidualSeeds selected Gamma QA QB
  let H := gcd12 QA QB
  let Q := quotientB QA QB
  let T := quotientA QA QB
  have hH : H ≠ 0 := gcd_ne_zero_of_left hQA
  have hQ : Q ≠ 0 :=
    ContactStackedResidualCells6656Research.quotientB_ne_zero QA QB hQB
  have hT : T ≠ 0 := by
    change quotientA QA QB ≠ 0
    intro hz
    apply hQA
    rw [a_eq_gcd12_mul_quotientA QA QB,hz,mul_zero]
  have hsolutions := firstResidualSeeds_quotient_vanish selected Gamma
    QA QB QC hcover
  have hQsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).2
  have hTsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma T = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).1
  have hQflag : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 14746212 w (firstQTotal QA QB) (firstQSlope QA QB) := by
    exact quotient_flag_box_keep_contact QB H Q 14746212 1242 25
      (wt residualTotalWeights H) (wt residualSWeights H)
      hQB hH hQ hflagB (b_eq_gcd12_mul_quotientB QA QB) rfl rfl
  have hTflag : T ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 7464132 w (firstTTotal QA QB) (firstTSlope QA QB) := by
    exact quotient_flag_box_keep_contact QA H T 7464132 1003041 12
      (wt residualTotalWeights H) (wt residualSWeights H)
      hQA hH hT hflagA (a_eq_gcd12_mul_quotientA QA QB) rfl rfl
  have hQord0 := ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
    IRSProfile.Field 14746212 w (firstQTotal QA QB) (firstQSlope QA QB) Q hQflag
  have hQord := pad_ordinary_slope Q 14746212
    (firstQTotal QA QB) (firstQSlope QA QB) hQord0
  have hTord := ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
    IRSProfile.Field 7464132 w (firstTTotal QA QB) (firstTSlope QA QB) T hTflag
  have hTcaps := degree_bounds_of_mem_box T 7464132 w
    (firstTTotal QA QB) (firstTSlope QA QB) (by norm_num [w]) hTord
  by_cases hzero : firstQTotal QA QB = 0
  · have hQY : Q.degreeOf 1 = 0 := by
      apply Nat.eq_zero_of_le_zero
      have htotal : Q.degreeOf 1 ≤ firstQTotal QA QB := by
        apply MvPolynomial.degreeOf_le_iff.mpr
        intro d hd
        have hh := hQflag hd
        change d 1 + d 2 + d 3 ≤ firstQTotal QA QB ∧
          d 2 ≤ firstQSlope QA QB ∧ _ at hh
        omega
      simpa [hzero] using htotal
    have hQR : Q.degreeOf 2 = 0 := by
      apply Nat.eq_zero_of_le_zero
      have htotal : Q.degreeOf 2 ≤ firstQTotal QA QB := by
        apply MvPolynomial.degreeOf_le_iff.mpr
        intro d hd
        have hh := hQflag hd
        change d 1 + d 2 + d 3 ≤ firstQTotal QA QB ∧
          d 2 ≤ firstQSlope QA QB ∧ _ at hh
        omega
      simpa [hzero] using htotal
    have hQZ : Q.degreeOf 3 ≤ 0 := by
      have htotal : Q.degreeOf 3 ≤ firstQTotal QA QB := by
        apply MvPolynomial.degreeOf_le_iff.mpr
        intro d hd
        have hh := hQflag hd
        change d 1 + d 2 + d 3 ≤ firstQTotal QA QB ∧
          d 2 ≤ firstQSlope QA QB ∧ _ at hh
        omega
      simpa [hzero] using htotal
    have hcard := ContactExceptionalSeedCount.card_actual_solution_seeds_le
      Q hQ hQY hQR Delta (fun gamma hgamma =>
        ⟨selected gamma,hQsolution gamma hgamma⟩)
    have : Delta.card = 0 := Nat.eq_zero_of_le_zero (hcard.trans hQZ)
    simp [firstCeiling,hzero,Delta,this]
  · have hsub : Delta ⊆ Gamma := by
      simpa [Delta] using firstResidualSeeds_subset selected Gamma QA QB
    have hdegreeDelta : ∀ gamma ∈ Delta,
        (selected gamma).natDegree ≤ w :=
      fun gamma hgamma => hdegree gamma (hsub hgamma)
    have hagreementDelta : ∀ gamma ∈ Delta,
        a ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i)).card :=
      fun gamma hgamma => hagreement gamma (hsub hgamma)
    have hnoPencilDelta : NoLargeSelectedPencil selected Delta w errors :=
      noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
    have hstage := dynamic_stage_count_lt
      (firstStage QA QB) (firstSingular QA QB) Q T hQ
      (firstQuotients_isRelPrime hQA).symm hQord
      (by simpa [firstStage,residualParameters,w] using hTcaps.1)
      (by simpa [firstStage,residualParameters] using hTcaps.2.1)
      (by simpa [firstStage,residualParameters] using hTcaps.2.2)
      (hgates hzero) selected Delta u0 u1 hdegreeDelta hQsolution hTsolution
      hagreementDelta hnoPencilDelta
      (by simp [firstStage,residualParameters,n,w,a])
      (by simp [firstSingular,singularParameters,n,w,a])
    simpa [firstCeiling,hzero,Delta] using hstage
def secondQTotal (QA QB QC : Poly) : ℕ :=
  wt residualTotalWeights (gcd12 QA QB) -
    wt residualTotalWeights (gcd123 QA QB QC)
def secondQSlope (QA QB QC : Poly) : ℕ :=
  wt residualSWeights (gcd12 QA QB) -
    wt residualSWeights (gcd123 QA QB QC)
def secondTTotal (QA QB QC : Poly) : ℕ :=
  624668 - wt residualTotalWeights (gcd123 QA QB QC)
def secondTSlope (QA QB QC : Poly) : ℕ :=
  11 - wt residualSWeights (gcd123 QA QB QC)
def secondStage (QA QB QC : Poly) : UnequalParameters :=
  residualParameters 56 59 (secondQTotal QA QB QC) (secondQSlope QA QB QC)
    (secondTTotal QA QB QC) (secondTSlope QA QB QC)
def secondSingular (QA QB QC : Poly) : TightParameters :=
  singularParameters 7464132 (secondQTotal QA QB QC) (secondQSlope QA QB QC)
def secondCeiling (QA QB QC : Poly) : ℕ :=
  if secondQTotal QA QB QC = 0 then 1
  else (secondStage QA QB QC).regularCountCap +
    (secondSingular QA QB QC).countCap + 1
theorem secondResidualCell_count_lt
    (QA QB QC : Poly) (hQA : QA ≠ 0) (hQC : QC ≠ 0)
    (hflagA : QA ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 7464132 w 1003041 12)
    (hflagC : QC ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 7828236 w 624668 11)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hcover : ∀ gamma ∈ Gamma,
      RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
    (hdegree : ∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hgates : secondQTotal QA QB QC ≠ 0 →
      StageGates (secondStage QA QB QC) (secondSingular QA QB QC)) :
    (secondResidualSeeds selected Gamma QA QB QC).card <
      secondCeiling QA QB QC := by
  let Delta := secondResidualSeeds selected Gamma QA QB QC
  let H := gcd12 QA QB
  let G := gcd123 QA QB QC
  let Q := middleQuotient QA QB QC
  let T := quotientC QA QB QC
  have hH : H ≠ 0 := gcd_ne_zero_of_left hQA
  have hG : G ≠ 0 := gcd_ne_zero_of_left hH
  have hQ : Q ≠ 0 :=
    ContactStackedResidualCells6656Research.middleQuotient_ne_zero QA QB QC hQA
  have hT : T ≠ 0 := by
    change quotientC QA QB QC ≠ 0
    intro hz
    apply hQC
    rw [c_eq_gcd123_mul_quotientC QA QB QC,hz,mul_zero]
  have hHflag : H ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 7464132 w (wt residualTotalWeights H)
        (wt residualSWeights H) :=
    tight_flag_box_of_dvd H QA 7464132 1003041 12 hQA
      (gcd_dvd_left QA QB) hflagA
  have hsolutions := secondResidualSeeds_quotient_vanish selected Gamma
    QA QB QC hcover
  have hQsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).1
  have hTsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma T = 0 :=
    fun gamma hgamma => (hsolutions gamma hgamma).2
  have hQflag : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 7464132 w (secondQTotal QA QB QC)
        (secondQSlope QA QB QC) := by
    exact quotient_flag_box_keep_contact H G Q 7464132
      (wt residualTotalWeights H) (wt residualSWeights H)
      (wt residualTotalWeights G) (wt residualSWeights G)
      hH hG hQ hHflag (gcd12_eq_gcd123_mul_middleQuotient QA QB QC) rfl rfl
  have hTflag : T ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field 7828236 w (secondTTotal QA QB QC)
        (secondTSlope QA QB QC) := by
    exact quotient_flag_box_keep_contact QC G T 7828236 624668 11
      (wt residualTotalWeights G) (wt residualSWeights G)
      hQC hG hT hflagC (c_eq_gcd123_mul_quotientC QA QB QC) rfl rfl
  have hQord0 := ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
    IRSProfile.Field 7464132 w (secondQTotal QA QB QC)
      (secondQSlope QA QB QC) Q hQflag
  have hQord := pad_ordinary_slope Q 7464132
    (secondQTotal QA QB QC) (secondQSlope QA QB QC) hQord0
  have hTord := ContactFlagKernelUniversalityResearch.flag_box_to_ordinary
    IRSProfile.Field 7828236 w (secondTTotal QA QB QC)
      (secondTSlope QA QB QC) T hTflag
  have hTcaps := degree_bounds_of_mem_box T 7828236 w
    (secondTTotal QA QB QC) (secondTSlope QA QB QC) (by norm_num [w]) hTord
  by_cases hzero : secondQTotal QA QB QC = 0
  · have hQY : Q.degreeOf 1 = 0 := by
      apply Nat.eq_zero_of_le_zero
      have htotal : Q.degreeOf 1 ≤ secondQTotal QA QB QC := by
        apply MvPolynomial.degreeOf_le_iff.mpr
        intro d hd
        have hh := hQflag hd
        change d 1 + d 2 + d 3 ≤ secondQTotal QA QB QC ∧
          d 2 ≤ secondQSlope QA QB QC ∧ _ at hh
        omega
      simpa [hzero] using htotal
    have hQR : Q.degreeOf 2 = 0 := by
      apply Nat.eq_zero_of_le_zero
      have htotal : Q.degreeOf 2 ≤ secondQTotal QA QB QC := by
        apply MvPolynomial.degreeOf_le_iff.mpr
        intro d hd
        have hh := hQflag hd
        change d 1 + d 2 + d 3 ≤ secondQTotal QA QB QC ∧
          d 2 ≤ secondQSlope QA QB QC ∧ _ at hh
        omega
      simpa [hzero] using htotal
    have hQZ : Q.degreeOf 3 ≤ 0 := by
      have htotal : Q.degreeOf 3 ≤ secondQTotal QA QB QC := by
        apply MvPolynomial.degreeOf_le_iff.mpr
        intro d hd
        have hh := hQflag hd
        change d 1 + d 2 + d 3 ≤ secondQTotal QA QB QC ∧
          d 2 ≤ secondQSlope QA QB QC ∧ _ at hh
        omega
      simpa [hzero] using htotal
    have hcard := ContactExceptionalSeedCount.card_actual_solution_seeds_le
      Q hQ hQY hQR Delta (fun gamma hgamma =>
        ⟨selected gamma,hQsolution gamma hgamma⟩)
    have : Delta.card = 0 := Nat.eq_zero_of_le_zero (hcard.trans hQZ)
    simp [secondCeiling,hzero,Delta,this]
  · have hsub : Delta ⊆ Gamma := by
      simpa [Delta] using secondResidualSeeds_subset selected Gamma QA QB QC
    have hdegreeDelta : ∀ gamma ∈ Delta,
        (selected gamma).natDegree ≤ w :=
      fun gamma hgamma => hdegree gamma (hsub hgamma)
    have hagreementDelta : ∀ gamma ∈ Delta,
        a ≤ ((Finset.univ : Finset IRSProfile.Index).filter (fun i =>
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i)).card :=
      fun gamma hgamma => hagreement gamma (hsub hgamma)
    have hnoPencilDelta : NoLargeSelectedPencil selected Delta w errors :=
      noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
    have hstage := dynamic_stage_count_lt
      (secondStage QA QB QC) (secondSingular QA QB QC) Q T hQ
      (secondQuotients_isRelPrime hQA) hQord
      (by simpa [secondStage,residualParameters,w] using hTcaps.1)
      (by simpa [secondStage,residualParameters] using hTcaps.2.1)
      (by simpa [secondStage,residualParameters] using hTcaps.2.2)
      (hgates hzero) selected Delta u0 u1 hdegreeDelta hQsolution hTsolution
      hagreementDelta hnoPencilDelta
      (by simp [secondStage,residualParameters,n,w,a])
      (by simp [secondSingular,singularParameters,n,w,a])
    simpa [secondCeiling,hzero,Delta] using hstage
end
end ProximityPrize.SubmissionLower.ContactKernelResidualCells6733Research

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ContactStackedParameters6656Research
import ProximityPrize.SubmissionLower.ContactTightSingularLedgerResearch
namespace ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
open scoped BigOperators
open ContactTightSingularLedgerResearch
open ContactParameters6600Research
open ContactSingularLedger6600Research
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
structure UnequalParameters where
  n:ℕ
  w:ℕ
  a:ℕ
  leftY:ℕ
  leftR:ℕ
  leftZ:ℕ
  rightY:ℕ
  rightR:ℕ
  rightZ:ℕ
  deriving DecidableEq
namespace UnequalParameters
def errors (P:UnequalParameters):ℕ:=P.n-P.a
def gap (P:UnequalParameters):ℕ:=P.a-P.w
def leftAgreement (P:UnequalParameters):ContactParameters6600Research.DegreeVector:=
  ⟨1+2*P.w*P.leftY,
    P.w*(2*P.leftR-1),
    2*P.w*P.leftZ+1⟩
def rightAgreement (P:UnequalParameters):ContactParameters6600Research.DegreeVector:=
  ⟨1+2*P.w*P.rightY,
    P.w*(2*P.rightR-1),
    2*P.w*P.rightZ+1⟩
def agreement (P:UnequalParameters):ContactParameters6600Research.DegreeVector:=
  ⟨max P.leftAgreement.y P.rightAgreement.y,
    max P.leftAgreement.r P.rightAgreement.r,
    max P.leftAgreement.z P.rightAgreement.z⟩
def mixedCost (P:UnequalParameters):ContactParameters6600Research.DegreeVector:=
  ⟨P.leftR*P.rightZ+P.leftZ*P.rightR,
    P.leftY*P.rightZ+P.leftZ*P.rightY,
    P.leftY*P.rightR+P.leftR*P.rightY⟩
def regularNumerator (P:UnequalParameters):ℕ:=
  (P.n-P.w)*dot P.agreement P.mixedCost+
    (P.errors+1)*P.gap*P.mixedCost.z
def regularCountCap (P:UnequalParameters):ℕ:=P.regularNumerator/P.gap
theorem regular_count_le (P:UnequalParameters) (count:ℕ)
    (hgap:0 < P.gap) (hcount:count*P.gap ≤ P.regularNumerator):
    count ≤ P.regularCountCap:=
  (Nat.le_div_iff_mul_le hgap).mpr hcount
end UnequalParameters
theorem complete_stage_count_lt
    (R:UnequalParameters) (S:TightParameters)
    (hgap:0 < R.gap) (hgapEq:S.gap=R.gap)
    {I:Type} [Fintype I]
    (total regular exceptions:ℕ) (count:I → ℕ)
    (cost:I → ContactParameters6600Research.DegreeVector)
    (hcover:total ≤ regular+((∑ i,count i)+exceptions))
    (hregular:regular*R.gap ≤ R.regularNumerator)
    (hy:(∑ i,(cost i).y) ≤ S.algebraicCap)
    (hr:(∑ i,(cost i).r) ≤ 2*S.implicitYCap*S.algebraicCap)
    (hz:(∑ i,(cost i).z) ≤ S.implicitYCap)
    (hcount:∀ i,count i*S.gap ≤
      (S.n-S.w)*dot S.agreement (cost i)+
        (S.errors+1)*S.gap*(cost i).z)
    (hexceptions:exceptions ≤ 2*S.algebraicCap^2):
    total < R.regularCountCap+S.countCap+1:=by
  have hregularCap:regular ≤ R.regularCountCap:=
    R.regular_count_le regular hgap hregular
  have hsingularScaled:=
    S.with_exceptions_bound count cost exceptions hy hr hz hcount hexceptions
  have hsingularGap:0 < S.gap:=by
    rw [hgapEq]
    exact hgap
  have hsingularCap:(∑ i,count i)+exceptions ≤ S.countCap:=by
    exact S.count_le_countCap _ hsingularGap hsingularScaled
  omega
def residualStageOne:UnequalParameters:=
  ⟨262144,131071,182807,34,7,5263,65,14,598⟩
def residualStageTwo:UnequalParameters:=
  ⟨262144,131071,182807,34,7,598,37,6,579299⟩
theorem residual_stage_values:
    residualStageOne.agreement=⟨17039231,3538917,1379653347⟩∧
      residualStageOne.mixedCost=⟨77868,362427,931⟩∧
      residualStageOne.regularCountCap=9865174615710∧
      residualStageTwo.agreement=⟨9699255,1703923,151858598459⟩∧
      residualStageTwo.mixedCost=⟨4058681,19718292,463⟩∧
      residualStageTwo.regularCountCap=362987233541405:=by
  norm_num [residualStageOne,residualStageTwo,UnequalParameters.agreement,
    UnequalParameters.leftAgreement,UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost,UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator,UnequalParameters.errors,
    UnequalParameters.gap,dot]
theorem residual_stage_ceilings:
    residualStageOne.regularCountCap+maximalResidualQA.countCap+1=
        9865174615710+61761704341774∧
      residualStageTwo.regularCountCap+maximalResidualH.countCap+1=
        362987233541405+7016664323607:=by
  rw [residual_stage_values.2.2.1,residual_stage_values.2.2.2.2.2,
    maximal_residual_count_caps.1,maximal_residual_count_caps.2]
  norm_num
theorem residual_stage_one_count_lt
    {I:Type} [Fintype I]
    (total regular exceptions:ℕ) (count:I → ℕ)
    (cost:I → ContactParameters6600Research.DegreeVector)
    (hcover:total ≤ regular+((∑ i,count i)+exceptions))
    (hregular:regular*residualStageOne.gap ≤ residualStageOne.regularNumerator)
    (hy:(∑ i,(cost i).y) ≤ maximalResidualQA.algebraicCap)
    (hr:(∑ i,(cost i).r) ≤
      2*maximalResidualQA.implicitYCap*maximalResidualQA.algebraicCap)
    (hz:(∑ i,(cost i).z) ≤ maximalResidualQA.implicitYCap)
    (hcount:∀ i,count i*maximalResidualQA.gap ≤
      (maximalResidualQA.n-maximalResidualQA.w)*
          dot maximalResidualQA.agreement (cost i)+
        (maximalResidualQA.errors+1)*maximalResidualQA.gap*(cost i).z)
    (hexceptions:exceptions ≤ 2*maximalResidualQA.algebraicCap^2):
    total < 9865174615710+61761704341774:=by
  have h:=complete_stage_count_lt residualStageOne maximalResidualQA
    (by norm_num [residualStageOne,UnequalParameters.gap])
    (by norm_num [residualStageOne,maximalResidualQA,UnequalParameters.gap,
      TightParameters.gap]) total regular exceptions count cost hcover hregular
      hy hr hz hcount hexceptions
  rw [residual_stage_ceilings.1] at h
  exact h
theorem residual_stage_two_count_lt
    {I:Type} [Fintype I]
    (total regular exceptions:ℕ) (count:I → ℕ)
    (cost:I → ContactParameters6600Research.DegreeVector)
    (hcover:total ≤ regular+((∑ i,count i)+exceptions))
    (hregular:regular*residualStageTwo.gap ≤ residualStageTwo.regularNumerator)
    (hy:(∑ i,(cost i).y) ≤ maximalResidualH.algebraicCap)
    (hr:(∑ i,(cost i).r) ≤
      2*maximalResidualH.implicitYCap*maximalResidualH.algebraicCap)
    (hz:(∑ i,(cost i).z) ≤ maximalResidualH.implicitYCap)
    (hcount:∀ i,count i*maximalResidualH.gap ≤
      (maximalResidualH.n-maximalResidualH.w)*
          dot maximalResidualH.agreement (cost i)+
        (maximalResidualH.errors+1)*maximalResidualH.gap*(cost i).z)
    (hexceptions:exceptions ≤ 2*maximalResidualH.algebraicCap^2):
    total < 362987233541405+7016664323607:=by
  have h:=complete_stage_count_lt residualStageTwo maximalResidualH
    (by norm_num [residualStageTwo,UnequalParameters.gap])
    (by norm_num [residualStageTwo,maximalResidualH,UnequalParameters.gap,
      TightParameters.gap]) total regular exceptions count cost hcover hregular
      hy hr hz hcount hexceptions
  rw [residual_stage_ceilings.2] at h
  exact h
end ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research

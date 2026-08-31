import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSingularLedger6600Research
namespace ProximityPrize.SubmissionLower.ContactTightSingularLedgerResearch
open scoped BigOperators
open ContactParameters6600Research
open ContactSingularLedger6600Research
theorem implicit_with_exceptions_tight_bound {I:Type} [Fintype I]
    (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
    (hy:(∑ i,(cost i).y) ≤ algebraicCap)
    (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
    (hz:(∑ i,(cost i).z) ≤ implicitYCap)
    (hcount:∀ i,count i*gap ≤
      (n-w)*dot liftedAgreement (cost i)+
        (errors+1)*gap*(cost i).z)
    (hexceptions:exceptions ≤ 2*algebraicCap^2):
    ((∑ i,count i)+exceptions)*gap ≤
      implicitCoreNumerator+2*algebraicCap^2*gap:=by
  have hmain:=sum_implicit_counts_bound count cost hy hr hz hcount
  calc
    _=(∑ i,count i)*gap+exceptions*gap:=Nat.add_mul _ _ _
    _ ≤ implicitCoreNumerator+2*algebraicCap^2*gap:=
      Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
theorem implicit_with_exceptions_tight_scaled_bound {I:Type} [Fintype I]
    (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
    (hy:(∑ i,(cost i).y) ≤ algebraicCap)
    (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
    (hz:(∑ i,(cost i).z) ≤ implicitYCap)
    (hcount:∀ i,count i*gap ≤
      (n-w)*dot liftedAgreement (cost i)+
        (errors+1)*gap*(cost i).z)
    (hexceptions:exceptions ≤ 2*algebraicCap^2):
    ((∑ i,count i)+exceptions)*gap^2 ≤
      (implicitCoreNumerator+2*algebraicCap^2*gap)*gap:=by
  have h:=implicit_with_exceptions_tight_bound count cost exceptions
    hy hr hz hcount hexceptions
  calc
    ((∑ i,count i)+exceptions)*gap^2=
        (((∑ i,count i)+exceptions)*gap)*gap:=by ring
    _ ≤ (implicitCoreNumerator+2*algebraicCap^2*gap)*gap:=
      Nat.mul_le_mul_right gap h
structure TightParameters where
  n:ℕ
  w:ℕ
  a:ℕ
  D:ℕ
  L:ℕ
  s:ℕ
  deriving DecidableEq
namespace TightParameters
def errors (P:TightParameters):ℕ:=P.n-P.a
def gap (P:TightParameters):ℕ:=P.a-P.w
def kappa (P:TightParameters):ℕ:=2*P.s-1
def implicitYCap (P:TightParameters):ℕ:=(P.kappa*P.D-1)/P.w
def algebraicCap (P:TightParameters):ℕ:=P.kappa*P.L
def agreement (P:TightParameters):DegreeVector:=
  ⟨1+2*P.w*P.implicitYCap,
    P.w,
    2*P.w*P.algebraicCap+1⟩
def aggregateCost (P:TightParameters):DegreeVector:=
  ⟨P.algebraicCap,
    2*P.implicitYCap*P.algebraicCap,
    P.implicitYCap⟩
def coefficients (P:TightParameters):DegreeVector:=
  ⟨(P.n-P.w)*P.agreement.y,
    (P.n-P.w)*P.agreement.r,
    (P.n-P.w)*P.agreement.z+(P.errors+1)*P.gap⟩
def coreNumerator (P:TightParameters):ℕ:=
  (P.n-P.w)*dot P.agreement P.aggregateCost+
    (P.errors+1)*P.gap*P.implicitYCap
def tightNumerator (P:TightParameters):ℕ:=
  P.coreNumerator+2*P.algebraicCap^2*P.gap
def countCap (P:TightParameters):ℕ:=P.tightNumerator/P.gap
theorem bound_eq_dot (P:TightParameters) (v:DegreeVector):
    (P.n-P.w)*dot P.agreement v+
        (P.errors+1)*P.gap*v.z=
      dot v P.coefficients:=by
  simp only [coefficients,errors,gap,dot]
  ring
theorem aggregate_eq_core (P:TightParameters):
    dot P.aggregateCost P.coefficients=P.coreNumerator:=by
  simp only [aggregateCost,coefficients,coreNumerator,dot]
  ring
theorem sum_counts_bound (P:TightParameters) {I:Type} [Fintype I]
    (count:I → ℕ) (cost:I → DegreeVector)
    (hy:(∑ i,(cost i).y) ≤ P.algebraicCap)
    (hr:(∑ i,(cost i).r) ≤ 2*P.implicitYCap*P.algebraicCap)
    (hz:(∑ i,(cost i).z) ≤ P.implicitYCap)
    (hcount:∀ i,count i*P.gap ≤
      (P.n-P.w)*dot P.agreement (cost i)+
        (P.errors+1)*P.gap*(cost i).z):
    (∑ i,count i)*P.gap ≤ P.coreNumerator:=by
  calc
    _=∑ i,count i*P.gap:=Finset.sum_mul _ _ _
    _ ≤ ∑ i,dot (cost i) P.coefficients:=by
      apply Finset.sum_le_sum
      intro i _
      rw [←P.bound_eq_dot]
      exact hcount i
    _=dot (sumVector cost) P.coefficients:=
      (dot_sum_left cost P.coefficients).symm
    _ ≤ dot P.aggregateCost P.coefficients:=
      dot_mono_left P.coefficients ⟨hy,hr,hz⟩
    _=P.coreNumerator:=P.aggregate_eq_core
theorem with_exceptions_bound (P:TightParameters) {I:Type} [Fintype I]
    (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
    (hy:(∑ i,(cost i).y) ≤ P.algebraicCap)
    (hr:(∑ i,(cost i).r) ≤ 2*P.implicitYCap*P.algebraicCap)
    (hz:(∑ i,(cost i).z) ≤ P.implicitYCap)
    (hcount:∀ i,count i*P.gap ≤
      (P.n-P.w)*dot P.agreement (cost i)+
        (P.errors+1)*P.gap*(cost i).z)
    (hexceptions:exceptions ≤ 2*P.algebraicCap^2):
    ((∑ i,count i)+exceptions)*P.gap ≤ P.tightNumerator:=by
  have hmain:=P.sum_counts_bound count cost hy hr hz hcount
  calc
    _=(∑ i,count i)*P.gap+exceptions*P.gap:=Nat.add_mul _ _ _
    _ ≤ P.coreNumerator+2*P.algebraicCap^2*P.gap:=
      Nat.add_le_add hmain (Nat.mul_le_mul_right P.gap hexceptions)
    _=P.tightNumerator:=rfl
theorem count_le_countCap (P:TightParameters) (count:ℕ)
    (hgap:0 < P.gap) (hcount:count*P.gap ≤ P.tightNumerator):
    count ≤ P.countCap:=by
  exact (Nat.le_div_iff_mul_le hgap).mpr hcount
end TightParameters
def maximalResidualQA:TightParameters:=
  ⟨262144,131071,182807,4570175,5263,7⟩
def maximalResidualH:TightParameters:=
  ⟨262144,131071,182807,4570175,598,7⟩
theorem maximal_residual_values:
    maximalResidualQA.implicitYCap=453∧
      maximalResidualQA.algebraicCap=68419∧
      maximalResidualH.implicitYCap=453∧
      maximalResidualH.algebraicCap=7774:=by
  norm_num [maximalResidualQA,maximalResidualH,TightParameters.implicitYCap,
    TightParameters.algebraicCap,TightParameters.kappa]
theorem maximal_residual_count_caps:
    maximalResidualQA.countCap=61761704341773∧
      maximalResidualH.countCap=7016664323606:=by
  norm_num [maximalResidualQA,maximalResidualH,TightParameters.countCap,
    TightParameters.tightNumerator,TightParameters.coreNumerator,
    TightParameters.aggregateCost,TightParameters.agreement,
    TightParameters.implicitYCap,TightParameters.algebraicCap,
    TightParameters.kappa,TightParameters.errors,TightParameters.gap,dot]
theorem maximal_residual_total_below_budget:
    96129765351580058+maximalResidualQA.countCap+
        maximalResidualH.countCap < 100000000000000000:=by
  rw [maximal_residual_count_caps.1,maximal_residual_count_caps.2]
  norm_num
end ProximityPrize.SubmissionLower.ContactTightSingularLedgerResearch

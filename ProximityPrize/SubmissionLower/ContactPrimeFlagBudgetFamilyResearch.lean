import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualZeroBudgetTransportResearch
import ProximityPrize.SubmissionLower.ContactFlagSymbolicTrapezoidResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6600FlagResearch
import ProximityPrize.SubmissionLower.ContactResidualSupportParametersResearch
namespace ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamilyResearch
open scoped Classical BigOperators
open ContactRegularComponentCover
open ContactFlagBezout6543Research
open ContactFlagSymbolicTrapezoidResearch
open ContactIdentityResidualZeroBudgetTransportResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactNearPencil6600ArithmeticResearch
open ContactNearPencil6600FlagResearch
open ContactResidualSupportParametersResearch
noncomputable section
variable {Omega:Type} [Field Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
structure PrimeFlagBudgetFamily (p q:FlagDegree) where
  zCost:RegularComponent Omega G T H → ℕ
  yzCost:RegularComponent Omega G T H → ℕ
  allCost:RegularComponent Omega G T H → ℕ
  primeBudget:∀ C:RegularComponent Omega G T H,
    PrimeFlagZeroBudget C.1 (fun r↦
      r.zOnly*zCost C+r.yz*yzCost C+r.all*allCost C)
  sum_zCost_le:(∑ C:RegularComponent Omega G T H,zCost C) ≤
    flagMixed p q unitZFlag
  sum_yzCost_le:(∑ C:RegularComponent Omega G T H,yzCost C) ≤
    flagMixed p q unitYZFlag
  sum_allCost_le:(∑ C:RegularComponent Omega G T H,allCost C) ≤
    flagMixed p q unitAllFlag
def PrimeFlagBudgetFamily.weightedCost
    {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
    (r:FlagDegree) (C:RegularComponent Omega G T H):ℕ:=
  r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C
theorem PrimeFlagBudgetFamily.sum_weightedCost_le
    {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
    (r:FlagDegree):
    (∑ C:RegularComponent Omega G T H,B.weightedCost r C) ≤
      flagMixed p q r:=by
  calc
    (∑ C:RegularComponent Omega G T H,B.weightedCost r C)=
        r.zOnly*(∑ C:RegularComponent Omega G T H,B.zCost C)+
        r.yz*(∑ C:RegularComponent Omega G T H,B.yzCost C)+
        r.all*(∑ C:RegularComponent Omega G T H,B.allCost C):=by
      simp only [PrimeFlagBudgetFamily.weightedCost,
        Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ r.zOnly*flagMixed p q unitZFlag+
        r.yz*flagMixed p q unitYZFlag+
        r.all*flagMixed p q unitAllFlag:=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.mul_le_mul_left r.zOnly B.sum_zCost_le)
          (Nat.mul_le_mul_left r.yz B.sum_yzCost_le))
        (Nat.mul_le_mul_left r.all B.sum_allCost_le)
    _=flagMixed p q r:=(flagMixed_projection_decomposition p q r).symm
theorem PrimeFlagBudgetFamily.weightedCost_residualAgreementFlag
    {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
    (C:RegularComponent Omega G T H) (d:ℕ):
    B.weightedCost (residualAgreementFlag d) C=
      d*B.weightedCost agreementDirection6600 C+
        B.weightedCost unitYZFlag C:=by
  rw [residualAgreementFlag_eq_affine]
  simp only [PrimeFlagBudgetFamily.weightedCost,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  ring
theorem PrimeFlagBudgetFamily.weightedCost_supportResidualAgreementFlag
    {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
    (support:ResidualSupportParameters)
    (C:RegularComponent Omega G T H) (d:ℕ):
    B.weightedCost (support.residualAgreementFlag d) C=
      d*B.weightedCost support.agreementDirection C+
        B.weightedCost unitYZFlag C:=by
  simp only [ResidualSupportParameters.residualAgreementFlag,
    ResidualSupportParameters.agreementDirection,
    PrimeFlagBudgetFamily.weightedCost,unitYZFlag]
  ring
theorem flagMixed_supportResidualAgreement_direction
    (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
    flagMixed p (support.residualAgreementFlag d) support.agreementDirection=
      d*flagMixed p support.agreementDirection support.agreementDirection+
        flagMixed p support.agreementDirection unitYZFlag:=by
  simp [flagMixed,ResidualSupportParameters.residualAgreementFlag,
    ResidualSupportParameters.agreementDirection,unitYZFlag]
  ring
theorem flagMixed_supportResidualAgreement_unit
    (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
    flagMixed p (support.residualAgreementFlag d) unitYZFlag=
      d*flagMixed p support.agreementDirection unitYZFlag+
        flagMixed p unitYZFlag unitYZFlag:=by
  simp [flagMixed,ResidualSupportParameters.residualAgreementFlag,
    ResidualSupportParameters.agreementDirection,unitYZFlag]
  ring
theorem flagMixed_supportResidualAgreement_z
    (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
    flagMixed p (support.residualAgreementFlag d) unitZFlag=
      d*flagMixed p support.agreementDirection unitZFlag+
        flagMixed p unitYZFlag unitZFlag:=by
  simp [flagMixed,ResidualSupportParameters.residualAgreementFlag,
    ResidualSupportParameters.agreementDirection,unitYZFlag,unitZFlag]
  ring
theorem flagMixed_supportResidualAgreement_all
    (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
    flagMixed p (support.residualAgreementFlag d) unitAllFlag=
      d*flagMixed p support.agreementDirection unitAllFlag+
        flagMixed p unitYZFlag unitAllFlag:=by
  simp [flagMixed,ResidualSupportParameters.residualAgreementFlag,
    ResidualSupportParameters.agreementDirection,unitYZFlag,unitAllFlag]
  ring
theorem flagMixed_residualAgreement_direction
    (p:FlagDegree) (d:ℕ):
    flagMixed p (residualAgreementFlag d) agreementDirection6600=
      d*flagMixed p agreementDirection6600 agreementDirection6600+
        flagMixed p agreementDirection6600 unitYZFlag:=by
  rw [residualAgreementFlag_eq_affine]
  simp [flagMixed,unitYZFlag,agreementDirection6600]
  ring
theorem flagMixed_residualAgreement_unit
    (p:FlagDegree) (d:ℕ):
    flagMixed p (residualAgreementFlag d) unitYZFlag=
      d*flagMixed p agreementDirection6600 unitYZFlag+
        flagMixed p unitYZFlag unitYZFlag:=by
  rw [residualAgreementFlag_eq_affine]
  simp [flagMixed,unitYZFlag,agreementDirection6600]
  ring
theorem flagMixed_residualAgreement_z
    (p:FlagDegree) (d:ℕ):
    flagMixed p (residualAgreementFlag d) unitZFlag=
      d*flagMixed p agreementDirection6600 unitZFlag+
        flagMixed p unitYZFlag unitZFlag:=by
  rw [residualAgreementFlag_eq_affine]
  simp [flagMixed,unitYZFlag,unitZFlag,agreementDirection6600]
  ring
theorem flagMixed_residualAgreement_all
    (p:FlagDegree) (d:ℕ):
    flagMixed p (residualAgreementFlag d) unitAllFlag=
      d*flagMixed p agreementDirection6600 unitAllFlag+
        flagMixed p unitYZFlag unitAllFlag:=by
  rw [residualAgreementFlag_eq_affine]
  simp [flagMixed,unitYZFlag,unitAllFlag,agreementDirection6600]
  ring
end
end ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamilyResearch

import ProximityPrize.SubmissionLower.CJ
import ProximityPrize.SubmissionLower.I
namespace ProximityPrize.SubmissionLower.ContactTwoTailTangentCost6732Research
open ContactFlagBezout6543Research
open ContactPrimeFlagBudgetFamilyResearch
open ContactRegularComponentCover
open ContactTwoTailParameters6733Research
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
variable {G T1 H:MvPolynomial (Fin 3) Omega}
variable {flag tailFlag1:FlagDegree}
theorem yzCost_mul_le_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RegularComponent Omega G T1 H)
   (coefficient:ℕ) (hcoefficient:coefficient ≤ r.yz):
   coefficient*B.yzCost C ≤ B.weightedCost r C:=by
 unfold PrimeFlagBudgetFamily.weightedCost
 calc
   coefficient*B.yzCost C ≤ r.yz*B.yzCost C:=
     Nat.mul_le_mul_right (B.yzCost C) hcoefficient
   _ ≤ r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C:=by
     omega
theorem multiplicity_mul_yzCost_le_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RegularComponent Omega G T1 H)
   (multiplicity coefficient:ℕ) (hcoefficient:coefficient ≤ r.yz):
   multiplicity*(coefficient*B.yzCost C) ≤
     multiplicity*B.weightedCost r C:=
 Nat.mul_le_mul_left multiplicity
   (yzCost_mul_le_weightedCost B r C coefficient hcoefficient)
theorem yzCost_le_multiplicity_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RegularComponent Omega G T1 H)
   (multiplicity coefficient:ℕ) (hmultiplicity:1 ≤ multiplicity)
   (hcoefficient:coefficient ≤ r.yz):
   coefficient*B.yzCost C ≤ multiplicity*B.weightedCost r C:=by
 calc
   coefficient*B.yzCost C ≤ B.weightedCost r C:=
     yzCost_mul_le_weightedCost B r C coefficient hcoefficient
   _=1*B.weightedCost r C:=by simp
   _ ≤ multiplicity*B.weightedCost r C:=
     Nat.mul_le_mul_right (B.weightedCost r C) hmultiplicity
theorem errors_succ_le_secondTail_yz:
   errors+1 ≤ (tailFlag (w+2)).yz:=by
 decide
theorem tangentCost_le_secondTail_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (C:RegularComponent Omega G T1 H):
   (errors+1)*B.yzCost C ≤
     B.weightedCost (tailFlag (w+2)) C:=
 yzCost_mul_le_weightedCost B (tailFlag (w+2)) C (errors+1)
   errors_succ_le_secondTail_yz
theorem tangentCost_le_multiplicity_secondTail_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (C:RegularComponent Omega G T1 H) (multiplicity:ℕ)
   (hmultiplicity:1 ≤ multiplicity):
   (errors+1)*B.yzCost C ≤
     multiplicity*B.weightedCost (tailFlag (w+2)) C:=
 yzCost_le_multiplicity_weightedCost B (tailFlag (w+2)) C
   multiplicity (errors+1) hmultiplicity errors_succ_le_secondTail_yz
end
end ProximityPrize.SubmissionLower.ContactTwoTailTangentCost6732Research

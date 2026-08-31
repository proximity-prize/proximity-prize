import ProximityPrize.SubmissionLower.ContactTwoTailResultantMultiplicity6732Research
import ProximityPrize.SubmissionLower.ContactDelayedTailMultiplicityProvider6732Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailResultantProvider6732Research
open scoped Classical BigOperators
open ContactFlagBezout6543Research ContactRegularComponentCover
open ContactPrimeFlagBudgetFamilyResearch
open ContactFlagSymbolicTrapezoidResearch
open ContactTwoTailResultantMultiplicity6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
structure RegularComponentWeightedInertiaResultantCertificate
    (B:PrimeFlagBudgetFamily
      (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
    (multiplicity:RegularComponent Omega G T H → ℕ) where
  z:(∑ C,multiplicity C*B.zCost C) ≤
    flagMixed surfaceFlag firstTailFlag unitZFlag
  yz:(∑ C,multiplicity C*B.yzCost C) ≤
    flagMixed surfaceFlag firstTailFlag unitYZFlag
  all:(∑ C,multiplicity C*B.allCost C) ≤
    flagMixed surfaceFlag firstTailFlag unitAllFlag
theorem RegularComponentWeightedInertiaResultantCertificate.divisor_le
    (B:PrimeFlagBudgetFamily
      (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
    (multiplicity:RegularComponent Omega G T H → ℕ)
    (C:RegularComponentWeightedInertiaResultantCertificate B multiplicity):
    (∑ component,
      multiplicity component*B.weightedCost secondTailFlag component) ≤
        flagMixed surfaceFlag firstTailFlag secondTailFlag:=by
  have hz:=C.z
  have hyz:=C.yz
  have hall:=C.all
  calc
    (∑ component,
        multiplicity component*B.weightedCost secondTailFlag component)=
      secondTailFlag.zOnly*
          (∑ component,multiplicity component*B.zCost component)+
        secondTailFlag.yz*
          (∑ component,multiplicity component*B.yzCost component)+
        secondTailFlag.all*
          (∑ component,multiplicity component*B.allCost component):=by
      simp only [PrimeFlagBudgetFamily.weightedCost,
        Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,
        Nat.mul_left_comm]
    _ ≤ secondTailFlag.zOnly*
          flagMixed surfaceFlag firstTailFlag unitZFlag+
        secondTailFlag.yz*
          flagMixed surfaceFlag firstTailFlag unitYZFlag+
        secondTailFlag.all*
          flagMixed surfaceFlag firstTailFlag unitAllFlag:=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.mul_le_mul_left secondTailFlag.zOnly hz)
          (Nat.mul_le_mul_left secondTailFlag.yz hyz))
        (Nat.mul_le_mul_left secondTailFlag.all hall)
    _=flagMixed surfaceFlag firstTailFlag secondTailFlag:=
      (flagMixed_projection_decomposition
        surfaceFlag firstTailFlag secondTailFlag).symm
end
end ProximityPrize.SubmissionLower.ContactTwoTailResultantProvider6732Research

import ProximityPrize.SubmissionLower.ContactIdentityResidualZeroBudgetTransport
import ProximityPrize.SubmissionLower.ContactFlagSymbolicTrapezoid
import ProximityPrize.SubmissionLower.ContactNearPencil6600Arithmetic
import ProximityPrize.SubmissionLower.ContactResidualSupportParameters
namespace ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily

open scoped Classical BigOperators
open ContactRegularComponentCover
open ContactFlagBezout
open ContactFlagSymbolicTrapezoid
open ContactIdentityResidualZeroBudgetTransport
open ContactIdentityResidualGlobalFlag
open ContactNearPencil6600Arithmetic
open ContactResidualSupportParameters

noncomputable section

variable {Omega : Type} [Field Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}

structure PrimeFlagBudgetFamily (p q : FlagDegree) where
  zCost : RegularComponent Omega G T H → ℕ
  yzCost : RegularComponent Omega G T H → ℕ
  allCost : RegularComponent Omega G T H → ℕ
  primeBudget : ∀ C : RegularComponent Omega G T H,
    PrimeFlagZeroBudget C.1 (fun r ↦
      r.zOnly * zCost C + r.yz * yzCost C + r.all * allCost C)
  sum_zCost_le : (∑ C : RegularComponent Omega G T H, zCost C) ≤
    flagMixed p q unitZFlag
  sum_yzCost_le : (∑ C : RegularComponent Omega G T H, yzCost C) ≤
    flagMixed p q unitYZFlag
  sum_allCost_le : (∑ C : RegularComponent Omega G T H, allCost C) ≤
    flagMixed p q unitAllFlag

def PrimeFlagBudgetFamily.weightedCost
    {p q : FlagDegree} (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H) p q)
    (r : FlagDegree) (C : RegularComponent Omega G T H) : ℕ :=
  r.zOnly * B.zCost C + r.yz * B.yzCost C + r.all * B.allCost C

theorem PrimeFlagBudgetFamily.sum_weightedCost_le
    {p q : FlagDegree} (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H) p q)
    (r : FlagDegree) :
    (∑ C : RegularComponent Omega G T H, B.weightedCost r C) ≤
      flagMixed p q r := by
  calc
    (∑ C : RegularComponent Omega G T H, B.weightedCost r C) =
        r.zOnly * (∑ C : RegularComponent Omega G T H, B.zCost C) +
        r.yz * (∑ C : RegularComponent Omega G T H, B.yzCost C) +
        r.all * (∑ C : RegularComponent Omega G T H, B.allCost C) := by
      simp only [PrimeFlagBudgetFamily.weightedCost,
        Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ r.zOnly * flagMixed p q unitZFlag +
        r.yz * flagMixed p q unitYZFlag +
        r.all * flagMixed p q unitAllFlag :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.mul_le_mul_left r.zOnly B.sum_zCost_le)
          (Nat.mul_le_mul_left r.yz B.sum_yzCost_le))
        (Nat.mul_le_mul_left r.all B.sum_allCost_le)
    _ = flagMixed p q r := (flagMixed_projection_decomposition p q r).symm

end

end ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily

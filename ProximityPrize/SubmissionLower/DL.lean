import ProximityPrize.SubmissionLower.AN
import ProximityPrize.SubmissionLower.AM
namespace ProximityPrize.SubmissionLower.RCN033
open scoped Classical BigOperators
open RCN264 RCN095
open RCN237
open RCN343
open RCN338
noncomputable section
set_option autoImplicit false
variable {Base Omega:Type} [Field Base] [Field Omega]
local instance:DecidableEq Base:=Classical.decEq Base
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {surfaceFlag firstTailFlag:FlagDegree}
theorem regularComponentWeightedInertiaCertificate_of_active_channels
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   {zIndex uIndex:Type*} [Fintype zIndex] [Fintype uIndex]
   (zComponent:zIndex → RegularComponent Omega G T H)
   (uComponent:uIndex → RegularComponent Omega G T H)
   (zRewrite:(∑ C,multiplicity C*B.zCost C)=
     ∑ a:zIndex,multiplicity (zComponent a)*B.zCost (zComponent a))
   (uRewrite:(∑ C,multiplicity C*B.yzCost C)=
     ∑ a:uIndex,multiplicity (uComponent a)*B.yzCost (uComponent a))
   (zChannel:WeightedGroupedResultantChannel (Base:=Base)
     (fun a↦multiplicity (zComponent a))
     (fun a↦B.zCost (zComponent a))
     (flagMixed surfaceFlag firstTailFlag unitZFlag))
   (uChannel:WeightedGroupedResultantChannel (Base:=Base)
     (fun a↦multiplicity (uComponent a))
     (fun a↦B.yzCost (uComponent a))
     (flagMixed surfaceFlag firstTailFlag unitYZFlag))
   (allChannel:WeightedGroupedResultantChannel (Base:=Base) multiplicity
     B.allCost (flagMixed surfaceFlag firstTailFlag unitAllFlag)):
   RegularComponentWeightedInertiaResultantCertificate B multiplicity where
 z:=by
   rw [zRewrite]
   exact zChannel.sum_mul_cost_le
 yz:=by
   rw [uRewrite]
   exact uChannel.sum_mul_cost_le
 all:=allChannel.sum_mul_cost_le
end
end ProximityPrize.SubmissionLower.RCN033

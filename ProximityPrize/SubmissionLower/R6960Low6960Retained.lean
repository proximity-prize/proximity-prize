import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.R6960Low6960FatContacts
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily
import ProximityPrize.SubmissionLower.Final50Price

set_option Elab.async false

-- merged module R6960Low6960Fat
section Merged_R6960Low6960Fat

-- merged module ModelExactPole
section Merged_ModelExactPole

set_option Elab.async false
namespace ModelExactPole
noncomputable section
open P1 (I K node)
open K1_13 (Geom embed extend)
open Polynomial
open scoped Polynomial






































































end
end ModelExactPole

end Merged_ModelExactPole

-- merged module R6960Low6960Primary
section Merged_R6960Low6960Primary

noncomputable section
set_option Elab.async false
namespace Lower6960.Low
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox Contact)
open Wide50EulerPrimary (primary_family sourceRank layerNeed)
open scoped Polynomial




































end Lower6960.Low

end
end Merged_R6960Low6960Primary

-- merged module R6960Low6960Fat
section Merged_R6960Low6960Fat


set_option Elab.async false
section
namespace Low6960Fat
noncomputable section
open K1 K1_13
open K1_13_4 hiding firstOrder secondOrder firstCut secondCut mixedWeight Necessary MixedOrder PairOrders CommonPair
open P0_9_4 (clear_denominators)
open scoped Polynomial BigOperators
open P3_6_4 (eval_cleared order_cleared)
















































end
end Low6960Fat
end


namespace Lower6960.Low
open K1_13 (extend)













end Lower6960.Low

end Merged_R6960Low6960Fat

end Merged_R6960Low6960Fat

-- merged module R6960Low6960Order
section Merged_R6960Low6960Order

-- merged module R6960Low6960Profile
section Merged_R6960Low6960Profile

set_option Elab.async false

namespace Lower6960.Low
open P3 (I K node)
open K1_13 (Row Shape InBox shape OrderAt extend)
open scoped Polynomial BigOperators




















end Lower6960.Low

end Merged_R6960Low6960Profile

-- merged module R6960Low6960Order
section Merged_R6960Low6960Order
set_option Elab.async false
namespace Low6960Order
noncomputable section
open K1_13 (Geom Row shape InBox Contact)
open P3 (I K)

















end
end Low6960Order
section
namespace Low6960OrderProof
noncomputable section
open P3 (I K)

open K1_13 (Row InBox shape Contact)





end
end Low6960OrderProof
end
section
namespace Low6960OrderProof
noncomputable section
open Polynomial
open P3 (I K node)



open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)

























































































































end
end Low6960OrderProof
end
section
set_option maxRecDepth 12000
namespace Low6960OrderProof_1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (I K node)



open K1_13 (Geom embed Row jet Contact)
open K1_13_3_1 (line)
open scoped BigOperators
open K1_13_3_1 (eval_line line_contacts_zero)
open K1_13_3_1 (order_of_locator_lines)






















































































































end
end Low6960OrderProof_1
end
section
namespace Low6960OrderProof_2
noncomputable section
open Polynomial

open K1_13 (Geom embed extend Row Shape shape InBox indexDegree)
open P0_9_3_2 (translateTop topHasse topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order topHasse_zero exact_hasse_not_dvd)























































































end
end Low6960OrderProof_2
end
section
namespace Low6960OrderProof_3
noncomputable section
open Polynomial
open P3 (I K node)


open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open P0_9_3 (jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor linearFactor_ne linearFactor_degree divide_specialization support_linear_mul)
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false

























































































































































































































end
end Low6960OrderProof_3
end
namespace Low6960Order
noncomputable section
open K1_13 (Row shape)
open P3 (K)
open scoped Polynomial





































end
end Low6960Order

end Merged_R6960Low6960Order

end Merged_R6960Low6960Order

-- merged module R6960Low6960Retained
section Merged_R6960Low6960Retained

-- merged module Final50PriceLayer
section Merged_Final50PriceLayer

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Final50PriceLayer
open K1_13 (Shape)
open K1_13_8 (zeroShape zeroMass fastRemaining)
open Final50Price (remaining symbolCount)
open P0_9_8 (symbol_count)
open scoped BigOperators



def layerTerm (r y : Shape) (L i : ℕ) : ℕ :=
  remaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j)


def availableMass (r y : Shape) (L : ℕ) : ℕ :=
  if r.j = 0 then L * symbolCount + zeroMass y.b y.j
  else K1_13_8.availableMass r y L

theorem remaining_anti {b j b' j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') :
    remaining b' j' ≤ remaining b j :=
  min_le_min_left _ (K1_13_8.remaining_anti hb hj)

















end Final50PriceLayer

end Merged_Final50PriceLayer

-- merged module R6960Low6960Retained
section Merged_R6960Low6960Retained

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Low6960Retained
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open P0_9_8 (symbol_count)

open Final50PriceLayer (layerTerm)
open scoped BigOperators
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty spend_le)
open P3_6_8_1 (sumBelow term mass_eq extend)







local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl




























































































































































































































end Low6960Retained

end Merged_R6960Low6960Retained

end Merged_R6960Low6960Retained

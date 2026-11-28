import ProximityPrize.SubmissionLower.Z6970CompanionCount
import ProximityPrize.SubmissionLower.Z6970H2307PriceDefs

set_option autoImplicit false
set_option Elab.async false

namespace Height2307Companion
open K1_13 (Shape InBox)
open Low6969Prices (physicalPriceOld)
open Low6969RetainedCut (contractedPrice)

theorem contract_le_old (x floor : Shape) (l : ℕ) :
    contractedPrice x floor l 179 ≤ physicalPriceOld x l := by
  apply le_trans _ (Low6969Monotone.physicalPrice_le_old x l 179)
  dsimp only [contractedPrice]
  split <;> split <;> first | exact le_rfl | exact min_le_left _ _ | exact (min_le_left _ _).trans (min_le_left _ _)

end Height2307Companion

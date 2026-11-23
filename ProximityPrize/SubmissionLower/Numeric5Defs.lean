import ProximityPrize.SubmissionLower.FiltrationLift
import ProximityPrize.SubmissionLower.Numeric6Defs
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_8
open CJ6 (VectorDots belowSucc belowZero block_rank_le rank_of_dots)
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l =>
  CJ6.Fast.vector b (buckets side q l) rfl rfl rfl (id (α := good side q l b) rfl)
end CJ6_8
end
section
namespace K1_13_2_3_5
open K1_13_2 K1_13_2_3
end K1_13_2_3_5
end

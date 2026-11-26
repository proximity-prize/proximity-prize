import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Anchor6966Local
import ProximityPrize.SubmissionLower.Low50Euler2367JetDegree
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.Low6966Retained
import ProximityPrize.SubmissionLower.Fat6966Defs
import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.RingHomShortcuts

set_option Elab.async false



-- merged module R6960Low6966RetainedFees
section Merged_R6960Low6966RetainedFees
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace LowProfile6966
open Finset
open K1_13 (Shape chart ceilDiv mixed32 shape)
open K1_13_8 (Valid)
open Low6966Fat (commonBox resultantBox)
open K1_13_8_4 (TotalLE)
open scoped BigOperators Classical






def lowDegreeCap : ℕ → ℕ
  | 3 => 27
  | 4 => 25
  | 5 => 22
  | 6 => 19
  | 7 => 14
  | 8 => 6
  | _ => 0






































































































































































































































































































































































































































































end LowProfile6966

end
end Merged_R6960Low6966RetainedFees

-- merged module R6960Low6966Width
section Merged_R6960Low6966Width

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace LowProfile6966
open Finset Polynomial
open P3 (K)
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Low6966Retained (Box)
open LowProfile6966 (lowDegreeCap)
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty)
open scoped Classical BigOperators

theorem degree_bound {r : Shape} (hr : Valid r) (hx : Box r) :
    r.b ≤ lowDegreeCap r.j := by
  have hjl : 3≤r.j := (Nat.mul_le_mul_left 3 hr.1).trans hr.2.1
  have hju := hx.2.1
  have hj : r.j=3 ∨ r.j=4 ∨ r.j=5 ∨ r.j=6 ∨ r.j=7 ∨ r.j=8 := by omega
  rcases hj with hj | hj | hj | hj | hj | hj <;> rw [hj] <;> simp only [lowDegreeCap]
  · exact hx.1
  · exact hx.2.2.1 (by omega)
  · exact hx.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.2 (by omega)


























end LowProfile6966

end
end Merged_R6960Low6966Width

-- merged module R6960Low6966Prices
section Merged_R6960Low6966Prices

set_option Elab.async false
namespace Low6966Prices
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial










abbrev layerNeed := LowProfile6966.need
abbrev symbolCount := Final50Price.symbolCount






























































































































































end
end Low6966Prices

end Merged_R6960Low6966Prices

-- merged module R6960Low6966Monotone
section Merged_R6960Low6966Monotone
set_option Elab.async false
section
namespace Low6966Monotone
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)




























































































end Low6966Monotone
end

namespace Low6966Monotone
open K1_13 (Shape)






























end Low6966Monotone

end Merged_R6960Low6966Monotone

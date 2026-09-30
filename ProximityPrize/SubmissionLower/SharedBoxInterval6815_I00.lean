import ProximityPrize.SubmissionLower.PortfolioRamifiedBoxes6815
import ProximityPrize.SubmissionLower.PortfolioUniqueCount6815
import ProximityPrize.SubmissionLower.SharedTreeCheck6815
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_I00
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨53,177,3543,6,8⟩
def valid : Box → Prop := Valid fixed 3599 3724 58 11 271000000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3599 3724 58 11 271000000000000000 7 0x32b00a100020d6d000000000000128d0002012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3599 3724 58 11 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3724 58 11 1*38+coefficient 3724 58 11 2*136)/2) 3724 58 11≤271000000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3724 58 11 1*38+coefficient 3724 58 11 2*136)/3) 3724 58 11≤271000000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3724 58 11 271000000000000000 := by decide +kernel
theorem identity : identityPrice 3724 58 11≤271000000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_I00

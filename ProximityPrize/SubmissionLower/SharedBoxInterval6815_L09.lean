import ProximityPrize.SubmissionLower.SharedBoxInterval6815_L08
import ProximityPrize.SubmissionLower.SharedTreeCheck6815
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L09
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨47,154,3146,5,7⟩
def valid : Box → Prop := Valid fixed 3261 3383 54 13 246600000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3261 3383 54 13 246600000000000000 11 0x130d00000000130d032b0000000000000069130d000000000000000015dd02ab006900000000000002ab0069130d032b00a10008000003ab0000000003ab00d90002084d0000000002ab0000000002ab00d9000207cd032b0000000003ab0002084d000200690002032b00a10d6d0000000000000000159d00d9016b0000000000d90000000000000f7d00d9016b128d00000000159d00000000159d01ab0000000200490000159d000201ab00690000000001ab00020069128d0006012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3261 3383 54 13 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3383 54 13 1*38+coefficient 3383 54 13 2*136)/2) 3383 54 13≤246600000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3383 54 13 1*38+coefficient 3383 54 13 2*136)/3) 3383 54 13≤246600000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3383 54 13 246600000000000000 := by decide +kernel
theorem identity : identityPrice 3383 54 13≤246600000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L09

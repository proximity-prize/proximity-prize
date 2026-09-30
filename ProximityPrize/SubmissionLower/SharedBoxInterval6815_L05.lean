import ProximityPrize.SubmissionLower.SharedBoxInterval6815_L04
import ProximityPrize.SubmissionLower.SharedTreeCheck6815
namespace ProximityPrize.SubmissionLower.SharedBoxInterval6815_L05
open PortfolioRamifiedBoxes6815 PortfolioCost6815 PortfolioUniqueCount6815 PortfolioSharedCount6815
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
def fixed : Degrees := ⟨46,153,3378,5,7⟩
def valid : Box → Prop := Valid fixed 3400 3516 57 12 257680000000000000
theorem covered : Covered valid initialBox :=
  SharedTreeCheck6815.covered_of_run fixed 3400 3516 57 12 257680000000000000 8 0x130d032b00000000130d00000000130d032b00a100000002084d0000000207cd032b000200a10d6d000000000000016b128d0000000200690002128d0002012b00a100020c6d022b _ (by decide +kernel)
theorem common : PortfolioChoice6815.Common fixed 3400 3516 57 12 := by
  unfold PortfolioChoice6815.Common Gates
  decide +kernel
theorem repeated : weightedPrice fixed (792*(coefficient 3516 57 12 1*38+coefficient 3516 57 12 2*136)/2) 3516 57 12≤257680000000000000 := by decide +kernel
theorem triple : weightedPrice fixed (792*(coefficient 3516 57 12 1*38+coefficient 3516 57 12 2*136)/3) 3516 57 12≤257680000000000000 := by decide +kernel
theorem linear : LinearChecks 3 119 775 3516 57 12 257680000000000000 := by decide +kernel
theorem identity : identityPrice 3516 57 12≤257680000000000000 := by decide +kernel
end ProximityPrize.SubmissionLower.SharedBoxInterval6815_L05
